package nsl-initiator

import ev "gitlab.inf.ethz.ch/arquintl/prototrace/event"
import "gitlab.inf.ethz.ch/arquintl/prototrace/label"
import ll "gitlab.inf.ethz.ch/arquintl/prototrace/labeled-library"
import lib "gitlab.inf.ethz.ch/arquintl/prototrace/labeled-library/library"
import "gitlab.inf.ethz.ch/arquintl/prototrace/labeling"
import . "gitlab.inf.ethz.ch/arquintl/prototrace/nsl-shared"
import . "gitlab.inf.ethz.ch/arquintl/prototrace/nsl-shared/library"
import p "gitlab.inf.ethz.ch/arquintl/prototrace/principal"
import tm "gitlab.inf.ethz.ch/arquintl/prototrace/term"
import tr "gitlab.inf.ethz.ch/arquintl/prototrace/trace"
import tman "gitlab.inf.ethz.ch/arquintl/prototrace/tracemanager"
import u "gitlab.inf.ethz.ch/arquintl/prototrace/usage"

type A struct {
	// identifier of A
	idA p.Principal
	// A's public key
	pkA lib.ByteString
	// A's secret key
	skA lib.ByteString
	// identifier of B
	idB p.Principal
	version uint // TODO is this ghost or not?
	// B's public key
	pkB lib.ByteString
	llib *ll.LabeledLibrary
	// TODO make these proper ghost field
	//@ skAT tm.Term
	//@ skBT tm.Term
}

/*@
pred (a *A) Mem(naT, nbT tm.Term) {
	acc(a) &&
	0 <= a.version && a.version <= 3 &&
	// full permission if not yet initialized, otherwise only 1/2:
	acc(lib.Mem(a.pkA), 1/2) && (a.version == 0 ==> acc(lib.Mem(a.pkA), 1/2)) &&
	lib.Size(a.pkA) == 32 &&
	lib.Mem(a.skA) &&
	lib.Size(a.skA) == 32 &&
	lib.Abs(a.skA) == tm.gamma(a.skAT) &&
	lib.Abs(a.pkA) == tm.gamma(tm.createPk(a.skAT)) &&
	a.llib.Mem() &&
	a.llib.Ctx() == GetNslContext() &&
	a.llib.LabelCtx() == GetNslLabeling() &&
	a.llib.Owner() == a.idA &&
	(GetNslLabeling()).IsSecretKey(a.llib.Snapshot(), p.principalId(a.idA), a.skAT, labeling.KeyTypePke(), NslKey) &&
	(a.version >= 1 ==>
		acc(lib.Mem(a.pkB), 1/2) &&
		lib.Size(a.pkB) == 32 &&
		lib.Abs(a.pkB) == tm.gamma(tm.createPk(a.skBT)) &&
		(GetNslLabeling()).IsPublicKey(a.llib.Snapshot(), p.principalId(a.idB), tm.createPk(a.skBT), a.skBT, labeling.KeyTypePke(), NslKey)) &&
	(a.version >= 2 ==>
		(GetNslLabeling()).IsLabeled(a.llib.Snapshot(), naT, label.Readers(set[p.Id]{ p.principalId(a.idA), p.principalId(a.idB) })) &&
		(a.llib.Snapshot()).eventOccurs(a.llib.Owner(), ev.NewEvent(FinishI, FinishIParams{ a.idA, a.idB, naT, nbT })) &&
		( 	// either a or b have been corrupted ...
			labeling.containsCorruptId((a.llib.Snapshot()).getCorruptIds(), set[p.Id]{ p.principalId(a.idA), p.principalId(a.idB) }) ||
			// ... or nbT is labeled to only be readable by a and b
            // this is stronger than `isMsg` as it excludes the possibility of restricting a
            // less secret value. This is necessary to invoke the secrecy lemma
			(GetNslLabeling()).IsLabeled(a.llib.Snapshot(), nbT, label.Readers(set[p.Id]{ p.principalId(a.idA), p.principalId(a.idB) })))) &&
	(a.version >= 3 ==>
		a.llib.Secrecy(naT, set[p.Id]{ p.principalId(a.idA), p.principalId(a.idB) }) &&
		a.llib.Secrecy(nbT, set[p.Id]{ p.principalId(a.idA), p.principalId(a.idB) }) &&
		a.llib.InjectiveAgreement(a.idA, a.idB, ev.NewEvent(FinishI, FinishIParams{ a.idA, a.idB, naT, nbT }), ev.NewEvent(Respond, RespondParams{ a.idA, a.idB, naT, nbT }), set[p.Id]{ p.principalId(a.idA), p.principalId(a.idB) }))
}

ghost
requires acc(a.Mem(naT, nbT), _)
pure func (a *A) Version(naT, nbT tm.Term) uint {
	return unfolding acc(a.Mem(naT, nbT), _) in a.version
}
@*/

//@ requires acc(l.LibMem(), 1/8)
//@ requires manager.Mem(GetNslContext(), initiator)
//@ requires defaultTerm == tm.zeroString(0)
//@ ensures  err == nil ==> a.Mem(defaultTerm, defaultTerm) && unfolding a.Mem(defaultTerm, defaultTerm) in a.version == 0 &&
//@ 			a.idA == initiator &&
//@				a.idB == responder &&
//@				manager == a.llib.Manager() &&
//@				// the following conjuncts are necessary such that monotonicity can be applied by the scheduler 
//@				// to the generated secret & public keys:
//@				old(manager.Trace(GetNslContext(), initiator)).isSuffix(a.llib.Snapshot()) &&
//@				(old(manager.ImmutableState(GetNslContext(), initiator)) == unfolding a.llib.Mem() in a.llib.manager.ImmutableState(GetNslContext(), initiator))
// TODO make manager ghost
// TODO remove `defaultTerm` as parameter and simply create it in the body
func initA(l *lib.LibraryState, initiator, responder p.Principal /*@, manager *tman.TraceManager, defaultTerm tm.Term @*/) (a *A, err error) {
	//@ ctx := GetNslContext()
	llib := ll.NewLabeledLibrary(l /*@, manager, ctx, initiator @*/)
	pk, sk, err /*@, skT @*/ := llib.GenerateKey(/*@ NslKey @*/)
	if err != nil {
		return nil, err
	}
	a = &A{initiator, pk, sk, responder, 0, nil, llib /*@, skT, defaultTerm @*/}
	//@ fold a.Mem(defaultTerm, defaultTerm)
	return a, nil
}

//@ requires a.Mem(defaultTerm, defaultTerm) && a.Version(defaultTerm, defaultTerm) == 1
//@ ensures  err == nil ==> a.Mem(naT, nbT) && a.Version(naT, nbT) == 3
func runA(a *A /*@, defaultTerm tm.Term @*/) (err error /*@, ghost naT tm.Term, ghost nbT tm.Term @*/) {
	//@ unfold a.Mem(defaultTerm, defaultTerm)

	//@ s0 := a.llib.Snapshot()
	//@ ctx := GetNslContext()
	//@ labelCtx := GetNslLabeling()
	//@ usageCtx := NslUsageContext{}

	// create na
	//@ ghost bothLabel := label.Readers(set[p.Id]{ p.principalId(a.idA), p.principalId(a.idB) })
	na, err := a.llib.CreateNonce(/*@ bothLabel, NslNonce, set[ev.EventType]{ Initiate, FinishI } @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	//@ s1 := a.llib.Snapshot()
	//@ naT = tm.random(lib.Abs(na), bothLabel, u.Nonce(NslNonce))
	// the following assert stmt is needed such that monotonicity will trigger for naT:
	//@ assert s1.nonceOccurs(naT, bothLabel, u.Nonce(NslNonce))

	/*@
	initEv := ev.NewEvent(Initiate, InitiateParams{ a.idA, a.idB, naT })
	fold ctx.eventInv(a.idA, initEv, s1)
	a.llib.TriggerEvent(initEv)
	s2 := a.llib.Snapshot()
	s0.isSuffixTransitive(s1, s2)
	a.llib.ApplyMonotonicityDflt(labelCtx)
	@*/

	// build & encrypt msg1
	msg1 := &Msg1{na, a.idA}
	msg1Data := MarshalMsg1(msg1)
	//@ msg1T := tm.tuple3(tm.integer32(1), naT, tm.stringTerm(a.idA))
	//@ justBLabel := label.Readers(set[p.Id]{ p.principalId(a.idB) })
	//@ labelCtx.Restrict(s2, naT, bothLabel, justBLabel)
	//@ labelCtx.IsMsgTuple3Create(s2, msg1T, justBLabel)
	ciphertext1, err := a.llib.Enc(msg1Data, a.pkB, a.skA /*@, msg1T, tm.createPk(a.skBT) @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// send msg1
	//@ ciphertext1T := tm.encrypt(msg1T, tm.createPk(a.skBT))
	err = a.llib.Send(a.idA, a.idB, ciphertext1 /*@, ciphertext1T @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	//@ s3 := a.llib.Snapshot()
	//@ s0.isSuffixTransitive(s2, s3)
	// receive msg2
	ciphertext2, err /*@, ciphertext2T @*/ := a.llib.Recv(a.idB, a.idA)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// decrypt msg2
	//@ a.llib.ApplyMonotonicityDflt(labelCtx)
	msg2Data, err := a.llib.Dec(ciphertext2, a.pkB, a.skA /*@, ciphertext2T, a.skAT, p.principalId(a.idA) @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// decompose msg2Data
	msg2, err := UnmarshalMsg2(msg2Data)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// check validity of msg2:
	if !lib.Compare(na, msg2.na) {
		return lib.NewError("na does not match") /*@, naT, nbT @*/
	}
	if a.idB != msg2.idB {
		return lib.NewError("idB does not match") /*@, naT, nbT @*/
	}
	//@ nbT = PatternPropertyMsg2(naT, tm.oneTerm(lib.Abs(msg2.nb)), tm.stringTerm(a.idB), a.skAT, ciphertext2T)
	// the following assert stmt is necessary to derive the assertion right after it:
	//@ assert tm.decryptB(tm.encryptB(tm.tuple4B(tm.integer32B(2), tm.gamma(naT), lib.Abs(msg2.nb), tm.gamma(tm.stringTerm(a.idB))), tm.createPkB(lib.Abs(a.skA))), lib.Abs(a.skA)) == tm.tuple4B(tm.integer32B(2), tm.gamma(naT), lib.Abs(msg2.nb), tm.gamma(tm.stringTerm(a.idB)))
	//@ assert lib.Abs(msg2.nb) == tm.gamma(nbT)
	
	//@ msg2T := tm.tuple4(tm.integer32(2), naT, nbT, tm.stringTerm(a.idB))
	//@ assert lib.Abs(msg2Data) == tm.gamma(msg2T)
	//@ assert ciphertext2T == tm.encrypt(msg2T, tm.createPk(a.skAT))

	// we have now reconstructed msg2T and thus Dec's postcondition yields:
	//@ assert labelCtx.IsMsg(s3, msg2T, label.Readers(set[p.Id]{ p.principalId(a.idA) }))

	/*
	if (len(msg2) <= 2*lib.NonceLength) {
		return lib.NewError("msg2 is too short")
	}
	receivedNa, rem := lib.sliceHelper(msg2, lib.NonceLength, writePerm)
	receivedNb, receivedIdB := lib.sliceHelper(rem, lib.NonceLength, writePerm)
	// this is the same as:
	receivedNa := msg2[:NonceLength]
	receivedNb := msg2[NonceLength:2*NonceLength]
	receivedIdB := msg2[2*NonceLength:]
	// or as:
	var receivedNa [NonceLength]byte
	copy(receivedNa[:], msg2[:NonceLength], perm(1)/2)
	var receivedNb = make([]byte, NonceLength)
	copy(receivedNb[:], msg2[NonceLength:2*NonceLength], perm(1)/2)
	var receivedIdB = make([]byte, len(msg2)-2*NonceLength)
	copy(receivedIdB[:], msg2[2*NonceLength:], perm(1)/2)

	// check validity of msg2:
	if !lib.Compare(na[:], receivedNa) {
		return lib.NewError("na does not match")
	}
	idBBytes := []byte(a.idB)
	// fold lib.Mem(idBBytes)
	if !lib.Compare(idBBytes, receivedIdB) {
		return lib.NewError("idB does not match")
	}
	*/

	/*@
	ghost var msg2Label label.SecrecyLabel
	ghost if labelCtx.IsPublishable(s3, msg2T) {
		msg2Label = label.Public()
	} else {
		msg2Label = label.Readers(set[p.Id]{ p.principalId(a.idA) })
	}

	labelCtx.IsMsgTuple4Resolve(s3, msg2T, msg2Label)

	ghost if (!msg2Label.IsPublic()) {
		// since msg2 is not publishable, we know now that `PkePred` must hold
		nonceAtSnapshot := a.llib.NonceOccursImpliesRandInv(nbT)

		// assert tr.pureRandInv(ctx, nbT, tr.getPrev(nonceAtSnapshot))
		// assert bothLabel == labelCtx.GetLabel(nbT)
		// we get nbT's label from `pureRandInv`. nbT's validity is deduced from msg2T's validity.
	} else {
		labelCtx.IsMsgTransitive(s3, nbT, label.Public(), bothLabel)
	}
	@*/

	/*@
	// facts after receiving msg2:
	corruptionOccurred := p.principalId(a.idA) in s3.getCorruptIds() ||
		p.principalId(a.idB) in s3.getCorruptIds()
	ghost if corruptionOccurred {
		assert labelCtx.IsPublishable(s3, nbT)
	} else {
		assert s3.nonceOccurs(nbT, label.Readers(set[p.Id]{ p.principalId(a.idA), p.principalId(a.idB) }), u.Nonce(NslNonce))
		assert s3.eventOccurs(a.idB, ev.NewEvent(Respond, RespondParams{ a.idA, a.idB, naT, nbT }))
	}
	@*/

	/*@
	finishIEv := ev.NewEvent(FinishI, FinishIParams{ a.idA, a.idB, naT, nbT })
	fold ctx.eventInv(a.idA, finishIEv, s3)
	a.llib.TriggerEvent(finishIEv)
	s4 := a.llib.Snapshot()
	s0.isSuffixTransitive(s3, s4)
	a.llib.ApplyMonotonicityDflt(labelCtx)
	@*/
	
	// build & encrypt msg3
	msg3 := &Msg3{ msg2.nb }
	msg3Data := MarshalMsg3(msg3)
	//@ msg3T := tm.tuple2(tm.integer32(3), nbT)
	//@ assert lib.Abs(msg3Data) == tm.gamma(msg3T)
	//@ labelCtx.Restrict(s4, nbT, bothLabel, justBLabel)
	//@ labelCtx.IsMsgTuple2Create(s4, msg3T, justBLabel)
	//@ usageCtx.ppredShowWitness(s4, "", msg3T, tm.createPk(a.skBT), a.idB, a.idA, naT)
	ciphertext3, err := a.llib.Enc(msg3Data, a.pkB, a.skA /*@, msg3T, tm.createPk(a.skBT) @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}

	// send msg3
	//@ ghost ciphertext3T := tm.encrypt(msg3T, tm.createPk(a.skBT))
	// the following assert stmt is needed:
	//@ assert labelCtx.IsPublishable(s4, ciphertext3T)
	err = a.llib.Send(a.idA, a.idB, ciphertext3 /*@, ciphertext3T @*/)
	if err == nil {
		lib.PrintInitiatorSuccess(na, msg2.nb)
	}
	//@ s5 := a.llib.Snapshot()
	//@ s0.isSuffixTransitive(s4, s5)
	//@ a.llib.ApplyMonotonicityDflt(labelCtx)
	a.version = 2
	// the following assert stmt is needed:
	//@ assert s4.eventOccurs(a.llib.Owner(), finishIEv)
	//@ fold a.Mem(naT, nbT)

	//@ a.proveSecurityProperties(naT, nbT)

	return err /*@, naT, nbT @*/
}
