package nslinitiator

//@ import ev "gitlab.inf.ethz.ch/arquintl/prototrace/event"
//@ import "gitlab.inf.ethz.ch/arquintl/prototrace/label"
import ll "gitlab.inf.ethz.ch/arquintl/prototrace/labeledlibrary"
import lib "gitlab.inf.ethz.ch/arquintl/prototrace/labeledlibrary/library"
//@ import "gitlab.inf.ethz.ch/arquintl/prototrace/labeling"
//@ import . "gitlab.inf.ethz.ch/arquintl/prototrace/nslshared"
import . "gitlab.inf.ethz.ch/arquintl/prototrace/nslshared/library"
import p "gitlab.inf.ethz.ch/arquintl/prototrace/principal"
//@ import tm "gitlab.inf.ethz.ch/arquintl/prototrace/term"
//@ import tr "gitlab.inf.ethz.ch/arquintl/prototrace/trace"
//@ import tman "gitlab.inf.ethz.ch/arquintl/prototrace/tracemanager"
//@ import u "gitlab.inf.ethz.ch/arquintl/prototrace/usage"

type A struct {
	// identifier of A
	IdA p.Principal
	// A's public key
	PkA lib.ByteString
	// A's secret key
	SkA lib.ByteString
	// identifier of B
	IdB p.Principal
	Version uint // TODO is this ghost or not?
	// B's public key
	PkB lib.ByteString
	llib *ll.LabeledLibrary
	// TODO make these proper ghost field
	//@ SkAT tm.Term
	//@ SkBT tm.Term
}

/*@
pred (a *A) Mem(naT, nbT tm.Term) {
	acc(a) &&
	0 <= a.Version && a.Version <= 3 &&
	// full permission if not yet initialized, otherwise only 1/2:
	acc(lib.Mem(a.PkA), 1/2) && (a.Version == 0 ==> acc(lib.Mem(a.PkA), 1/2)) &&
	lib.Size(a.PkA) == 32 &&
	lib.Mem(a.SkA) &&
	lib.Size(a.SkA) == 32 &&
	lib.Abs(a.SkA) == tm.gamma(a.SkAT) &&
	lib.Abs(a.PkA) == tm.gamma(tm.createPk(a.SkAT)) &&
	a.llib.Mem() &&
	a.llib.Ctx() == GetNslContext() &&
	a.llib.LabelCtx() == GetNslLabeling() &&
	a.llib.Owner() == a.IdA &&
	(GetNslLabeling()).IsSecretKey(a.llib.Snapshot(), p.principalId(a.IdA), a.SkAT, labeling.KeyTypePke(), NslKey) &&
	(a.Version >= 1 ==>
		acc(lib.Mem(a.PkB), 1/2) &&
		lib.Size(a.PkB) == 32 &&
		lib.Abs(a.PkB) == tm.gamma(tm.createPk(a.SkBT)) &&
		(GetNslLabeling()).IsPublicKey(a.llib.Snapshot(), p.principalId(a.IdB), tm.createPk(a.SkBT), a.SkBT, labeling.KeyTypePke(), NslKey)) &&
	(a.Version >= 2 ==>
		(GetNslLabeling()).IsLabeled(a.llib.Snapshot(), naT, label.Readers(set[p.Id]{ p.principalId(a.IdA), p.principalId(a.IdB) })) &&
		(a.llib.Snapshot()).eventOccurs(a.llib.Owner(), ev.NewEvent(FinishI, FinishIParams{ a.IdA, a.IdB, naT, nbT })) &&
		( 	// either a or b have been corrupted ...
			labeling.containsCorruptId((a.llib.Snapshot()).getCorruptIds(), set[p.Id]{ p.principalId(a.IdA), p.principalId(a.IdB) }) ||
			// ... or nbT is labeled to only be readable by a and b
            // this is stronger than `isMsg` as it excludes the possibility of restricting a
            // less secret value. This is necessary to invoke the secrecy lemma
			(GetNslLabeling()).IsLabeled(a.llib.Snapshot(), nbT, label.Readers(set[p.Id]{ p.principalId(a.IdA), p.principalId(a.IdB) })))) &&
	(a.Version >= 3 ==>
		a.llib.Secrecy(naT, set[p.Id]{ p.principalId(a.IdA), p.principalId(a.IdB) }) &&
		a.llib.Secrecy(nbT, set[p.Id]{ p.principalId(a.IdA), p.principalId(a.IdB) }) &&
		a.llib.InjectiveAgreement(a.IdA, a.IdB, ev.NewEvent(FinishI, FinishIParams{ a.IdA, a.IdB, naT, nbT }), ev.NewEvent(Respond, RespondParams{ a.IdA, a.IdB, naT, nbT }), set[p.Id]{ p.principalId(a.IdA), p.principalId(a.IdB) }))
}

ghost
requires acc(a.Mem(naT, nbT), _)
pure func (a *A) Vers(naT, nbT tm.Term) uint {
	return unfolding acc(a.Mem(naT, nbT), _) in a.Version
}
@*/

//@ requires acc(l.LibMem(), 1/8)
//@ requires manager.Mem(GetNslContext(), initiator)
//@ requires defaultTerm == tm.zeroString(0)
//@ ensures  err == nil ==> a.Mem(defaultTerm, defaultTerm) && unfolding a.Mem(defaultTerm, defaultTerm) in a.Version == 0 &&
//@ 			a.IdA == initiator &&
//@				a.IdB == responder &&
//@				manager == a.llib.Manager() &&
//@				// the following conjuncts are necessary such that monotonicity can be applied by the scheduler 
//@				// to the generated secret & public keys:
//@				old(manager.Trace(GetNslContext(), initiator)).isSuffix(a.llib.Snapshot()) &&
//@				(old(manager.ImmutableState(GetNslContext(), initiator)) == unfolding a.llib.Mem() in a.llib.manager.ImmutableState(GetNslContext(), initiator))
// TODO make manager ghost
// TODO remove `defaultTerm` as parameter and simply create it in the body
func InitA(l *lib.LibraryState, initiator, responder p.Principal /*@, manager *tman.TraceManager, defaultTerm tm.Term @*/) (a *A, err error) {
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

//@ requires a.Mem(defaultTerm, defaultTerm) && a.Vers(defaultTerm, defaultTerm) == 1
//@ ensures  err == nil ==> a.Mem(naT, nbT) && a.Vers(naT, nbT) == 3
func RunA(a *A /*@, defaultTerm tm.Term @*/) (err error /*@, ghost naT tm.Term, ghost nbT tm.Term @*/) {
	//@ unfold a.Mem(defaultTerm, defaultTerm)

	//@ s0 := a.llib.Snapshot()
	//@ ctx := GetNslContext()
	//@ labelCtx := GetNslLabeling()
	//@ usageCtx := NslUsageContext{}

	// create na
	//@ ghost bothLabel := label.Readers(set[p.Id]{ p.principalId(a.IdA), p.principalId(a.IdB) })
	na, err := a.llib.CreateNonce(/*@ bothLabel, NslNonce, set[ev.EventType]{ Initiate, FinishI } @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	//@ s1 := a.llib.Snapshot()
	//@ naT = tm.random(lib.Abs(na), bothLabel, u.Nonce(NslNonce))
	// the following assert stmt is needed such that monotonicity will trigger for naT:
	//@ assert s1.nonceOccurs(naT, bothLabel, u.Nonce(NslNonce))

	/*@
	initEv := ev.NewEvent(Initiate, InitiateParams{ a.IdA, a.IdB, naT })
	fold ctx.eventInv(a.IdA, initEv, s1)
	a.llib.TriggerEvent(initEv)
	s2 := a.llib.Snapshot()
	s0.isSuffixTransitive(s1, s2)
	a.llib.ApplyMonotonicityDflt(labelCtx)
	@*/

	// build & encrypt msg1
	msg1 := &Msg1{na, a.IdA}
	msg1Data := MarshalMsg1(msg1)
	//@ msg1T := tm.tuple3(tm.integer32(1), naT, tm.stringTerm(a.IdA))
	//@ justBLabel := label.Readers(set[p.Id]{ p.principalId(a.IdB) })
	//@ labelCtx.Restrict(s2, naT, bothLabel, justBLabel)
	//@ labelCtx.IsMsgTuple3Create(s2, msg1T, justBLabel)
	ciphertext1, err := a.llib.Enc(msg1Data, a.PkB, a.SkA /*@, msg1T, tm.createPk(a.SkBT) @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// send msg1
	//@ ciphertext1T := tm.encrypt(msg1T, tm.createPk(a.SkBT))
	err = a.llib.Send(a.IdA, a.IdB, ciphertext1 /*@, ciphertext1T @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	//@ s3 := a.llib.Snapshot()
	//@ s0.isSuffixTransitive(s2, s3)
	// receive msg2
	ciphertext2, err /*@, ciphertext2T @*/ := a.llib.Recv(a.IdB, a.IdA)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// decrypt msg2
	//@ a.llib.ApplyMonotonicityDflt(labelCtx)
	msg2Data, err := a.llib.Dec(ciphertext2, a.PkB, a.SkA /*@, ciphertext2T, a.SkAT, p.principalId(a.IdA) @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// decompose msg2Data
	msg2, err := UnmarshalMsg2(msg2Data)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// check validity of msg2:
	if !lib.Compare(na, msg2.Na) {
		return lib.NewError("na does not match") /*@, naT, nbT @*/
	}
	if a.IdB != msg2.IdB {
		return lib.NewError("idB does not match") /*@, naT, nbT @*/
	}
	//@ nbT = PatternPropertyMsg2(naT, tm.oneTerm(lib.Abs(msg2.Nb)), tm.stringTerm(a.IdB), a.SkAT, ciphertext2T)
	// the following assert stmt is necessary to derive the assertion right after it:
	//@ assert tm.decryptB(tm.encryptB(tm.tuple4B(tm.integer32B(2), tm.gamma(naT), lib.Abs(msg2.Nb), tm.gamma(tm.stringTerm(a.IdB))), tm.createPkB(lib.Abs(a.SkA))), lib.Abs(a.SkA)) == tm.tuple4B(tm.integer32B(2), tm.gamma(naT), lib.Abs(msg2.Nb), tm.gamma(tm.stringTerm(a.IdB)))
	//@ assert lib.Abs(msg2.Nb) == tm.gamma(nbT)
	
	//@ msg2T := tm.tuple4(tm.integer32(2), naT, nbT, tm.stringTerm(a.IdB))
	//@ assert lib.Abs(msg2Data) == tm.gamma(msg2T)
	//@ assert ciphertext2T == tm.encrypt(msg2T, tm.createPk(a.SkAT))

	// we have now reconstructed msg2T and thus Dec's postcondition yields:
	//@ assert labelCtx.IsMsg(s3, msg2T, label.Readers(set[p.Id]{ p.principalId(a.IdA) }))

	/*@
	ghost var msg2Label label.SecrecyLabel
	ghost if labelCtx.IsPublishable(s3, msg2T) {
		msg2Label = label.Public()
	} else {
		msg2Label = label.Readers(set[p.Id]{ p.principalId(a.IdA) })
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
	corruptionOccurred := p.principalId(a.IdA) in s3.getCorruptIds() ||
		p.principalId(a.IdB) in s3.getCorruptIds()
	ghost if corruptionOccurred {
		assert labelCtx.IsPublishable(s3, nbT)
	} else {
		assert s3.nonceOccurs(nbT, label.Readers(set[p.Id]{ p.principalId(a.IdA), p.principalId(a.IdB) }), u.Nonce(NslNonce))
		assert s3.eventOccurs(a.IdB, ev.NewEvent(Respond, RespondParams{ a.IdA, a.IdB, naT, nbT }))
	}
	@*/

	/*@
	finishIEv := ev.NewEvent(FinishI, FinishIParams{ a.IdA, a.IdB, naT, nbT })
	fold ctx.eventInv(a.IdA, finishIEv, s3)
	a.llib.TriggerEvent(finishIEv)
	s4 := a.llib.Snapshot()
	s0.isSuffixTransitive(s3, s4)
	a.llib.ApplyMonotonicityDflt(labelCtx)
	@*/
	
	// build & encrypt msg3
	msg3 := &Msg3{ msg2.Nb }
	msg3Data := MarshalMsg3(msg3)
	//@ msg3T := tm.tuple2(tm.integer32(3), nbT)
	//@ assert lib.Abs(msg3Data) == tm.gamma(msg3T)
	//@ labelCtx.Restrict(s4, nbT, bothLabel, justBLabel)
	//@ labelCtx.IsMsgTuple2Create(s4, msg3T, justBLabel)
	//@ usageCtx.ppredShowWitness(s4, "", msg3T, tm.createPk(a.SkBT), a.IdB, a.IdA, naT)
	ciphertext3, err := a.llib.Enc(msg3Data, a.PkB, a.SkA /*@, msg3T, tm.createPk(a.SkBT) @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}

	// send msg3
	//@ ghost ciphertext3T := tm.encrypt(msg3T, tm.createPk(a.SkBT))
	// the following assert stmt is needed:
	//@ assert labelCtx.IsPublishable(s4, ciphertext3T)
	err = a.llib.Send(a.IdA, a.IdB, ciphertext3 /*@, ciphertext3T @*/)
	if err == nil {
		lib.PrintInitiatorSuccess(na, msg2.Nb)
	}
	//@ s5 := a.llib.Snapshot()
	//@ s0.isSuffixTransitive(s4, s5)
	//@ a.llib.ApplyMonotonicityDflt(labelCtx)
	a.Version = 2
	// the following assert stmt is needed:
	//@ assert s4.eventOccurs(a.llib.Owner(), finishIEv)
	//@ fold a.Mem(naT, nbT)

	//@ a.proveSecurityProperties(naT, nbT)

	return err /*@, naT, nbT @*/
}
