package nslresponder

//@ import ev "gitlab.inf.ethz.ch/arquintl/prototrace/event"
//@ import fa "gitlab.inf.ethz.ch/arquintl/prototrace/forall"
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

type B struct {
	// identifier of B
	IdB p.Principal
	// B's public key
	PkB []byte
	// B's secret key
	SkB []byte
	// identifier of A
	IdA p.Principal
	Version uint
	// A's public key
	PkA []byte
	llib *ll.LabeledLibrary
	// TODO make these proper ghost field
	//@ SkAT tm.Term
	//@ SkBT tm.Term
}

/*@
pred (b *B) Mem(naT, nbT tm.Term) {
	acc(b) &&
	0 <= b.Version && b.Version <= 3 &&
	// full permission if not yet initialized, otherwise only 1/2:
	acc(lib.Mem(b.PkB), 1/2) && (b.Version == 0 ==> acc(lib.Mem(b.PkB), 1/2)) &&
	lib.Size(b.PkB) == 32 &&
	lib.Mem(b.SkB) &&
	lib.Size(b.SkB) == 32 &&
	lib.Abs(b.SkB) == tm.gamma(b.SkBT) &&
	lib.Abs(b.PkB) == tm.gamma(tm.createPk(b.SkBT)) &&
	b.llib.Mem() &&
	b.llib.Ctx() == GetNslContext() &&
	b.llib.LabelCtx() == GetNslLabeling() &&
	b.llib.Owner() == b.IdB &&
	(GetNslLabeling()).IsSecretKey(b.llib.Snapshot(), p.principalId(b.IdB), b.SkBT, labeling.KeyTypePke(), NslKey) &&
	(b.Version >= 1 ==>
		acc(lib.Mem(b.PkA), 1/2) &&
		lib.Size(b.PkA) == 32 &&
		lib.Abs(b.PkA) == tm.gamma(tm.createPk(b.SkAT)) &&
		(GetNslLabeling()).IsPublicKey(b.llib.Snapshot(), p.principalId(b.IdA), tm.createPk(b.SkAT), b.SkAT, labeling.KeyTypePke(), NslKey)) &&
	(b.Version >= 2 ==>
		(GetNslLabeling()).IsLabeled(b.llib.Snapshot(), nbT, label.Readers(set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) })) &&
		(b.llib.Snapshot()).eventOccurs(b.llib.Owner(), ev.NewEvent(FinishR, FinishRParams{ b.IdA, b.IdB, naT, nbT })) &&
		(	// either a or b have been corrupted ...
			labeling.containsCorruptId((b.llib.Snapshot()).getCorruptIds(), set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) }) ||
			// ... or naT is labeled to only be readable by a and b
            // this is stronger than `isMsg` as it excludes the possibility of restricting a
            // less secret value. This is necessary to invoke the secrecy lemma
			(GetNslLabeling()).IsLabeled(b.llib.Snapshot(), naT, label.Readers(set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) })))) &&
	(b.Version >= 3 ==>
		b.llib.Secrecy(naT, set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) }) &&
		b.llib.Secrecy(nbT, set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) }) &&
		b.llib.InjectiveAgreement(b.IdB, b.IdA, ev.NewEvent(FinishR, FinishRParams{ b.IdA, b.IdB, naT, nbT }), ev.NewEvent(FinishI, FinishIParams{ b.IdA, b.IdB, naT, nbT }), set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) }))
}

ghost
requires acc(b.Mem(naT, nbT), _)
pure func (b *B) Vers(naT, nbT tm.Term) uint {
	return unfolding acc(b.Mem(naT, nbT), _) in b.Version
}
@*/

//@ requires acc(l.LibMem(), 1/8)
//@ requires manager.Mem(GetNslContext(), responder)
//@ requires defaultTerm == tm.zeroString(0)
//@ ensures  err == nil ==> b.Mem(defaultTerm, defaultTerm) && unfolding b.Mem(defaultTerm, defaultTerm) in b.Version == 0 &&
//@				b.IdA == initiator &&
//@				b.IdB == responder &&
//@				manager == b.llib.Manager() &&
//@				// the following conjuncts are necessary such that monotonicity can be applied by the scheduler 
//@				// to the generated secret & public keys:
//@				old(manager.Trace(GetNslContext(), responder)).isSuffix(b.llib.Snapshot()) &&
//@				(old(manager.ImmutableState(GetNslContext(), responder)) == unfolding b.llib.Mem() in b.llib.manager.ImmutableState(GetNslContext(), responder))
// TODO make manager ghost
// TODO remove `defaultTerm` as parameter and simply create it in the body
func InitB(l *lib.LibraryState, initiator, responder p.Principal /*@, manager *tman.TraceManager, defaultTerm tm.Term @*/) (b *B, err error) {
	//@ ctx := GetNslContext()
	llib := ll.NewLabeledLibrary(l /*@, manager, ctx, responder @*/)
	pk, sk, err /*@, skT @*/ := llib.GenerateKey(/*@ NslKey @*/)
	if err != nil {
		return nil, err
	}
	b = &B{responder, pk, sk, initiator, 0, nil, llib /*@, defaultTerm, skT @*/}
	//@ fold b.Mem(defaultTerm, defaultTerm)
	return b, nil
}

//@ requires b.Mem(defaultTerm, defaultTerm) && b.Vers(defaultTerm, defaultTerm) == 1
//@ ensures  err == nil ==> b.Mem(naT, nbT) && b.Vers(naT, nbT) == 3
func RunB(b *B /*@, defaultTerm tm.Term @*/) (err error /*@, ghost naT tm.Term, ghost nbT tm.Term @*/) {
	//@ unfold b.Mem(defaultTerm, defaultTerm)
	//@ s0 := b.llib.Snapshot()
	//@ ctx := GetNslContext()
	//@ labelCtx := GetNslLabeling()
	//@ usageCtx := NslUsageContext{}

	// receive msg1
	ciphertext1, err /*@, ciphertext1T @*/ := b.llib.Recv(b.IdA, b.IdB)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// decrypt msg1
	msg1Data, err := b.llib.Dec(ciphertext1, b.PkA, b.SkB /*@, ciphertext1T, b.SkBT, p.principalId(b.IdB) @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// decompose msg1Data
	msg1, err := UnmarshalMsg1(msg1Data)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// check validity of msg1:
	if b.IdA != msg1.IdA {
		return lib.NewError("idA does not match") /*@, naT, nbT @*/
	}
	
	/*@
	naT = PatternPropertyMsg1(tm.oneTerm(lib.Abs(msg1.Na)), tm.stringTerm(b.IdA), b.SkBT, ciphertext1T)
	// the following assert stmt is necessary to derive the assertion right after it:
	assert tm.decryptB(tm.encryptB(tm.tuple3B(tm.integer32B(1), lib.Abs(msg1.Na), tm.gamma(tm.stringTerm(b.IdA))), tm.createPkB(lib.Abs(b.SkB))), lib.Abs(b.SkB)) == tm.tuple3B(tm.integer32B(1), lib.Abs(msg1.Na), tm.gamma(tm.stringTerm(b.IdA)))
	assert lib.Abs(msg1.Na) == tm.gamma(naT)
	msg1T := tm.tuple3(tm.integer32(1), naT, tm.stringTerm(b.IdA))
	
	bothLabel := label.Readers(set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) })
	ghost var msg1Label label.SecrecyLabel
	ghost if labelCtx.IsPublishable(s0, msg1T) {
		msg1Label = label.Public()
	} else {
		msg1Label = label.Readers(set[p.Id]{ p.principalId(b.IdB) })
	}

	labelCtx.IsMsgTuple3Resolve(s0, msg1T, msg1Label)

	ghost if (!msg1Label.IsPublic()) {
		assert s0.nonceOccurs(naT, bothLabel, u.Nonce(NslNonce))
		// since msg1 is not publishable, we know now that `PkePred` must hold
		nonceAtSnapshot := b.llib.NonceOccursImpliesRandInv(naT)

		// assert tr.randInv(ctx, naT, tr.getPrev(nonceAtSnapshot))
		// assert labelCtx.IsLabeled(s0, naT, label.Readers(set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) }))
	} else {
		labelCtx.IsMsgTransitive(s0, naT, label.Public(), bothLabel)
	}
	@*/

	/*@
	// facts after receiving msg1:
	assert labelCtx.IsMsg(s0, naT, bothLabel)
	assert labelCtx.IsPublishable(s0, naT) || s0.nonceOccurs(naT, bothLabel, u.Nonce(NslNonce))
	@*/

	// create nb
	nb, err := b.llib.CreateNonce(/*@ bothLabel, NslNonce, set[ev.EventType]{ Respond, FinishR } @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	//@ s1 := b.llib.Snapshot()
	//@ nbT = tm.random(lib.Abs(nb), bothLabel, u.Nonce(NslNonce))
	// the following assert stmt is needed such that monotonicity will trigger for nbT:
	//@ assert s1.OnlyNonceOccurs(nbT)

	/*@
	respEv := ev.NewEvent(Respond, RespondParams{ b.IdA, b.IdB, naT, nbT })
	fold ctx.eventInv(b.IdB, respEv, s1)
	b.llib.TriggerEvent(respEv)
	s2 := b.llib.Snapshot()
	s0.isSuffixTransitive(s1, s2)
	assert s2.eventOccurs(b.IdB, ev.NewEvent(Respond, RespondParams{ b.IdA, b.IdB, naT, nbT }))
	@*/

	// build & encrypt msg2
	msg2 := &Msg2{msg1.Na, nb, b.IdB}
	msg2Data := MarshalMsg2(msg2)
	//@ msg2T := tm.tuple4(tm.integer32(2), naT, nbT, tm.stringTerm(b.IdB))
	//@ assert lib.Abs(msg2Data) == tm.gamma(msg2T)
	//@ b.llib.ApplyMonotonicityDflt(labelCtx)
	//@ justALabel := label.Readers(set[p.Id]{ p.principalId(b.IdA) })
	//@ labelCtx.Restrict(s2, naT, bothLabel, justALabel)
	//@ labelCtx.IsMsgTuple4Create(s2, msg2T, justALabel)
	ciphertext2, err := b.llib.Enc(msg2Data, b.PkA, b.SkB /*@, msg2T, tm.createPk(b.SkAT) @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// send msg2
	//@ ciphertext2T := tm.encrypt(msg2T, tm.createPk(b.SkAT))
	err = b.llib.Send(b.IdB, b.IdA, ciphertext2 /*@, ciphertext2T @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	//@ s3 := b.llib.Snapshot()
	//@ s0.isSuffixTransitive(s2, s3)
	// receive msg3
	ciphertext3, err /*@, ciphertext3T @*/ := b.llib.Recv(b.IdA, b.IdB)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// decrypt msg3
	//@ b.llib.ApplyMonotonicityDflt(labelCtx)
	// the following assert stmt is necessary to derive Dec's precondition:
	//@ assert labelCtx.IsPrivateDecKey(s3, p.principalId(b.IdB), b.SkBT, NslKey)
	msg3Data, err := b.llib.Dec(ciphertext3, b.PkA, b.SkB /*@, ciphertext3T, b.SkBT, p.principalId(b.IdB) @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// decompose msg3Data
	msg3, err := UnmarshalMsg3(msg3Data)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// check validity of msg3 (assuming no corruption, the equality of receivedNa and receivedIdA can be deduced (see below)):
	if !lib.Compare(nb, msg3.Nb) {
		return lib.NewError("nb does not match") /*@, naT, nbT @*/
	}

	/*@
	PatternPropertyMsg3(nbT, b.SkBT, ciphertext3T)
	msg3T := tm.tuple2(tm.integer32(3), nbT)
	// PatternPropertyMsg3 gives us uniqueness for ciphertext3T:
	assert ciphertext3T == tm.encrypt(msg3T, tm.createPk(b.SkBT))

	ghost var msg3Label label.SecrecyLabel
	ghost if labelCtx.IsPublishable(s3, msg3T) {
		msg3Label = label.Public()
	} else {
		msg3Label = label.Readers(set[p.Id]{ p.principalId(b.IdB) })
	}

	ghost if (msg3Label.IsPublic()) {
		// corruption must have occurred because plaintext is publishable and contains nbT
		labelCtx.IsMsgTuple2Resolve(s3, msg3T, label.Public())
	} else {
		// ppred holds because message is not known to the attacker
		// assert usageCtx.ppred(s3, NslKey, msg3T, tm.createPk(b.SkBT), b.IdB)

		assert exists idA p.Principal, na tm.Term :: { s3.eventOccurs(idA, ev.NewEvent(FinishI, FinishIParams{ idA, b.IdB, na, nbT })) } s3.eventOccurs(idA, ev.NewEvent(FinishI, FinishIParams{ idA, b.IdB, na, nbT }))
		// get witness
		idAWitness := fa.GetArbPrincipal()
		naWitness := fa.GetArbTerm()
		assume s3.eventOccurs(idAWitness, ev.NewEvent(FinishI, FinishIParams{ idAWitness, b.IdB, naWitness, nbT }))
	
		// FinishI event must have occurred based on ppred, which in turn implies that the 
        // respond event has occurred.
        // By uniqueness of the respond event, we know that the respond events
        // from programStateB and ppred must be the same one:

		// get respond event via FinishI event:
		finishIS := b.llib.EventOccursImpliesEventInv(idAWitness, ev.NewEvent(FinishI, FinishIParams{ idAWitness, b.IdB, naWitness, nbT }))
		finishIS.getCorruptIdsMonotonic(s3)
		(tr.getPrev(finishIS)).isSuffixTransitive(finishIS, s3)
		respond1 := ev.NewEvent(Respond, RespondParams{ idAWitness, b.IdB, naWitness, nbT })
		if labelCtx.IsPublishable(s3, nbT) {
			// nbT being publishable means that either b.IdA or b.IdB have been corrupted because
			// nbT is only readable by them
			// this fact can automatically be derived, thus no assert stmt is needed:
			assert p.principalId(b.IdA) in s3.getCorruptIds() ||
				p.principalId(b.IdB) in s3.getCorruptIds()
		} else {
			// from the FinishI event, we learn that either idAWitness or b.IdB must have been corrupted or the
			// Respond event has occurred.
			// However, b.IdB cannot have been corrupted because nbT would otherwise be publishable and we would
			// not reach this branch.
			// Therefore, we distinguish two cases here:
			// (1) idAWitness has not been corrupted. Thus, Respond event has occurred and due to uniqueness of
			//		the Respond event, we know that idAWitness == b.IdA
			// (2) idAWitness has been corrupted. In this case, we can use the fact that we know the labeling of
			// 		nbT (because we have created the nonce) and nbT's labeling given by `pureEventInv`: Because
			//		the labeling is unique, idAWitness must be equal to b.IdA
			
			// the following commented out assertions hold but are not necessary:
			// assert !(p.principalId(b.IdA) in s3.getCorruptIds())
			// assert !(p.principalId(b.IdB) in s3.getCorruptIds())
			if (p.principalId(idAWitness) in s3.getCorruptIds()) {
				// assert labelCtx.IsLabeled(s3, nbT, bothLabel)
				// assert labelCtx.IsLabeled(s3, nbT, label.Readers(set[p.Id]{ p.principalId(idAWitness), p.principalId(b.IdB) }))
				// assert idAWitness == b.IdA
				// this is a contradiction because we know that b.IdA has not been corrupted, otherwise nbT would be publishable:
				// assert false
			} else {
				(tr.getPrev(finishIS)).eventOccursMonotonic(s3, b.IdB, respond1)
				// lift respond event from this program state to s3:
				respond2 := ev.NewEvent(Respond, RespondParams{ b.IdA, b.IdB, naT, nbT })
				s2.eventOccursMonotonic(s3, b.IdB, respond2)
				b.llib.UniqueEventsAreUnique(b.IdB, b.IdB, respond1, respond2)
			}

			// assert idAWitness == b.IdA
			// assert naWitness == naT
			
			// we therefore know that the FinishI event with naT and nbT must have occurred:
			// assert s3.eventOccurs(b.IdA, ev.NewEvent(FinishI, FinishIParams{ b.IdA, b.IdB, naT, nbT }))
		}
	}
	@*/

	/*@
	// facts after receiving msg3:
	corruptionOccurred := p.principalId(b.IdA) in s3.getCorruptIds() ||
		p.principalId(b.IdB) in s3.getCorruptIds()
	ghost if !corruptionOccurred {
		assert s3.eventOccurs(b.IdA, ev.NewEvent(FinishI, FinishIParams{ b.IdA, b.IdB, naT, nbT }))
	}
	@*/

	/*@
	finishREv := ev.NewEvent(FinishR, FinishRParams{ b.IdA, b.IdB, naT, nbT })
	fold ctx.eventInv(b.IdB, finishREv, s3)
	b.llib.TriggerEvent(finishREv)
	s4 := b.llib.Snapshot()
	s0.isSuffixTransitive(s3, s4)
	b.llib.ApplyMonotonicityDflt(labelCtx)
	@*/

	if err == nil {
		lib.PrintResponderSuccess(msg1.Na, nb)
	}
	b.Version = 2
	//@ fold b.Mem(naT, nbT)

	//@ b.proveSecurityProperties(naT, nbT)

	return err /*@, naT, nbT @*/
}
