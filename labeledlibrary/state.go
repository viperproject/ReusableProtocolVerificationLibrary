package labeledlibrary

import (
	//@ arb "github.com/viperproject/ReusableProtocolVerificationLibrary/arbitrary"
	//@ att "github.com/viperproject/ReusableProtocolVerificationLibrary/attacker"
	//@ ev "github.com/viperproject/ReusableProtocolVerificationLibrary/event"
	//@ "github.com/viperproject/ReusableProtocolVerificationLibrary/label"
	//@ "github.com/viperproject/ReusableProtocolVerificationLibrary/labeling"
	lib "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/library"
	//@ p "github.com/viperproject/ReusableProtocolVerificationLibrary/principal"
	//@ tm "github.com/viperproject/ReusableProtocolVerificationLibrary/term"
	//@ tr "github.com/viperproject/ReusableProtocolVerificationLibrary/trace"
	//@ tri "github.com/viperproject/ReusableProtocolVerificationLibrary/traceinvariant"
	//@ tman "github.com/viperproject/ReusableProtocolVerificationLibrary/tracemanager"
	//@ ts "github.com/viperproject/ReusableProtocolVerificationLibrary/concurrentdatastructure"
	//@ u "github.com/viperproject/ReusableProtocolVerificationLibrary/usage"
)

// TODO ghost fields should be ghost
type LabeledLibrary struct {
	s *lib.LibraryState
	com Communication
	//@ ctx tri.TraceContext
	//@ manager *tman.TraceManager
	//@ owner p.Id
}

/*@
pred (l *LabeledLibrary) Mem() {
	acc(l) &&
	acc(l.s.Mem(), 1/8) &&
	acc(l.com.LibMem(), 1/8) &&
	l.com != nil && isComparable(l.com) &&
	l.ctx != nil && isComparable(l.ctx) && l.ctx.Props() &&
	l.manager.Mem(l.ctx, l.owner)
}

// abstract over all memory that remains unchanged after library initialization
// TODO should be ghost
type ImmutableState struct {
	l LabeledLibrary // the entire struct remains constant after initialization
	managerState tman.ImmutableState
}

ghost
requires acc(l.Mem(), _)
pure func (l *LabeledLibrary) ImmutableState() ImmutableState {
	return unfolding acc(l.Mem(), _) in ImmutableState{ *l, l.manager.ImmutableState(l.ctx, l.owner) }
}

ghost
requires acc(l.Mem(), _)
ensures  res != nil && isComparable(res) && res.Props()
pure func (l *LabeledLibrary) Ctx() (res tri.TraceContext) {
	return unfolding acc(l.Mem(), _) in l.ctx
}

ghost
requires acc(l.Mem(), _)
pure func (l *LabeledLibrary) Manager() *tman.TraceManager {
	return unfolding acc(l.Mem(), _) in l.manager
}

ghost
requires acc(l.Mem(), _)
pure func (l *LabeledLibrary) Owner() p.Id {
	return unfolding acc(l.Mem(), _) in l.owner
}

ghost
requires acc(l.Mem(), _)
pure func (l *LabeledLibrary) OwnerWoThread() p.Id {
	return unfolding acc(l.Mem(), _) in l.owner.IsSessionThread() ? p.sessionId(p.getIdPrincipal(l.owner), p.getIdSession(l.owner)) : l.owner
}

ghost
requires acc(l.Mem(), _)
pure func (l *LabeledLibrary) LabelCtx() labeling.LabelingContext {
	return tri.GetLabeling(l.Ctx())
}

ghost
requires acc(l.Mem(), _)
pure func (l *LabeledLibrary) Snapshot() tr.TraceEntry {
	return unfolding acc(l.Mem(), _) in l.manager.Snapshot(l.ctx, l.owner)
}
@*/

//@ requires acc(s.Mem(), 1/8)
//@ requires acc(com.LibMem(), 1/8)
//@ requires com != nil && isComparable(com)
//@ requires manager.Mem(ctx, owner)
//@ requires ctx != nil && isComparable(ctx) && ctx.Props()
//@ ensures  res.Mem()
//@ ensures  res.Ctx() == ctx
//@ ensures  res.Manager() == manager
//@ ensures  res.Owner() == owner
//@ ensures  (res.ImmutableState()).managerState == old(manager.ImmutableState(ctx, owner))
//@ ensures  res.Snapshot() == old(manager.Snapshot(ctx, owner))
// TODO manager, ctx, owner should be ghost
func NewLabeledLibrary(s *lib.LibraryState, com Communication /*@, manager *tman.TraceManager, ctx tri.TraceContext, owner p.Id @*/) (res *LabeledLibrary) {
	res = &LabeledLibrary{ s, com /*@, ctx, manager, owner @*/ }
	//@ fold res.Mem()
	return
}

/*@
ghost
decreases
requires l.Mem()
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  forall oldSnap tr.TraceEntry :: { oldSnap.getCorruptIds() } oldSnap.isSuffix(l.Snapshot()) ==> oldSnap.getCorruptIds() subset (l.Snapshot()).getCorruptIds()
ensures  forall oldSnap tr.TraceEntry, term tm.Term :: { l.LabelCtx().IsValid(oldSnap, term) } oldSnap.isSuffix(l.Snapshot()) && l.LabelCtx().IsValid(oldSnap, term) ==> l.LabelCtx().IsValid(l.Snapshot(), term)
ensures  forall oldSnap tr.TraceEntry, term tm.Term, sLabel label.SecrecyLabel :: { l.LabelCtx().IsLabeled(oldSnap, term, sLabel) } oldSnap.isSuffix(l.Snapshot()) && l.LabelCtx().IsLabeled(oldSnap, term, sLabel) ==> l.LabelCtx().IsLabeled(l.Snapshot(), term, sLabel)
ensures  forall oldSnap tr.TraceEntry, l1, l2 label.SecrecyLabel :: { l.LabelCtx().CanFlow(oldSnap, l1, l2) } oldSnap.isSuffix(l.Snapshot()) && l.LabelCtx().CanFlow(oldSnap, l1, l2) ==> l.LabelCtx().CanFlow(l.Snapshot(), l1, l2)
ensures  forall oldSnap tr.TraceEntry, term tm.Term, sLabel label.SecrecyLabel, usage u.Usage :: { l.LabelCtx().IsSecret(oldSnap, term, sLabel, usage) } oldSnap.isSuffix(l.Snapshot()) && l.LabelCtx().IsSecret(oldSnap, term, sLabel, usage) ==> l.LabelCtx().IsSecret(l.Snapshot(), term, sLabel, usage)
ensures  forall oldSnap tr.TraceEntry, term tm.Term, sLabel label.SecrecyLabel :: { l.LabelCtx().IsMsg(oldSnap, term, sLabel) } oldSnap.isSuffix(l.Snapshot()) && l.LabelCtx().IsMsg(oldSnap, term, sLabel) ==> l.LabelCtx().IsMsg(l.Snapshot(), term, sLabel)
ensures  forall oldSnap tr.TraceEntry, owner p.Id, sk tm.Term, keyType labeling.KeyType, usage string :: { l.LabelCtx().IsSecretKey(oldSnap, owner, sk, keyType, usage) } oldSnap.isSuffix(l.Snapshot()) && l.LabelCtx().IsSecretKey(oldSnap, owner, sk, keyType, usage) ==> l.LabelCtx().IsSecretKey(l.Snapshot(), owner, sk, keyType, usage)
ensures  forall oldSnap tr.TraceEntry, owner p.Id, pk, sk tm.Term, keyType labeling.KeyType, usage string :: { l.LabelCtx().IsPublicKey(oldSnap, owner, pk, sk, keyType, usage) } oldSnap.isSuffix(l.Snapshot()) && l.LabelCtx().IsPublicKey(oldSnap, owner, pk, sk, keyType, usage) ==> l.LabelCtx().IsPublicKey(l.Snapshot(), owner, pk, sk, keyType, usage)
ensures  forall oldSnap tr.TraceEntry, owner p.Id, pk tm.Term, keyType labeling.KeyType, usage string :: { l.LabelCtx().IsPublicKeyExistential(oldSnap, owner, pk, keyType, usage) } oldSnap.isSuffix(l.Snapshot()) && l.LabelCtx().IsPublicKeyExistential(oldSnap, owner, pk, keyType, usage) ==> l.LabelCtx().IsPublicKeyExistential(l.Snapshot(), owner, pk, keyType, usage)
ensures  forall oldSnap tr.TraceEntry, principal p.Principal, event ev.Event :: { oldSnap.eventOccurs(principal, event) } oldSnap.isSuffix(l.Snapshot()) && oldSnap.eventOccurs(principal, event) ==> l.Snapshot().eventOccurs(principal, event)
ensures  forall oldSnap tr.TraceEntry, principal p.Principal, event ev.Event :: { oldSnap.eventOccursWitness(principal, event) } oldSnap.isSuffix(l.Snapshot()) && oldSnap.eventOccurs(principal, event) ==> oldSnap.eventOccursWitness(principal, event).isSuffix(l.Snapshot().eventOccursWitness(principal, event))
ensures  forall oldSnap tr.TraceEntry, sender, receiver p.Principal, payload tm.Term :: { oldSnap.messageOccurs(sender, receiver, payload) } oldSnap.isSuffix(l.Snapshot()) &&oldSnap.messageOccurs(sender, receiver, payload) ==>  (l.Snapshot()).messageOccurs(sender, receiver, payload)
ensures  forall oldSnap tr.TraceEntry, nonce tm.Term :: { oldSnap.OnlyNonceOccurs(nonce) } oldSnap.isSuffix(l.Snapshot()) && oldSnap.OnlyNonceOccurs(nonce) ==>  (l.Snapshot()).OnlyNonceOccurs(nonce)
ensures  forall oldSnap tr.TraceEntry, nonce tm.Term, nonceLabel label.SecrecyLabel, nonceUsage u.Usage :: { oldSnap.nonceOccurs(nonce, nonceLabel, nonceUsage) } oldSnap.isSuffix(l.Snapshot()) && oldSnap.nonceOccurs(nonce, nonceLabel, nonceUsage) ==>  (l.Snapshot()).nonceOccurs(nonce, nonceLabel, nonceUsage)
func (l *LabeledLibrary) ApplyMonotonicity() {
	l.ApplyMonotonicityWithSnap(l.Snapshot())
}

ghost
decreases
requires l.Mem()
requires snap.isSuffix(l.Snapshot())
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  forall oldSnap tr.TraceEntry :: { oldSnap.getCorruptIds() } oldSnap.isSuffix(snap) ==> oldSnap.getCorruptIds() subset (snap).getCorruptIds()
ensures  forall oldSnap tr.TraceEntry, term tm.Term :: { l.LabelCtx().IsValid(oldSnap, term) } oldSnap.isSuffix(snap) && l.LabelCtx().IsValid(oldSnap, term) ==> l.LabelCtx().IsValid(snap, term)
ensures  forall oldSnap tr.TraceEntry, term tm.Term, sLabel label.SecrecyLabel :: { l.LabelCtx().IsLabeled(oldSnap, term, sLabel) } oldSnap.isSuffix(snap) && l.LabelCtx().IsLabeled(oldSnap, term, sLabel) ==> l.LabelCtx().IsLabeled(snap, term, sLabel)
ensures  forall oldSnap tr.TraceEntry, l1, l2 label.SecrecyLabel :: { l.LabelCtx().CanFlow(oldSnap, l1, l2) } oldSnap.isSuffix(snap) && l.LabelCtx().CanFlow(oldSnap, l1, l2) ==> l.LabelCtx().CanFlow(snap, l1, l2)
ensures  forall oldSnap tr.TraceEntry, term tm.Term, sLabel label.SecrecyLabel, usage u.Usage :: { l.LabelCtx().IsSecret(oldSnap, term, sLabel, usage) } oldSnap.isSuffix(snap) && l.LabelCtx().IsSecret(oldSnap, term, sLabel, usage) ==> l.LabelCtx().IsSecret(snap, term, sLabel, usage)
ensures  forall oldSnap tr.TraceEntry, term tm.Term, sLabel label.SecrecyLabel :: { l.LabelCtx().IsMsg(oldSnap, term, sLabel) } oldSnap.isSuffix(snap) && l.LabelCtx().IsMsg(oldSnap, term, sLabel) ==> l.LabelCtx().IsMsg(snap, term, sLabel)
ensures  forall oldSnap tr.TraceEntry, owner p.Id, sk tm.Term, keyType labeling.KeyType, usage string :: { l.LabelCtx().IsSecretKey(oldSnap, owner, sk, keyType, usage) } oldSnap.isSuffix(snap) && l.LabelCtx().IsSecretKey(oldSnap, owner, sk, keyType, usage) ==> l.LabelCtx().IsSecretKey(snap, owner, sk, keyType, usage)
ensures  forall oldSnap tr.TraceEntry, owner p.Id, pk, sk tm.Term, keyType labeling.KeyType, usage string :: { l.LabelCtx().IsPublicKey(oldSnap, owner, pk, sk, keyType, usage) } oldSnap.isSuffix(snap) && l.LabelCtx().IsPublicKey(oldSnap, owner, pk, sk, keyType, usage) ==> l.LabelCtx().IsPublicKey(snap, owner, pk, sk, keyType, usage)
ensures  forall oldSnap tr.TraceEntry, owner p.Id, pk tm.Term, keyType labeling.KeyType, usage string :: { l.LabelCtx().IsPublicKeyExistential(oldSnap, owner, pk, keyType, usage) } oldSnap.isSuffix(snap) && l.LabelCtx().IsPublicKeyExistential(oldSnap, owner, pk, keyType, usage) ==> l.LabelCtx().IsPublicKeyExistential(snap, owner, pk, keyType, usage)
ensures  forall oldSnap tr.TraceEntry, principal p.Principal, event ev.Event :: { oldSnap.eventOccurs(principal, event) } oldSnap.isSuffix(snap) && oldSnap.eventOccurs(principal, event) ==> snap.eventOccurs(principal, event)
ensures  forall oldSnap tr.TraceEntry, principal p.Principal, event ev.Event :: { oldSnap.eventOccursWitness(principal, event) } oldSnap.isSuffix(snap) && oldSnap.eventOccurs(principal, event) ==> oldSnap.eventOccursWitness(principal, event).isSuffix(snap.eventOccursWitness(principal, event))
ensures  forall oldSnap tr.TraceEntry, sender, receiver p.Principal, payload tm.Term :: { oldSnap.messageOccurs(sender, receiver, payload) } oldSnap.isSuffix(snap) &&oldSnap.messageOccurs(sender, receiver, payload) ==>  (snap).messageOccurs(sender, receiver, payload)
ensures  forall oldSnap tr.TraceEntry, nonce tm.Term :: { oldSnap.OnlyNonceOccurs(nonce) } oldSnap.isSuffix(snap) && oldSnap.OnlyNonceOccurs(nonce) ==>  (snap).OnlyNonceOccurs(nonce)
ensures  forall oldSnap tr.TraceEntry, nonce tm.Term, nonceLabel label.SecrecyLabel, nonceUsage u.Usage :: { oldSnap.nonceOccurs(nonce, nonceLabel, nonceUsage) } oldSnap.isSuffix(snap) && oldSnap.nonceOccurs(nonce, nonceLabel, nonceUsage) ==>  (snap).nonceOccurs(nonce, nonceLabel, nonceUsage)
func (l *LabeledLibrary) ApplyMonotonicityWithSnap(snap tr.TraceEntry) {
	labelCtx := l.LabelCtx()
	// forall introduction
	arbSnap := arb.GetArbTraceEntry()
	arbTerm := arb.GetArbTerm()
	arbLabel := arb.GetArbLabel()
	arbLabel2 := arb.GetArbLabel()
	arbPrincipal := arb.GetArbPrincipal()
	arbEvent := arb.GetArbEvent()
	arbSender := arb.GetArbPrincipal()
	arbReceiver := arb.GetArbPrincipal()
	arbPayload := arb.GetArbTerm()
	arbNonceLabel := arb.GetArbLabel()
	arbNonceUsage := arb.GetArbUsage()
	if (arbSnap.isSuffix(snap)) {
		arbSnap.getCorruptIdsMonotonic(snap)
		if (labelCtx.IsValid(arbSnap, arbTerm)) {
			labelCtx.IsValidMonotonic(arbSnap, snap, arbTerm)
		}
		if (labelCtx.CanFlow(arbSnap, arbLabel, arbLabel2)) {
			labelCtx.CanFlowMonotonic(arbSnap, snap, arbLabel, arbLabel2)
		}
		if (labelCtx.IsMsg(arbSnap, arbTerm, arbLabel)) {
			labelCtx.IsMsgMonotonic(arbSnap, snap, arbTerm, arbLabel)
		}
		if (arbSnap.eventOccurs(arbPrincipal, arbEvent)) {
			arbSnap.eventOccursMonotonic(snap, arbPrincipal, arbEvent)
			arbSnap.eventOccursWitnessMonotonic(snap, arbPrincipal, arbEvent)
		}
		if (arbSnap.messageOccurs(arbSender, arbReceiver, arbPayload)) {
			arbSnap.messageOccursMonotonic(snap, arbSender, arbReceiver, arbPayload)
		}
		if (arbSnap.OnlyNonceOccurs(arbTerm)) {
			arbSnap.OnlyNonceOccursMonotonic(snap, arbTerm)
		}
		if (arbSnap.nonceOccurs(arbTerm, arbNonceLabel, arbNonceUsage)) {
			arbSnap.nonceOccursMonotonic(snap, arbTerm, arbNonceLabel, arbNonceUsage)
		}
	}
	assert arbSnap.isSuffix(snap) ==> arbSnap.getCorruptIds() subset (snap).getCorruptIds()
	assume forall oldSnap tr.TraceEntry :: { oldSnap.getCorruptIds() } oldSnap.isSuffix(snap) ==> oldSnap.getCorruptIds() subset (snap).getCorruptIds()
	assert arbSnap.isSuffix(snap) && labelCtx.IsValid(arbSnap, arbTerm) ==> labelCtx.IsValid(snap, arbTerm)
	assume forall oldSnap tr.TraceEntry, term tm.Term :: { labelCtx.IsValid(oldSnap, term) } oldSnap.isSuffix(snap) && labelCtx.IsValid(oldSnap, term) ==> labelCtx.IsValid(snap, term)
	assert arbSnap.isSuffix(snap) && labelCtx.CanFlow(arbSnap, arbLabel, arbLabel2) ==> labelCtx.CanFlow(snap, arbLabel, arbLabel2)
	assume forall oldSnap tr.TraceEntry, l1, l2 label.SecrecyLabel :: { labelCtx.CanFlow(oldSnap, l1, l2) } oldSnap.isSuffix(snap) && labelCtx.CanFlow(oldSnap, l1, l2) ==> labelCtx.CanFlow(snap, l1, l2)
	assert arbSnap.isSuffix(snap) && labelCtx.IsMsg(arbSnap, arbTerm, arbLabel) ==> labelCtx.IsMsg(snap, arbTerm, arbLabel)
	assume forall oldSnap tr.TraceEntry, term tm.Term, sLabel label.SecrecyLabel :: { labelCtx.IsMsg(oldSnap, term, sLabel) } oldSnap.isSuffix(snap) && labelCtx.IsMsg(oldSnap, term, sLabel) ==> labelCtx.IsMsg(snap, term, sLabel)
	assert arbSnap.isSuffix(snap) && arbSnap.eventOccurs(arbPrincipal, arbEvent) ==> snap.eventOccurs(arbPrincipal, arbEvent)
	assume forall oldSnap tr.TraceEntry, principal p.Principal, event ev.Event :: { oldSnap.eventOccurs(principal, event) } oldSnap.isSuffix(snap) && oldSnap.eventOccurs(principal, event) ==> (snap).eventOccurs(principal, event)
	assert arbSnap.isSuffix(snap) && arbSnap.eventOccurs(arbPrincipal, arbEvent) ==> arbSnap.eventOccursWitness(arbPrincipal, arbEvent).isSuffix(snap.eventOccursWitness(arbPrincipal, arbEvent))
	assume forall oldSnap tr.TraceEntry, principal p.Principal, event ev.Event :: { oldSnap.eventOccursWitness(principal, event) } oldSnap.isSuffix(snap) && oldSnap.eventOccurs(principal, event) ==> oldSnap.eventOccursWitness(principal, event).isSuffix(snap.eventOccursWitness(principal, event))
	assert arbSnap.isSuffix(snap) && arbSnap.messageOccurs(arbSender, arbReceiver, arbPayload) ==> (snap).messageOccurs(arbSender, arbReceiver, arbPayload)
	assume forall oldSnap tr.TraceEntry, sender, receiver p.Principal, payload tm.Term :: { oldSnap.messageOccurs(sender, receiver, payload) } oldSnap.isSuffix(snap) && oldSnap.messageOccurs(sender, receiver, payload) ==> (snap).messageOccurs(sender, receiver, payload)
	assert arbSnap.isSuffix(snap) && arbSnap.OnlyNonceOccurs(arbTerm) ==> (snap).OnlyNonceOccurs(arbTerm)
	assume forall oldSnap tr.TraceEntry, nonce tm.Term :: { oldSnap.OnlyNonceOccurs(nonce) } oldSnap.isSuffix(snap) && oldSnap.OnlyNonceOccurs(nonce) ==> (snap).OnlyNonceOccurs(nonce)
	assert arbSnap.isSuffix(snap) && arbSnap.nonceOccurs(arbTerm, arbNonceLabel, arbNonceUsage) ==> (snap).nonceOccurs(arbTerm, arbNonceLabel, arbNonceUsage)
	assume forall oldSnap tr.TraceEntry, nonce tm.Term, nonceLabel label.SecrecyLabel, nonceUsage u.Usage :: { oldSnap.nonceOccurs(nonce, nonceLabel, nonceUsage) } oldSnap.isSuffix(snap) && oldSnap.nonceOccurs(nonce, nonceLabel, nonceUsage) ==> (snap).nonceOccurs(nonce, nonceLabel, nonceUsage)

	// IsPublicKey does not require any proof steps but IsPublicKeyExistential does:
	arbOwner := arb.GetArbId()
	arbPk := arb.GetArbTerm()
	arbKeyType := labeling.GetArbKeyType()
	arbUsageString := arb.GetArbString()
	if (arbSnap.isSuffix(snap) &&
		labelCtx.IsPublicKeyExistential(arbSnap, arbOwner, arbPk, arbKeyType, arbUsageString)) {
		skWitness := arb.GetArbTerm()
		if arbKeyType == labeling.KeyTypePke() {
			assert exists sk tm.Term :: { labelCtx.IsPublicEncKey(arbSnap, arbOwner, arbPk, sk, arbUsageString) } labelCtx.IsPublicEncKey(arbSnap, arbOwner, arbPk, sk, arbUsageString)
			// get witness
			assume labelCtx.IsPublicEncKey(arbSnap, arbOwner, arbPk, skWitness, arbUsageString)
		} else if arbKeyType == labeling.KeyTypeDh() {
			assert exists sk tm.Term :: { labelCtx.IsPublicDhKey(arbSnap, arbOwner, arbPk, sk, arbUsageString) } labelCtx.IsPublicDhKey(arbSnap, arbOwner, arbPk, sk, arbUsageString)
			// get witness
			assume labelCtx.IsPublicDhKey(arbSnap, arbOwner, arbPk, skWitness, arbUsageString)
		} else if arbKeyType == labeling.KeyTypeSigning() {
			assert exists sk tm.Term :: { labelCtx.IsPublicSigningKey(arbSnap, arbOwner, arbPk, sk, arbUsageString) } labelCtx.IsPublicSigningKey(arbSnap, arbOwner, arbPk, sk, arbUsageString)
			// get witness
			assume labelCtx.IsPublicSigningKey(arbSnap, arbOwner, arbPk, skWitness, arbUsageString)
		}
		assert labelCtx.IsPublicKey(arbSnap, arbOwner, arbPk, skWitness, arbKeyType, arbUsageString)
		assert labelCtx.IsPublicKey(snap, arbOwner, arbPk, skWitness, arbKeyType, arbUsageString)
		assert labelCtx.IsPublicKeyExistential(snap, arbOwner, arbPk, arbKeyType, arbUsageString)
	}
	assert arbSnap.isSuffix(snap) && labelCtx.IsPublicKeyExistential(arbSnap, arbOwner, arbPk, arbKeyType, arbUsageString) ==> labelCtx.IsPublicKeyExistential(snap, arbOwner, arbPk, arbKeyType, arbUsageString)
	assume forall oldSnap tr.TraceEntry, owner p.Id, pk tm.Term, keyType labeling.KeyType, usage string :: { labelCtx.IsPublicKeyExistential(oldSnap, owner, pk, keyType, usage) } oldSnap.isSuffix(snap) && labelCtx.IsPublicKeyExistential(oldSnap, owner, pk, keyType, usage) ==> labelCtx.IsPublicKeyExistential(snap, owner, pk, keyType, usage)
}

ghost
decreases
requires l.Mem()
requires att.attackerKnows(l.Snapshot(), term)
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  l.LabelCtx().IsPublishable(l.Snapshot(), term)
func (l *LabeledLibrary) AttackerOnlyKnowsPublishableValues(term tm.Term) {
	l.AttackerOnlyKnowsPublishableValuesWithSnap(l.Snapshot(), term)
}

ghost
decreases
requires l.Mem()
requires snap.isSuffix(l.Snapshot())
requires att.attackerKnows(snap, term)
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  l.LabelCtx().IsPublishable(snap, term)
func (l *LabeledLibrary) AttackerOnlyKnowsPublishableValuesWithSnap(snap tr.TraceEntry, term tm.Term) {
	publicTerms := snap.getPublicTerms()
	msgPayloads := snap.getMessagePayloads()
	publishedTerms := snap.getTermsMadePublic()

	if term in publicTerms {
		prev := l.PublicTermImpliesPublicInvWithSnap(snap, term)
		l.LabelCtx().IsPublishableMonotonic(prev, snap, term)
	} else if term in msgPayloads {
		sender, receiver := snap.getMsgSenderReceiver(term)
		prev := l.MessageOccursImpliesMessageInvWithSnap(snap, sender, receiver, term)
		tr.getPrev(prev).isSuffixTransitive(prev, snap)
		l.LabelCtx().IsPublishableMonotonic(tr.getPrev(prev), snap, term)
	} else {
		// assert term in publishedTerms
		prev := l.PublishedTermImpliesMadePublicInvWithSnap(snap, term)
		tr.getPrev(prev).isSuffixTransitive(prev, snap)
		l.LabelCtx().IsPublishableMonotonic(tr.getPrev(prev), snap, term)
	}
}

ghost
decreases
requires l.Mem()
requires l.Snapshot().eventOccurs(principal, event)
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  prev.isSuffix(l.Snapshot())
ensures  prev.isEventAt(principal, event)
ensures  prev == l.Snapshot().eventOccursWitness(principal, event)
ensures  l.Ctx().pureEventInv(principal, event, tr.getPrev(prev))
ensures  l.Ctx().pureEventInv(principal, event, l.Snapshot())
func (l *LabeledLibrary) EventOccursImpliesEventInv(principal p.Principal, event ev.Event) (prev tr.TraceEntry) {
	prev = l.EventOccursImpliesEventInvWithSnap(l.Snapshot(), principal, event)
}

ghost
decreases
requires l.Mem()
requires snap.isSuffix(l.Snapshot())
requires snap.eventOccurs(principal, event)
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  prev.isSuffix(snap)
ensures  prev.isEventAt(principal, event)
ensures  prev == snap.eventOccursWitness(principal, event)
ensures  l.Ctx().pureEventInv(principal, event, tr.getPrev(prev))
ensures  l.Ctx().pureEventInv(principal, event, snap)
ensures  l.Ctx().pureEventInv(principal, event, l.Snapshot())
func (l *LabeledLibrary) EventOccursImpliesEventInvWithSnap(snap tr.TraceEntry, principal p.Principal, event ev.Event) (prev tr.TraceEntry) {
	unfold l.Mem()
	prev = l.manager.EventOccursImpliesEventInvWithSnap(l.ctx, l.owner, snap, principal, event)
	fold l.Mem()
	tr.getPrev(prev).isSuffixTransitive(prev, snap)
	l.Ctx().pureEventInvMonotonic(principal, event, tr.getPrev(prev), snap)
	l.Ctx().pureEventInvMonotonic(principal, event, snap, l.Snapshot())
}

ghost
decreases
requires l.Mem()
requires (l.Snapshot()).OnlyNonceOccurs(nonce)
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  prev.isSuffix(l.Snapshot())
ensures  prev.isNonceAt(nonce)
ensures  tri.pureRandInv(l.Ctx(), nonce, tr.getPrev(prev))
ensures  tri.pureRandInv(l.Ctx(), nonce, l.Snapshot())
func (l *LabeledLibrary) NonceOccursImpliesRandInv(nonce tm.Term) (prev tr.TraceEntry) {
	unfold l.Mem()
	prev = l.manager.NonceOccursImpliesRandInv(l.ctx, l.owner, nonce)
	fold l.Mem()
	tr.getPrev(prev).isSuffixTransitive(prev, l.Snapshot())
	tri.pureRandInvTransitive(l.Ctx(), nonce, tr.getPrev(prev), l.Snapshot())
}

ghost
decreases
requires l.Mem()
requires term in l.Snapshot().getPublicTerms()
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  prev.isSuffix(l.Snapshot())
ensures  prev.isRoot()
ensures  tri.publicInv(l.Ctx(), l.Snapshot().getPublicTerms(), prev)
func (l *LabeledLibrary) PublicTermImpliesPublicInv(term tm.Term) (prev tr.TraceEntry) {
	prev = l.PublicTermImpliesPublicInvWithSnap(l.Snapshot(), term)
}

ghost
decreases
requires l.Mem()
requires snap.isSuffix(l.Snapshot())
requires term in snap.getPublicTerms()
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  prev.isSuffix(snap)
ensures  prev.isSuffix(l.Snapshot())
ensures  prev.isRoot()
ensures  tri.publicInv(l.Ctx(), snap.getPublicTerms(), prev)
func (l *LabeledLibrary) PublicTermImpliesPublicInvWithSnap(snap tr.TraceEntry, term tm.Term) (prev tr.TraceEntry) {
	unfold l.Mem()
	prev = l.manager.PublicTermImpliesPublicInvWithSnap(l.ctx, l.owner, snap, term)
	fold l.Mem()
}

ghost
decreases
requires l.Mem()
requires l.Snapshot().messageOccurs(sender, receiver, msg)
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  prev.isSuffix(l.Snapshot())
ensures  prev.isMessageAt(sender, receiver, msg)
ensures  tri.messageInv(l.Ctx(), sender, receiver, msg, tr.getPrev(prev))
ensures  tri.messageInv(l.Ctx(), sender, receiver, msg, l.Snapshot())
func (l *LabeledLibrary) MessageOccursImpliesMessageInv(sender, receiver p.Principal, msg tm.Term) (prev tr.TraceEntry) {
	prev = l.MessageOccursImpliesMessageInvWithSnap(l.Snapshot(), sender, receiver, msg)
}

ghost
decreases
requires l.Mem()
requires snap.isSuffix(l.Snapshot())
requires snap.messageOccurs(sender, receiver, msg)
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  prev.isSuffix(snap)
ensures  prev.isSuffix(l.Snapshot())
ensures  prev.isMessageAt(sender, receiver, msg)
ensures  tri.messageInv(l.Ctx(), sender, receiver, msg, tr.getPrev(prev))
ensures  tri.messageInv(l.Ctx(), sender, receiver, msg, snap)
func (l *LabeledLibrary) MessageOccursImpliesMessageInvWithSnap(snap tr.TraceEntry, sender, receiver p.Principal, msg tm.Term) (prev tr.TraceEntry) {
	unfold l.Mem()
	prev = l.manager.MessageOccursImpliesMessageInvWithSnap(l.ctx, l.owner, snap, sender, receiver, msg)
	fold l.Mem()
	tr.getPrev(prev).isSuffixTransitive(prev, snap)
	tr.getPrev(prev).isSuffixTransitive(prev, l.Snapshot())
	tri.messageInvTransitive(l.Ctx(), sender, receiver, msg, tr.getPrev(prev), snap)
}

ghost
decreases
requires l.Mem()
requires term in l.Snapshot().getTermsMadePublic()
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  prev.isSuffix(l.Snapshot())
ensures  prev.isPublic()
ensures  tri.madePublicInv(l.Ctx(), term, tr.getPrev(prev))
func (l *LabeledLibrary) PublishedTermImpliesMadePublicInv(term tm.Term) (prev tr.TraceEntry) {
	prev = l.PublishedTermImpliesMadePublicInvWithSnap(l.Snapshot(), term)
}

ghost
decreases
requires l.Mem()
requires snap.isSuffix(l.Snapshot())
requires term in snap.getTermsMadePublic()
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  prev.isSuffix(snap)
ensures  prev.isSuffix(l.Snapshot())
ensures  prev.isPublic()
ensures  tri.madePublicInv(l.Ctx(), term, tr.getPrev(prev))
func (l *LabeledLibrary) PublishedTermImpliesMadePublicInvWithSnap(snap tr.TraceEntry, term tm.Term) (prev tr.TraceEntry) {
	unfold l.Mem()
	prev = l.manager.PublishedTermImpliesMadePublicInvWithSnap(l.ctx, l.owner, snap, term)
	fold l.Mem()
}

ghost
requires l.Mem()
requires (l.Ctx()).eventInv(l.Owner().getPrincipal(), event, l.Snapshot())
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  old(l.Snapshot()).isSuffix(l.Snapshot())
ensures  (l.Snapshot()).isEventAt(l.Owner().getPrincipal(), event)
func (l *LabeledLibrary) TriggerEvent(event ev.Event) {
	unfold l.Mem()
	l.manager.LogEvent(l.ctx, l.owner, event)
	fold l.Mem()
	assert (l.Snapshot()).isEventAt(l.Owner().getPrincipal(), event)
}
@*/
