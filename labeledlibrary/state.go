package labeledlibrary

import (
	//@ arb "gitlab.inf.ethz.ch/arquintl/prototrace/arbitrary"
	//@ att "gitlab.inf.ethz.ch/arquintl/prototrace/attacker"
	//@ ev "gitlab.inf.ethz.ch/arquintl/prototrace/event"
	//@ "gitlab.inf.ethz.ch/arquintl/prototrace/label"
	//@ "gitlab.inf.ethz.ch/arquintl/prototrace/labeling"
	lib "gitlab.inf.ethz.ch/arquintl/prototrace/labeledlibrary/library"
	//@ p "gitlab.inf.ethz.ch/arquintl/prototrace/principal"
	//@ tm "gitlab.inf.ethz.ch/arquintl/prototrace/term"
	//@ tr "gitlab.inf.ethz.ch/arquintl/prototrace/trace"
	//@ tman "gitlab.inf.ethz.ch/arquintl/prototrace/tracemanager"
	//@ ts "gitlab.inf.ethz.ch/arquintl/prototrace/twostate"
	//@ u "gitlab.inf.ethz.ch/arquintl/prototrace/usage"
)

// TODO ghost fields should be ghost
type LabeledLibrary struct {
	s *lib.LibraryState
	com Communication
	//@ ctx tr.TraceContext
	//@ manager *tman.TraceManager
	//@ owner p.Principal
}

/*@
pred (l *LabeledLibrary) Mem() {
	acc(l) &&
	acc(l.s.Mem(), 1/8) &&
	acc(l.com.LibMem(), 1/8) &&
	l.com != nil && isComparable(l.com) &&
	l.ctx != nil && isComparable(l.ctx) &&
	typeOf(l.ctx.GetLabeling()) == labeling.DefaultLabelingContext &&
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
ensures  res != nil && isComparable(res)
pure func (l *LabeledLibrary) Ctx() (res tr.TraceContext) {
	return unfolding acc(l.Mem(), _) in l.ctx
}

ghost
requires acc(l.Mem(), _)
pure func (l *LabeledLibrary) Manager() *tman.TraceManager {
	return unfolding acc(l.Mem(), _) in l.manager
}

ghost
requires acc(l.Mem(), _)
pure func (l *LabeledLibrary) Owner() p.Principal {
	return unfolding acc(l.Mem(), _) in l.owner
}

ghost
requires acc(l.Mem(), _)
pure func (l *LabeledLibrary) LabelCtx() tr.LabelingContext {
	return l.Ctx().GetLabeling()
}

ghost
requires acc(l.Mem(), _)
pure func (l *LabeledLibrary) Snapshot() tr.TraceEntry {
	return unfolding acc(l.Mem(), _) in l.manager.Trace(l.ctx, l.owner)
}
@*/

//@ requires acc(s.Mem(), 1/8)
//@ requires acc(com.LibMem(), 1/8)
//@ requires com != nil && isComparable(com)
//@ requires manager.Mem(ctx, owner)
//@ requires ctx != nil && isComparable(ctx)
//@ requires typeOf(ctx.GetLabeling()) == labeling.DefaultLabelingContext
//@ ensures  res.Mem()
//@ ensures  res.Ctx() == ctx
//@ ensures  res.Manager() == manager
//@ ensures  res.Owner() == owner
//@ ensures  (res.ImmutableState()).managerState == old(manager.ImmutableState(ctx, owner))
//@ ensures  res.Snapshot() == old(manager.Trace(ctx, owner))
// TODO manager, ctx, owner should be ghost
func NewLabeledLibrary(s *lib.LibraryState, com Communication /*@, manager *tman.TraceManager, ctx tr.TraceContext, owner p.Principal @*/) (res *LabeledLibrary) {
	res = &LabeledLibrary{ s, com /*@, ctx, manager, owner @*/ }
	//@ fold res.Mem()
	return
}

/*@
ghost
requires l.Mem()
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  forall oldSnap tr.TraceEntry :: { oldSnap.getCorruptIds() } oldSnap.isSuffix(l.Snapshot()) ==> oldSnap.getCorruptIds() subset l.Snapshot().getCorruptIds()
ensures  forall oldSnap tr.TraceEntry, term tm.Term, sLabel label.SecrecyLabel, usage u.Usage :: { l.LabelCtx().IsSecret(oldSnap, term, sLabel, usage) } oldSnap.isSuffix(l.Snapshot()) && l.LabelCtx().IsSecret(oldSnap, term, sLabel, usage) ==> l.LabelCtx().IsSecret(l.Snapshot(), term, sLabel, usage)
ensures  forall oldSnap tr.TraceEntry, term tm.Term, sLabel label.SecrecyLabel :: { l.LabelCtx().IsLabeled(oldSnap, term, sLabel) } oldSnap.isSuffix(l.Snapshot()) && l.LabelCtx().IsLabeled(oldSnap, term, sLabel) ==> l.LabelCtx().IsLabeled(l.Snapshot(), term, sLabel)
ensures  forall oldSnap tr.TraceEntry, principal p.Principal, event ev.Event :: { oldSnap.eventOccurs(principal, event) } oldSnap.isSuffix(l.Snapshot()) &&oldSnap.eventOccurs(principal, event) ==>  (l.Snapshot()).eventOccurs(principal, event)
ensures  forall oldSnap tr.TraceEntry, sender, receiver p.Principal, payload tm.Term :: { oldSnap.messageOccurs(sender, receiver, payload) } oldSnap.isSuffix(l.Snapshot()) &&oldSnap.messageOccurs(sender, receiver, payload) ==>  (l.Snapshot()).messageOccurs(sender, receiver, payload)
ensures  forall oldSnap tr.TraceEntry, nonce tm.Term :: { oldSnap.OnlyNonceOccurs(nonce) } oldSnap.isSuffix(l.Snapshot()) && oldSnap.OnlyNonceOccurs(nonce) ==>  (l.Snapshot()).OnlyNonceOccurs(nonce)
ensures  forall oldSnap tr.TraceEntry, nonce tm.Term, nonceLabel label.SecrecyLabel, nonceUsage u.Usage :: { oldSnap.nonceOccurs(nonce, nonceLabel, nonceUsage) } oldSnap.isSuffix(l.Snapshot()) && oldSnap.nonceOccurs(nonce, nonceLabel, nonceUsage) ==>  (l.Snapshot()).nonceOccurs(nonce, nonceLabel, nonceUsage)
func (l *LabeledLibrary) ApplyMonotonicity() {
	// forall introduction
	arbSnap := arb.GetArbTraceEntry()
	arbTerm := arb.GetArbTerm()
	arbLabel := arb.GetArbLabel()
	arbUsage := arb.GetArbUsage()
	arbPrincipal := arb.GetArbPrincipal()
	arbEvent := arb.GetArbEvent()
	arbSender := arb.GetArbPrincipal()
	arbReceiver := arb.GetArbPrincipal()
	arbPayload := arb.GetArbTerm()
	arbNonceLabel := arb.GetArbLabel()
	arbNonceUsage := arb.GetArbUsage()
	if (arbSnap.isSuffix(l.Snapshot())) {
		arbSnap.getCorruptIdsMonotonic(l.Snapshot())
		if (l.LabelCtx().IsSecret(arbSnap, arbTerm, arbLabel, arbUsage)) {
			l.LabelCtx().IsSecretMonotonic(arbSnap, l.Snapshot(), arbTerm, arbLabel, arbUsage)
		}
		if (l.LabelCtx().IsLabeled(arbSnap, arbTerm, arbLabel)) {
			l.LabelCtx().IsLabeledMonotonic(arbSnap, l.Snapshot(), arbTerm, arbLabel)
		}
		if (l.LabelCtx().IsPublishable(arbSnap, arbTerm)) {
			l.LabelCtx().IsPublishableMonotonic(arbSnap, l.Snapshot(), arbTerm)
		}
		if (arbSnap.eventOccurs(arbPrincipal, arbEvent)) {
			arbSnap.eventOccursMonotonic(l.Snapshot(), arbPrincipal, arbEvent)
		}
		if (arbSnap.messageOccurs(arbSender, arbReceiver, arbPayload)) {
			arbSnap.messageOccursMonotonic(l.Snapshot(), arbSender, arbReceiver, arbPayload)
		}
		if (arbSnap.OnlyNonceOccurs(arbTerm)) {
			arbSnap.OnlyNonceOccursMonotonic(l.Snapshot(), arbTerm)
		}
		if (arbSnap.nonceOccurs(arbTerm, arbNonceLabel, arbNonceUsage)) {
			arbSnap.nonceOccursMonotonic(l.Snapshot(), arbTerm, arbNonceLabel, arbNonceUsage)
		}
	}
	assert arbSnap.isSuffix(l.Snapshot()) ==> arbSnap.getCorruptIds() subset (l.Snapshot()).getCorruptIds()
	assume forall oldSnap tr.TraceEntry :: { oldSnap.getCorruptIds() } oldSnap.isSuffix(l.Snapshot()) ==> oldSnap.getCorruptIds() subset (l.Snapshot()).getCorruptIds()
	assert arbSnap.isSuffix(l.Snapshot()) && l.LabelCtx().IsSecret(arbSnap, arbTerm, arbLabel, arbUsage) ==> l.LabelCtx().IsSecret(l.Snapshot(), arbTerm, arbLabel, arbUsage)
	assume forall oldSnap tr.TraceEntry, term tm.Term, sLabel label.SecrecyLabel, usage u.Usage :: { l.LabelCtx().IsSecret(oldSnap, term, sLabel, usage) } oldSnap.isSuffix(l.Snapshot()) && l.LabelCtx().IsSecret(oldSnap, term, sLabel, usage) ==> l.LabelCtx().IsSecret(l.Snapshot(), term, sLabel, usage)
	assert arbSnap.isSuffix(l.Snapshot()) && l.LabelCtx().IsLabeled(arbSnap, arbTerm, arbLabel) ==> l.LabelCtx().IsLabeled(l.Snapshot(), arbTerm, arbLabel)
	assume forall oldSnap tr.TraceEntry, term tm.Term, sLabel label.SecrecyLabel :: { l.LabelCtx().IsLabeled(oldSnap, term, sLabel) } oldSnap.isSuffix(l.Snapshot()) && l.LabelCtx().IsLabeled(oldSnap, term, sLabel) ==> l.LabelCtx().IsLabeled(l.Snapshot(), term, sLabel)
	assert arbSnap.isSuffix(l.Snapshot()) && l.LabelCtx().IsPublishable(arbSnap, arbTerm) ==> l.LabelCtx().IsPublishable(l.Snapshot(), arbTerm)
	assume forall oldSnap tr.TraceEntry, term tm.Term :: { l.LabelCtx().IsPublishable(oldSnap, term) } oldSnap.isSuffix(l.Snapshot()) && l.LabelCtx().IsPublishable(oldSnap, term) ==> l.LabelCtx().IsPublishable(l.Snapshot(), term)
	assert arbSnap.isSuffix(l.Snapshot()) && arbSnap.eventOccurs(arbPrincipal, arbEvent) ==> (l.Snapshot()).eventOccurs(arbPrincipal, arbEvent)
	assume forall oldSnap tr.TraceEntry, principal p.Principal, event ev.Event :: { oldSnap.eventOccurs(principal, event) } oldSnap.isSuffix(l.Snapshot()) && oldSnap.eventOccurs(principal, event) ==> (l.Snapshot()).eventOccurs(principal, event)
	assert arbSnap.isSuffix(l.Snapshot()) && arbSnap.messageOccurs(arbSender, arbReceiver, arbPayload) ==> (l.Snapshot()).messageOccurs(arbSender, arbReceiver, arbPayload)
	assume forall oldSnap tr.TraceEntry, sender, receiver p.Principal, payload tm.Term :: { oldSnap.messageOccurs(sender, receiver, payload) } oldSnap.isSuffix(l.Snapshot()) && oldSnap.messageOccurs(sender, receiver, payload) ==> (l.Snapshot()).messageOccurs(sender, receiver, payload)
	assert arbSnap.isSuffix(l.Snapshot()) && arbSnap.OnlyNonceOccurs(arbTerm) ==> (l.Snapshot()).OnlyNonceOccurs(arbTerm)
	assume forall oldSnap tr.TraceEntry, nonce tm.Term :: { oldSnap.OnlyNonceOccurs(nonce) } oldSnap.isSuffix(l.Snapshot()) && oldSnap.OnlyNonceOccurs(nonce) ==> (l.Snapshot()).OnlyNonceOccurs(nonce)
	assert arbSnap.isSuffix(l.Snapshot()) && arbSnap.nonceOccurs(arbTerm, arbNonceLabel, arbNonceUsage) ==> (l.Snapshot()).nonceOccurs(arbTerm, arbNonceLabel, arbNonceUsage)
	assume forall oldSnap tr.TraceEntry, nonce tm.Term, nonceLabel label.SecrecyLabel, nonceUsage u.Usage :: { oldSnap.nonceOccurs(nonce, nonceLabel, nonceUsage) } oldSnap.isSuffix(l.Snapshot()) && oldSnap.nonceOccurs(nonce, nonceLabel, nonceUsage) ==> (l.Snapshot()).nonceOccurs(nonce, nonceLabel, nonceUsage)
}

ghost
requires l.Mem()
requires l.LabelCtx() == labelCtx
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  forall oldSnap tr.TraceEntry :: { oldSnap.getCorruptIds() } oldSnap.isSuffix(l.Snapshot()) ==> oldSnap.getCorruptIds() subset (l.Snapshot()).getCorruptIds()
ensures  forall oldSnap tr.TraceEntry, term tm.Term :: { labelCtx.IsValid(oldSnap, term) } oldSnap.isSuffix(l.Snapshot()) && labelCtx.IsValid(oldSnap, term) ==> labelCtx.IsValid(l.Snapshot(), term)
ensures  forall oldSnap tr.TraceEntry, term tm.Term, sLabel label.SecrecyLabel :: { labelCtx.IsLabeled(oldSnap, term, sLabel) } oldSnap.isSuffix(l.Snapshot()) && labelCtx.IsLabeled(oldSnap, term, sLabel) ==> labelCtx.IsLabeled(l.Snapshot(), term, sLabel)
ensures  forall oldSnap tr.TraceEntry, l1, l2 label.SecrecyLabel :: { labelCtx.CanFlow(oldSnap, l1, l2) } oldSnap.isSuffix(l.Snapshot()) && labelCtx.CanFlow(oldSnap, l1, l2) ==> labelCtx.CanFlow(l.Snapshot(), l1, l2)
ensures  forall oldSnap tr.TraceEntry, term tm.Term, sLabel label.SecrecyLabel, usage u.Usage :: { labelCtx.IsSecret(oldSnap, term, sLabel, usage) } oldSnap.isSuffix(l.Snapshot()) && labelCtx.IsSecret(oldSnap, term, sLabel, usage) ==> labelCtx.IsSecret(l.Snapshot(), term, sLabel, usage)
ensures  forall oldSnap tr.TraceEntry, term tm.Term, sLabel label.SecrecyLabel :: { labelCtx.IsMsg(oldSnap, term, sLabel) } oldSnap.isSuffix(l.Snapshot()) && labelCtx.IsMsg(oldSnap, term, sLabel) ==> labelCtx.IsMsg(l.Snapshot(), term, sLabel)
ensures  forall oldSnap tr.TraceEntry, owner p.Id, sk tm.Term, keyType labeling.KeyType, usage string :: { labelCtx.IsSecretKey(oldSnap, owner, sk, keyType, usage) } oldSnap.isSuffix(l.Snapshot()) && labelCtx.IsSecretKey(oldSnap, owner, sk, keyType, usage) ==> labelCtx.IsSecretKey(l.Snapshot(), owner, sk, keyType, usage)
ensures  forall oldSnap tr.TraceEntry, owner p.Id, pk, sk tm.Term, keyType labeling.KeyType, usage string :: { labelCtx.IsPublicKey(oldSnap, owner, pk, sk, keyType, usage) } oldSnap.isSuffix(l.Snapshot()) && labelCtx.IsPublicKey(oldSnap, owner, pk, sk, keyType, usage) ==> labelCtx.IsPublicKey(l.Snapshot(), owner, pk, sk, keyType, usage)
ensures  forall oldSnap tr.TraceEntry, owner p.Id, pk tm.Term, keyType labeling.KeyType, usage string :: { labelCtx.IsPublicKeyExistential(oldSnap, owner, pk, keyType, usage) } oldSnap.isSuffix(l.Snapshot()) && labelCtx.IsPublicKeyExistential(oldSnap, owner, pk, keyType, usage) ==> labelCtx.IsPublicKeyExistential(l.Snapshot(), owner, pk, keyType, usage)
ensures  forall oldSnap tr.TraceEntry, principal p.Principal, event ev.Event :: { oldSnap.eventOccurs(principal, event) } oldSnap.isSuffix(l.Snapshot()) &&oldSnap.eventOccurs(principal, event) ==>  (l.Snapshot()).eventOccurs(principal, event)
ensures  forall oldSnap tr.TraceEntry, sender, receiver p.Principal, payload tm.Term :: { oldSnap.messageOccurs(sender, receiver, payload) } oldSnap.isSuffix(l.Snapshot()) &&oldSnap.messageOccurs(sender, receiver, payload) ==>  (l.Snapshot()).messageOccurs(sender, receiver, payload)
ensures  forall oldSnap tr.TraceEntry, nonce tm.Term :: { oldSnap.OnlyNonceOccurs(nonce) } oldSnap.isSuffix(l.Snapshot()) && oldSnap.OnlyNonceOccurs(nonce) ==>  (l.Snapshot()).OnlyNonceOccurs(nonce)
ensures  forall oldSnap tr.TraceEntry, nonce tm.Term, nonceLabel label.SecrecyLabel, nonceUsage u.Usage :: { oldSnap.nonceOccurs(nonce, nonceLabel, nonceUsage) } oldSnap.isSuffix(l.Snapshot()) && oldSnap.nonceOccurs(nonce, nonceLabel, nonceUsage) ==>  (l.Snapshot()).nonceOccurs(nonce, nonceLabel, nonceUsage)
// TODO reuse `ApplyMonotonicity`
func (l *LabeledLibrary) ApplyMonotonicityDflt(labelCtx labeling.DefaultLabelingContext) {
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
	if (arbSnap.isSuffix(l.Snapshot())) {
		arbSnap.getCorruptIdsMonotonic(l.Snapshot())
		if (labelCtx.IsValid(arbSnap, arbTerm)) {
			labelCtx.IsValidMonotonic(arbSnap, l.Snapshot(), arbTerm)
		}
		if (labelCtx.CanFlow(arbSnap, arbLabel, arbLabel2)) {
			labelCtx.CanFlowMonotonic(arbSnap, l.Snapshot(), arbLabel, arbLabel2)
		}
		if (labelCtx.IsMsg(arbSnap, arbTerm, arbLabel)) {
			labelCtx.IsMsgMonotonic(arbSnap, l.Snapshot(), arbTerm, arbLabel)
		}
		if (arbSnap.eventOccurs(arbPrincipal, arbEvent)) {
			arbSnap.eventOccursMonotonic(l.Snapshot(), arbPrincipal, arbEvent)
		}
		if (arbSnap.messageOccurs(arbSender, arbReceiver, arbPayload)) {
			arbSnap.messageOccursMonotonic(l.Snapshot(), arbSender, arbReceiver, arbPayload)
		}
		if (arbSnap.OnlyNonceOccurs(arbTerm)) {
			arbSnap.OnlyNonceOccursMonotonic(l.Snapshot(), arbTerm)
		}
		if (arbSnap.nonceOccurs(arbTerm, arbNonceLabel, arbNonceUsage)) {
			arbSnap.nonceOccursMonotonic(l.Snapshot(), arbTerm, arbNonceLabel, arbNonceUsage)
		}
	}
	assert arbSnap.isSuffix(l.Snapshot()) ==> arbSnap.getCorruptIds() subset (l.Snapshot()).getCorruptIds()
	assume forall oldSnap tr.TraceEntry :: { oldSnap.getCorruptIds() } oldSnap.isSuffix(l.Snapshot()) ==> oldSnap.getCorruptIds() subset (l.Snapshot()).getCorruptIds()
	assert arbSnap.isSuffix(l.Snapshot()) && labelCtx.IsValid(arbSnap, arbTerm) ==> labelCtx.IsValid(l.Snapshot(), arbTerm)
	assume forall oldSnap tr.TraceEntry, term tm.Term :: { labelCtx.IsValid(oldSnap, term) } oldSnap.isSuffix(l.Snapshot()) && labelCtx.IsValid(oldSnap, term) ==> labelCtx.IsValid(l.Snapshot(), term)
	assert arbSnap.isSuffix(l.Snapshot()) && labelCtx.CanFlow(arbSnap, arbLabel, arbLabel2) ==> labelCtx.CanFlow(l.Snapshot(), arbLabel, arbLabel2)
	assume forall oldSnap tr.TraceEntry, l1, l2 label.SecrecyLabel :: { labelCtx.CanFlow(oldSnap, l1, l2) } oldSnap.isSuffix(l.Snapshot()) && labelCtx.CanFlow(oldSnap, l1, l2) ==> labelCtx.CanFlow(l.Snapshot(), l1, l2)
	assert arbSnap.isSuffix(l.Snapshot()) && labelCtx.IsMsg(arbSnap, arbTerm, arbLabel) ==> labelCtx.IsMsg(l.Snapshot(), arbTerm, arbLabel)
	assume forall oldSnap tr.TraceEntry, term tm.Term, sLabel label.SecrecyLabel :: { labelCtx.IsMsg(oldSnap, term, sLabel) } oldSnap.isSuffix(l.Snapshot()) && labelCtx.IsMsg(oldSnap, term, sLabel) ==> labelCtx.IsMsg(l.Snapshot(), term, sLabel)
	assert arbSnap.isSuffix(l.Snapshot()) && arbSnap.eventOccurs(arbPrincipal, arbEvent) ==> (l.Snapshot()).eventOccurs(arbPrincipal, arbEvent)
	assume forall oldSnap tr.TraceEntry, principal p.Principal, event ev.Event :: { oldSnap.eventOccurs(principal, event) } oldSnap.isSuffix(l.Snapshot()) && oldSnap.eventOccurs(principal, event) ==> (l.Snapshot()).eventOccurs(principal, event)
	assert arbSnap.isSuffix(l.Snapshot()) && arbSnap.messageOccurs(arbSender, arbReceiver, arbPayload) ==> (l.Snapshot()).messageOccurs(arbSender, arbReceiver, arbPayload)
	assume forall oldSnap tr.TraceEntry, sender, receiver p.Principal, payload tm.Term :: { oldSnap.messageOccurs(sender, receiver, payload) } oldSnap.isSuffix(l.Snapshot()) && oldSnap.messageOccurs(sender, receiver, payload) ==> (l.Snapshot()).messageOccurs(sender, receiver, payload)
	assert arbSnap.isSuffix(l.Snapshot()) && arbSnap.OnlyNonceOccurs(arbTerm) ==> (l.Snapshot()).OnlyNonceOccurs(arbTerm)
	assume forall oldSnap tr.TraceEntry, nonce tm.Term :: { oldSnap.OnlyNonceOccurs(nonce) } oldSnap.isSuffix(l.Snapshot()) && oldSnap.OnlyNonceOccurs(nonce) ==> (l.Snapshot()).OnlyNonceOccurs(nonce)
	assert arbSnap.isSuffix(l.Snapshot()) && arbSnap.nonceOccurs(arbTerm, arbNonceLabel, arbNonceUsage) ==> (l.Snapshot()).nonceOccurs(arbTerm, arbNonceLabel, arbNonceUsage)
	assume forall oldSnap tr.TraceEntry, nonce tm.Term, nonceLabel label.SecrecyLabel, nonceUsage u.Usage :: { oldSnap.nonceOccurs(nonce, nonceLabel, nonceUsage) } oldSnap.isSuffix(l.Snapshot()) && oldSnap.nonceOccurs(nonce, nonceLabel, nonceUsage) ==> (l.Snapshot()).nonceOccurs(nonce, nonceLabel, nonceUsage)

	// IsPublicKey does not require any proof steps but IsPublicKeyExistential does:
	arbOwner := arb.GetArbId()
	arbPk := arb.GetArbTerm()
	arbKeyType := labeling.GetArbKeyType()
	arbUsageString := arb.GetArbString()
	if (arbSnap.isSuffix(l.Snapshot()) &&
		labelCtx.IsPublicKeyExistential(arbSnap, arbOwner, arbPk, arbKeyType, arbUsageString)) {
		skWitness := arb.GetArbTerm()
		if arbKeyType == labeling.KeyTypePke() {
			assert exists sk tm.Term :: { labelCtx.IsPublicEncKey(arbSnap, arbOwner, arbPk, sk, arbUsageString) } labelCtx.IsPublicEncKey(arbSnap, arbOwner, arbPk, sk, arbUsageString)
			// get witness
			assume labelCtx.IsPublicEncKey(arbSnap, arbOwner, arbPk, skWitness, arbUsageString)
		} else if arbKeyType == labeling.KeyTypeDHPk() {
			assert exists sk tm.Term :: { labelCtx.IsPublicDhPk(arbSnap, arbOwner, arbPk, sk, arbUsageString) } labelCtx.IsPublicDhPk(arbSnap, arbOwner, arbPk, sk, arbUsageString)
			// get witness
			assume labelCtx.IsPublicDhPk(arbSnap, arbOwner, arbPk, skWitness, arbUsageString)
		}
		assert labelCtx.IsPublicKey(arbSnap, arbOwner, arbPk, skWitness, arbKeyType, arbUsageString)
		assert labelCtx.IsPublicKey(l.Snapshot(), arbOwner, arbPk, skWitness, arbKeyType, arbUsageString)
		if arbKeyType == labeling.KeyTypePke() {
			assert labelCtx.IsPublicKeyExistential(l.Snapshot(), arbOwner, arbPk, arbKeyType, arbUsageString)
		} else if arbKeyType == labeling.KeyTypeDHPk() {
			assert labelCtx.IsPublicDhPkExistential(l.Snapshot(), arbOwner, arbPk, arbUsageString)
		}
	}
	assert arbSnap.isSuffix(l.Snapshot()) && labelCtx.IsPublicKeyExistential(arbSnap, arbOwner, arbPk, arbKeyType, arbUsageString) ==> labelCtx.IsPublicKeyExistential(l.Snapshot(), arbOwner, arbPk, arbKeyType, arbUsageString)
	assume forall oldSnap tr.TraceEntry, owner p.Id, pk tm.Term, keyType labeling.KeyType, usage string :: { labelCtx.IsPublicKeyExistential(oldSnap, owner, pk, keyType, usage) } oldSnap.isSuffix(l.Snapshot()) && labelCtx.IsPublicKeyExistential(oldSnap, owner, pk, keyType, usage) ==> labelCtx.IsPublicKeyExistential(l.Snapshot(), owner, pk, keyType, usage)
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
	publicTerms := (l.Snapshot()).getPublicTerms()
	msgPayloads := (l.Snapshot()).getMessagePayloads()
	publishedTerms := (l.Snapshot()).getTermsMadePublic()

	if term in publicTerms {
		prev := l.PublicTermImpliesPublicInv(term)
		l.LabelCtx().IsPublishableMonotonic(prev, l.Snapshot(), term)
	} else if term in msgPayloads {
		sender, receiver := (l.Snapshot()).getMsgSenderReceiver(term)
		prev := l.MessageOccursImpliesMessageInv(sender, receiver, term)
		(tr.getPrev(prev)).isSuffixTransitive(prev, l.Snapshot())
		l.LabelCtx().IsPublishableMonotonic(tr.getPrev(prev), l.Snapshot(), term)
	} else {
		// assert term in publishedTerms
		prev := l.PublishedTermImpliesMadePublicInv(term)
		(tr.getPrev(prev)).isSuffixTransitive(prev, l.Snapshot())
		l.LabelCtx().IsPublishableMonotonic(tr.getPrev(prev), l.Snapshot(), term)
	}
}

ghost
decreases
requires l.Mem()
requires (l.Snapshot()).eventOccurs(principal, event)
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  prev.isSuffix(l.Snapshot())
ensures  prev.isEventAt(principal, event)
ensures  l.Ctx().pureEventInv(principal, event, tr.getPrev(prev))
ensures  l.Ctx().pureEventInv(principal, event, l.Snapshot())
func (l *LabeledLibrary) EventOccursImpliesEventInv(principal p.Principal, event ev.Event) (prev tr.TraceEntry) {
	unfold l.Mem()
	prev = l.manager.EventOccursImpliesEventInv(l.ctx, l.owner, principal, event)
	fold l.Mem()
	tr.getPrev(prev).isSuffixTransitive(prev, l.Snapshot())
	l.Ctx().pureEventInvTransitive(principal, event, tr.getPrev(prev), l.Snapshot())
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
ensures  tr.pureRandInv(l.Ctx(), nonce, tr.getPrev(prev))
func (l *LabeledLibrary) NonceOccursImpliesRandInv(nonce tm.Term) (prev tr.TraceEntry) {
	unfold l.Mem()
	prev = l.manager.NonceOccursImpliesRandInv(l.ctx, l.owner, nonce)
	fold l.Mem()
}

ghost
decreases
requires l.Mem()
requires term in (l.Snapshot()).getPublicTerms()
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  prev.isSuffix(l.Snapshot())
ensures  prev.isRoot()
ensures  tr.publicInv(l.Ctx(), (l.Snapshot()).getPublicTerms(), prev)
func (l *LabeledLibrary) PublicTermImpliesPublicInv(term tm.Term) (prev tr.TraceEntry) {
	unfold l.Mem()
	prev = l.manager.PublicTermImpliesPublicInv(l.ctx, l.owner, term)
	fold l.Mem()
}

ghost
decreases
requires l.Mem()
requires (l.Snapshot()).messageOccurs(sender, receiver, msg)
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  prev.isSuffix(l.Snapshot())
ensures  prev.isMessageAt(sender, receiver, msg)
ensures  tr.messageInv(l.Ctx(), sender, receiver, msg, tr.getPrev(prev))
ensures  tr.messageInv(l.Ctx(), sender, receiver, msg, l.Snapshot())
func (l *LabeledLibrary) MessageOccursImpliesMessageInv(sender, receiver p.Principal, msg tm.Term) (prev tr.TraceEntry) {
	unfold l.Mem()
	prev = l.manager.MessageOccursImpliesMessageInv(l.ctx, l.owner, sender, receiver, msg)
	fold l.Mem()
	tr.getPrev(prev).isSuffixTransitive(prev, l.Snapshot())
	tr.messageInvTransitive(l.Ctx(), sender, receiver, msg, tr.getPrev(prev), l.Snapshot())
}

ghost
decreases
requires l.Mem()
requires term in (l.Snapshot()).getTermsMadePublic()
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  l.Snapshot() == old(l.Snapshot())
ensures  prev.isSuffix(l.Snapshot())
ensures  prev.isPublic()
ensures  tr.madePublicInv(l.Ctx(), term, tr.getPrev(prev))
func (l *LabeledLibrary) PublishedTermImpliesMadePublicInv(term tm.Term) (prev tr.TraceEntry) {
	unfold l.Mem()
	prev = l.manager.PublishedTermImpliesMadePublicInv(l.ctx, l.owner, term)
	fold l.Mem()
}

ghost
requires l.Mem()
requires (l.Ctx()).eventInv(l.Owner(), event, l.Snapshot())
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  old(l.Snapshot()).isSuffix(l.Snapshot())
ensures  (l.Snapshot()).isEventAt(l.Owner(), event)
func (l *LabeledLibrary) TriggerEvent(event ev.Event) {
	unfold l.Mem()
	l.manager.LogEvent(l.ctx, l.owner, event)
	fold l.Mem()
	assert (l.Snapshot()).isEventAt(l.Owner(), event)
}
@*/
