package labeledlibrary

import (
	//@ att "github.com/ModularVerification/ReusableVerificationLibrary/attacker"
	//@ "github.com/ModularVerification/ReusableVerificationLibrary/labeling"
	lib "github.com/ModularVerification/ReusableVerificationLibrary/labeledlibrary/library"
	p "github.com/ModularVerification/ReusableVerificationLibrary/principal"
	//@ tm "github.com/ModularVerification/ReusableVerificationLibrary/term"
	//@ tr "github.com/ModularVerification/ReusableVerificationLibrary/trace"
	//@ tri "github.com/ModularVerification/ReusableVerificationLibrary/traceinvariant"
)

/** abstracts over different communication channels */
type Communication interface {
	//@ pred LibMem()

	//@ requires acc(LibMem(), 1/16)
	//@ requires acc(lib.Mem(msg), 1/16)
	//@ requires lib.Abs(msg) == tm.gamma(msgT)
	//@ requires snapshot.isMessageAt(idSender, idReceiver, msgT)
	//@ ensures  acc(LibMem(), 1/16)
	//@ ensures  acc(lib.Mem(msg), 1/16)
	Send(idSender, idReceiver p.Principal, msg lib.ByteString /*@, ghost msgT tm.Term, ghost snapshot tr.TraceEntry @*/) error

	/*@
	ghost
	decreases
	requires acc(LibMem(), 1/16)
	requires acc(lib.Mem(msg), 1/16)
	requires lib.Abs(msg) == tm.gamma(msgT)
	requires snapshot.isMessageAt(idSender, idReceiver, msgT)
	ensures  acc(LibMem(), 1/16)
	ensures  acc(lib.Mem(msg), 1/16)
	// Send operation that the attacker uses (for proving attacker completeness)
	AttackerSend(idSender, idReceiver p.Principal, msg lib.ByteString, ghost msgT tm.Term, ghost snapshot tr.TraceEntry) error
	@*/

	//@ requires acc(LibMem(), 1/16)
	//@ ensures  acc(LibMem(), 1/16)
	//@ ensures  err == nil ==> lib.Mem(msg)
	//@ ensures  err == nil ==> lib.Abs(msg) == tm.gamma(msgT)
	//@ ensures  err == nil ==> snapshot.messageOccurs(idSender, idReceiver, msgT)
	// returns a message that was at or before `snapshot`. It's thus adviceable to synchronize to the global
	// trace first such that the set of receivable messages is as big as possible
	Receive(idSender, idReceiver p.Principal /*@, ghost snapshot tr.TraceEntry @*/) (msg lib.ByteString, err error /*@, ghost msgT tm.Term @*/)

	/*@
	ghost
	decreases // we assume termination, i.e., this function returns an error if there are no messages that can be received
	requires acc(LibMem(), 1/16)
	ensures  acc(LibMem(), 1/16)
	ensures  err == nil ==> lib.Mem(msg)
	ensures  err == nil ==> lib.Abs(msg) == tm.gamma(msgT)
	ensures  err == nil ==> snapshot.messageOccurs(idSender, idReceiver, msgT)
	// returns a message that was at or before `snapshot`. It's thus adviceable to synchronize to the global
	// trace first such that the set of receivable messages is as big as possible
	// Receive operation that the attacker uses (for proving attacker completeness)
	AttackerReceive(idSender, idReceiver p.Principal, ghost snapshot tr.TraceEntry) (msg lib.ByteString, err error, ghost msgT tm.Term)
	@*/
}

/**
 * acts as a middleware between participant implementation and the library:
 * it not only delegates the call to the library but also creates a corresponding
 * trace trace
 */
//@ requires l.Mem()
//@ requires l.Owner().getPrincipal() == idSender
//@ requires acc(lib.Mem(msg), 1/16)
//@ requires tm.gamma(msgT) == lib.Abs(msg)
//@ requires tri.messageInv(l.Ctx(), idSender, idReceiver, msgT, l.Snapshot())
//@ ensures  l.Mem()
//@ ensures  l.ImmutableState() == old(l.ImmutableState())
//@ ensures  old(l.Snapshot()).isSuffix(l.Snapshot())
//@ ensures  acc(lib.Mem(msg), 1/16)
//@ ensures  err == nil ==> (l.Snapshot()).isMessageAt(idSender, idReceiver, msgT)
func (l *LabeledLibrary) Send(idSender, idReceiver p.Principal, msg lib.ByteString /*@, ghost msgT tm.Term @*/) (err error) {
	//@ unfold l.Mem()
	//@ l.manager.LogSend(l.ctx, l.owner, l.owner.getPrincipal(), idReceiver, msgT)
	//@ snapshot := l.manager.Snapshot(l.ctx, l.owner)
	err = l.com.Send(idSender, idReceiver, msg /*@, msgT, snapshot @*/)
	//@ fold l.Mem()
	return
}

//@ requires l.Mem()
//@ requires l.Owner().getPrincipal() == idReceiver
//@ ensures  l.Mem()
//@ ensures  l.ImmutableState() == old(l.ImmutableState())
//@ ensures  old(l.Snapshot()).isSuffix(l.Snapshot())
//@ ensures  err == nil ==> lib.Mem(msg)
//@ ensures  err == nil ==> lib.Abs(msg) == tm.gamma(msgT)
//@ ensures  err == nil ==> tri.messageInv(l.Ctx(), idSender, idReceiver, msgT, l.Snapshot())
//@ ensures  err == nil ==> (l.Snapshot()).messageOccurs(idSender, idReceiver, msgT)
func (l *LabeledLibrary) Receive(idSender, idReceiver p.Principal) (msg lib.ByteString, err error /*@, ghost msgT tm.Term @*/) {
	//@ unfold l.Mem()
	// we first synchronize the local snapshot to the global trace:
	//@ snapshot := l.manager.Sync(l.ctx, l.owner)
	// and now get a message that was sent up until now:
	msg, err /*@, msgT @*/ = l.com.Receive(idSender, idReceiver /*@, snapshot @*/)
	//@ fold l.Mem()
	/*@
	ghost if err == nil {
		prev := l.MessageOccursImpliesMessageInv(idSender, idReceiver, msgT)
		(tr.getPrev(prev)).isSuffixTransitive(prev, l.Snapshot())
		tri.messageInvTransitive(l.Ctx(), idSender, idReceiver, msgT, tr.getPrev(prev), l.Snapshot())
	}
	@*/
	return
}

/*@
ghost
decreases
requires l.Mem()
requires (l.LabelCtx()).IsPublishable(l.Snapshot(), term)
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState())
ensures  old(l.Snapshot()).isSuffix(l.Snapshot())
ensures  att.attackerKnows(l.Snapshot(), term)
func (l *LabeledLibrary) Publish(term tm.Term) {
	unfold l.Mem()
	l.manager.LogPublish(l.ctx, l.owner, term)
	fold l.Mem()
}
@*/
