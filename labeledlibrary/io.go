package labeledlibrary

import (
	//@ att "gitlab.inf.ethz.ch/arquintl/prototrace/attacker"
	//@ "gitlab.inf.ethz.ch/arquintl/prototrace/labeling"
	lib "gitlab.inf.ethz.ch/arquintl/prototrace/labeledlibrary/library"
	p "gitlab.inf.ethz.ch/arquintl/prototrace/principal"
	//@ tm "gitlab.inf.ethz.ch/arquintl/prototrace/term"
	//@ tr "gitlab.inf.ethz.ch/arquintl/prototrace/trace"
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

	//@ requires acc(LibMem(), 1/16)
	//@ ensures  acc(LibMem(), 1/16)
	//@ ensures  err == nil ==> lib.Mem(msg)
	//@ ensures  err == nil ==> lib.Abs(msg) == tm.gamma(msgT)
	//@ ensures  err == nil ==> snapshot.messageOccurs(idSender, idReceiver, msgT)
	Receive(idSender, idReceiver p.Principal /*@, ghost snapshot tr.TraceEntry @*/) (msg lib.ByteString, err error /*@, ghost msgT tm.Term @*/)
}


/** 
 * acts as a middleware between participant implementation and the library:
 * it not only delegates the call to the library but also creates a corresponding
 * trace trace
 */
//@ requires l.Mem()
//@ requires l.Owner() == idSender
//@ requires acc(lib.Mem(msg), 1/16)
//@ requires tm.gamma(msgT) == lib.Abs(msg)
//@ requires tr.messageInv(l.Ctx(), idSender, idReceiver, msgT, l.Snapshot())
//@ ensures  l.Mem()
//@ ensures  l.ImmutableState() == old(l.ImmutableState())
//@ ensures  old(l.Snapshot()).isSuffix(l.Snapshot())
//@ ensures  acc(lib.Mem(msg), 1/16)
//@ ensures  err == nil ==> (l.Snapshot()).isMessageAt(idSender, idReceiver, msgT)
func (l *LabeledLibrary) Send(idSender, idReceiver p.Principal, msg lib.ByteString /*@, ghost msgT tm.Term @*/) (err error) {
	//@ unfold l.Mem()
	//@ l.manager.LogSend(l.ctx, idSender, idReceiver, msgT)
	//@ snapshot := l.manager.Trace(l.ctx, l.owner)
	err = l.com.Send(idSender, idReceiver, msg /*@, msgT, snapshot @*/)
	//@ fold l.Mem()
	return
}

//@ requires l.Mem()
//@ requires l.Owner() == idReceiver
//@ ensures  l.Mem()
//@ ensures  l.ImmutableState() == old(l.ImmutableState())
//@ ensures  l.Snapshot() == old(l.Snapshot())
//@ ensures  err == nil ==> lib.Mem(msg)
//@ ensures  err == nil ==> lib.Abs(msg) == tm.gamma(msgT)
//@ ensures  err == nil ==> tr.messageInv(l.Ctx(), idSender, idReceiver, msgT, l.Snapshot())
//@ ensures  err == nil ==> (l.Snapshot()).messageOccurs(idSender, idReceiver, msgT)
func (l *LabeledLibrary) Receive(idSender, idReceiver p.Principal) (msg lib.ByteString, err error /*@, ghost msgT tm.Term @*/) {
	//@ snapshot := l.Snapshot()
	//@ unfold l.Mem()
	msg, err /*@, msgT @*/ = l.com.Receive(idSender, idReceiver /*@, snapshot @*/)
	//@ fold l.Mem()
	/*@
	ghost if err == nil {
		prev := l.MessageOccursImpliesMessageInv(idSender, idReceiver, msgT)
		(tr.getPrev(prev)).isSuffixTransitive(prev, l.Snapshot())
		tr.messageInvTransitive(l.Ctx(), idSender, idReceiver, msgT, tr.getPrev(prev), l.Snapshot())
	}
	@*/
	return
}

/*@
ghost
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