package channelcommunication

//@ import ll "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary"
import lib "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/library"
import p "github.com/viperproject/ReusableProtocolVerificationLibrary/principal"
//@ import tm "github.com/viperproject/ReusableProtocolVerificationLibrary/term"
//@ import tr "github.com/viperproject/ReusableProtocolVerificationLibrary/trace"


type ChannelCommunicaton struct {
	channels map[ChannelKey]chan []byte
}
// the following statement is not necessary but makes subtyping explicit (for documentation purposes)
//@ (* ChannelCommunicaton) implements ll.Communication

type ChannelKey struct {
	idSender   p.Principal
	idReceiver p.Principal
}

/*@
pred (com *ChannelCommunicaton) LibMem() {
	acc(com)
}
@*/

//@ decreases
//@ ensures res.LibMem()
func NewChannelCommunication(initiator, responder p.Principal) (res *ChannelCommunicaton) {
	res = &ChannelCommunicaton{}
	res.channels = make(map[ChannelKey]chan []byte)
	// create a channel per communication direction:
	(res.channels)[ChannelKey{initiator, responder}] = make(chan []byte)
	(res.channels)[ChannelKey{responder, initiator}] = make(chan []byte)
	//@ fold res.LibMem()
	return res
}

//@ trusted
//@ requires acc(com.LibMem(), 1/16)
//@ requires acc(lib.Mem(msg), 1/16)
//@ requires lib.Abs(msg) == tm.gamma(msgT)
//@ requires snapshot.isMessageAt(idSender, idReceiver, msgT)
//@ ensures  acc(com.LibMem(), 1/16)
//@ ensures  acc(lib.Mem(msg), 1/16)
func (com *ChannelCommunicaton) Send(idSender, idReceiver p.Principal, msg lib.ByteString /*@, ghost msgT tm.Term, ghost snapshot tr.TraceEntry @*/) error {
	channel := (com.channels)[ChannelKey{idSender, idReceiver}]
	channel <- msg
	return nil
}

//@ trusted
//@ requires acc(com.LibMem(), 1/16)
//@ ensures  acc(com.LibMem(), 1/16)
//@ ensures  err == nil ==> lib.Mem(msg)
//@ ensures  err == nil ==> lib.Abs(msg) == tm.gamma(msgT)
//@ ensures  err == nil ==> snapshot.messageOccurs(idSender, idReceiver, msgT)
func (com *ChannelCommunicaton) Receive(idSender, idReceiver p.Principal /*@, ghost snapshot tr.TraceEntry @*/) (msg lib.ByteString, err error /*@, ghost msgT tm.Term @*/) {
	channel := (com.channels)[ChannelKey{idSender, idReceiver}]
	msg = <-channel
	return msg, nil /*@, tm.oneTerm(msg) @*/
}
