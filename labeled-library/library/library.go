package library

import (
	rand "crypto/rand"
	"errors"
	fmt "fmt"
	io "io"
	box "golang.org/x/crypto/nacl/box"
	ev "protocols/library/event"
	"protocols/library/label"
	"protocols/library/labeling"
	p "protocols/library/principal"
	tm "protocols/library/term"
	tr "protocols/library/trace"
	u "protocols/library/usage"
)

type ByteString []byte

// wraps IO calls and crypto

// number of bytes that should be used for nonces
const NonceLength = 24 // 8 // TODO switch to 24


type LibraryState struct {
	channels map[ChannelKey]chan []byte
}

type ChannelKey struct {
	idSender   p.Principal
	idReceiver p.Principal
}

/*@
pred (l *LibraryState) LibMem() {
	acc(l)
}
@*/

//@ ensures res.LibMem()
func NewLibrary(initiator, responder p.Principal) (res *LibraryState) {
	res = &LibraryState{}
	res.channels = make(map[ChannelKey]chan []byte)
	// create a channel per communication direction:
	(res.channels)[ChannelKey{initiator, responder}] = make(chan []byte)
	(res.channels)[ChannelKey{responder, initiator}] = make(chan []byte)
	return res
}

//@ requires acc(l.LibMem(), 1/16)
//@ requires acc(Mem(msg), 1/16)
//@ ensures  acc(l.LibMem(), 1/16)
//@ ensures  acc(Mem(msg), 1/16)
func (l *LibraryState) Send(idSender, idReceiver p.Principal, msg ByteString) error {
	channel := (l.channels)[ChannelKey{idSender, idReceiver}]
	channel <- msg
	return nil
}

//@ requires acc(l.LibMem(), 1/16)
//@ ensures  acc(l.LibMem(), 1/16)
//@ ensures  err == nil ==> Mem(msg)
func (l *LibraryState) Recv(idSender, idReceiver p.Principal) (msg ByteString, err error) {
	channel := (l.channels)[ChannelKey{idSender, idReceiver}]
	msg := <-channel
	return msg, nil
}

/*@
// abstract resource to mark nonces as such
pred IsNonce(b tm.Bytes)
@*/

//@ requires acc(l.LibMem(), 1/16)
//@ ensures  acc(l.LibMem(), 1/16)
//@ ensures  err == nil ==> Mem(pk) && Size(pk) == 32
//@ ensures  err == nil ==> Mem(sk) && Size(sk) == 32
//@ ensures  err == nil ==> Abs(pk) == tm.createPkB(Abs(sk))
//@ ensures  err == nil ==> Abs(sk) == tm.gamma(tm.random(Abs(sk), keyLabel, u.PkeKey(usageString)))
//@ ensures  err == nil ==> ctx.NonceIsUnique(tm.random(Abs(sk), keyLabel, u.PkeKey(usageString)))
//@ ensures  err == nil ==> forall eventType ev.EventType :: { eventType in eventTypes } eventType in eventTypes ==> ctx.NonceForEventIsUnique(tm.random(Abs(sk), keyLabel, u.PkeKey(usageString)), eventType)
func (l *LibraryState) GenerateKey(/*@ ghost ctx tr.LabelingContext, ghost keyLabel label.SecrecyLabel, ghost usageString string, ghost eventTypes set[ev.EventType] @*/) (pk, sk ByteString, err error) {
	return box.GenerateKey(rand.Reader)
}

//@ requires acc(l.LibMem(), 1/16)
//@ ensures  acc(l.LibMem(), 1/16)
//@ ensures  err == nil ==> Mem(nonce) && Size(nonce) == NonceLength
//@ ensures  err == nil ==> Abs(nonce) == tm.gamma(tm.random(Abs(nonce), nonceLabel, u.Nonce(usageString)))
//@ ensures  err == nil ==> ctx.NonceIsUnique(tm.random(Abs(nonce), nonceLabel, u.Nonce(usageString)))
//@ ensures  err == nil ==> forall eventType ev.EventType :: { eventType in eventTypes } eventType in eventTypes ==> ctx.NonceForEventIsUnique(tm.random(Abs(nonce), nonceLabel, u.Nonce(usageString)), eventType)
func (l *LibraryState) CreateNonce(/*@ ghost ctx tr.LabelingContext, ghost nonceLabel label.SecrecyLabel, ghost usageString string, ghost eventTypes set[ev.EventType] @*/) (nonce ByteString, err error) {
	io.ReadFull(rand.Reader, nonce)
	// inhale `NonceIsUnique` and `NonceForEventIsUnique` instances
	return nonce, nil
}

//@ requires acc(l.LibMem(), 1/16)
//@ requires acc(Mem(msg), 1/16)
//@ requires acc(Mem(recv_pk), 1/16) && Size(recv_pk) == 32
//@ requires acc(Mem(sender_sk), 1/16) && Size(sender_sk) == 32
//@ ensures  acc(l.LibMem(), 1/16)
//@ ensures  acc(Mem(msg), 1/16)
//@ ensures  acc(Mem(recv_pk), 1/16)
//@ ensures  acc(Mem(sender_sk), 1/16)
//@ ensures  err == nil ==> Mem(ciphertext)
//@ ensures  err == nil ==> Size(ciphertext) == Size(msg) + NonceLength + 16
//@ ensures  err == nil ==> Abs(ciphertext) == tm.encryptB(Abs(msg), Abs(recv_pk))
func (l *LibraryState) Enc(msg, recv_pk, sender_sk ByteString) (ciphertext ByteString, err error) {
	nonce, err := l.CreateNonce()
	if err != nil {
		return nil, err
	}
	ciphertext = box.Seal(nonce[:], msg, &nonce, recv_pk, sender_sk)
	// first NonceLength bytes of ciphertext are the nonce
	return ciphertext, nil
}

//@ requires acc(l.LibMem(), 1/16)
//@ requires acc(Mem(ciphertext), 1/16)
//@ requires acc(Mem(sender_pk), 1/16) && Size(sender_pk) == 32
//@ requires acc(Mem(recv_sk), 1/16) && Size(recv_sk) == 32
//@ ensures  acc(l.LibMem(), 1/16)
//@ ensures  acc(Mem(ciphertext), 1/16)
//@ ensures  acc(Mem(sender_pk), 1/16)
//@ ensures  acc(Mem(recv_sk), 1/16)
//@ ensures  err == nil ==> Mem(msg)
//@ ensures  err == nil ==> Size(msg) == Size(ciphertext) - NonceLength - 16
//@ ensures  err == nil ==> Abs(ciphertext) == tm.encryptB(Abs(msg), tm.createPkB(Abs(recv_sk)))
func (l *LibraryState) Dec(ciphertext, sender_pk, recv_sk ByteString) (msg ByteString, err error) {
	var nonce/*@@@*/ [NonceLength]byte
	copy(nonce[:], ciphertext[:NonceLength] /*@, perm(1)/2 @*/)
	var res bool
	msg, res = box.Open(nil, ciphertext[NonceLength:], &nonce, sender_pk, recv_sk)
	if res {
		err = nil
	} else {
		err = errors.New("Decryption failed")
	}
	return msg, err
}

//@ requires acc(Mem(s1), 1/16)
//@ requires acc(Mem(s2), 1/16)
//@ ensures  acc(Mem(s1), 1/16)
//@ ensures  acc(Mem(s2), 1/16)
// ensures  res ==> Size(s1) == Size(s2)
//@ ensures  res == (Abs(s1) == Abs(s2))
// ensures  res ==> unfolding acc(Mem(s1), 1/16) in unfolding acc(Mem(s2), 1/16) in forall i int :: { s1[i], s2[i] } 0 <= i && i < len(s1) ==> s1[i] == s2[i]
func Compare(s1, s2 ByteString) (res bool) {
	return bytes.Compare(s1, s2) == 0
}

//@ ensures res != nil
func NewError(desc string) (res error) {
	return errors.New("idB does not match")
}

func Println(msg string) {
	fmt.Println(msg)
}

//@ requires acc(Mem(na), 1/16)
//@ requires acc(Mem(receivedNb), 1/16)
//@ ensures  acc(Mem(na), 1/16)
//@ ensures  acc(Mem(receivedNb), 1/16)
func PrintInitiatorSuccess(na, receivedNb ByteString) {
	fmt.Println("A has successfully finished the protocol run")
	fmt.Println("A.na: ", na)
	fmt.Println("A.nb: ", receivedNb)
}

//@ requires acc(Mem(receivedNa), 1/16)
//@ requires acc(Mem(nb), 1/16)
//@ ensures  acc(Mem(receivedNa), 1/16)
//@ ensures  acc(Mem(nb), 1/16)
func PrintResponderSuccess(receivedNa, nb ByteString) {
	fmt.Println("B has successfully finished the protocol run")
	fmt.Println("B.na: ", receivedNa)
	fmt.Println("B.nb: ", nb)
}

/*@
pred Mem(s ByteString) // {
	// forall i int :: 0 <= i && i < len(s) ==> acc(&s[i])
// }

ghost
requires acc(Mem(b), _)
ensures  Size(b) == 0 ==> res == tm.zeroStringB(0)
pure func Abs(b ByteString) (res tm.Bytes)

ghost
ensures Mem(res) && Abs(res) == bytes
// allocates a new slice of bytes and sets the elements according to `bytes`
func NewByteString(bytes tm.Bytes) (res ByteString)

ghost
requires b != nil ==> acc(Mem(b), _)
ensures  b != nil ? res == Abs(b) : res == tm.zeroStringB(l)
pure func SafeAbs(b ByteString, l int) (res tm.Bytes)
@*/

//@ requires acc(Mem(b), _)
//@ ensures res >= 0 && res == len(b)
//@ pure
func Size(b ByteString) (res int) {
	return len(b)
}

//@ requires noPerm < p && p <= writePerm
//@ requires len1 < len(s)
// requires forall i int :: { s[i] } 0 <= i && i < len(s) ==> acc(&s[i], p)
//@ requires acc(Mem(s), p)
//@ ensures  len(part1) == len1 && len(part2) == len(s) - len1
// ensures  forall i int :: { part1[i] } 0 <= i && i < len(part1) ==> acc(&part1[i], p) && part1[i] == old(s[i])
// ensures  forall i int :: { part2[i] } 0 <= i && i < len(part2) ==> acc(&part2[i], p) && part2[i] == old(s[i + len1])
//@ ensures  acc(Mem(part1), p)
//@ ensures  acc(Mem(part2), p)
func sliceHelper(s ByteString, len1 int /*@, ghost p perm @*/) (part1, part2 ByteString) /*{
	//@ unfold acc(Mem(s), p)
	part1 = s[:len1] // TODO: why might this slicing fail with Gobra?
	part2 = s[len1:]
	//@ fold acc(Mem(part1), p)
	//@ fold acc(Mem(part2), p)
}*/
