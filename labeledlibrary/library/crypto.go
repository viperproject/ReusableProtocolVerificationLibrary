package library

import (
	rand "crypto/rand"
	"errors"
	io "io"
	box "golang.org/x/crypto/nacl/box"
	//@ ev "gitlab.inf.ethz.ch/arquintl/prototrace/event"
	//@ "gitlab.inf.ethz.ch/arquintl/prototrace/label"
	p "gitlab.inf.ethz.ch/arquintl/prototrace/principal"
	//@ tm "gitlab.inf.ethz.ch/arquintl/prototrace/term"
	//@ tr "gitlab.inf.ethz.ch/arquintl/prototrace/trace"
	//@ u "gitlab.inf.ethz.ch/arquintl/prototrace/usage"
)


type ByteString []byte

// wraps IO calls and crypto

// number of bytes that should be used for nonces
const NonceLength = 24


type LibraryState struct {
	// we need at least a field to not run into unknown equality issues
	dummy int
}

/*@
pred (l *LibraryState) Mem() {
	acc(l)
}
@*/

//@ ensures res.Mem()
func NewLibrary(initiator, responder p.Principal) (res *LibraryState) {
	res = &LibraryState{}
	//@ fold res.Mem()
	return res
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
func NewByteStringWithContent(bytes tm.Bytes) (res ByteString)

ghost
requires b != nil ==> acc(Mem(b), _)
ensures  b != nil ? res == Abs(b) : res == tm.zeroStringB(l)
pure func SafeAbs(b ByteString, l int) (res tm.Bytes)

// abstract resource to mark nonces as such
pred IsNonce(b tm.Bytes)
@*/

//@ requires acc(Mem(b), _)
//@ ensures res >= 0 && res == len(b)
//@ pure
func Size(b ByteString) (res int) {
	return len(b)
}

//@ trusted
//@ requires acc(l.Mem(), 1/16)
//@ ensures  acc(l.Mem(), 1/16)
//@ ensures  err == nil ==> Mem(pk) && Size(pk) == 32
//@ ensures  err == nil ==> Mem(sk) && Size(sk) == 32
//@ ensures  err == nil ==> Abs(pk) == tm.createPkB(Abs(sk))
//@ ensures  err == nil ==> Abs(sk) == tm.gamma(tm.random(Abs(sk), keyLabel, u.PkeKey(usageString)))
//@ ensures  err == nil ==> ctx.NonceIsUnique(tm.random(Abs(sk), keyLabel, u.PkeKey(usageString)))
//@ ensures  err == nil ==> forall eventType ev.EventType :: { eventType in eventTypes } eventType in eventTypes ==> ctx.NonceForEventIsUnique(tm.random(Abs(sk), keyLabel, u.PkeKey(usageString)), eventType)
func (l *LibraryState) GenerateKey(/*@ ghost ctx tr.LabelingContext, ghost keyLabel label.SecrecyLabel, ghost usageString string, ghost eventTypes set[ev.EventType] @*/) (pk, sk ByteString, err error) {
	pkArr, skArr, err := box.GenerateKey(rand.Reader)
	pk = pkArr[:]
	sk = skArr[:]
	return
}

//@ trusted
//@ requires acc(l.Mem(), 1/16)
//@ ensures  acc(l.Mem(), 1/16)
//@ ensures  err == nil ==> Mem(nonce) && Size(nonce) == NonceLength
//@ ensures  err == nil ==> Abs(nonce) == tm.gamma(tm.random(Abs(nonce), nonceLabel, u.Nonce(usageString)))
//@ ensures  err == nil ==> ctx.NonceIsUnique(tm.random(Abs(nonce), nonceLabel, u.Nonce(usageString)))
//@ ensures  err == nil ==> forall eventType ev.EventType :: { eventType in eventTypes } eventType in eventTypes ==> ctx.NonceForEventIsUnique(tm.random(Abs(nonce), nonceLabel, u.Nonce(usageString)), eventType)
func (l *LibraryState) CreateNonce(/*@ ghost ctx tr.LabelingContext, ghost nonceLabel label.SecrecyLabel, ghost usageString string, ghost eventTypes set[ev.EventType] @*/) (nonce ByteString, err error) {
	var nonceArr [NonceLength]byte
	nonce = nonceArr[:]
	io.ReadFull(rand.Reader, nonce)
	// inhale `NonceIsUnique` and `NonceForEventIsUnique` instances
	return nonce, nil
}

//@ trusted
//@ requires acc(l.Mem(), 1/16)
//@ requires acc(Mem(msg), 1/16)
//@ requires acc(Mem(recv_pk), 1/16) && Size(recv_pk) == 32
//@ requires acc(Mem(sender_sk), 1/16) && Size(sender_sk) == 32
//@ ensures  acc(l.Mem(), 1/16)
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
	var nonceArr [24]byte
	copy(nonceArr[:], nonce)
	var pkArr [32]byte
	copy(pkArr[:], recv_pk)
	var skArr [32]byte
	copy(skArr[:], sender_sk)
	ciphertext = box.Seal(nonce[:], msg, &nonceArr, &pkArr, &skArr)
	// first NonceLength bytes of ciphertext are the nonce
	return ciphertext, nil
}

//@ trusted
//@ requires acc(l.Mem(), 1/16)
//@ requires acc(Mem(ciphertext), 1/16)
//@ requires acc(Mem(sender_pk), 1/16) && Size(sender_pk) == 32
//@ requires acc(Mem(recv_sk), 1/16) && Size(recv_sk) == 32
//@ ensures  acc(l.Mem(), 1/16)
//@ ensures  acc(Mem(ciphertext), 1/16)
//@ ensures  acc(Mem(sender_pk), 1/16)
//@ ensures  acc(Mem(recv_sk), 1/16)
//@ ensures  err == nil ==> Mem(msg)
//@ ensures  err == nil ==> Size(msg) == Size(ciphertext) - NonceLength - 16
//@ ensures  err == nil ==> Abs(ciphertext) == tm.encryptB(Abs(msg), tm.createPkB(Abs(recv_sk)))
func (l *LibraryState) Dec(ciphertext, sender_pk, recv_sk ByteString) (msg ByteString, err error) {
	var nonce/*@@@*/ [NonceLength]byte
	copy(nonce[:], ciphertext[:NonceLength] /*@, perm(1)/2 @*/)
	var pkArr [32]byte
	copy(pkArr[:], sender_pk)
	var skArr [32]byte
	copy(skArr[:], recv_sk)
	var res bool
	msg, res = box.Open(nil, ciphertext[NonceLength:], &nonce, &pkArr, &skArr)
	if res {
		err = nil
	} else {
		err = errors.New("Decryption failed")
	}
	return msg, err
}
