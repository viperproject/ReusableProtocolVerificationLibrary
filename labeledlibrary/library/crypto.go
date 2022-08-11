package library

import (
	rand "crypto/rand"
	rsa "crypto/rsa"
	x509 "crypto/x509"
	sha256 "crypto/sha256"
	"errors"
	"fmt"
	io "io"
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
//@ ensures  err == nil ==> Mem(pk)
//@ ensures  err == nil ==> Mem(sk)
//@ ensures  err == nil ==> Abs(pk) == tm.createPkB(Abs(sk))
//@ ensures  err == nil ==> Abs(sk) == tm.gamma(tm.random(Abs(sk), keyLabel, u.PkeKey(usageString)))
//@ ensures  err == nil ==> ctx.NonceIsUnique(tm.random(Abs(sk), keyLabel, u.PkeKey(usageString)))
//@ ensures  err == nil ==> forall eventType ev.EventType :: { eventType in eventTypes } eventType in eventTypes ==> ctx.NonceForEventIsUnique(tm.random(Abs(sk), keyLabel, u.PkeKey(usageString)), eventType)
func (l *LibraryState) GenerateKey(/*@ ghost ctx tr.LabelingContext, ghost keyLabel label.SecrecyLabel, ghost usageString string, ghost eventTypes set[ev.EventType] @*/) (pk, sk ByteString, err error) {
	privateKey, err := rsa.GenerateKey(rand.Reader, 4096)
	fmt.Printf("Gen PrivateKey: %+v\n", privateKey)
	if err != nil {
		return
	}
	publicKey := privateKey.Public()
	fmt.Printf("Gen PublicKey: %+v\n", publicKey)

	// we serialize the private and public key as PKCS #1, ASN.1 DER and PKIX, ASN.1 DER, respectively.
	sk = x509.MarshalPKCS1PrivateKey(privateKey)

	pk, err = x509.MarshalPKIXPublicKey(publicKey)
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
//@ requires acc(Mem(pk), 1/16)
//@ requires Abs(pk) == tm.gamma(tm.createPk(tm.random(skB, keyLabel, u.PkeKey(usageString))))
//@ ensures  acc(l.Mem(), 1/16)
//@ ensures  acc(Mem(msg), 1/16)
//@ ensures  acc(Mem(pk), 1/16)
//@ ensures  err == nil ==> Mem(ciphertext)
//@ ensures  err == nil ==> Abs(ciphertext) == tm.encryptB(Abs(msg), Abs(pk))
func (l *LibraryState) Enc(msg, pk ByteString /*@, ghost skB tm.Bytes, ghost keyLabel label.SecrecyLabel, ghost usageString string @*/) (ciphertext ByteString, err error) {
	// unmarshal pk:
	publicKey, err := x509.ParsePKIXPublicKey(pk)
	if err != nil {
		return
	}

	var rsaPublicKey *rsa.PublicKey
	switch publicKey := publicKey.(type) {
    	case *rsa.PublicKey:
			rsaPublicKey = publicKey
            break
    	default:
			err = errors.New("invalid public key")
            return
    }
	fmt.Printf("Encrypt PublicKey: %+v\n", rsaPublicKey)
	rng := rand.Reader
	ciphertext, err = rsa.EncryptOAEP(sha256.New(), rng, rsaPublicKey, msg, nil)
	return
}

//@ trusted
//@ requires acc(l.Mem(), 1/16)
//@ requires acc(Mem(ciphertext), 1/16)
//@ requires acc(Mem(sk), 1/16)
//@ requires Abs(sk) == tm.gamma(tm.random(Abs(sk), keyLabel, u.PkeKey(usageString)))
//@ ensures  acc(l.Mem(), 1/16)
//@ ensures  acc(Mem(ciphertext), 1/16)
//@ ensures  acc(Mem(sk), 1/16)
//@ ensures  err == nil ==> Mem(msg)
//@ ensures  err == nil ==> Abs(ciphertext) == tm.encryptB(Abs(msg), tm.createPkB(Abs(sk)))
func (l *LibraryState) Dec(ciphertext, sk ByteString /*@, ghost keyLabel label.SecrecyLabel, ghost usageString string @*/) (msg ByteString, err error) {
	// unmarshal sk:
	privateKey, err := x509.ParsePKCS1PrivateKey(sk)
	if err != nil {
		return
	}
	fmt.Printf("Decrypt PrivateKey: %+v\n", privateKey)
	rng := rand.Reader
	msg, err = rsa.DecryptOAEP(sha256.New(), rng, privateKey, ciphertext, nil)
	return
}
