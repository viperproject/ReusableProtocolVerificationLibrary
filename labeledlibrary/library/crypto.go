package library

import (
	rand "crypto/rand"
	rsa "crypto/rsa"
	x509 "crypto/x509"
	sha256 "crypto/sha256"
	"errors"
	chacha20poly1305 "golang.org/x/crypto/chacha20poly1305"
	io "io"
	//@ ev "github.com/ModularVerification/ReusableVerificationLibrary/event"
	//@ "github.com/ModularVerification/ReusableVerificationLibrary/label"
	//@ "github.com/ModularVerification/ReusableVerificationLibrary/labeling"
	p "github.com/ModularVerification/ReusableVerificationLibrary/principal"
	//@ tm "github.com/ModularVerification/ReusableVerificationLibrary/term"
	//@ tr "github.com/ModularVerification/ReusableVerificationLibrary/trace"
	//@ u "github.com/ModularVerification/ReusableVerificationLibrary/usage"
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

//@ decreases
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

// Predicate partially consumed on creation of versioned nonces
pred guard(v uint32)
pred guardNext(v uint32) // Necessary for ratcheting

// Predicate partially obtained on creation of versioned nonces
pred receipt(key ByteString, v uint32)

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
//@ requires versionPerm >= 0
//@ requires versionPerm > 0 ==> acc(guard(version), versionPerm)
//@ ensures  acc(l.Mem(), 1/16)
//@ ensures  err == nil ==> Mem(pk)
//@ ensures  err == nil ==> Mem(sk)
//@ ensures  err == nil ==> Abs(pk) == tm.createPkB(Abs(sk))
//@ ensures  err == nil ==> Abs(sk) == tm.gamma(tm.random(Abs(sk), keyLabel, u.PkeKey(usageString)))
//@ ensures  err == nil ==> ctx.NonceIsUnique(tm.random(Abs(sk), keyLabel, u.PkeKey(usageString)))
//@ ensures  err == nil ==> forall eventType ev.EventType :: { eventType in eventTypes } eventType in eventTypes ==> ctx.NonceForEventIsUnique(tm.random(Abs(sk), keyLabel, u.PkeKey(usageString)), eventType)
//@ ensures  err == nil ==> versionPerm > 0 ==> acc(receipt(sk, version), versionPerm)
// GeneratePkeKey takes a versionPerm parameter, allowing the caller to specify how much (versionPerm) permission to take from the guard when creating a key with version `version`. If versionPerm is set to 0, the key is not versioned, and the value of `version` is ignored. If versionPerm is >0, we are assured that it is the current version because we require permission to `guard(version)`.
func (l *LibraryState) GeneratePkeKey(/*@ ghost ctx labeling.LabelingContext, ghost keyLabel label.SecrecyLabel, ghost versionPerm perm, ghost version uint32, ghost usageString string, ghost eventTypes set[ev.EventType] @*/) (pk, sk ByteString, err error) {
	privateKey, err := rsa.GenerateKey(rand.Reader, 4096)
	if err != nil {
		return
	}
	publicKey := privateKey.Public()

	// we serialize the private and public key as PKCS #1, ASN.1 DER and PKIX, ASN.1 DER, respectively.
	sk = x509.MarshalPKCS1PrivateKey(privateKey)

	pk, err = x509.MarshalPKIXPublicKey(publicKey)
	return
}

//@ trusted
//@ requires acc(l.Mem(), 1/16)
//@ requires versionPerm >= 0
//@ requires versionPerm > 0 ==> acc(guard(version), versionPerm)
//@ ensures  acc(l.Mem(), 1/16)
//@ ensures  err == nil ==> Mem(key) && Size(key) == 32
//@ ensures  err == nil ==> Abs(key) == tm.gamma(tm.random(Abs(key), keyLabel, u.DhKey(usageString)))
//@ ensures  err == nil ==> ctx.NonceIsUnique(tm.random(Abs(key), keyLabel, u.DhKey(usageString)))
//@ ensures  err == nil ==> forall eventType ev.EventType :: { eventType in eventTypes } eventType in eventTypes ==> ctx.NonceForEventIsUnique(tm.random(Abs(key), keyLabel, u.DhKey(usageString)), eventType)
//@ ensures  err == nil ==> versionPerm > 0 ==> acc(receipt(key, version), versionPerm)
// GenerateDHKey takes a versionPerm parameter, allowing the caller to specify how much (versionPerm) permission to take from the guard when creating a key with version `version`. If versionPerm is set to 0, the key is not versioned, and the value of `version` is ignored. If versionPerm is >0, we are assured that it is the current version because we require permission to `guard(version)`.
func (l *LibraryState) GenerateDHKey(/*@ ghost ctx labeling.LabelingContext, ghost keyLabel label.SecrecyLabel, ghost versionPerm perm, ghost version uint32, ghost usageString string, ghost eventTypes set[ev.EventType] @*/) (key ByteString, err error) {
	var keyBuf [32]byte
	key = keyBuf[:]
	_, err = rand.Read(key)
	if err != nil {
		return
	}
	// clamp
	key[0] &= 248
	key[31] = (key[31] & 127) | 64
	return
}

//@ trusted
//@ requires acc(l.Mem(), 1/16)
//@ requires versionPerm >= 0
//@ requires versionPerm > 0 ==> acc(guard(version), versionPerm)
//@ ensures  acc(l.Mem(), 1/16)
//@ ensures  err == nil ==> Mem(nonce) && Size(nonce) == NonceLength
//@ ensures  err == nil ==> Abs(nonce) == tm.gamma(tm.random(Abs(nonce), nonceLabel, u.Nonce(usageString)))
//@ ensures  err == nil ==> ctx.NonceIsUnique(tm.random(Abs(nonce), nonceLabel, u.Nonce(usageString)))
//@ ensures  err == nil ==> forall eventType ev.EventType :: { eventType in eventTypes } eventType in eventTypes ==> ctx.NonceForEventIsUnique(tm.random(Abs(nonce), nonceLabel, u.Nonce(usageString)), eventType)
//@ ensures  err == nil ==> versionPerm > 0 ==> acc(receipt(nonce, version), versionPerm)
// CreateNonce takes a versionPerm parameter, allowing the caller to specify how much (versionPerm) permission to take from the guard when creating a nonce with version `version`. If versionPerm is set to 0, the nonce is not versioned, and the value of `version` is ignored. If versionPerm is >0, we are assured that it is the current version because we require permission to `guard(version)`.
func (l *LibraryState) CreateNonce(/*@ ghost ctx labeling.LabelingContext, ghost nonceLabel label.SecrecyLabel, ghost versionPerm perm, ghost version uint32, ghost usageString string, ghost eventTypes set[ev.EventType] @*/) (nonce ByteString, err error) {
	var nonceArr [NonceLength]byte
	nonce = nonceArr[:]
	io.ReadFull(rand.Reader, nonce)
	// inhale `NonceIsUnique` and `NonceForEventIsUnique` instances
	return nonce, nil
}

//@ trusted
//@ requires Mem(value)
//@ requires versionPerm > 0 && acc(receipt(value, version), versionPerm)
//@ requires acc(guard(version), versionPerm) // This is to ensure that the version parameter corresponds to the current version // TODO_ Use two versionPerm here
//@ ensures acc(guard(version), versionPerm)
//@ ensures err == nil ==> acc(guard(version), versionPerm)
func (l* LibraryState) DeleteSafely(value ByteString /*@, ghost version uint32, ghost versionPerm perm @*/) (err error) {
	// TODO_ add an actual implementation of memory deletion
}

//@ trusted
//@ requires acc(l.Mem(), 1/16)
//@ requires acc(Mem(msg), 1/16)
//@ requires acc(Mem(pk), 1/16)
//@ ensures  acc(l.Mem(), 1/16)
//@ ensures  acc(Mem(msg), 1/16)
//@ ensures  acc(Mem(pk), 1/16)
//@ ensures  err == nil ==> Mem(ciphertext)
//@ ensures  err == nil ==> Abs(ciphertext) == tm.encryptB(Abs(msg), Abs(pk))
func (l *LibraryState) Enc(msg, pk ByteString) (ciphertext ByteString, err error) {
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

	rng := rand.Reader
	ciphertext, err = rsa.EncryptOAEP(sha256.New(), rng, rsaPublicKey, msg, nil)
	return
}

//@ pred IsUnversioned (value ByteString) // Abstract predicate whose only purpose is to ensure a method that requires it that the value is unversioned, when the method cannot prove it itself. TODO_ maybe move elsewhere

//@ trusted
//@ requires acc(l.Mem(), 1/16)
//@ requires acc(Mem(ciphertext), 1/16)
//@ requires acc(Mem(sk), 1/16)
//@ requires versionPerm >= 0
//@ requires versionPerm == 0 ==> IsUnversioned(sk)
//@ requires versionPerm > 0 ==> acc(guard(version), versionPerm)
//@ ensures  acc(l.Mem(), 1/16)
//@ ensures  acc(Mem(ciphertext), 1/16)
//@ ensures  acc(Mem(sk), 1/16)
//@ ensures  err == nil ==> Mem(msg)
//@ ensures  err == nil ==> Abs(ciphertext) == tm.encryptB(Abs(msg), tm.createPkB(Abs(sk)))
//@ ensures  err == nil ==> versionPerm > 0 ==> acc(receipt(msg, version), versionPerm)
// Dec takes a versionPerm parameter, allowing the caller to specify how much (versionPerm) permission to take from the guard when decrypting a value that is encrypted with a versioned key with version `version`. If versionPerm is set to 0, the value of `version` is ignored. If versionPerm is >0, we are assured that it is the current version because we require permission to `guard(version)`.
func (l *LibraryState) Dec(ciphertext, sk ByteString /*@, ghost versionPerm perm, ghost version uint32 @*/) (msg ByteString, err error) {
	// unmarshal sk:
	privateKey, err := x509.ParsePKCS1PrivateKey(sk)
	if err != nil {
		return
	}

	rng := rand.Reader
	msg, err = rsa.DecryptOAEP(sha256.New(), rng, privateKey, ciphertext, nil)
	return
}

//@ trusted
//@ requires acc(l.Mem(), 1/16)
//@ requires acc(Mem(key), 1/16) && acc(Mem(nonce), 1/16)
//@ requires Size(key) == 32 && Size(nonce) == 12
//@ requires plaintext != nil ==> acc(Mem(plaintext), 1/16)
//@ requires additionalData != nil ==> acc(Mem(additionalData), 1/16)
//@ ensures  acc(l.Mem(), 1/16)
//@ ensures  acc(Mem(key), 1/16) && acc(Mem(nonce), 1/16)
//@ ensures  plaintext != nil ==> acc(Mem(plaintext), 1/16)
//@ ensures  additionalData != nil ==> acc(Mem(additionalData), 1/16)
//@ ensures  err == nil ==> Mem(ciphertext) && Size(ciphertext) == (plaintext == nil ? 0 : Size(plaintext)) + 16
//@ ensures  err == nil ==> Abs(ciphertext) == tm.aeadB(Abs(key), Abs(nonce), SafeAbs(plaintext, 0), SafeAbs(additionalData, 0))
func (l *LibraryState) AeadEnc(key, nonce, plaintext, additionalData ByteString) (ciphertext ByteString, err error) {
	aead, err := chacha20poly1305.New(key)
	if err != nil {
		return
	}
	ciphertext = make([]byte, len(plaintext)+16)
	aead.Seal(ciphertext[:0], nonce, plaintext, additionalData)
	return
}

//@ trusted
//@ requires acc(l.Mem(), 1/16)
//@ requires acc(Mem(key), 1/16) && acc(Mem(nonce), 1/16)
//@ requires Size(key) == 32 && Size(nonce) == 12
//@ requires acc(Mem(ciphertext), 1/16)
//@ requires additionalData != nil ==> acc(Mem(additionalData), 1/16)
//@ requires versionPerm >= 0
//@ requires versionPerm == 0 ==> IsUnversioned(key)
//@ requires versionPerm > 0 ==> acc(guard(version), versionPerm)
//@ ensures  acc(l.Mem(), 1/16)
//@ ensures  acc(Mem(key), 1/16) && acc(Mem(nonce), 1/16)
//@ ensures  acc(Mem(ciphertext), 1/16)
//@ ensures  additionalData != nil ==> acc(Mem(additionalData), 1/16)
//@ ensures  err == nil ==> Mem(res) && Size(res) == Size(ciphertext) - 16
//@ ensures  err == nil ==> Abs(ciphertext) == tm.aeadB(Abs(key), Abs(nonce), Abs(res), SafeAbs(additionalData, 0))
//@ ensures  err == nil ==> versionPerm > 0 ==> acc(receipt(res, version), versionPerm)
// AeadDec takes a versionPerm parameter, allowing the caller to specify how much (versionPerm) permission to take from the guard when decrypting a value that is encrypted with a versioned key with version `version`. If versionPerm is set to 0, the value of `version` is ignored. If versionPerm is >0, we are assured that it is the current version because we require permission to `guard(version)`.
func (l *LibraryState) AeadDec(key, nonce, ciphertext, additionalData ByteString /*@, ghost versionPerm perm, ghost version uint32 @*/) (res ByteString, err error) {
	aead, err := chacha20poly1305.New(key)
	if err != nil {
		return
	}
	res = make([]byte, len(ciphertext)-16)
	_, err = aead.Open(res[:0], nonce, ciphertext, additionalData)
	return
}
