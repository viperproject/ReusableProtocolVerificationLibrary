package library

import (
	rand "crypto/rand"
	rsa "crypto/rsa"
	x509 "crypto/x509"
	sha256 "crypto/sha256"
	"errors"
	hex "encoding/hex"
	big "math/big"
	chacha20poly1305 "golang.org/x/crypto/chacha20poly1305"
	sign "golang.org/x/crypto/nacl/sign"
	io "io"
	//@ ev "github.com/viperproject/ReusableProtocolVerificationLibrary/event"
	//@ "github.com/viperproject/ReusableProtocolVerificationLibrary/label"
	//@ "github.com/viperproject/ReusableProtocolVerificationLibrary/labeling"
	p "github.com/viperproject/ReusableProtocolVerificationLibrary/principal"
	//@ tm "github.com/viperproject/ReusableProtocolVerificationLibrary/term"
	//@ tr "github.com/viperproject/ReusableProtocolVerificationLibrary/trace"
	//@ u "github.com/viperproject/ReusableProtocolVerificationLibrary/usage"
)


type ByteString []byte

// wraps IO calls and crypto

// number of bytes that should be used for nonces
const NonceLength = 24

// based on RFC 3526
const GroupGenerator = 2
const GroupSizeString = "FFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B139B22514A08798E3404DDEF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7EDEE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3DC2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F83655D23DCA3AD961C62F356208552BB9ED529077096966D670C354E4ABC9804F1746C08CA18217C32905E462E36CE3BE39E772C180E86039B2783A2EC07A28FB5C55DF06F4C52C9DE2BCBF6955817183995497CEA956AE515D2261898FA051015728E5A8AACAA68FFFFFFFFFFFFFFFF"
const DHHalfKeyLength = 256


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
//@ preserves acc(l.Mem(), 1/16)
//@ ensures  err == nil ==> Mem(pk) && Mem(sk)
//@ ensures  err == nil ==> Abs(pk) == tm.createPkB(Abs(sk)) && Abs(sk) == tm.gamma(tm.random(Abs(sk), keyLabel, u.PkeKey(usageString)))
//@ ensures  err == nil ==> ctx.NonceIsUnique(tm.random(Abs(sk), keyLabel, u.PkeKey(usageString)))
//@ ensures  err == nil ==> forall eventType ev.EventType :: { eventType in eventTypes } eventType in eventTypes ==> ctx.NonceForEventIsUnique(tm.random(Abs(sk), keyLabel, u.PkeKey(usageString)), eventType)
func (l *LibraryState) GeneratePkeKey(/*@ ghost ctx labeling.LabelingContext, ghost keyLabel label.SecrecyLabel, ghost usageString string, ghost eventTypes set[ev.EventType] @*/) (pk, sk ByteString, err error) {
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
//@ preserves acc(l.Mem(), 1/16)
//@ ensures  err == nil ==> Mem(key) && Size(key) == 32
//@ ensures  err == nil ==> Abs(key) == tm.gamma(tm.random(Abs(key), keyLabel, u.DhKey(usageString)))
//@ ensures  err == nil ==> ctx.NonceIsUnique(tm.random(Abs(key), keyLabel, u.DhKey(usageString)))
//@ ensures  err == nil ==> forall eventType ev.EventType :: { eventType in eventTypes } eventType in eventTypes ==> ctx.NonceForEventIsUnique(tm.random(Abs(key), keyLabel, u.DhKey(usageString)), eventType)
func (l *LibraryState) GenerateDHKey(/*@ ghost ctx labeling.LabelingContext, ghost keyLabel label.SecrecyLabel, ghost usageString string, ghost eventTypes set[ev.EventType] @*/) (key ByteString, err error) {
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
//@ preserves acc(l.Mem(), 1/16)
//@ ensures  err == nil ==> Mem(pk) && Mem(sk)
//@ ensures  err == nil ==> Abs(pk) == tm.createPkB(Abs(sk)) && Abs(sk) == tm.gamma(tm.random(Abs(sk), keyLabel, u.SigningKey(usageString)))
//@ ensures  err == nil ==> ctx.NonceIsUnique(tm.random(Abs(sk), keyLabel, u.SigningKey(usageString)))
//@ ensures  err == nil ==> forall eventType ev.EventType :: { eventType in eventTypes } eventType in eventTypes ==> ctx.NonceForEventIsUnique(tm.random(Abs(sk), keyLabel, u.SigningKey(usageString)), eventType)
func (l *LibraryState) GenerateSigningKey(/*@ ghost ctx labeling.LabelingContext, ghost keyLabel label.SecrecyLabel, ghost usageString string, ghost eventTypes set[ev.EventType] @*/) (pk, sk ByteString, err error) {
	publicKey, privateKey, err := sign.GenerateKey(rand.Reader)
	if err != nil {
		return
	}

	pk = (*publicKey)[:]
	sk = (*privateKey)[:]
	return
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ ensures  err == nil ==> Mem(nonce) && Size(nonce) == NonceLength
//@ ensures  err == nil ==> Abs(nonce) == tm.gamma(tm.random(Abs(nonce), nonceLabel, u.Nonce(usageString)))
//@ ensures  err == nil ==> ctx.NonceIsUnique(tm.random(Abs(nonce), nonceLabel, u.Nonce(usageString)))
//@ ensures  err == nil ==> forall eventType ev.EventType :: { eventType in eventTypes } eventType in eventTypes ==> ctx.NonceForEventIsUnique(tm.random(Abs(nonce), nonceLabel, u.Nonce(usageString)), eventType)
func (l *LibraryState) CreateNonce(/*@ ghost ctx labeling.LabelingContext, ghost nonceLabel label.SecrecyLabel, ghost usageString string, ghost eventTypes set[ev.EventType] @*/) (nonce ByteString, err error) {
	var nonceArr [NonceLength]byte
	nonce = nonceArr[:]
	io.ReadFull(rand.Reader, nonce)
	// inhale `NonceIsUnique` and `NonceForEventIsUnique` instances
	return nonce, nil
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ preserves acc(Mem(msg), 1/16)
//@ preserves acc(Mem(pk), 1/16)
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

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ preserves acc(Mem(ciphertext), 1/16)
//@ preserves acc(Mem(sk), 1/16)
//@ ensures  err == nil ==> Mem(msg)
//@ ensures  err == nil ==> Abs(ciphertext) == tm.encryptB(Abs(msg), tm.createPkB(Abs(sk)))
func (l *LibraryState) Dec(ciphertext, sk ByteString) (msg ByteString, err error) {
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
//@ preserves acc(l.Mem(), 1/16)
//@ requires acc(Mem(key), 1/16) && acc(Mem(nonce), 1/16)
//@ requires Size(key) == 32 && Size(nonce) == 12
//@ preserves plaintext != nil ==> acc(Mem(plaintext), 1/16)
//@ preserves additionalData != nil ==> acc(Mem(additionalData), 1/16)
//@ ensures  acc(Mem(key), 1/16) && acc(Mem(nonce), 1/16)
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
//@ preserves acc(l.Mem(), 1/16)
//@ requires acc(Mem(key), 1/16) && acc(Mem(nonce), 1/16)
//@ requires Size(key) == 32 && Size(nonce) == 12
//@ preserves acc(Mem(ciphertext), 1/16)
//@ preserves additionalData != nil ==> acc(Mem(additionalData), 1/16)
//@ ensures  acc(Mem(key), 1/16) && acc(Mem(nonce), 1/16)
//@ ensures  err == nil ==> Mem(res) && Size(res) == Size(ciphertext) - 16
//@ ensures  err == nil ==> Abs(ciphertext) == tm.aeadB(Abs(key), Abs(nonce), Abs(res), SafeAbs(additionalData, 0))
func (l *LibraryState) AeadDec(key, nonce, ciphertext, additionalData ByteString) (res ByteString, err error) {
	aead, err := chacha20poly1305.New(key)
	if err != nil {
		return
	}
	res = make([]byte, len(ciphertext)-16)
	_, err = aead.Open(res[:0], nonce, ciphertext, additionalData)
	return
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ preserves acc(Mem(data), 1/16) && acc(Mem(sk), 1/16)
//@ ensures err == nil ==> Mem(res)
//@ ensures err == nil ==> Abs(res) == tm.signB(Abs(data), Abs(sk))
func (l *LibraryState) Sign(data []byte, sk []byte) (res []byte, err error) {
	if len(sk) != 64 {
		return nil, errors.New("invalid secret key")
	}
	var skBuf [64]byte
	copy(skBuf[:], sk)

	var out []byte
	// not that the (64 bytes) signature is prepended to the plaintext
	return sign.Sign(out, data, &skBuf), nil
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ preserves acc(Mem(signedData), 1/16)
//@ requires acc(Mem(pk), 1/16)
//@ requires Abs(pk) == tm.gamma(tm.createPk(skT))
//@ ensures  acc(Mem(pk), 1/16)
//@ ensures err == nil ==> Mem(res)
//@ ensures err == nil ==> Abs(signedData) == tm.signB(Abs(res), tm.gamma(skT))
func (l *LibraryState) Open(signedData []byte, pk []byte /*@, ghost skT tm.Term @*/) (res []byte, err error) {
	if len(pk) != 32 {
		return nil, errors.New("invalid public key")
	}
	var pkBuf [32]byte
	copy(pkBuf[:], pk)
	
	var out []byte
	data, success := sign.Open(out, signedData, &pkBuf)
	if success {
		return data, nil
	} else {
		return nil, errors.New("signature check has failed")
	}
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ preserves acc(Mem(exp), 1/16)
//@ ensures err == nil ==> Mem(res)
// arg is big-endian
func (l *LibraryState) expModWithIntBase(base *big.Int, exp []byte) (res []byte, err error) {
	// prepare mod argument:
	groupSizeBytes, err := hex.DecodeString(GroupSizeString)
	if err != nil {
		return nil, err
	}
	mod := big.NewInt(0)
	mod.SetBytes(groupSizeBytes)

	// prepare exp argument:
	expInt := big.NewInt(0)
	expInt.SetBytes(exp)

	// perform calculation:
	r := big.NewInt(0)
	r.Exp(base, expInt, mod)

	// extract result:
	var resBuf [DHHalfKeyLength]byte
	r.FillBytes(resBuf[:])
	return resBuf[:], nil
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ preserves acc(Mem(base), 1/16) && acc(Mem(exp), 1/16)
//@ ensures err == nil ==> Mem(res)
// args are big-endian
func (l *LibraryState) expMod(base, exp []byte) (res []byte, err error) {
	// prepare mod argument:
	baseInt := big.NewInt(0)
	baseInt.SetBytes(base)
	return l.expModWithIntBase(baseInt, exp)
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ preserves acc(Mem(exp), 1/16)
//@ ensures err == nil ==> Mem(res)
//@ ensures err == nil ==> Abs(res) == tm.expB(tm.generatorB(), Abs(exp))
// arg is big-endian
func (l *LibraryState) DhExp(exp []byte) (res []byte, err error) {
	g := big.NewInt(GroupGenerator)
	return l.expModWithIntBase(g, exp)
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ preserves acc(Mem(dhSecret), 1/16) && acc(Mem(dhHalfKey), 1/16)
//@ ensures err == nil ==> Mem(res)
//@ ensures err == nil ==> Abs(res) == tm.expB(Abs(dhHalfKey), Abs(dhSecret))
// args are big-endian
func (l *LibraryState) DhSharedSecret(dhSecret, dhHalfKey []byte) (res []byte, err error) {
	return l.expMod(dhHalfKey, dhSecret)
}
