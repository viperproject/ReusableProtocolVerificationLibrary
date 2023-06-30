package labeledlibrary

import (
	//@ arb "github.com/ModularVerification/ReusableVerificationLibrary/arbitrary"
	//@ ev "github.com/ModularVerification/ReusableVerificationLibrary/event"
	//@ "github.com/ModularVerification/ReusableVerificationLibrary/label"
	//@ "github.com/ModularVerification/ReusableVerificationLibrary/labeling"
	lib "github.com/ModularVerification/ReusableVerificationLibrary/labeledlibrary/library"
	//@ p "github.com/ModularVerification/ReusableVerificationLibrary/principal"
	//@ tm "github.com/ModularVerification/ReusableVerificationLibrary/term"
	//@ tri "github.com/ModularVerification/ReusableVerificationLibrary/traceinvariant"
	//@ u "github.com/ModularVerification/ReusableVerificationLibrary/usage"
)

//@ requires l.Mem()
// versionPerm == 0 ==> the nonce is not versioned
//@ requires versionPerm >= 0
// If the nonce is versioned, consume a partial permission to the guard and verify that it is readable by the owner at the current version (or the owner in general)
//@ requires versionPerm > 0 ==> acc(lib.guard(l.Version()), 1/versionPerm) && l.Owner().IsSession() && tri.GetLabeling(l.Ctx()).CanFlow(l.Snapshot(), nonceLabel, label.Readers(set[p.Id]{ l.OwnerWithVersion() }))
// If the nonce is unversioned, just verify that it is readable by the owner
//@ requires versionPerm == 0 ==> tri.GetLabeling(l.Ctx()).CanFlow(l.Snapshot(), nonceLabel, label.Readers(set[p.Id]{ l.Owner() }))
//@ ensures  l.Mem()
//@ ensures  l.ImmutableState() == old(l.ImmutableState())
//@ ensures  old(l.Snapshot()).isSuffix(l.Snapshot())
//@ ensures  err == nil ==> lib.Mem(nonce) && lib.Size(nonce) == lib.NonceLength
//@ ensures  err == nil ==> lib.Abs(nonce) == tm.gamma(tm.random(lib.Abs(nonce), nonceLabel, u.Nonce(usageString)))
//@ ensures  err == nil ==> l.Snapshot().isNonceAt(tm.random(lib.Abs(nonce), nonceLabel, u.Nonce(usageString)))
//@ ensures  err == nil ==> forall eventType ev.EventType :: { eventType in eventTypes } eventType in eventTypes ==> (l.LabelCtx()).NonceForEventIsUnique(tm.random(lib.Abs(nonce), nonceLabel, u.Nonce(usageString)), eventType)
// Return the same amount of receipt permission
//@ ensures  err == nil && versionPerm > 0 ==> acc(lib.receipt(nonce, l.Version()), 1/versionPerm)
// CreateNonce takes a versionPerm parameter, allowing the caller to specify how much (1/versionPerm) permission to take from the guard when creating a versioned nonce. If versionPerm is set to 0, the nonce is not versioned.
func (l *LabeledLibrary) CreateNonce(/*@ ghost nonceLabel label.SecrecyLabel, ghost versionPerm int, ghost usageString string, ghost eventTypes set[ev.EventType] @*/) (nonce lib.ByteString, err error) {
	//@ unfold l.Mem()
	nonce, err = l.s.CreateNonce(/*@ tri.GetLabeling(l.ctx), nonceLabel, usageString, eventTypes @*/)
	// store nonce on trace
	/*@
	ghost if err == nil {
		nonceT := tm.random(lib.Abs(nonce), nonceLabel, u.Nonce(usageString))
		l.manager.LogNonce(l.ctx, l.owner, nonceT)
	}
	@*/
	//@ fold l.Mem()
	return
}

//@ requires l.Mem()
// versionPerm == 0 ==> the nonce is not versioned
//@ requires versionPerm >= 0
// If the key is versioned, consume a partial permission to the guard
//@ requires versionPerm > 0 ==> acc(lib.guard(l.Version()), 1/versionPerm) && l.Owner().IsSession()
//@ ensures  l.Mem()
//@ ensures  l.ImmutableState() == old(l.ImmutableState())
//@ ensures  old(l.Snapshot()).isSuffix(l.Snapshot())
//@ ensures  err == nil ==> lib.Mem(pk)
//@ ensures  err == nil ==> lib.Mem(sk)
//@ ensures  err == nil ==> lib.Abs(sk) == tm.gamma(skT) && lib.Abs(pk) == tm.createPkB(lib.Abs(sk))
//@ ensures  err == nil ==> l.Snapshot().isNonceAt(skT)
//@ ensures  err == nil && versionPerm == 0 ==> skT == tm.random(lib.Abs(sk), label.Readers(set[p.Id]{ l.Owner() }), u.PkeKey(usageString))
// Return the same amount of receipt permission
//@ ensures  err == nil && versionPerm > 0 ==> skT == tm.random(lib.Abs(sk), label.Readers(set[p.Id]{ l.OwnerWithVersion() }), u.PkeKey(usageString)) && acc(lib.receipt(sk, l.Version()), 1/versionPerm)
// TODO make skT ghost
// GeneratePkeKey takes a versionPerm parameter, allowing the caller to specify how much (1/versionPerm) permission to take from the guard when creating a versioned key. If versionPerm is set to 0, the key is not versioned.
func (l *LabeledLibrary) GeneratePkeKey(/*@ ghost versionPerm int, ghost usageString string @*/) (pk, sk lib.ByteString, err error /*@, skT tm.Term @*/) {
	//@ unfold l.Mem()
	//@ keyLabel := label.Readers(set[p.Id]{ l.owner })
	//@ ghost if versionPerm>0 {
	//@ 	keyLabel = label.Readers(set[p.Id]{ p.versionId(p.getIdPrincipal(l.owner), p.getIdSession(l.owner), l.version) }) // OwnerWithVersion label
	//@ }
	pk, sk, err = l.s.GeneratePkeKey(/*@ tri.GetLabeling(l.ctx), keyLabel, versionPerm, l.version, usageString, set[ev.EventType]{} @*/)
	// store sk on trace
	/*@
	ghost if err == nil {
		skT = tm.random(lib.Abs(sk), keyLabel, u.PkeKey(usageString))
		tri.GetLabeling(l.ctx).CanFlowReflexive(l.manager.Snapshot(l.ctx, l.owner), keyLabel)
		l.manager.LogNonceV(l.ctx, l.owner, l.version, versionPerm>0, skT)
	}
	@*/
	//@ fold l.Mem()
	return
}

//@ requires l.Mem()
// versionPerm == 0 ==> the nonce is not versioned
//@ requires versionPerm >= 0
// If the key is versioned, consume a partial permission to the guard
//@ requires versionPerm > 0 ==> acc(lib.guard(l.Version()), 1/versionPerm) && l.Owner().IsSession()
//@ ensures  l.Mem()
//@ ensures  l.ImmutableState() == old(l.ImmutableState())
//@ ensures  old(l.Snapshot()).isSuffix(l.Snapshot())
//@ ensures  err == nil ==> lib.Mem(key) && lib.Size(key) == 32
//@ ensures  err == nil ==> lib.Abs(key) == tm.gamma(skT)
//@ ensures  err == nil && versionPerm == 0  ==> skT == tm.random(lib.Abs(key), label.Readers(set[p.Id]{ l.Owner() }), u.DhKey(usageString))
//@ ensures  err == nil && versionPerm > 0  ==> skT == tm.random(lib.Abs(key), label.Readers(set[p.Id]{ l.OwnerWithVersion() }), u.DhKey(usageString)) && acc(lib.receipt(key, l.Version()), 1/versionPerm)
//@ ensures  err == nil ==> l.Snapshot().isNonceAt(skT)
//@ ensures  err == nil ==> forall eventType ev.EventType :: { eventType in eventTypes } eventType in eventTypes ==> l.LabelCtx().NonceForEventIsUnique(skT, eventType)
// GenerateDHKey takes a versionPerm parameter, allowing the caller to specify how much (1/versionPerm) permission to take from the guard when creating a versioned key. If versionPerm is set to 0, the key is not versioned.
func (l *LabeledLibrary) GenerateDHKey(/*@ ghost versionPerm int, ghost usageString string, ghost eventTypes set[ev.EventType] @*/) (key lib.ByteString, err error /*@, ghost skT tm.Term @*/) {
	//@ unfold l.Mem()
	//@ keyLabel := label.Readers(set[p.Id]{ l.owner })
	//@ ghost if versionPerm>0 {
	//@ 	keyLabel = label.Readers(set[p.Id]{ p.versionId(p.getIdPrincipal(l.owner), p.getIdSession(l.owner), l.version) }) // OwnerWithVersion label
	//@ }
	key, err = l.s.GenerateDHKey(/*@ tri.GetLabeling(l.ctx), keyLabel, versionPerm, l.version, usageString, eventTypes @*/)
	// store key on trace
	/*@
	ghost if err == nil {
		skT = tm.random(lib.Abs(key), keyLabel, u.DhKey(usageString))
		tri.GetLabeling(l.ctx).CanFlowReflexive(l.manager.Snapshot(l.ctx, l.owner), keyLabel)
		l.manager.LogNonceV(l.ctx, l.owner, l.version, versionPerm>0, skT)
	}
	@*/
	//@ fold l.Mem()
	return
}

//@ requires l.Mem()
//@ requires versionPerm > 0 && acc(lib.receipt(value, l.Version()), 1/versionPerm) && acc(lib.guard(l.Version()), 1/versionPerm)
//@ requires lib.Mem(value)
//@ ensures  l.Mem()
//@ ensures  acc(lib.guard(l.Version()), 1/versionPerm)
//@ ensures  l.ImmutableState() == old(l.ImmutableState())
//@ ensures  l.Snapshot() == old(l.Snapshot()) // TODO_ once I log the value deletion on the trace, this should be changed
//@ ensures  err == nil ==> acc(lib.guard(l.Version()), 1/versionPerm)
func (l* LabeledLibrary) DeleteSafely(value lib.ByteString /*@, ghost versionPerm int @*/) (err error) {
	//@ unfold l.Mem()
	err = l.s.DeleteSafely(value /*@, l.version, versionPerm @*/)
	// TODO_ log the value deletion on the trace
	//@ fold l.Mem()
}

/*@
ghost
requires l.Mem()
requires acc(lib.Mem(value), 1/8)
requires lib.Abs(value) == tm.gamma(valueT)
requires l.Owner().IsSession()
requires versionPerm > 0 && acc(lib.receipt(value, l.Version()), 1/versionPerm)
requires acc(lib.guardNext(l.Version() + 1), 1/versionPerm)
requires tri.GetLabeling(l.Ctx()).CanFlow(l.Snapshot(), l.LabelCtx().GetLabel(valueT), label.Readers(set[p.Id]{ l.OwnerWithNextVersion() }))
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState()) // TODO_ If ConvertToNextVersion should be logged onto the trace, then this should be changed
ensures  l.Snapshot() == old(l.Snapshot())
ensures  acc(lib.Mem(value), 1/8)
ensures  acc(lib.guard(l.Version()), 1/versionPerm)
ensures  acc(lib.receipt(value, l.Version() + 1), 1/versionPerm)
func (l* LabeledLibrary) ConvertToNextVersion(value lib.ByteString, valueT tm.Term, versionPerm int)

ghost
requires l.Mem()
requires acc(lib.Mem(value), 1/8)
requires lib.Abs(value) == tm.gamma(valueT)
requires versionPerm > 0 && acc(lib.receipt(value, l.Version()), 1/versionPerm)
requires tri.GetLabeling(l.Ctx()).CanFlow(l.Snapshot(), l.LabelCtx().GetLabel(valueT), label.Readers(set[p.Id]{ l.Owner() }))
ensures  l.Mem()
ensures  l.ImmutableState() == old(l.ImmutableState()) // TODO_ If GuardFromReceiptUnversioned should be logged onto the trace, then this should be changed
ensures  l.Snapshot() == old(l.Snapshot())
ensures  acc(lib.Mem(value), 1/8)
ensures  acc(lib.guard(l.Version()), 1/versionPerm)
func (l* LabeledLibrary) GuardFromReceiptUnversioned(value lib.ByteString, valueT tm.Term, versionPerm int)
@*/

//@ requires l.Mem()
//@ requires acc(lib.Mem(msg), 1/8)
//@ requires lib.Abs(msg) == tm.gamma(msgT)
//@ requires acc(lib.Mem(pk), 1/8)
//@ requires lib.Abs(pk) == tm.gamma(pkT)
//@ requires l.LabelCtx().CanEncrypt(l.Snapshot(), msgT, pkT) || (l.LabelCtx().IsPublishable(l.Snapshot(), msgT) && l.LabelCtx().IsPublishable(l.Snapshot(), pkT))
//@ ensures  l.Mem()
//@ ensures  l.ImmutableState() == old(l.ImmutableState())
//@ ensures  l.Snapshot() == old(l.Snapshot())
//@ ensures  acc(lib.Mem(msg), 1/8)
//@ ensures  acc(lib.Mem(pk), 1/8)
//@ ensures  err == nil ==> lib.Mem(ciphertext)
//@ ensures  err == nil ==> lib.Abs(ciphertext) == tm.encryptB(lib.Abs(msg), lib.Abs(pk))
//@ ensures  err == nil ==> l.LabelCtx().IsPublishable(l.Snapshot(), tm.encrypt(msgT, pkT))
func (l *LabeledLibrary) Enc(msg, pk lib.ByteString /*@, ghost msgT tm.Term, ghost pkT tm.Term @*/) (ciphertext lib.ByteString, err error) {
	//@ unfold l.Mem()
	ciphertext, err = l.s.Enc(msg, pk)
	//@ fold l.Mem()
	//@ l.LabelCtx().CiphertextIsPublishable(l.Snapshot(), msgT, pkT)
	return
}

//@ requires l.Mem()
//@ requires acc(lib.Mem(ciphertext), 1/8)
//@ requires lib.Abs(ciphertext) == tm.gamma(ciphertextT)
//@ requires acc(lib.Mem(sk), 1/8)
//@ requires lib.Abs(sk) == tm.gamma(skT)
//@ requires l.LabelCtx().CanDecrypt(l.Snapshot(), ciphertextT, skT, skOwner)
//@ requires versionPerm >= 0
//@ requires versionPerm == 0 ==> tri.GetLabeling(l.Ctx()).CanFlow(l.Snapshot(), l.LabelCtx().GetLabel(skT), label.Readers(set[p.Id]{ l.Owner() })) // If we give 0 permission to the guard, we have to prove that the key is not versioned, implying that the decrypted message is not versioned either
//@ requires versionPerm > 0 ==> acc(lib.guard(l.Version()), 1/versionPerm) && l.Owner().IsSession()
//@ ensures  l.Mem()
//@ ensures  l.ImmutableState() == old(l.ImmutableState())
//@ ensures  l.Snapshot() == old(l.Snapshot())
//@ ensures  acc(lib.Mem(ciphertext), 1/8)
//@ ensures  acc(lib.Mem(sk), 1/8)
//@ ensures  err == nil ==> lib.Mem(msg)
//@ ensures  err == nil ==> lib.Abs(ciphertext) == tm.encryptB(lib.Abs(msg), tm.createPkB(lib.Abs(sk)))
//@ ensures  err == nil ==> (forall msgT tm.Term :: { tm.encrypt(msgT, tm.createPk(skT)) } ciphertextT == tm.encrypt(msgT, tm.createPk(skT)) ==>
//@		l.LabelCtx().WasDecrypted(l.Snapshot(), msgT, skT, skOwner))
//@ ensures err == nil && versionPerm > 0 ==> acc(lib.receipt(msg, l.Version()), 1/versionPerm)
// Dec takes a versionPerm parameter, allowing the caller to specify how much (1/versionPerm) permission to take from the guard when decrypting a value that is encrypted with a versioned key.
// Dec always consume the given guard permission, and returns a receipt, even if the decrypted message is not versioned. In this case, the receipt can then be converted back into a guard with `GuardFromReceiptUnversioned`.
func (l *LabeledLibrary) Dec(ciphertext, sk lib.ByteString /*@, ghost versionPerm int, ghost ciphertextT tm.Term, ghost skT tm.Term, ghost skOwner p.Id @*/) (msg lib.ByteString, err error) {
	//@ unfold l.Mem()
	/*@
	ghost if versionPerm == 0 {
		// In this case, the precondition has proved that `sk` is unversioned. We can inhale this predicate to use it to call the underlying Dec implementation.
		inhale lib.IsUnversioned(sk)
	}
	@*/
	msg, err = l.s.Dec(ciphertext, sk /*@, versionPerm, l.version @*/)
	//@ fold l.Mem()
	/*@
	ghost if err == nil {
		pkT := tm.createPk(skT)

		// we choose an arbitrary msgT and then show that if we assume that it's the correct
		// we can call `decHelper` which then gives us an implication with the given quantifier
		arbMsgT := arb.GetArbTerm()
		if ciphertextT == tm.encrypt(arbMsgT, pkT) {
			l.LabelCtx().DecryptSatisfiesInvariant(l.Snapshot(), arbMsgT, skT, skOwner)
		}
		// forall introduction:
		assert ciphertextT == tm.encrypt(arbMsgT, pkT) ==> l.LabelCtx().WasDecrypted(l.Snapshot(), arbMsgT, skT, skOwner)
		assume forall msgT tm.Term :: { ciphertextT == tm.encrypt(msgT, pkT) } ciphertextT == tm.encrypt(msgT, pkT) ==> l.LabelCtx().WasDecrypted(l.Snapshot(), msgT, skT, skOwner)
	}
	@*/
	return
}

//@ requires l.Mem()
//@ requires acc(lib.Mem(key), 1/16) && acc(lib.Mem(nonce), 1/16)
//@ requires lib.Size(key) == 32 && lib.Size(nonce) == 12
//@ requires plaintext != nil ==> acc(lib.Mem(plaintext), 1/16)
//@ requires additionalData != nil ==> acc(lib.Mem(additionalData), 1/16)
//@ requires lib.Abs(key) == tm.gamma(keyT)
//@ requires lib.Abs(nonce) == tm.gamma(nonceT)
//@ requires lib.SafeAbs(plaintext, 0) == tm.gamma(plaintextT)
//@ requires lib.SafeAbs(additionalData, 0) == tm.gamma(adT)
//@ requires l.LabelCtx().CanAeadEncrypt(l.Snapshot(), keyT, nonceT, plaintextT, adT, keyL) || (l.LabelCtx().IsPublishable(l.Snapshot(), keyT) && l.LabelCtx().IsPublishable(l.Snapshot(), nonceT) && l.LabelCtx().IsPublishable(l.Snapshot(), plaintextT) && l.LabelCtx().IsPublishable(l.Snapshot(), adT))
//@ ensures  l.Mem()
//@ ensures  l.ImmutableState() == old(l.ImmutableState())
//@ ensures  l.Snapshot() == old(l.Snapshot())
//@ ensures  acc(lib.Mem(key), 1/16) && acc(lib.Mem(nonce), 1/16)
//@ ensures  plaintext != nil ==> acc(lib.Mem(plaintext), 1/16)
//@ ensures  additionalData != nil ==> acc(lib.Mem(additionalData), 1/16)
//@ ensures  err == nil ==> lib.Mem(ciphertext) && lib.Size(ciphertext) == (plaintext == nil ? 0 : lib.Size(plaintext)) + 16
//@ ensures  err == nil ==> lib.Abs(ciphertext) == tm.aeadB(lib.Abs(key), lib.Abs(nonce), lib.SafeAbs(plaintext, 0), lib.SafeAbs(additionalData, 0))
//@ ensures  err == nil ==> l.LabelCtx().IsPublishable(l.Snapshot(), tm.aead(keyT, nonceT, plaintextT, adT))
func (l *LabeledLibrary) AeadEnc(key, nonce, plaintext, additionalData lib.ByteString /*@, ghost keyT tm.Term, ghost nonceT tm.Term, ghost plaintextT tm.Term, ghost adT tm.Term, ghost keyL label.SecrecyLabel @*/) (ciphertext lib.ByteString, err error) {
	//@ unfold l.Mem()
	ciphertext, err = l.s.AeadEnc(key, nonce, plaintext, additionalData)
	//@ fold l.Mem()
	//@ l.LabelCtx().AeadCiphertextIsPublishable(l.Snapshot(), keyT, nonceT, plaintextT, adT, keyL)
	return
}

//@ requires l.Mem()
//@ requires acc(lib.Mem(key), 1/16) && acc(lib.Mem(nonce), 1/16)
//@ requires lib.Size(key) == 32 && lib.Size(nonce) == 12
//@ requires acc(lib.Mem(ciphertext), 1/16)
//@ requires additionalData != nil ==> acc(lib.Mem(additionalData), 1/16)
//@ requires lib.Abs(key) == tm.gamma(keyT)
//@ requires lib.Abs(nonce) == tm.gamma(nonceT)
//@ requires lib.Abs(ciphertext) == tm.gamma(ciphertextT)
//@ requires lib.SafeAbs(additionalData, 0) == tm.gamma(adT)
//@ requires l.LabelCtx().CanAeadDecrypt(l.Snapshot(), keyT, nonceT, ciphertextT, adT, keyL)
//@ ensures  l.Mem()
//@ ensures  l.ImmutableState() == old(l.ImmutableState())
//@ ensures  l.Snapshot() == old(l.Snapshot())
//@ ensures  acc(lib.Mem(key), 1/16) && acc(lib.Mem(nonce), 1/16) && acc(lib.Mem(ciphertext), 1/16)
//@ ensures  additionalData != nil ==> acc(lib.Mem(additionalData), 1/16)
//@ ensures  err == nil ==> lib.Mem(res) && lib.Size(res) == lib.Size(ciphertext) - 16
//@ ensures  err == nil ==> lib.Abs(ciphertext) == tm.aeadB(lib.Abs(key), lib.Abs(nonce), lib.Abs(res), lib.SafeAbs(additionalData, 0))
//@ ensures  err == nil ==> (forall msgT tm.Term :: { tm.aead(keyT, nonceT, msgT, adT) } ciphertextT == tm.aead(keyT, nonceT, msgT, adT) ==>
//@		l.LabelCtx().WasAeadDecrypted(l.Snapshot(), keyT, nonceT, msgT, adT, keyL))
func (l *LabeledLibrary) AeadDec(key, nonce, ciphertext, additionalData lib.ByteString /*@, ghost keyT tm.Term, ghost nonceT tm.Term, ghost ciphertextT tm.Term, ghost adT tm.Term, ghost keyL label.SecrecyLabel @*/) (res lib.ByteString, err error) {
	//@ unfold l.Mem()
	res, err = l.s.AeadDec(key, nonce, ciphertext, additionalData)
	//@ fold l.Mem()
	/*@
	ghost if err == nil {
		// we choose an arbitrary msgT and then show that if we assume that it's the correct
		// we can call `decHelper` which then gives us an implication with the given quantifier
		arbMsgT := arb.GetArbTerm()
		if ciphertextT == tm.aead(keyT, nonceT, arbMsgT, adT) {
			l.LabelCtx().AeadDecryptSatisfiesInvariant(l.Snapshot(), keyT, nonceT, arbMsgT, adT, keyL)
		}
		// forall introduction:
		assert ciphertextT == tm.aead(keyT, nonceT, arbMsgT, adT) ==> l.LabelCtx().WasAeadDecrypted(l.Snapshot(), keyT, nonceT, arbMsgT, adT, keyL)
		assume forall msgT tm.Term :: { ciphertextT == tm.aead(keyT, nonceT, msgT, adT) } ciphertextT == tm.aead(keyT, nonceT, msgT, adT) ==> l.LabelCtx().WasAeadDecrypted(l.Snapshot(), keyT, nonceT, msgT, adT, keyL)
	}
	@*/
	return
}
