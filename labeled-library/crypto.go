package labeledLibrary

import (
	ev "gitlab.inf.ethz.ch/arquintl/prototrace/event"
	fa "gitlab.inf.ethz.ch/arquintl/prototrace/forall"
	"gitlab.inf.ethz.ch/arquintl/prototrace/label"
	"gitlab.inf.ethz.ch/arquintl/prototrace/labeling"
	lib "gitlab.inf.ethz.ch/arquintl/prototrace/labeled-library/library"
	p "gitlab.inf.ethz.ch/arquintl/prototrace/principal"
	tm "gitlab.inf.ethz.ch/arquintl/prototrace/term"
	u "gitlab.inf.ethz.ch/arquintl/prototrace/usage"
)

//@ requires l.Mem()
//@ ensures  l.Mem()
//@ ensures  l.ImmutableState() == old(l.ImmutableState())
//@ ensures  old(l.Snapshot()).isSuffix(l.Snapshot())
//@ ensures  err == nil ==> lib.Mem(nonce) && lib.Size(nonce) == lib.NonceLength
//@ ensures  err == nil ==> lib.Abs(nonce) == tm.gamma(tm.random(lib.Abs(nonce), nonceLabel, u.Nonce(usageString)))
//@ ensures  err == nil ==> (l.Snapshot()).isNonceAt(tm.random(lib.Abs(nonce), nonceLabel, u.Nonce(usageString)))
//@ ensures  err == nil ==> forall eventType ev.EventType :: { eventType in eventTypes } eventType in eventTypes ==> (l.LabelCtx()).NonceForEventIsUnique(tm.random(lib.Abs(nonce), nonceLabel, u.Nonce(usageString)), eventType)
func (l *LabeledLibrary) CreateNonce(/*@ ghost nonceLabel label.SecrecyLabel, ghost usageString string, ghost eventTypes set[ev.EventType] @*/) (nonce lib.ByteString, err error) {
	//@ unfold l.Mem()
	nonce, err = l.s.CreateNonce(/*@ l.ctx.GetLabeling(), nonceLabel, usageString, eventTypes @*/)
	// store nonce on trace
	/*@
	ghost if (err == nil) {
		nonceT := tm.random(lib.Abs(nonce), nonceLabel, u.Nonce(usageString))
		l.manager.LogNonce(l.ctx, l.owner, nonceT)
	}
	@*/
	//@ fold l.Mem()
	return
}

//@ requires l.Mem()
//@ ensures  l.Mem()
//@ ensures  l.ImmutableState() == old(l.ImmutableState())
//@ ensures  old(l.Snapshot()).isSuffix(l.Snapshot())
//@ ensures  err == nil ==> lib.Mem(pk) && lib.Size(pk) == 32
//@ ensures  err == nil ==> lib.Mem(sk) && lib.Size(sk) == 32
//@ ensures  err == nil ==> lib.Abs(sk) == tm.gamma(skT) && lib.Abs(pk) == tm.createPkB(lib.Abs(sk))
//@ ensures  err == nil ==> (l.Snapshot()).isNonceAt(skT)
//@ ensures  err == nil ==> skT == tm.random(lib.Abs(sk), label.Readers(set[p.Id]{ p.principalId(l.Owner()) }), u.PkeKey(usageString))
// TODO make skT ghost
func (l *LabeledLibrary) GenerateKey(/*@ ghost usageString string @*/) (pk, sk lib.ByteString, err error /*@, skT tm.Term @*/) {
	//@ unfold l.Mem()
	//@ keyLabel := label.Readers(set[p.Id]{ p.principalId(l.owner) })
	pk, sk, err = l.s.GenerateKey(/*@ l.ctx.GetLabeling(), keyLabel, usageString, set[ev.EventType]{} @*/)
	// store sk on trace
	/*@
	ghost if (err == nil) {
		skT = tm.random(lib.Abs(sk), keyLabel, u.PkeKey(usageString))
		l.manager.LogNonce(l.ctx, l.owner, skT)
	}
	@*/
	//@ fold l.Mem()
	return
}

//@ requires l.Mem()
//@ requires acc(lib.Mem(msg), 1/8)
//@ requires lib.Abs(msg) == tm.gamma(msgT)
//@ requires acc(lib.Mem(recv_pk), 1/8) && lib.Size(recv_pk) == 32
//@ requires lib.Abs(recv_pk) == tm.gamma(recv_pkT)
//@ requires acc(lib.Mem(sender_sk), 1/8) && lib.Size(sender_sk) == 32
//@ requires (l.LabelCtx()).CanEncrypt(l.Snapshot(), msgT, recv_pkT) || ((l.LabelCtx()).IsPublishable(l.Snapshot(), msgT) && (l.LabelCtx()).IsPublishable(l.Snapshot(), recv_pkT))
//@ ensures  l.Mem()
//@ ensures  l.ImmutableState() == old(l.ImmutableState())
//@ ensures  l.Snapshot() == old(l.Snapshot())
//@ ensures  acc(lib.Mem(msg), 1/8)
//@ ensures  acc(lib.Mem(recv_pk), 1/8)
//@ ensures  acc(lib.Mem(sender_sk), 1/8)
//@ ensures  err == nil ==> lib.Mem(ciphertext)
//@ ensures  err == nil ==> lib.Size(ciphertext) == lib.Size(msg) + lib.NonceLength + 16
//@ ensures  err == nil ==> lib.Abs(ciphertext) == tm.encryptB(lib.Abs(msg), lib.Abs(recv_pk))
// ensures  err == nil ==> lib.Abs(ciphertext) == tm.gamma(tm.encrypt(msgT, recv_pkT))
//@ ensures  err == nil ==> (l.LabelCtx()).IsPublishable(l.Snapshot(), tm.encrypt(msgT, recv_pkT))
func (l *LabeledLibrary) Enc(msg, recv_pk, sender_sk lib.ByteString /*@, ghost msgT tm.Term, ghost recv_pkT tm.Term @*/) (ciphertext lib.ByteString, err error) {
	//@ unfold l.Mem()
	ciphertext, err = l.s.Enc(msg, recv_pk, sender_sk)
	//@ fold l.Mem()
	//@ (l.LabelCtx()).CiphertextIsPublishable(l.Snapshot(), msgT, recv_pkT)
	return
}

//@ requires l.Mem()
//@ requires acc(lib.Mem(ciphertext), 1/8)
//@ requires lib.Abs(ciphertext) == tm.gamma(ciphertextT)
//@ requires acc(lib.Mem(sender_pk), 1/8) && lib.Size(sender_pk) == 32
//@ requires acc(lib.Mem(recv_sk), 1/8) && lib.Size(recv_sk) == 32
//@ requires lib.Abs(recv_sk) == tm.gamma(recv_skT)
//@ requires (l.LabelCtx()).CanDecrypt(l.Snapshot(), ciphertextT, recv_skT, skOwner)
//@ ensures  l.Mem()
//@ ensures  l.ImmutableState() == old(l.ImmutableState())
//@ ensures  l.Snapshot() == old(l.Snapshot())
//@ ensures  acc(lib.Mem(ciphertext), 1/8)
//@ ensures  acc(lib.Mem(sender_pk), 1/8)
//@ ensures  acc(lib.Mem(recv_sk), 1/8)
//@ ensures  err == nil ==> lib.Mem(msg)
//@ ensures  err == nil ==> lib.Size(msg) == lib.Size(ciphertext) - lib.NonceLength - 16
//@ ensures  err == nil ==> lib.Abs(ciphertext) == tm.encryptB(lib.Abs(msg), tm.createPkB(lib.Abs(recv_sk)))
//@ ensures err == nil ==> (forall msgT tm.Term :: { tm.encrypt(msgT, tm.createPk(recv_skT)) } ciphertextT == tm.encrypt(msgT, tm.createPk(recv_skT)) ==>
//@		(l.LabelCtx()).WasDecrypted(l.Snapshot(), msgT, recv_skT, skOwner))
func (l *LabeledLibrary) Dec(ciphertext, sender_pk, recv_sk lib.ByteString /*@, ghost ciphertextT tm.Term, ghost recv_skT tm.Term, ghost skOwner p.Id @*/) (msg lib.ByteString, err error) {
	//@ unfold l.Mem()
	msg, err = l.s.Dec(ciphertext, sender_pk, recv_sk)
	//@ fold l.Mem()
	/*@
	ghost if (err == nil) {
		pkT := tm.createPk(recv_skT)

		// we choose an arbitrary msgT and then show that if we assume that it's the correct
		// we can call `decHelper` which then gives us an implication with the given quantifier
		arbMsgT := fa.GetArbTerm()
		if (ciphertextT == tm.encrypt(arbMsgT, pkT)) {
			(l.LabelCtx()).DecryptSatisfiesInvariant(l.Snapshot(), arbMsgT, recv_skT, skOwner)
		}
		// forall introduction:
		assert ciphertextT == tm.encrypt(arbMsgT, pkT) ==> (l.LabelCtx()).WasDecrypted(l.Snapshot(), arbMsgT, recv_skT, skOwner)
		assume forall msgT tm.Term :: { ciphertextT == tm.encrypt(msgT, pkT) } ciphertextT == tm.encrypt(msgT, pkT) ==> (l.LabelCtx()).WasDecrypted(l.Snapshot(), msgT, recv_skT, skOwner)
	}
	@*/
	return
}
