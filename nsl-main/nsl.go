// Needham-Schroeder-Lowe

// Tamarin:
// A∶ knows(sk(A),pk(B))
// B∶ knows(sk(B),pk(A))
// A∶ fresh(na)
// 1: A -> B∶ enc(⟨na, A⟩, pk(B))
// B∶ fresh(nb)
// 2: B -> A∶ enc(⟨na, nb, B⟩, pk(A))
// 3: A -> B∶ enc(nb, pk(B))

// Needham-Schroeder: B is not sent in the second message
// Therefore, A could talk to adversary E (using E's public key)
// E forwards first message to B using B's public key
// B does not non-injectively agree with A on <na, nb>

// Needham-Schroeder-Lowe: A non-injectively agrees with B on <na, nb> and vice-versa.
// secrecy holds for na and nb

// Tamarin assumptions:
// - na and nb are fresh (random) variables
// - necessary secret/public keys are known to A and B
// - message can only be decrypted if matching secret key is known
// - received na, nb, A, and B are as expected
//(-)messages have to conform to protocol, i.e. encrypted/signed as specified and contain the specified content

package nsl-main

import (
	"sync"
	lib "gitlab.inf.ethz.ch/arquintl/prototrace/labeled-library/library"
	"gitlab.inf.ethz.ch/arquintl/prototrace/labeling"
	init "gitlab.inf.ethz.ch/arquintl/prototrace/nsl-initiator"
	resp "gitlab.inf.ethz.ch/arquintl/prototrace/nsl-responder"
	shared "gitlab.inf.ethz.ch/arquintl/prototrace/nsl-shared"
	library "gitlab.inf.ethz.ch/arquintl/prototrace/nsl-shared/library"
	p "gitlab.inf.ethz.ch/arquintl/prototrace/principal"
	tm "gitlab.inf.ethz.ch/arquintl/prototrace/term"
	tr "gitlab.inf.ethz.ch/arquintl/prototrace/trace"
	tman "gitlab.inf.ethz.ch/arquintl/prototrace/tracemanager"
	two "gitlab.inf.ethz.ch/arquintl/prototrace/twostate"
)

//@ requires root == tr.makeRoot(set[tm.Term]{})
//@ requires defaultTerm == tm.zeroString(0)
// TODO remove these two dummy arguments and make them ghost
func main(/*@ root tr.TraceEntry, defaultTerm tm.Term @*/) {
	a, b, err := initPrincipals(/*@ root, defaultTerm @*/)
	if err == nil {
		// wait for the following go routines
		wg := &sync.WaitGroup{}
		//@ wg.Init()
		wg.Add(2 /*@, writePerm, PredTrue!<!>@*/)
		//@ fold PredTrue!<!>()
		//@ wg.GenerateTokenAndDebt(PredTrue!<!>)
		//@ wg.Start(1/2, PredTrue!<!>)
		// run in parallel:
		go workerA(wg, a /*@, defaultTerm @*/)
		go workerB(wg, b /*@, defaultTerm @*/)
		//@ wg.SetWaitMode(1/2, 1/2)
		wg.Wait(/*@ 1/1, seq[pred()]{ } @*/)
		lib.Println("Program has ended")
	} else {
		lib.Println("Initialization failed")
	}
}

//@ requires root == tr.makeRoot(set[tm.Term]{})
//@ requires defaultTerm == tm.zeroString(0)
//@ ensures err == nil ==> a.Mem(defaultTerm, defaultTerm) && a.Version(defaultTerm, defaultTerm) == 1
//@ ensures err == nil ==> b.Mem(defaultTerm, defaultTerm) && b.Version(defaultTerm, defaultTerm) == 1
// TODO remove these two dummy arguments and make them ghost
func initPrincipals(/*@ root tr.TraceEntry, defaultTerm tm.Term @*/) (a *init.A, b *resp.B, err error) {
	initiator := "Initiator"
	responder := "Responder"
	//@ ctx := shared.GetNslContext() // TODO make ghost
	l := lib.NewLibrary(initiator, responder)
	//@ initManager, respManager := createManagers(root, defaultTerm, ctx, initiator, responder)
	a, err = init.initA(l, initiator, responder /*@, initManager, defaultTerm @*/)
	// ghost var s1 tr.TraceEntry
	if (err == nil) {
		//@ unfold acc(a.Mem(defaultTerm, defaultTerm), 1/2)
		// s1 = a.llib.Snapshot()
		//@ unfold acc(a.llib.Mem(), 1/2)
		respManager.SetSnapshot(initManager, ctx, responder, initiator)
		//@ fold acc(a.llib.Mem(), 1/2)
		//@ fold acc(a.Mem(defaultTerm, defaultTerm), 1/2)
		b, err = resp.initB(l, initiator, responder /*@, respManager, defaultTerm @*/)
	}
	if (err == nil) {
		//@ unfold a.Mem(defaultTerm, defaultTerm)
		//@ unfold a.llib.Mem()
		//@ unfold acc(b.Mem(defaultTerm, defaultTerm), 1/2)
		// s2 := b.llib.Snapshot()
		//@ unfold acc(b.llib.Mem(), 1/2)
		initManager.SetSnapshot(respManager, ctx, initiator, responder)
		//@ fold acc(b.llib.Mem(), 1/2)
		//@ fold acc(b.Mem(defaultTerm, defaultTerm), 1/2)
		//@ fold a.llib.Mem()
		// with apply montonicity: 76.54s
		//@ a.llib.ApplyMonotonicity()
		// with IsValidMonotonic 77.31s
		// (a.llib.LabelCtx()).IsValidMonotonic(s1, s2, a.skAT)
		//@ fold a.Mem(defaultTerm, defaultTerm)
	}
	if err == nil {
		// the following assert stmt is necessary to avoid triggering a bug in Silicon:
		//@ assert a.Version(defaultTerm, defaultTerm) == 0
		//@ unfold a.Mem(defaultTerm, defaultTerm)
		//@ unfold b.Mem(defaultTerm, defaultTerm)
		a.pkB = b.pkB
		//@ a.skBT = b.skBT
		a.version = 1
		b.pkA = a.pkA
		//@ b.skAT = a.skAT
		b.version = 1
		//@ fold a.Mem(defaultTerm, defaultTerm)
		//@ fold b.Mem(defaultTerm, defaultTerm)
	}
}

/*@
// TODO make ghost
requires initiator != responder
requires root == tr.makeRoot(set[tm.Term]{})
requires defaultTerm == tm.zeroString(0)
ensures  initManager.Mem(ctx, initiator)
ensures  respManager.Mem(ctx, responder)
ensures  initManager.ImmutableState(ctx, initiator) == respManager.ImmutableState(ctx, responder)
func createManagers(root tr.TraceEntry, defaultTerm tm.Term, ctx shared.NslContext, initiator, responder p.Principal) (initManager, respManager *tman.TraceManager) {
	participants := []p.Principal { initiator, responder }
	fold tr.validTrace(ctx, root)
	managers := tman.NewTraceManager(ctx, participants, root, perm(1)/2)
	initManager = managers[participants[0]]
	respManager = managers[participants[1]]
}
@*/

//@ requires wg.UnitDebt(PredTrue!<!>)
//@ requires a.Mem(defaultTerm, defaultTerm) && a.Version(defaultTerm, defaultTerm) == 1
func workerA(wg *sync.WaitGroup, a *init.A /*@, defaultTerm tm.Term @*/) {
	err /*@, naT, nbT @*/ := init.runA(a /*@, defaultTerm @*/)
	if err != nil {
		lib.Println("An error occurred in A")
	}
	//@ fold PredTrue!<!>()
	//@ wg.PayDebt(PredTrue!<!>)
	wg.Done()
}

//@ requires wg.UnitDebt(PredTrue!<!>)
//@ requires b.Mem(defaultTerm, defaultTerm) && b.Version(defaultTerm, defaultTerm) == 1
func workerB(wg *sync.WaitGroup, b *resp.B /*@, defaultTerm tm.Term @*/) {
	err /*@, naT, nbT @*/ := resp.runB(b /*@, defaultTerm @*/)
	if err != nil {
		lib.Println("An error occurred in B")
	}
	//@ fold PredTrue!<!>()
	//@ wg.PayDebt(PredTrue!<!>)
	wg.Done()
}
