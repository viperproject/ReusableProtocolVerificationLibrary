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

package nslmain

import (
	"sync"
	lib "gitlab.inf.ethz.ch/arquintl/prototrace/labeledlibrary/library"
	//@ "gitlab.inf.ethz.ch/arquintl/prototrace/labeling"
	initiator "gitlab.inf.ethz.ch/arquintl/prototrace/nslinitiator"
	responder "gitlab.inf.ethz.ch/arquintl/prototrace/nslresponder"
	//@ shared "gitlab.inf.ethz.ch/arquintl/prototrace/nslshared"
	//@ p "gitlab.inf.ethz.ch/arquintl/prototrace/principal"
	//@ tm "gitlab.inf.ethz.ch/arquintl/prototrace/term"
	//@ tr "gitlab.inf.ethz.ch/arquintl/prototrace/trace"
	//@ tman "gitlab.inf.ethz.ch/arquintl/prototrace/tracemanager"
	//@ two "gitlab.inf.ethz.ch/arquintl/prototrace/twostate"
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
//@ ensures err == nil ==> a.Mem(defaultTerm, defaultTerm) && a.Vers(defaultTerm, defaultTerm) == 1
//@ ensures err == nil ==> b.Mem(defaultTerm, defaultTerm) && b.Vers(defaultTerm, defaultTerm) == 1
// TODO remove these two dummy arguments and make them ghost
func initPrincipals(/*@ root tr.TraceEntry, defaultTerm tm.Term @*/) (a *initiator.A, b *responder.B, err error) {
	pInitiator := "Initiator"
	pResponder := "Responder"
	//@ ctx := shared.GetNslContext() // TODO make ghost
	l := lib.NewLibrary(pInitiator, pResponder)
	//@ initManager, respManager := createManagers(root, defaultTerm, ctx, pInitiator, pResponder)
	a, err = initiator.InitA(l, pInitiator, pResponder /*@, initManager, defaultTerm @*/)
	// ghost var s1 tr.TraceEntry
	if (err == nil) {
		//@ unfold acc(a.Mem(defaultTerm, defaultTerm), 1/2)
		// s1 = a.llib.Snapshot()
		//@ unfold acc(a.llib.Mem(), 1/2)
		//@ respManager.SetSnapshot(initManager, ctx, pResponder, pInitiator)
		//@ fold acc(a.llib.Mem(), 1/2)
		//@ fold acc(a.Mem(defaultTerm, defaultTerm), 1/2)
		b, err = responder.InitB(l, pInitiator, pResponder /*@, respManager, defaultTerm @*/)
	}
	if (err == nil) {
		//@ unfold a.Mem(defaultTerm, defaultTerm)
		//@ unfold a.llib.Mem()
		//@ unfold acc(b.Mem(defaultTerm, defaultTerm), 1/2)
		// s2 := b.llib.Snapshot()
		//@ unfold acc(b.llib.Mem(), 1/2)
		//@ initManager.SetSnapshot(respManager, ctx, pInitiator, pResponder)
		//@ fold acc(b.llib.Mem(), 1/2)
		//@ fold acc(b.Mem(defaultTerm, defaultTerm), 1/2)
		//@ fold a.llib.Mem()
		// with apply montonicity: 76.54s
		//@ a.llib.ApplyMonotonicity()
		// with IsValidMonotonic 77.31s
		// (a.llib.LabelCtx()).IsValidMonotonic(s1, s2, a.SkAT)
		//@ fold a.Mem(defaultTerm, defaultTerm)
	}
	if err == nil {
		// the following assert stmt is necessary to avoid triggering a bug in Silicon:
		//@ assert a.Vers(defaultTerm, defaultTerm) == 0
		//@ unfold a.Mem(defaultTerm, defaultTerm)
		//@ unfold b.Mem(defaultTerm, defaultTerm)
		a.PkB = b.PkB
		//@ a.SkBT = b.SkBT
		a.Version = 1
		b.PkA = a.PkA
		//@ b.SkAT = a.SkAT
		b.Version = 1
		//@ fold a.Mem(defaultTerm, defaultTerm)
		//@ fold b.Mem(defaultTerm, defaultTerm)
	}
	return
}

/*@
// TODO make ghost
requires pInitiator != pResponder
requires root == tr.makeRoot(set[tm.Term]{})
requires defaultTerm == tm.zeroString(0)
ensures  initManager.Mem(ctx, pInitiator)
ensures  respManager.Mem(ctx, pResponder)
ensures  initManager.ImmutableState(ctx, pInitiator) == respManager.ImmutableState(ctx, pResponder)
func createManagers(root tr.TraceEntry, defaultTerm tm.Term, ctx shared.NslContext, pInitiator, pResponder p.Principal) (initManager, respManager *tman.TraceManager) {
	participants := []p.Principal { pInitiator, pResponder }
	fold tr.validTrace(ctx, root)
	managers := tman.NewTraceManager(ctx, participants, root, perm(1)/2)
	initManager = managers[participants[0]]
	respManager = managers[participants[1]]
}
@*/

//@ requires wg.UnitDebt(PredTrue!<!>)
//@ requires a.Mem(defaultTerm, defaultTerm) && a.Vers(defaultTerm, defaultTerm) == 1
func workerA(wg *sync.WaitGroup, a *initiator.A /*@, defaultTerm tm.Term @*/) {
	err /*@, naT, nbT @*/ := initiator.RunA(a /*@, defaultTerm @*/)
	if err != nil {
		lib.Println("An error occurred in A")
	}
	//@ fold PredTrue!<!>()
	//@ wg.PayDebt(PredTrue!<!>)
	wg.Done()
}

//@ requires wg.UnitDebt(PredTrue!<!>)
//@ requires b.Mem(defaultTerm, defaultTerm) && b.Vers(defaultTerm, defaultTerm) == 1
func workerB(wg *sync.WaitGroup, b *responder.B /*@, defaultTerm tm.Term @*/) {
	err /*@, naT, nbT @*/ := responder.RunB(b /*@, defaultTerm @*/)
	if err != nil {
		lib.Println("An error occurred in B")
	}
	//@ fold PredTrue!<!>()
	//@ wg.PayDebt(PredTrue!<!>)
	wg.Done()
}
