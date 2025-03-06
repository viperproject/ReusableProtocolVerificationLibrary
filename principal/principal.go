package principal

type Principal = string

/*@
ghost type Id domain {
	// constructors
	// type 0
	func principalId(Principal) Id
	// type 1
	func sessionId(Principal, uint32) Id
	// type 2; similar to type1 but allows to distinguish between
	// different threads belonging to the same session
	func sessionThreadId(Principal, uint32, uint32) Id
	// type 3
	func stepId(Principal, uint32, uint32) Id

	// deconstructors
	func getIdType(Id) int
	func getIdPrincipal(Id) Principal
	func getIdSession(Id) uint32
	func getIdThread(Id) uint32
	func getIdStep(Id) uint32

	// WARNING: adapt first axiom if another Id is added!

    axiom { // every Id belongs to a known type
        forall id Id :: { getIdType(id) } 0 <= getIdType(id) && getIdType(id) <= 3
    }

	axiom { // principalId is injective
		forall principal Principal :: { principalId(principal) } getIdType(principalId(principal)) == 0 &&
			getIdPrincipal(principalId(principal)) == principal
	}
	axiom { // principalId implies its constructions
        forall id Id :: { getIdType(id) } getIdType(id) == 0 ==>
            id == principalId(getIdPrincipal(id))
    }

	axiom { // sessionId is injective
		forall principal Principal, session uint32 :: { sessionId(principal, session) } getIdType(sessionId(principal, session)) == 1 &&
			getIdPrincipal(sessionId(principal, session)) == principal &&
			getIdSession(sessionId(principal, session)) == session
	}
	axiom { // sessionId implies its constructions
        forall id Id :: { getIdType(id) } getIdType(id) == 1 ==>
            id == sessionId(getIdPrincipal(id), getIdSession(id))
    }

	axiom { // sessionThreadId is injective
		forall principal Principal, session, threadId uint32 :: { sessionThreadId(principal, session, threadId) } getIdType(sessionThreadId(principal, session, threadId)) == 2 &&
			getIdPrincipal(sessionThreadId(principal, session, threadId)) == principal &&
			getIdSession(sessionThreadId(principal, session, threadId)) == session &&
			getIdThread(sessionThreadId(principal, session, threadId)) == threadId
	}
	axiom { // sessionThreadId implies its constructions
        forall id Id :: { getIdType(id) } getIdType(id) == 2 ==>
            id == sessionThreadId(getIdPrincipal(id), getIdSession(id), getIdThread(id))
    }

	axiom { // stepId is injective
		forall principal Principal, session, step uint32 :: { stepId(principal, session, step) } getIdType(stepId(principal, session, step)) == 3 &&
			getIdPrincipal(stepId(principal, session, step)) == principal &&
			getIdSession(stepId(principal, session, step)) == session &&
			getIdStep(stepId(principal, session, step)) == step
	}
	axiom { // stepId implies its constructions
        forall id Id :: { getIdType(id) } getIdType(id) == 3 ==>
            id == stepId(getIdPrincipal(id), getIdSession(id), getIdStep(id))
    }
}

ghost
decreases
ensures res == principalId(principal)
pure func NewPrincipalId(principal Principal) (res Id)

ghost
decreases
pure func (id Id) IsPrincipal() bool {
	return getIdType(id) == 0
}

ghost
decreases
pure func (id Id) IsSession() bool {
	return getIdType(id) == 1
}

ghost
decreases
pure func (id Id) IsSessionThread() bool {
	return getIdType(id) == 2
}

ghost
decreases
pure func (id Id) IsVersion() bool {
	return getIdType(id) == 3
}

ghost
decreases
pure func (id Id) getPrincipal() Principal {
	return getIdPrincipal(id)
}

ghost
decreases
pure func (id Id) getSession() option[uint32] {
	return id.IsPrincipal() ? none[uint32] :
		some(getIdSession(id))
}

ghost
decreases
pure func (id Id) getPrincipalId() Id {
	return principalId(id.getPrincipal())
}

ghost
decreases
// returns true iff `id1` covers `id2` meaning that versions covered by `id1`
// is equal or a superset of the versions covered by `id2`
pure func (id1 Id) Covers(id2 Id) bool {
	return id1.IsPrincipal() ? (id1.getPrincipal() == id2.getPrincipal()) :
		id1.IsSession() || id1.IsSessionThread() ? (id1.getPrincipal() == id2.getPrincipal() &&
			id1.getSession() == id2.getSession()) :
		id1 == id2 // if id1 is a version
}

ghost
decreases
ensures id1.Covers(id1)
func (id1 Id) CoversReflexive() {
	// no body needed
}

ghost
decreases
requires id1.Covers(id2) && id2.Covers(id3)
ensures  id1.Covers(id3)
func (id1 Id) CoversTransitive(id2, id3 Id) {
	// no body needed
}

ghost
decreases
ensures id.getPrincipalId().Covers(id)
func (id Id) CoveredByPrincipal() {
	// no body needed
}
@*/
