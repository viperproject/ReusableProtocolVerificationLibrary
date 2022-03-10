package principal

type Principal = string

/*@
type Id domain {
	// constructors
	func principalId(Principal) Id
	func sessionId(Principal, int) Id
	func stepId(Principal, int, int) Id

	// deconstructors
	func getIdPrincipal(Id) Principal
	func getIdSession(Id) int
	func getIdStep(Id) int

	axiom { // principalId is injective
		forall principal Principal :: { principalId(principal) } getIdPrincipal(principalId(principal)) == principal
	}

	axiom { // sessionId is injective
		forall principal Principal, session int :: { sessionId(principal, session) } getIdPrincipal(sessionId(principal, session)) == principal &&
			getIdSession(sessionId(principal, session)) == session
	}

	axiom { // stepId is injective
		forall principal Principal, session, step int :: { stepId(principal, session, step) } getIdPrincipal(stepId(principal, session, step)) == principal &&
			getIdSession(stepId(principal, session, step)) == session &&
			getIdStep(stepId(principal, session, step)) == step
	}
}

ghost
decreases
pure func (id Id) getPrincipal() Principal {
	return getIdPrincipal(id)
}
@*/
