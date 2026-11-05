module meta/action/tests/action

open meta/action/action
open meta/model_time/model_time   // precedes, notAfter (over Tick) — for the projection

/*
 * v1 (state-as-projection, bindings-over-univ). Two parts: the state-agnostic anatomy laws, and a worked
 * demonstration that System state is a PROJECTION over the reified log — here, existence reconstructed
 * from the committed Create/Delete log, with NO `World` sig. `Action` is abstract, so concrete kinds are
 * used. `Thing` is a root-LOCAL toy sig standing in for any bindable model element (in the live model a
 * binding is an Entity, a Quantity, …— anything in `univ`); the framework itself has no binding type.
 */

/** Thing — a toy bindable element (root-local; the framework binds over `univ`). */
sig Thing {}

/** Op — a concrete action with a free outcome, to exercise the anatomy. */
sig Op extends Action {} { no bindings }

// ── anatomy (state-agnostic) ─────────────────────────────────────────────────────────────────────
// A committed action exists.
run unit_action_committed { some a: Op | committed[a] } for 4 expect 1

// ONE gate (MP, Journal 193772; TN-003 row 9; the Dafny spine has no post-commit check): an admitted action IS committed.
// RED on the tree before this cut: the second gate could refuse an admitted action (SAT against expectation).
run unit_action_admittedNotCommitted { some a: Op | a.admission = Accepted and not committed[a] } for 4 expect 0

// Every refusal carries at least one reason.
assert unit_action_refusalHasReason { all a: Action | not committed[a] implies some refusalReasons[a] }
check unit_action_refusalHasReason for 5 expect 0

// A success carries no reasons.
assert unit_action_successNoReason { all a: Action | committed[a] implies no refusalReasons[a] }
check unit_action_successNoReason for 5 expect 0

// The two named outcomes PARTITION Action: every action satisfies exactly one.
assert unit_action_outcomesPartition {
  all a: Action | (committed[a] or refusedAtAdmission[a]) and not (committed[a] and refusedAtAdmission[a])
}
check unit_action_outcomesPartition for 5 expect 0

// Pre vs post projection domain: the inclusive prefix exceeds the strict one by exactly the
// committed action AT the tick (if any) — the "own contribution visible at own tick" law.
assert unit_action_prePostDomains {
  all t: Tick | committedUpTo[t] - committedBefore[t] = { a: Action | committed[a] and a.tick = t }
}
check unit_action_prePostDomains for 5 expect 0

// ── state-as-projection: existence folded from the committed Create/Delete log (no `World`) ─────────
/** Create — brings a new element into existence; bindings = the created element (an output binding). */
sig Create extends Action { made: one Thing } { bindings = made }
/** Delete — removes an existing element; bindings = the deleted element (an input binding). */
sig Delete extends Action { gone: one Thing } { bindings = gone }

/** existsAt — the existence PROJECTION over the committed log prefix (`committedUpTo`): `x` is present at
    tick `t` iff a COMMITTED Create of `x` sits at/before `t` with no COMMITTED Delete of `x` strictly
    after that create (and at/before `t`). State is a fold of the log; refused actions contribute nothing. */
pred existsAt[x: Thing, t: Tick] {
  some c: Create & committedUpTo[t] | c.made = x and
    (no d: Delete & committedUpTo[t] | d.gone = x and precedes[c.tick, d.tick])
}

// The committed prefix contains no refused action (the projection domain is exactly the committed log).
assert unit_action_prefixOnlyCommitted { all t: Tick, a: committedUpTo[t] | committed[a] }
check unit_action_prefixOnlyCommitted for 5 expect 0

// The committed prefix is monotone along model time (an earlier prefix is contained in a later one).
assert unit_action_prefixMonotone {
  all t1, t2: Tick | notAfter[t1, t2] implies committedUpTo[t1] in committedUpTo[t2]
}
check unit_action_prefixMonotone for 5 expect 0

// A committed Create projects its element into existence (state reflects committed effects).
run unit_action_createProjects {
  some c: Create | committed[c] and existsAt[c.made, c.tick]
} for 4 expect 1

// A REFUSED Create contributes nothing — its element is absent from the projection at every tick.
run unit_action_refusedCreateNoProject {
  some c: Create | not committed[c] and (all t: Tick | not existsAt[c.made, t])
} for 4 expect 1

// A committed Delete after a committed Create removes the element from the projection at the delete tick.
run unit_action_deleteProjects {
  some c: Create, d: Delete |
    committed[c] and committed[d] and c.made = d.gone
    and precedes[c.tick, d.tick] and not existsAt[c.made, d.tick]
} for 5 expect 1
