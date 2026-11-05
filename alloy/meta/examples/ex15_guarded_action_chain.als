module meta/examples/ex15_guarded_action_chain

/*
 * PATTERN:  A guarded ACTION CHAIN over the reified log (meta/action, DT-006 Layer 1): concrete action
 *           kinds bind typed quantifier variables (`bindings` — the "∃ x such that …" prefix); guards
 *           are made EVALUABLE by the witnessing pattern (`admission = Accepted iff <pred over the
 *           bindings + pre-projection>`); and the state after a chain of actions is QUERIED by folding
 *           the committed log prefix (`committedUpTo`). Refused actions are recorded with reasons but
 *           contribute nothing.
 * UML:      command + guard [precondition] on a sequence diagram; the log is an event store.
 * FP:       state = foldl over a filtered event list; guards = predicates evaluated at each step.
 * USE WHEN:  an operation must be admitted/refused based on the state PRODUCED BY PRIOR operations —
 *           i.e., legality depends on the chain, not on a stored snapshot.
 * AVOID:     a free `admission` verdict (then the log can record impossible histories), or re-deriving
 *           state from a `var` trace (the log IS the state carrier — DT-001.03/DT-006).
 * SEE ALSO:  meta/action/action.als; meta/action/tests/action.als (existence projection);
 *           ex14 (event-sourced level); design/meta/action; DT-006 decision 2026-07-01 (bindings).
 *
 * Neutral cast: hotel room CHECK-IN / CHECK-OUT. The admission guard reads the pre-projection ("is the
 * room occupied just before my tick?"); double check-in is refused. Occupancy after any chain is a
 * projection over committedUpTo — no `var`, no World.
 */

open meta/action/action   // Action (by, bindings, admission, commit), committed, committedUpTo, Tick order

/** Room — a toy bindable domain element (in the live model: an Entity). */
sig Room {}

/** CheckIn — binds the room it occupies (an input binding; the quantifier variable of its guard). */
sig CheckIn extends Action { into: one Room } { bindings = into }

/** CheckOut — binds the room it frees. */
sig CheckOut extends Action { from: one Room } { bindings = from }

// ── the pre-projection read: occupancy STRICTLY BEFORE a tick (what an admission guard sees) ────────
/** occupiedBefore — `r` is occupied just before `t`: a committed CheckIn of `r` strictly precedes `t`
    with no committed CheckOut of `r` strictly between them and `t`. A fold over the committed log. */
pred occupiedBefore[r: Room, t: Tick] {
  some ci: CheckIn | committed[ci] and ci.into = r and precedes[ci.tick, t] and
    (no co: CheckOut | committed[co] and co.from = r
       and precedes[ci.tick, co.tick] and precedes[co.tick, t])
}

// ── the WITNESSING PATTERN: the stored verdict is exactly the guard predicate's value ────────────────
// (Alloy cannot store a predicate as data; the per-kind fact ties the Decision to the evaluable formula.)
fact CheckInAdmission  { all a: CheckIn  | a.admission = Accepted iff not occupiedBefore[a.into, a.tick] }
fact CheckOutAdmission { all a: CheckOut | a.admission = Accepted iff occupiedBefore[a.from, a.tick] }

// ── the post-projection: occupancy AT a tick, folded from the committed prefix (committedUpTo) ──────
/** occupiedAt — the state query after a chain: fold the committed log prefix at `t`. */
pred occupiedAt[r: Room, t: Tick] {
  some ci: CheckIn & committedUpTo[t] | ci.into = r and
    (no co: CheckOut & committedUpTo[t] | co.from = r and precedes[ci.tick, co.tick])
}

// ── it works (expect SAT) ────────────────────────────────────────────────────────────────────────────
// A chain: check-in → check-out → check-in again, all committed; the final state query reads occupied.
run unit_ex15_chainThenQuery {
  some r: Room, ci1, ci2: CheckIn, co: CheckOut |
    ci1.into = r and co.from = r and ci2.into = r
    and precedes[ci1.tick, co.tick] and precedes[co.tick, ci2.tick]
    and committed[ci1] and committed[co] and committed[ci2]
    and occupiedAt[r, ci2.tick]
} for 6 expect 1

// A refusal is RECORDED (with reasons), not absent: a non-committed check-in carries its because.
run unit_ex15_refusalRecorded {
  some a: CheckIn | not committed[a] and some refusalReasons[a]
} for 5 expect 1

// ── the guard makes illegal chains unrepresentable (check; UNSAT = holds) ────────────────────────────
// Two COMMITTED check-ins to one room must have a committed check-out between them: double check-in
// cannot be committed, because the second one's admission guard reads occupiedBefore = true.
assert unit_ex15_noDoubleCheckIn {
  all disj c1, c2: CheckIn |
    (committed[c1] and committed[c2] and c1.into = c2.into and precedes[c1.tick, c2.tick])
      implies (some co: CheckOut | committed[co] and co.from = c1.into
                 and precedes[c1.tick, co.tick] and precedes[co.tick, c2.tick])
}
check unit_ex15_noDoubleCheckIn for 6 expect 0

// Refused actions contribute nothing: a room all of whose check-ins were refused is never occupied.
assert unit_ex15_refusedContributesNothing {
  all r: Room |
    (all ci: CheckIn | ci.into = r implies not committed[ci])
      implies (all t: Tick | not occupiedAt[r, t])
}
check unit_ex15_refusedContributesNothing for 6 expect 0
