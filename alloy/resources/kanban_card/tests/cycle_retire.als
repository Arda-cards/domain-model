module resources/kanban_card/tests/cycle_retire

open resources/kanban_card/kanban_card_implementation
open resources/kanban_card/kanban_card_contracts
open resources/kanban_card/kanban_card_types as kt            // DIRECT (rule 10): the parameters below are alias-qualified
open meta/subject_log/lifecycle[kt/CardCycle, kt/CycleState] as lc   // the SHAPES for the cycle log (the cut's adoption)

/*
 * RED-FIRST witnesses for the card cycle under the lifecycle family (Q24 (a)): `WithdrawOcc` is the EXISTING tombstone
 * (the abandon), declared under `lc/RetireOcc`; NEW `RetireCycleOcc extends lc/RetireOcc` is the COMPLETION retire — refused
 * `RClosed` (never started / already withdrawn or retired) and `RCardInCirculation` (live and NOT rolloverEligible: mid-trip).
 * The rollover row (Q25) is NOT assumed here: no witness relies on the successor's genesis writing a retire row.
 * Run RED at 1e79b89 before any sig lands: the root fails to parse on `RetireCycleOcc` / `lc`.
 * Scopes: cycle_occurrences.als (5 Int required — region ranks reach 8; the PRINT machine pinned 5/8/8/1).
 */

// ── Withdraw IS a retire shape now (the family's word, not a domain re-statement) ──────────────
run unit_cyr_withdrawIsRetireShape {
  some w: WithdrawOcc | committed[w] and w in lc/RetireOcc and not lc/retiredBefore[w]
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// ── the completion retire commits on a cycle open at a COMPLETABLE status, and tombstones ───────
run unit_cyr_retireCompletableCommits {
  some o: RetireCycleOcc | committed[o] and statusAt[o.cycle, o.tick] in completableStatuses and o.post = o.pre
    and not liveCycleAt[o.cycle, o.tick]
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// ── complement: mid-trip (live, not rolloverEligible) → RCardInCirculation ─────────────────────
run unit_cyr_retireMidTripRefused {
  some o: RetireCycleOcc | refusedAtAdmission[o] and o.admission.because = RCardInCirculation
    and liveAtOcc[o] and not rolloverEligible[o.cycle, o.tick]
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// ── refused after a committed Withdraw (closed) — the generic arm, the adopter's existing atom ──
run unit_cyr_retireAfterWithdrawRefused {
  some w: WithdrawOcc, o: RetireCycleOcc | committed[w] and o.subject = w.subject and precedes[w.tick, o.tick]
    and refusedAtAdmission[o] and RClosed in o.admission.because
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// ── refused on a cycle that never started ──────────────────────────────────────────────────────
run unit_cyr_retireNeverStartedRefused {
  some o: RetireCycleOcc | refusedAtAdmission[o] and RClosed in o.admission.because and no o.pre
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// ── complement of the pair: a Withdraw after a committed completion retire is refused ──────────
run unit_cyr_withdrawAfterRetireRefused {
  some o: RetireCycleOcc, w: WithdrawOcc | committed[o] and w.subject = o.subject and precedes[o.tick, w.tick]
    and refusedAtAdmission[w] and RClosed in w.admission.because
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// ── the forward kinds are Mutate shapes: none commits after either retire ─────────────────────
assert unit_cyr_nothingAfterRetire { lc/nothingAfterRetire }
check unit_cyr_nothingAfterRetire for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 0

// ── the existing readings survive the adoption: abandonedAt is exactly "withdrawn before t" ────
assert unit_cyr_abandonedIsWithdrawn {
  all c: CardCycle, t: Tick | abandonedAt[c, t] iff (some w: WithdrawOcc | committed[w] and w.subject = c and notAfter[w.tick, t])
}
check unit_cyr_abandonedIsWithdrawn for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 0
