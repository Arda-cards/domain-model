module resources/kanban_card/tests/cycle_retire

open resources/kanban_card/kanban_card_implementation
open resources/kanban_card/kanban_card_contracts
open resources/kanban_card/kanban_card_types as kt            // DIRECT (rule 10): the parameters below are alias-qualified
open meta/subject_log/lifecycle[kt/CardCycle, kt/CycleState] as lc   // the SHAPES for the cycle log (the cut's adoption)
open resources/inventory_item/inventory_pool as ip                       // DIRECT (rule 10): the pool's shapes below are alias-qualified
open meta/subject_log/lifecycle[ip/InventoryPool, ip/PoolState] as plc   // the POOL's shapes — to exclude membership rows in the attached-once witness

/*
 * RED-FIRST witnesses for the card cycle under the lifecycle family (Q24 (a)): `WithdrawOcc` is the EXISTING tombstone
 * (the abandon), declared under `lc/RetireOcc`; NEW `RetireCycleOcc extends lc/RetireOcc` is the COMPLETION retire — refused
 * `RNotStarted` (never started — Q199 M3, 2026-10-01; was `RClosed`), `RClosed` (already withdrawn or retired) and
 * `RCardInCirculation` (live and mid-trip: open at a NON-completable status).
 * Q25 RESOLVED (COORDINATOR-Q199 R3 + R3.1(ii), MP 2026-09-25; model cut 2026-10-01, MPBOT-11 M1): the rollover WRITES this row —
 * `rolloverPair` (retire, then the successor's genesis, adjacent); a genesis is admitted only over a CLOSED predecessor.
 * The 2026-10-01 witnesses below (M1, M3, attached-once) are RED-FIRST: at the tests-only commit the root fails to parse on
 * `RNotStarted` / `rolloverPair` / `poolAttachedOnce` / `closedBeforeSuccessorGenesis`; GREEN once the model commit lands.
 * Run RED at 1e79b89 before any sig lands: the root fails to parse on `RetireCycleOcc` / `lc`.
 * Scopes: cycle_occurrences.als (5 Int required — region ranks reach 8; the PRINT machine pinned 5/8/8/1).
 */

// ── Withdraw IS a retire shape now (the family's word, not a domain re-statement) ──────────────
run unit_cyr_withdrawIsRetireShape {
  some w: WithdrawOcc | committed[w] and w in lc/RetireOcc and not lc/retiredBefore[w]
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// ── the completion retire commits on a cycle open at a COMPLETABLE status, and tombstones ───────
run unit_cyr_retireCompletableCommits {
  some o: RetireCycleOcc | committed[o] and statusAt[o.cycle, o.tick] in completableStatuses and o.post = o.pre
    and not liveCycleAt[o.cycle, o.tick]
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// ── complement: mid-trip (live, open at a NON-completable status) → RCardInCirculation ────────
run unit_cyr_retireMidTripRefused {
  some o: RetireCycleOcc | refusedAtAdmission[o] and o.admission.because = RCardInCirculation
    and liveAtOcc[o] and o.pre.sStatus not in completableStatuses
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// ── refused after a committed Withdraw (closed) — the generic arm, the adopter's existing atom ──
run unit_cyr_retireAfterWithdrawRefused {
  some w: WithdrawOcc, o: RetireCycleOcc | committed[w] and o.subject = w.subject and precedes[w.tick, o.tick]
    and refusedAtAdmission[o] and RClosed in o.admission.because
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// ── refused on a cycle that never started — RNotStarted, the cycle's RPoolNotCreated (Q199 M3; was RClosed) ─
run unit_cyr_retireNeverStartedRefused {
  some o: RetireCycleOcc | refusedAtAdmission[o] and RNotStarted in o.admission.because and RClosed not in o.admission.because and no o.pre
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// ── complement of the pair: a Withdraw after a committed completion retire is refused ──────────
run unit_cyr_withdrawAfterRetireRefused {
  some o: RetireCycleOcc, w: WithdrawOcc | committed[o] and w.subject = o.subject and precedes[o.tick, w.tick]
    and refusedAtAdmission[w] and RClosed in w.admission.because
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// ── the forward kinds are Mutate shapes: none commits after either retire ─────────────────────
assert unit_cyr_nothingAfterRetire { lc/nothingAfterRetire }
check unit_cyr_nothingAfterRetire for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 0

// ── the existing readings survive the adoption: abandonedAt is exactly "withdrawn before t" ────
assert unit_cyr_abandonedIsWithdrawn {
  all c: CardCycle, t: Tick | abandonedAt[c, t] iff (some w: WithdrawOcc | committed[w] and w.subject = c and notAfter[w.tick, t])
}
check unit_cyr_abandonedIsWithdrawn for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 0

// ── Q42 (cut 2): a CREATED pool is fresh — the genesis row is the minting, not a use ───────────
// Written AFTER cycle_occurrences solved 29/29 with 0 mismatches (the existing witnesses never add to an attached pool):
// the collision is in the text, not in those witnesses. RED under the pre-Q42 text (the create row counts as history →
// RPoolNotFresh at the attach); GREEN once freshness reads MUTATE history only.
run unit_cyr_attachCreatedPoolThenAdd {
  some c: CreatePoolOcc, s: StartProcessingOcc, a: PoolAddOcc |
    committed[c] and committed[s] and committed[a]
    and resolve[s.pool] = c.subject and a.subject = c.subject
    and precedes[c.tick, s.tick] and precedes[s.tick, a.tick]
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 1 InventoryItem, 1 InventoryPool, 8 Tick, 8 Occurrence, 8 Snapshot, 2 Note expect 1

// complement: a USED pool (a committed add before the attach) is still refused RPoolNotFresh after Q42
run unit_cyr_attachUsedPoolRefused {
  some a: PoolAddOcc, s: StartProcessingOcc | committed[a] and resolve[s.pool] = a.subject and precedes[a.tick, s.tick]
    and refusedAtAdmission[s] and RPoolNotFresh in s.admission.because
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 1 InventoryItem, 1 InventoryPool, 8 Tick, 8 Occurrence, 8 Snapshot, 2 Note expect 1

// ══ 2026-10-01 — MPBOT-11 M1 (the rollover pairing), M3 (RNotStarted), and attached-once (V019) ══════════════════

// ── M1: the rollover is TWO rows — the completion retire on the predecessor, then the successor's genesis, adjacent ──
run unit_cyr_rolloverPair {
  some disj c1, c2: CardCycle, r: RetireCycleOcc, g: RequestOcc |
    r.subject = c1 and g.subject = c2 and rolloverPair[r, g]
    and completedAt[c1, g.tick] and not liveCycleAt[c1, g.tick] and liveCycleAt[c2, g.tick]
} for 7 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 8 Tick, 8 Occurrence, 8 Snapshot, 2 Note expect 1

// ── M1 complement: a genesis over a predecessor that is live (even at a COMPLETABLE status) is refused — the retire must come first ──
run unit_cyr_genesisOverLiveCompletablePredecessorRefused {
  some disj c1, c2: CardCycle, g: RequestOcc |
    g.subject = c2 and c2.precededBy = c1 and liveCycleAt[c1, g.tick] and statusAt[c1, g.tick] in completableStatuses
    and refusedAtAdmission[g] and RCardInCirculation in g.admission.because
} for 7 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 8 Tick, 8 Occurrence, 8 Snapshot, 2 Note expect 1

// ── M1 law: a committed successor genesis saw its predecessor closed (a theorem of requestViol) ──
assert unit_cyr_closedBeforeSuccessorGenesis { closedBeforeSuccessorGenesis }
check unit_cyr_closedBeforeSuccessorGenesis for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 0

// ── M3: a forward operation on a never-started cycle is RNotStarted, never RClosed ─────────────
run unit_cyr_forwardOnNeverStartedIsNotStarted {
  some o: AcceptOcc | refusedAtAdmission[o] and no o.pre
    and RNotStarted in o.admission.because and RClosed not in o.admission.because
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// ── M3 complement: on a WITHDRAWN cycle it is RClosed, never RNotStarted (the two atoms partition "not live") ──
run unit_cyr_forwardOnWithdrawnIsClosed {
  some w: WithdrawOcc, o: AcceptOcc | committed[w] and o.subject = w.subject and precedes[w.tick, o.tick]
    and refusedAtAdmission[o] and RClosed in o.admission.because and RNotStarted not in o.admission.because
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// ── attached-once (V019): a pool a committed StartProcessing named is USED — re-attaching it after ProductionFailure refuses ──
run unit_cyr_reattachAfterFailureRefused {
  some s1, s2: StartProcessingOcc, f: ProductionFailureOcc |
    committed[s1] and committed[f] and f.subject = s1.subject and precedes[s1.tick, f.tick] and precedes[f.tick, s2.tick]
    and resolve[s2.pool] = resolve[s1.pool]
    and (no b: plc/MutateOcc | committed[b] and b.subject in resolve[s1.pool])   // no membership row: cut 2's freshness arm has nothing to refuse
                                                                                //   on — only ATTACHED-ONCE refuses here (RED under bc58aa6). PARENTHESES: a
                                                                                //   quantifier's body runs to the end of the formula; unparenthesized it swallowed
                                                                                //   the refusal conjuncts below and the command was SAT on both models (08:19Z)
    and refusedAtAdmission[s2] and RPoolNotFresh in s2.admission.because
} for 7 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 1 InventoryItem, 1 InventoryPool, 8 Tick, 8 Occurrence, 8 Snapshot, 2 Note expect 1

// ── attached-once admission control: a REFUSED attach commits nothing, so a retry naming the same pool is admitted ──
run unit_cyr_retryAfterRefusedAttachAdmitted {
  some disj s1, s2: StartProcessingOcc | refusedAtAdmission[s1] and committed[s2]
    and resolve[s2.pool] = resolve[s1.pool] and precedes[s1.tick, s2.tick]
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 1 InventoryItem, 1 InventoryPool, 8 Tick, 8 Occurrence, 8 Snapshot, 2 Note expect 1

// ── attached-once law: at most one committed StartProcessing ever names a pool (a theorem of the freshness arm) ──
assert unit_cyr_poolAttachedOnce { poolAttachedOnce }
check unit_cyr_poolAttachedOnce for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 1 InventoryItem, 1 InventoryPool, 8 Tick, 8 Occurrence, 8 Snapshot, 2 Note expect 0
