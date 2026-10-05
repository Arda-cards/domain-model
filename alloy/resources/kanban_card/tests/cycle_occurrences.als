module resources/kanban_card/tests/cycle_occurrences

open resources/kanban_card/kanban_card_implementation
open resources/kanban_card/kanban_card_contracts

/*
 * Suite for the CardCycle occurrence log (DT-015 Phase A bones). Premises via the P1 profile in
 * the cone. Card-level readings live HERE for Phase A (they move into the slimmed kanban_card
 * module in Phase B): currentCycleAt / the one-live-cycle theorem need the card's containment
 * facts (Phase B: `currentCycleAt` lives in kanban_card.als). Scope notes: only the PRINT machine
 * remains reified (Phase B retired the op machine) — pins are 5 State / 8 Signal / 8 Transition /
 * 1 StateMachine; `5 Int` is REQUIRED — the region ranks reach 8, which overflows 4-bit Int.
 */

// ── witnesses ───────────────────────────────────────────────────────────────────────────────────
// Genesis births the cycle demanding: REQUESTING, live, empty-handed.
run unit_cyc_genesisBirths {
  some o: RequestOcc | committed[o]
    and statusAt[o.cycle, o.tick] = REQUESTING
    and liveCycleAt[o.cycle, o.tick]
    and no stateOfCycleAt[o.cycle, o.tick].sPool
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// The demand leg progresses: Request → Accept → StartProcessing, each reading the prior record.
run unit_cyc_demandLegChain {
  some c: CardCycle, r: RequestOcc, a: AcceptOcc, s: StartProcessingOcc | {
    r.cycle = c and a.cycle = c and s.cycle = c
    precedes[r.tick, a.tick] and precedes[a.tick, s.tick]
    committed[r] and committed[a] and committed[s]
    statusAt[c, s.tick] = IN_PROCESS
  }
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// KQ-S9 in action: with REQUESTED inactive, StartProcessing SKIPS it straight from REQUESTING.
run unit_cyc_skipsInactiveStatus {
  REQUESTED not in LifecycleConfig.active
  some r: RequestOcc, s: StartProcessingOcc | {
    s.cycle = r.cycle and precedes[r.tick, s.tick]
    committed[r] and committed[s] and s.pre.sStatus = REQUESTING
  }
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// Shelve — the sanctioned backward step: REQUESTED → REQUESTING.
run unit_cyc_shelveStepsBack {
  some a: AcceptOcc, sh: ShelveOcc | {
    sh.cycle = a.cycle and precedes[a.tick, sh.tick]
    committed[a] and committed[sh]
    statusAt[sh.cycle, sh.tick] = REQUESTING
  }
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// The pool story (KD12 revised): StartProcessing attaches a pool; a PoolAddOcc on the pool's own
// log (interleaved on the shared Tick order) fills it — pool-present-but-empty and pool-with-stock
// are both readable, distinct from no-pool.
run unit_cyc_poolAttachesThenFills {
  some sp: StartProcessingOcc, a: PoolAddOcc | {
    committed[sp] and committed[a]
    resolve[sp.pool] = a.pool and precedes[sp.tick, a.tick]
    no heldAt[a.pool, sp.tick]                                   // attached empty here (allowed, not required)
    some heldAt[a.pool, a.tick]                                  // filled by the pool log
    some stateOfCycleAt[sp.cycle, a.tick].sPool                  // still attached on the cycle side
  }
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 2 InventoryItem, 1 InventoryPool, 2 Note expect 1

// TOMBSTONE: `unit_cyc_residuePoolAttaches` stood here (RESIDUE ALLOWED — a pool with
// left-over stock could attach DIRECTLY). RETIRED — reverses the 2026-07-03 residue-at-attach
// ruling per DT-020 §8.5.3 (ownership-by-genesis; residue reaches a cycle's pool only by
// item-level moves) and docket SPEARHEAD-D1 A′-2 (MP, 2026-08-27). Its exact scenario is
// folded into `unit_start_usedPoolRefused` below as the RED→GREEN pair: before the
// `RPoolNotFresh` arm, `sp` was ACCEPTED in this shape (this old test, expect 1/SAT); after,
// it is REFUSED with exactly `RPoolNotFresh` — same shape, opposite verdict.
run unit_start_usedPoolRefused {
  some sp: StartProcessingOcc | {
    some heldAt[resolve[sp.pool] & InventoryPool, sp.tick]        // residue present AT attach —
                                                                   //   i.e. committed history before sp.tick
    refusedAtAdmission[sp] and sp.admission.because = RPoolNotFresh
  }
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 2 InventoryItem, 1 InventoryPool, 2 Note expect 1

// The POSITIVE companion: a FRESH pool (no committed history before the attach tick) is
// accepted normally — freshness does not block an ordinary first attach.
run unit_start_freshPoolAccepted {
  some sp: StartProcessingOcc | committed[sp]
    and no b: PoolOcc | committed[b] and b.pool = (resolve[sp.pool] & InventoryPool) and precedes[b.tick, sp.tick]
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 2 InventoryItem, 1 InventoryPool, 2 Note expect 1

// EXCLUSIVITY: attaching a pool held by another LIVE cycle is refused with RPoolInUse.
run unit_cyc_poolInUseRefused {
  some o: StartProcessingOcc | refusedAtAdmission[o] and RPoolInUse in o.admission.because
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 1 InventoryPool, 2 Note expect 1

// HOMOGENEITY (DT-015 R1, MP 2026-07-16): attaching a pool of a DIFFERENT Item than the card
// demands is refused with exactly RPoolWrongItem (the sight-of-card guard — the admission reads
// the owning card's itemRef). Exactness is the anti-vacuity load: the sole violation forces the
// pool to resolve, sit in-tenant, be unheld, and the forward step to be legal.
run unit_cyc_poolWrongItemRefused {
  some o: StartProcessingOcc | refusedAtAdmission[o] and o.admission.because = RPoolWrongItem
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 2 InventoryItem, 1 InventoryPool, 2 Note expect 1

// ROLLOVER completes the predecessor — as TWO rows since Q25 resolved (COORDINATOR-Q199 R3, model cut 2026-10-01, M1):
// the completion retire on the still-open predecessor at a completable status, then the successor's genesis, adjacent
// (`rolloverPair`); the predecessor reads back COMPLETED, not live. The `no WithdrawOcc` conjunct stays load-bearing
// (review 2026-07-08): without it the solver satisfied the witness by withdrawing c1 first.
run unit_cyc_rolloverCompletesPredecessor {
  some disj c1, c2: CardCycle, r1: RetireCycleOcc, r2: RequestOcc | {
    c2.precededBy = c1 and r1.cycle = c1 and r2.cycle = c2 and rolloverPair[r1, r2]
    no w: WithdrawOcc | committed[w] and w.cycle = c1
    completedAt[c1, r2.tick] and not liveCycleAt[c1, r2.tick] and liveCycleAt[c2, r2.tick]
  }
} for 7 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 1 KanbanCard, 0 InventoryItem, 8 Tick, 8 Occurrence, 8 Snapshot, 2 Note expect 1

// The FLUSH rollover (MP ruling 2026-07-08): the predecessor is mid-inventory at IN_USE and
// still holds its pool when the successor's genesis rolls it over — the pool is implicitly
// released (no live holder afterward; exclusivity counts LIVE cycles only), its items staying
// wherever they were.
run unit_cyc_rolloverFlushReleasesPool {
  some disj c1, c2: CardCycle, r1: RetireCycleOcc, r2: RequestOcc, p: InventoryPool | {
    c2.precededBy = c1 and r1.cycle = c1 and r2.cycle = c2 and rolloverPair[r1, r2]
    no w: WithdrawOcc | committed[w] and w.cycle = c1
    statusAt[c1, r1.tick] = IN_USE    // LOCF of c1's own records at the retire — the tombstone keeps them (post = pre)
    resolve[stateOfCycleAt[c1, r2.tick].sPool] = p
    completedAt[c1, r2.tick]
    no c: CardCycle | liveCycleAt[c, r2.tick] and resolve[stateOfCycleAt[c, r2.tick].sPool] = p
  }
} for 8 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 1 KanbanCard, 2 InventoryItem, 1 InventoryPool, 9 Tick, 9 Occurrence, 9 Snapshot, 2 Note expect 1

// A genesis over a MID-TRIP predecessor (before any inventory association — here REQUESTED)
// is refused with exactly RCardInCirculation: aborting mid-trip stays an explicit Withdraw.
run unit_cyc_genesisMidTripRefused {
  some c1: CardCycle, o: RequestOcc | {
    o.cycle.precededBy = c1
    statusAt[c1, o.tick] = REQUESTED
    refusedAtAdmission[o] and o.admission.because = RCardInCirculation
  }
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// WITHDRAW closes the cycle: read back as ABANDONED, not live (the tombstone).
run unit_cyc_withdrawAbandons {
  some w: WithdrawOcc | committed[w]
    and abandonedAt[w.cycle, w.tick] and not liveCycleAt[w.cycle, w.tick]
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// PRODUCTION FAILURE steps back (R8 — the 2nd sanctioned backward operation): IN_PROCESS →
// REQUESTING, the pool detached (back to the demand-leg queue), the cycle live and attachable by a new DemandItem (R8 amended 2026-07-06).
run unit_cyc_productionFailureRequeues {
  some o: ProductionFailureOcc | committed[o]
    and o.pre.sStatus = IN_PROCESS
    and statusAt[o.cycle, o.tick] = REQUESTING
    and no stateOfCycleAt[o.cycle, o.tick].sPool
    and liveCycleAt[o.cycle, o.tick]
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 2 InventoryItem, 1 InventoryPool, 2 Note expect 1

// ── reason-precise refusals ─────────────────────────────────────────────────────────────────────
// A backward jump (Accept after IN_PROCESS) is refused with exactly RBackward.
run unit_cyc_backwardRefused {
  some o: AcceptOcc | refusedAtAdmission[o] and o.admission.because = RBackward
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// Skipping an ACTIVE status is refused with exactly RSkippedActive.
run unit_cyc_skippedActiveRefused {
  some o: StartProcessingOcc | refusedAtAdmission[o] and o.admission.because = RSkippedActive
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// Operating on a withdrawn (closed) cycle is refused with RClosed among the reasons.
run unit_cyc_closedRefused {
  some w: WithdrawOcc, o: UseOcc | {
    committed[w] and o.cycle = w.cycle and precedes[w.tick, o.tick]
    refusedAtAdmission[o] and RClosed in o.admission.because
  }
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// A second genesis while the predecessor is still open is refused with exactly RCardInCirculation.
run unit_cyc_genesisWhileOpenRefused {
  some o: RequestOcc | refusedAtAdmission[o] and o.admission.because = RCardInCirculation
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// Shelve from a status other than REQUESTED is refused with exactly RNotRequested.
run unit_cyc_shelveWrongSourceRefused {
  some o: ShelveOcc | refusedAtAdmission[o] and o.admission.because = RNotRequested
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// ProductionFailure from a status other than IN_PROCESS is refused with exactly RNotInProcess (R8).
run unit_cyc_productionFailureWrongSourceRefused {
  some o: ProductionFailureOcc | refusedAtAdmission[o] and o.admission.because = RNotInProcess
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 1

// ── theorems (check; UNSAT = holds) — the PUBLISHED CONTRACT (kanban_card_contracts.als),
// discharged here by name against the real implementation (DT-017 co-change, 2026-07-08).
assert unit_cyc_oneLiveCyclePerCard { oneLiveCyclePerCard }
check unit_cyc_oneLiveCyclePerCard for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 2 Note expect 0

assert unit_cyc_forwardMonotone { forwardMonotone }
check unit_cyc_forwardMonotone for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 2 Note expect 0

assert unit_cyc_noPoolBeforeInProcess { noPoolBeforeInProcess }
check unit_cyc_noPoolBeforeInProcess for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 1 InventoryPool, 2 Note expect 0

assert unit_cyc_poolFrozenOnceAttached { poolFrozenOnceAttached }
check unit_cyc_poolFrozenOnceAttached for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 1 InventoryPool, 2 Note expect 0

assert unit_cyc_poolProvenance { poolProvenance }
check unit_cyc_poolProvenance for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 2 InventoryPool,
      8 Occurrence, 10 EntityId, 7 Tick, 8 Snapshot, 2 Note expect 0

assert unit_cyc_poolExclusiveWhileLive { poolExclusiveWhileLive }
check unit_cyc_poolExclusiveWhileLive for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 2 InventoryPool, 2 Note expect 0

assert unit_cyc_closureIsTerminal { closureIsTerminal }
check unit_cyc_closureIsTerminal for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 2 Note expect 0

assert unit_cyc_quantityFixedAtGenesis { quantityFixedAtGenesis }
check unit_cyc_quantityFixedAtGenesis for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 2 Note expect 0

// HOMOGENEITY theorem (DT-015 R1 — SUITE-LEVEL by ruling, not a published contract law; promote
// per L9 when a consumer stages reliance, e.g. demand's Distribute): a cycle's resolved pool
// always classifies under its card's demanded Item — derived from the attach guard +
// poolFrozenOnceAttached + the ProductionFailure detach (both itemRefs are immutable).
assert unit_cyc_poolItemHomogeneous {
  all c: CardCycle, t: Tick | let p = resolve[stateOfCycleAt[c, t].sPool] & InventoryPool |
    some p implies p.itemPin.subject = (cycles.c).itemPin.subject
}
check unit_cyc_poolItemHomogeneous for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 2 InventoryPool, 2 Note expect 0
