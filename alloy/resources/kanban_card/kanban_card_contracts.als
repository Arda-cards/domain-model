module resources/kanban_card/kanban_card_contracts

/*
 * KanbanCard/CardCycle — CONTRACTS (DT-017): the published laws, curated and few — lifted
 * verbatim from the suite's law-shaped theorems at the four-file cut (2026-07-08). All are
 * SINGLE-LOG (same module) laws — ATOMIC class; nothing here crosses a module boundary.
 */

open resources/kanban_card/kanban_card_types

/** oneLiveCyclePerCard — ≤ 1 live cycle per card, at every tick (DERIVED from the genesis
    guard + the chain facts — the retired LiveCycleIsOpenTail fact as a consequence). */
pred oneLiveCyclePerCard {
  all k: KanbanCard, t: Tick | lone currentCycleAt[k, t]
}

/** forwardMonotone — every committed forward operation strictly advances the region order
    (KD9 — backward motion is impossible outside the sanctioned Shelve / ProductionFailure). */
pred forwardMonotone {
  all o: cycleForwardOps | (committed[o] and some o.pre) implies
    regionBefore[o.pre.sStatus, o.post.sStatus]
}

/** noPoolBeforeInProcess — the demanding leg carries no pool: any state strictly before
    IN_PROCESS has no sPool (StartProcessing is the only attacher; Shelve cannot cross back
    over it). */
pred noPoolBeforeInProcess {
  all o: CycleOcc | (committed[o] and some o.post and regionBefore[o.post.sStatus, IN_PROCESS])
    implies no o.post.sPool
}

/** poolFrozenOnceAttached — once attached, the pool is FROZEN for the cycle's remainder (the
    frames carry it; no re-pointing). ProductionFailure is the ONE detacher (R8) — exempted
    alongside the attacher. */
pred poolFrozenOnceAttached {
  all o: CycleOcc - StartProcessingOcc - ProductionFailureOcc | (committed[o] and some o.pre.sPool)
    implies o.post.sPool = o.pre.sPool
}

/** poolProvenance — a cycle's attached pool is EXACTLY the pool its committed StartProcessing
    named (DT-020 cut 5, §8.5.3 L9 publication: the exclusivity-lattice rows in the demand and
    receiving modules rely on this to reason from attach-act payloads to record bindings —
    without it, a mock-tier record could bind a pool no act ever named). A theorem of the
    StartProcessing effect + the frozen frames (ProductionFailure, the one detacher, only
    CLEARS); holds for closed cycles' frozen records too. */
pred poolProvenance {
  all c: CardCycle, t: Tick | some stateOfCycleAt[c, t].sPool implies
    (some o: StartProcessingOcc | committed[o] and o.subject = c and notAfter[o.tick, t]
       and stateOfCycleAt[c, t].sPool = o.pool)
}

/** poolExclusiveWhileLive — at any moment, a pool has at most one LIVE holding cycle — derived
    from the attach guard + the frozen frames + closure semantics. Dismissal is implicit: when
    the holder closes (rollover/withdraw), the pool is no longer HELD — exclusivity counts live
    holders only. It does NOT become attachable again: `poolAttachedOnce` below (2026-10-01) binds
    a pool to its one committed attach for all time; a closed holder's pool is a USED pool. */
pred poolExclusiveWhileLive {
  all p: InventoryPool, t: Tick |
    lone { c: CardCycle | liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p }
}

/** poolAttachedOnce — a pool is named by at most one COMMITTED StartProcessing, across all cycles and all time
    (DT-020 §8.5.3 "pools never re-attach"; the runtime's V019 index, 2026-10-01). A theorem of the attach guard's
    freshness arm, which since 2026-10-01 counts a prior committed attach as USE — before that arm the guard admitted
    re-attaching an EMPTY pool whose holder had closed or detached it, a gap between the guard and the design. */
pred poolAttachedOnce {
  all p: InventoryPool | lone { o: StartProcessingOcc | committed[o] and resolve[o.pool] = p }
}

/** closedBeforeSuccessorGenesis — a successor's genesis commits only after its predecessor's retire row (Q25 resolved,
    COORDINATOR-Q199 M1: the rollover is `rolloverPair` — retire, then genesis, adjacent; a genesis never closes). A theorem
    of `requestViol`'s `RCardInCirculation` arm. */
pred closedBeforeSuccessorGenesis {
  all g: RequestOcc | (committed[g] and some g.subject.precededBy) implies closedStrictlyBefore[g.subject.precededBy, g.tick]
}

/** closureIsTerminal — nothing commits on a closed cycle (terminality of closure). */
pred closureIsTerminal {
  all o: CycleOcc | closedStrictlyBefore[o.subject, o.tick] implies not committed[o]
}

/** quantityFixedAtGenesis — `sQuantityOverride` is written by RequestOcc only; every other
    committed effect frames it (DT-016 R7, MP). The cycle's quantum
    (override-if-given-else-nominal) is immutable for the cycle's whole existence; mid-flight
    change = withdraw + re-request. */
pred quantityFixedAtGenesis {
  all o: CycleOcc - RequestOcc | (committed[o] and some o.pre)
    implies o.post.sQuantityOverride = o.pre.sQuantityOverride
}

/** guarantees — everything a consumer may assume of this module. */
pred guarantees {
  oneLiveCyclePerCard
  forwardMonotone
  noPoolBeforeInProcess
  poolFrozenOnceAttached
  poolProvenance
  poolExclusiveWhileLive
  poolAttachedOnce
  closedBeforeSuccessorGenesis
  closureIsTerminal
  quantityFixedAtGenesis
}
