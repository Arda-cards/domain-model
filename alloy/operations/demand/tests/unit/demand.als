module operations/demand/tests/unit/demand

open operations/demand/demand_implementation
open operations/demand/demand_contracts
open reference_data/item/item_mock                            // lower layer as CONTRACT (DT-017)
open resources/processing_network/processing_network_mock    // Station stub as CONTRACT
open resources/kanban_card/kanban_card_mock                   // kanban as CONTRACT (DT-017 — the cut retired the INTERIM real cone, 2026-07-08)

/*
 * UNIT suite for the demand module (DT-016; C/OP remodel 2026-07-06). INTERIM (R3): the kanban
 * cycle log and the inventory pool ride the implementation cone for REAL (no kanban mock yet —
 * tightened at the kanban four-file cut), so the saga commit gates are exercised against the
 * real cycle machinery even in this tier. Premises via the P1 profile in the cone. Machine pins:
 * the PRINT machine (5/8/8/1) rides the kanban_card open; 5 Int — the cycle region ranks reach
 * 8. NB `for N` silently caps the TOTALS of the ABSTRACT parents — Snapshot (records) AND
 * Occurrence (log entries): heavy traces pin BOTH explicitly (the 2026-07-06 build lost hours
 * to each in turn).
 * ResetQty's Σ is verified in the DEDICATED root (demand_reset.als — arity-4 confinement).
 */

// ── CONTRACT DISCHARGE (check; UNSAT = the law holds of the implementation) ─────────────────────
assert unit_dem_contract_cycleIndivisible { cycleIndivisible }
check unit_dem_contract_cycleIndivisible for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 0

assert unit_dem_contract_frozenOutsideOpen { frozenOutsideOpen }
check unit_dem_contract_frozenOutsideOpen for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 0

// The C/OP saga commit gates — theorems of the reason-precise guards:
assert unit_dem_contract_attachRequiresAccepted { attachRequiresAccepted }
check unit_dem_contract_attachRequiresAccepted for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 0

assert unit_dem_contract_removeRequiresShelved { removeRequiresShelved }
check unit_dem_contract_removeRequiresShelved for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 0

assert unit_dem_contract_startProductionRequiresStarted { startProductionRequiresStarted }
check unit_dem_contract_startProductionRequiresStarted for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 0

assert unit_dem_contract_distributeRequiresReady { distributeRequiresReady }
check unit_dem_contract_distributeRequiresReady for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 0

assert unit_dem_contract_completeRequiresSettled { completeRequiresSettled }
check unit_dem_contract_completeRequiresSettled for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 0

assert unit_dem_contract_completeRequiresDistributed { completeRequiresDistributed }
check unit_dem_contract_completeRequiresDistributed for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 2 InventoryItem, 1 InventoryPool expect 0

assert unit_dem_contract_withdrawnDetachReconciles { withdrawnDetachReconciles }
check unit_dem_contract_withdrawnDetachReconciles for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 8 Quantity expect 0

assert unit_dem_contract_terminalClosure { terminalClosure }
check unit_dem_contract_terminalClosure for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 0

// ── SAT witnesses — the §2 scenarios (C/OP call-first: cycle op, then demand commit) ────────────
// Scenario 1 (collate and release): Accept c1 → CreateWithCycle → Accept c2 → AddCycle → Release.
run unit_dem_collateAndRelease {
  some d: DemandItem, o1: CreateWithCycleOcc, o2: AddCycleOcc, r: ReleaseOcc | {
    o1.subject = d and o2.subject = d and r.subject = d
    precedes[o1.tick, o2.tick] and precedes[o2.tick, r.tick]
    committed[o1] and committed[o2] and committed[r]
    o1.member != o2.member
    demandStatusAt[d, r.tick] = DS_RELEASED
    #attachedAt[d, r.tick] = 2
  }
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 3 CardCycle, 2 KanbanCard, 0 InventoryItem, 9 Tick, 12 EntityId, 10 Snapshot expect 1

// A committed attach reads back: the member's Accept PRECEDED it (call-first), the member is
// attached and REQUESTED at the commit.
run unit_dem_attachReadsBack {
  some o: CreateWithCycleOcc, k: AcceptOcc | {
    committed[o] and committed[k]
    k.cycle = resolve[o.member] and precedes[k.tick, o.tick]
    resolve[o.member] in attachedAt[o.subject, o.tick]
    statusAt[k.cycle, o.tick] = REQUESTED
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId expect 1

// The saga SETTLES: a tick where the demand ↔ cycle logs are ALIGNED with real content (the
// quiescence law's witnessed side — the runtime probe watches this at scale).
run unit_dem_sagaSettles {
  some d: DemandItem, t: Tick | {
    demandCyclesAlignedAt[t]
    liveDemandAt[d, t] and some attachedLiveAt[d, t]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId expect 1

// Scenario 2 (characteristic refusal): AddCycle after Release → exactly RFrozen.
run unit_dem_frozenRefused {
  some o: AddCycleOcc | refusedAtAdmission[o] and o.admission.because = RFrozen
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId expect 1

// Scenario 3a (R7, OPEN): the cycle is withdrawn on its own log; the reaction detaches it and
// the demand SELF-CANCELS (detach → Cancel composite; RHasCards vacuous).
run unit_dem_withdrawalReactionSelfCancel {
  some d: DemandItem, w: WithdrawOcc, dt: DetachWithdrawnOcc, cn: CancelOcc | {
    dt.subject = d and cn.subject = d
    committed[w] and committed[dt] and committed[cn]
    resolve[dt.member] = w.cycle
    precedes[w.tick, dt.tick] and precedes[dt.tick, cn.tick]
    no attachedAt[d, dt.tick]
    demandStatusAt[d, cn.tick] = DS_CANCELED
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 Tick, 9 EntityId, 10 Snapshot expect 1

// Scenario 3b (R7, RELEASED) — BOUNDARY WITNESS (RECONCILED): the frozen-state dangle is LEGAL,
// surfaced by retiredMembersAt.
run unit_dem_frozenDangleBoundary {
  some d: DemandItem, t: Tick | {
    demandStatusAt[d, t] = DS_RELEASED
    some retiredMembersAt[d, t]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId expect 1

// R7 in-flight BOUNDARY WITNESS (C/NOTIF): an OPEN demand with a withdrawn member still
// attached — the legal intermediate between the withdrawal and the reaction.
run unit_dem_openWithdrawnInFlight {
  some d: DemandItem, t: Tick | {
    demandStatusAt[d, t] = DS_OPEN
    some retiredMembersAt[d, t]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId expect 1

// Scenario 4's SET form (the Σ is the dedicated root's): AdjustQty is a plain overwrite (R3b).
run unit_dem_adjustSetsIntent {
  some o: AdjustQtyOcc | committed[o] and dPost[o].sDemandQty = o.qty
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 8 Quantity expect 1

// Scenario 5 (R8, produce — call-first): the member's StartProcessing precedes the committed
// StartProduction; both logs read IN_PROCESS at the commit.
run unit_dem_startProductionCommits {
  some o: StartProductionOcc, k: StartProcessingOcc | {
    committed[o] and committed[k]
    k.cycle in attachedLiveAt[o.subject, o.tick] and precedes[k.tick, o.tick]
    demandStatusAt[o.subject, o.tick] = DS_IN_PROCESS
    statusAt[k.cycle, o.tick] = IN_PROCESS
  }
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 Tick, 9 EntityId, 10 Snapshot expect 1

// Scenario 5 variant (R8, production failure — call-first): the caller settles the
// inventory-less member back to the queue (ProductionFailure → REQUESTING), then Complete.
run unit_dem_completeWithProductionFailure {
  some o: CompleteOcc, pf: ProductionFailureOcc | {
    committed[o] and committed[pf]
    resolve[dPre[o].sMembership] = pf.cycle and precedes[pf.tick, o.tick]
    demandStatusAt[o.subject, o.tick] = DS_COMPLETE
    statusAt[pf.cycle, o.tick] = REQUESTING
  }
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 11 Tick, 9 EntityId, 12 Snapshot,
      10 Occurrence expect 1

// Terminal Delete/Retire (R7): the tombstoned retirement of a CANCELED task.
run unit_dem_deleteRetiresTerminal {
  some o: DeleteDemandOcc | committed[o] and dPre[o].sStatus = DS_CANCELED
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 Tick expect 1

// ── C/OP in-flight BOUNDARY WITNESSES (legal intermediates — the remodel's point) ───────────────
// An ACCEPTED cycle not (yet) attached: the attach saga's crash window; convergence = retry the
// attach or compensate with Shelve.
run unit_dem_acceptedUnattachedInFlight {
  some c: CardCycle, t: Tick | {
    liveCycleAt[c, t] and statusAt[c, t] = REQUESTED
    no demandOf[c, t]
    no o: MemberOcc | committed[o]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// A STARTED member under a still-RELEASED demand: the production saga's partial-call window.
run unit_dem_startedBeforeCommitInFlight {
  some d: DemandItem, c: CardCycle, t: Tick | {
    demandStatusAt[d, t] = DS_RELEASED
    c in attachedLiveAt[d, t] and statusAt[c, t] = IN_PROCESS
    no o: StartProductionOcc | committed[o]
  }
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 Tick, 9 EntityId, 10 Snapshot expect 1

// ── R1-amended BOUNDARY WITNESS: no uniqueness — two OPEN demands for ONE (Item, Station) pair
// in one tenant are LEGAL (single-OPEN, if wanted, is caller policy over `demandsFor`). ─────────
run unit_dem_twoOpenSameIdentityLegal {
  some disj a, b: DemandItem, t: Tick | {
    a.tenantId = b.tenantId
    demandStatusAt[a, t] = DS_OPEN and demandStatusAt[b, t] = DS_OPEN
    a.itemPin.subject = b.itemPin.subject and a.stationRef = b.stationRef
    a + b in demandsFor[a.itemPin.subject, a.stationRef, t]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId expect 1

// ── reason-precise refusal witnesses (one per Reason) ───────────────────────────────────────────
run unit_dem_demandStartedRefused {
  some o: CreateDemandOcc | refusedAtAdmission[o] and RDemandStarted in o.admission.because
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

run unit_dem_demandClosedRefused {
  some o: AdjustQtyOcc | refusedAtAdmission[o] and o.admission.because = RDemandClosed
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

run unit_dem_badStateRefused {
  some o: StartProductionOcc | refusedAtAdmission[o] and o.admission.because = RBadState
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// RForeignRef guards the RECORD-carried refs only (holding/delivery) — the entity's
// stationRef is kernel-covered; the itemPin rides DemandItemPinTenancy (cross-tenant = unrepresentable).
run unit_dem_foreignRefRefused {
  some o: StartProductionOcc | refusedAtAdmission[o] and RForeignRef in o.admission.because
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 9 EntityId expect 1

run unit_dem_foreignCycleRefused {
  some o: AddCycleOcc | refusedAtAdmission[o] and RForeignCycle in o.admission.because
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 2 KanbanCard, 0 InventoryItem, 9 EntityId expect 1

run unit_dem_cycleHeldRefused {
  some o: AddCycleOcc | refusedAtAdmission[o] and RCycleHeld in o.admission.because
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 Tick, 12 EntityId, 10 Snapshot expect 1

// The gate refusal: attaching a cycle still REQUESTING (its Accept — the saga's first leg —
// has not committed) is refused with exactly RCycleIneligible.
run unit_dem_cycleIneligibleRefused {
  some o: AddCycleOcc | {
    refusedAtAdmission[o] and o.admission.because = RCycleIneligible
    statusAt[resolve[o.member] & CardCycle, o.tick] = REQUESTING
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId expect 1

run unit_dem_cycleLiveRefused {
  some o: DetachWithdrawnOcc | refusedAtAdmission[o] and RCycleLive in o.admission.because
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId expect 1

run unit_dem_notAttachedRefused {
  some o: RemoveCycleOcc | refusedAtAdmission[o] and RNotAttached in o.admission.because
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId expect 1

run unit_dem_hasCardsRefused {
  some o: CancelOcc | refusedAtAdmission[o] and o.admission.because = RHasCards
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId expect 1

run unit_dem_badAllocationRefused {
  some o: DistributeOcc | refusedAtAdmission[o] and RBadAllocation in o.admission.because
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 Tick, 9 EntityId, 10 Snapshot expect 1

run unit_dem_undistributedRefused {
  some o: CompleteOcc | refusedAtAdmission[o] and RUndistributed in o.admission.because
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 2 InventoryItem, 1 InventoryPool, 11 Tick, 12 EntityId, 14 Snapshot expect 1

run unit_dem_notTerminalRefused {
  some o: DeleteDemandOcc | refusedAtAdmission[o] and o.admission.because = RNotTerminal
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// ── boundary witnesses (deliberate NON-theorems) ────────────────────────────────────────────────
// The intent may float free of the attached sum (R3b advisory stance).
run unit_dem_intentFloatsFree {
  some o: AdjustQtyOcc | committed[o] and some dPost[o].sMembership
    and dPost[o].sDemandQty != dPre[o].sDemandQty
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 8 Quantity expect 1

// An unattached REQUESTING cycle persists indefinitely (R6: attachment is NEVER automatic).
run unit_dem_unattachedRequestingLegal {
  some c: CardCycle, t: Tick | statusAt[c, t] = REQUESTING and no demandOf[c, t]
    and no o: demandOccKinds | committed[o]
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// ── the §8.5.3 lattice row + provenance (DT-020 cut 5) — UNIT-dischargeable since kanban
// published poolProvenance: the cross-kind clause reasons from attach payloads to record
// bindings through the mock. Scope discipline: 2 of the OWN kind + 1 cycle; explicit
// abstract-parent pins (knowledge-base/pool-lattice-genesis-premise.md §3). ────────────────────
assert unit_dem_contract_holdingProvenance { holdingProvenance }
check unit_dem_contract_holdingProvenance for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 InventoryPool,
      8 Occurrence, 10 EntityId, 7 Tick, 8 Snapshot expect 0

assert unit_dem_contract_holdingExclusive { holdingExclusiveWhileLive }
check unit_dem_contract_holdingExclusive for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 InventoryPool,
      8 Occurrence, 10 EntityId, 7 Tick, 8 Snapshot expect 0

// The SAT companion (anti-vacuity): the premise HOLDS with a live demand holding its pool and
// a live MOCK cycle holding a distinct one (the cycle's binding now needs its committed
// StartProcessing — poolProvenance in the mock).
run unit_dem_latticeCompanion {
  demandPoolGenesis
  some t: Tick, d: DemandItem, c: CardCycle, disj p1, p2: InventoryPool | {
    liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p1
    liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p2
  }
} for 8 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 InventoryPool,
      12 EntityId, 9 Tick, 10 Snapshot, 9 Occurrence expect 1

// ── the ProductionDelivery subject (§8.1.2/§8.1.4, DT-020 build cut 3) ──────────────────────────
// Contract discharge — the §8.1.4 gates as theorems of createDeliveryViol:
assert unit_dem_contract_createDeliveryGated { createDeliveryGated }
check unit_dem_contract_createDeliveryGated for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 ProductionDelivery expect 0

assert unit_dem_contract_deliveryTerminalRevoke { deliveryTerminalRevoke }
check unit_dem_contract_deliveryTerminalRevoke for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 ProductionDelivery expect 0

// The composed accrual arc (§8.1.2 ATOMIC): CreateDelivery + its RecordProduction on the
// target's log — the F7 edge as one demand tx (two ticks under OneOccurrencePerTick).
run unit_dem_deliveryComposedArc {
  some c: CreateDeliveryOcc, r: RecordProductionOcc | {
    committed[c] and committed[r]
    r.delivery = c.subject.eId and r.subject.eId = c.subject.demandRef
    deliveryStatusAt[c.subject, c.tick] = PD_CREATED
    c.subject in contributionsFor[resolve[c.subject.demandRef] & DemandItem, c.tick]
  }
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      9 Tick, 9 EntityId, 8 Snapshot expect 1

// The composed reversal arc: Revoke + ExtractProduction; the delivery leaves the
// contributions fold forever (reversing-entry semantics — §8.1.1).
run unit_dem_deliveryRevokedArc {
  some v: RevokeDeliveryOcc, x: ExtractProductionOcc | {
    committed[v] and committed[x]
    x.delivery = v.subject.eId
    deliveryStatusAt[v.subject, v.tick] = PD_REVOKED
    v.subject not in contributionsFor[resolve[v.subject.demandRef] & DemandItem, v.tick]
  }
} for 8 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      10 Tick, 10 EntityId, 9 Snapshot expect 1

// §8.1.4 refusal: a CreateDelivery whose target is not IN_PROCESS (here: still OPEN) —
// exactly RTargetNotInProcess. The OPEN→IN_PROCESS choreography is a composite's, not ours.
run unit_dem_targetNotInProcessRefused {
  some o: CreateDeliveryOcc | {
    refusedAtAdmission[o] and o.admission.because = RTargetNotInProcess
    demandStatusAt[resolve[o.subject.demandRef] & DemandItem, o.tick] = DS_OPEN
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      8 EntityId, 8 Snapshot expect 1

// §8.1.4 item agreement refusal: the delivery denominated in the WRONG item — exactly
// RWrongItem (the pool module's reason reused; agreement is a Create guard, never a
// downstream pool-law violation).
run unit_dem_deliveryWrongItemRefused {
  some o: CreateDeliveryOcc | {
    refusedAtAdmission[o] and o.admission.because = RWrongItem
    demandStatusAt[resolve[o.subject.demandRef] & DemandItem, o.tick] = DS_IN_PROCESS
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      9 EntityId, 8 Snapshot expect 1

// M3 (DT-020 §8.5.3 / SPEARHEAD-D1 A′-2, MINESWEEPER model-deltas M3.1): pool-vs-demand item
// agreement on the RECORD side too — a RecordProduction correlated (by the §8.1.2 ATOMIC
// pairing) with a CreateDelivery whose pool disagrees with the demand's item is refused with
// exactly RWrongItem. RED before the arm: recordProductionViol had no item-agreement clause at
// all (see the commit body for the RED evidence).
run unit_dem_recordProductionWrongPoolItemRefused {
  some r: RecordProductionOcc | refusedAtAdmission[r] and r.admission.because = RWrongItem
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery, 1 InventoryPool,
      10 EntityId, 9 Snapshot expect 1

// M3.2: the minted holding pool's itemPin always agrees with the demand's item — a THEOREM of
// the StartProduction effect (`StartProductionHoldingPoolPin`). RED before the fact: nothing
// constrained a resolved holding pool's itemPin, so the solver could freely disagree them.
assert unit_dem_holdingPoolPinMatchesItem {
  all o: StartProductionOcc, p: resolve[o.holding] & InventoryPool |
    committed[o] implies p.itemPin.subject = o.subject.itemPin.subject
}
check unit_dem_holdingPoolPinMatchesItem for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 InventoryPool,
      8 Occurrence, 10 EntityId, 7 Tick, 8 Snapshot expect 0

// Revoke on an already-REVOKED delivery — exactly RDeliveryClosed (terminal §8.1.1).
run unit_dem_revokeRevokedRefused {
  some o: RevokeDeliveryOcc | refusedAtAdmission[o] and o.admission.because = RDeliveryClosed
    and some o.pre and pdPre[o].sStatus = PD_REVOKED
} for 8 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      11 Tick, 11 EntityId, 10 Snapshot, 10 Occurrence expect 1
      // census +1 across the board at DT-023 cut 7a: the trace's item-log fixture (the
      // committed CreateItemOcc behind the demand genesis guard) pushed the occurrence
      // count past the old for-8 default this deep witness sat exactly at

// ── DT-023 cut 8: gate at INCEPTION, never at PROPAGATION ──────────────────────────────────────

// PROPAGATION is ungated: a scan-derived demand (CreateWithCycle — the pin inherited from
// the triggering cycle, whose REQUEST was the gated inception) COMMITS even though its item
// has since RETIRED. This is the anti-deadlock half of the cut-8 ruling: the scan workflow
// must not strand on a mid-flight retirement.
run unit_dem_scanDerivedRetiredAllowed {
  some o: CreateWithCycleOcc, k: AcceptOcc, d: RetireItemOcc | {
    committed[o] and committed[k] and committed[d]
    k.cycle = resolve[o.member] and precedes[k.tick, o.tick]
    d.subject = o.subject.itemPin.subject and precedes[d.tick, o.tick]
    not itemLiveAt[o.subject.itemPin.subject, o.tick]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem,
      12 EntityId, 9 Tick, 9 Snapshot, 9 Occurrence expect 1

// INCEPTION stays gated: a DIRECT create (the caller chooses the item — F6/queue-add) of a
// demand for a retired item refuses with exactly RRetiredRef.
run unit_dem_directCreateRetiredRefused {
  some o: CreateDemandOcc, d: RetireItemOcc | {
    committed[d]
    d.subject = o.subject.itemPin.subject and precedes[d.tick, o.tick]
    refusedAtAdmission[o] and o.admission.because = RRetiredRef
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem,
      10 EntityId, 7 Tick, 7 Snapshot, 7 Occurrence expect 1

// ── DT-030 retire cut (2026-09-09): terminality ──────────────────────────────────────────────────
// Nothing commits on a demand item after its committed delete (the tombstone is the end of history).
assert unit_dem_nothingAfterRetire {
  all r: DeleteDemandOcc, o: CreateDemandOcc + CreateWithCycleOcc + AddCycleOcc + RemoveCycleOcc + DetachWithdrawnOcc + AdjustQtyOcc + ResetQtyOcc + ReleaseOcc + ReopenOcc + StartProductionOcc + RecordProductionOcc + ExtractProductionOcc + DistributeOcc + CompleteOcc + CancelOcc + DeleteDemandOcc | (committed[r] and committed[o] and o.subject = r.subject) implies not precedes[r.tick, o.tick]
}
check unit_dem_nothingAfterRetire for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 3 CardCycle, 2 KanbanCard, 0 InventoryItem, 9 Tick, 12 EntityId, 10 Snapshot expect 0
