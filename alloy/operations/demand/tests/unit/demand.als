module operations/demand/tests/unit/demand
// Reflects dafny-domain src/operations/demand/tests/demand-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

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
 * The quantity read (the keyed sum of the live contributions, TN-004) is found in the DEDICATED root
 * (tests/unit/demand_quantity.als — arity-4 confinement).
 */

// ── CONTRACT DISCHARGE (check; UNSAT = the law holds of the implementation) ─────────────────────
assert unit_dem_contract_cycleIndivisible { cycleIndivisible }
check unit_dem_contract_cycleIndivisible for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note, 2 Reference expect 0

assert unit_dem_contract_frozenOutsideOpen { frozenOutsideOpen }
check unit_dem_contract_frozenOutsideOpen for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note, 2 Reference expect 0

// The C/OP saga commit gates — theorems of the reason-precise guards:
assert unit_dem_contract_attachRequiresAccepted { attachRequiresAccepted }
check unit_dem_contract_attachRequiresAccepted for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note, 2 Reference expect 0

assert unit_dem_contract_removeRequiresShelved { removeRequiresShelved }
check unit_dem_contract_removeRequiresShelved for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note, 2 Reference expect 0

assert unit_dem_contract_startProductionRequiresStarted { startProductionRequiresStarted }
check unit_dem_contract_startProductionRequiresStarted for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note, 2 Reference expect 0

assert unit_dem_contract_distributeRequiresReady { distributeRequiresReady }
check unit_dem_contract_distributeRequiresReady for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note, 2 Reference expect 0

assert unit_dem_contract_completeRequiresSettled { completeRequiresSettled }
check unit_dem_contract_completeRequiresSettled for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note, 2 Reference expect 0

// (`completeRequiresDistributed` left the contract with TN-004 row 11, dafny-domain MD-084: the release at Complete is derived
// from the status, and what the released pools hold is checked by the placements — `completedItemsPlaced`, below.)

assert unit_dem_contract_withdrawnDetachReconciles { withdrawnDetachReconciles }
check unit_dem_contract_withdrawnDetachReconciles for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 8 Quantity, 2 Note, 2 Reference expect 0

assert unit_dem_contract_terminalClosure { terminalClosure }
check unit_dem_contract_terminalClosure for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note, 2 Reference expect 0

// ── SAT witnesses — the §2 scenarios (C/OP call-first: cycle op, then demand commit) ────────────
// Scenario 1 (collate and release): Accept c1 → CreateWithContribution → Accept c2 → AddContribution → Release.
run unit_dem_collateAndRelease {
  some d: DemandItem, o1: CreateWithContributionOcc, o2: AddContributionOcc, r: ReleaseOcc | {
    o1.subject = d and o2.subject = d and r.subject = d
    precedes[o1.tick, o2.tick] and precedes[o2.tick, r.tick]
    committed[o1] and committed[o2] and committed[r]
    (o1.contribution + o2.contribution) in CardContribution and o1.contribution.cycleRef != o2.contribution.cycleRef
    demandStatusAt[d, r.tick] = DS_RELEASED
    #attachedAt[d, r.tick] = 2
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 3 CardCycle, 2 KanbanCard, 0 InventoryItem, 9 Tick, 12 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 1

// A committed attach reads back: the member's Accept PRECEDED it (call-first), the member is
// attached and REQUESTED at the commit.
run unit_dem_attachReadsBack {
  some o: CreateWithContributionOcc, k: AcceptOcc | {
    committed[o] and committed[k]
    k.cycle = cyclesOf[o.contribution] and precedes[k.tick, o.tick]
    cyclesOf[o.contribution] in attachedAt[o.subject, o.tick]
    statusAt[k.cycle, o.tick] = REQUESTED
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId, 2 Note, 2 Reference expect 1

// The saga SETTLES: a tick where the demand ↔ cycle logs are ALIGNED with real content (the
// quiescence law's witnessed side — the runtime probe watches this at scale).
run unit_dem_sagaSettles {
  some d: DemandItem, t: Tick | {
    demandCyclesAlignedAt[t]
    liveDemandAt[d, t] and some attachedLiveAt[d, t]
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId, 2 Note, 2 Reference expect 1

// Scenario 2 (characteristic refusal): AddContribution after Release → exactly RFrozen.
run unit_dem_frozenRefused {
  some o: AddContributionOcc | refusedAtAdmission[o] and o.admission.because = RFrozen
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId, 2 Note, 2 Reference expect 1

// Scenario 3a (R7, OPEN): the cycle is withdrawn on its own log; the reaction detaches it and
// the demand SELF-CANCELS (detach → Cancel composite; RHasCards vacuous).
run unit_dem_withdrawalReactionSelfCancel {
  some d: DemandItem, w: WithdrawOcc, dt: DetachWithdrawnOcc, cn: CancelOcc | {
    dt.subject = d and cn.subject = d
    committed[w] and committed[dt] and committed[cn]
    some c: dPre[dt].sContributions & CardContribution | c.cid = dt.target and cyclesOf[c] = w.cycle
    precedes[w.tick, dt.tick] and precedes[dt.tick, cn.tick]
    no attachedAt[d, dt.tick]
    demandStatusAt[d, cn.tick] = DS_CANCELED
  }
} for 10 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 11 Tick, 9 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 1

// Scenario 3b (R7, RELEASED) — BOUNDARY WITNESS (RECONCILED): the frozen-state dangle is LEGAL,
// surfaced by retiredMembersAt.
run unit_dem_frozenDangleBoundary {
  some d: DemandItem, t: Tick | {
    demandStatusAt[d, t] = DS_RELEASED
    some retiredMembersAt[d, t]
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId, 2 Note, 2 Reference expect 1

// R7 in-flight BOUNDARY WITNESS (C/NOTIF): an OPEN demand with a withdrawn member still
// attached — the legal intermediate between the withdrawal and the reaction.
run unit_dem_openWithdrawnInFlight {
  some d: DemandItem, t: Tick | {
    demandStatusAt[d, t] = DS_OPEN
    some retiredMembersAt[d, t]
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId, 2 Note, 2 Reference expect 1

// Scenario 5 (R8, produce — call-first): the member's StartProcessing precedes the committed
// StartProduction; both logs read IN_PROCESS at the commit.
run unit_dem_startProductionCommits {
  some o: StartProductionOcc, k: StartProcessingOcc | {
    committed[o] and committed[k]
    k.cycle in attachedLiveAt[o.subject, o.tick] and precedes[k.tick, o.tick]
    demandStatusAt[o.subject, o.tick] = DS_IN_PROCESS
    statusAt[k.cycle, o.tick] = IN_PROCESS
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 Tick, 9 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 1

// Scenario 5 variant (R8, production failure — call-first): the caller settles the
// inventory-less member back to the queue (ProductionFailure → REQUESTING), then Complete.
run unit_dem_completeWithProductionFailure {
  some o: CompleteOcc, pf: ProductionFailureOcc | {
    committed[o] and committed[pf]
    cyclesOf[dPre[o].sContributions] = pf.cycle and precedes[pf.tick, o.tick]
    demandStatusAt[o.subject, o.tick] = DS_COMPLETE
    statusAt[pf.cycle, o.tick] = REQUESTING
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 11 Tick, 9 EntityId, 12 Snapshot,
      10 Occurrence, 2 Note, 2 Reference expect 1

// Terminal Delete/Retire (R7): the tombstoned retirement of a CANCELED task.
run unit_dem_deleteRetiresTerminal {
  some o: DeleteDemandOcc | committed[o] and dPre[o].sStatus = DS_CANCELED
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 Tick, 2 Note, 2 Reference expect 1

// ── C/OP in-flight BOUNDARY WITNESSES (legal intermediates — the remodel's point) ───────────────
// An ACCEPTED cycle not (yet) attached: the attach saga's crash window; convergence = retry the
// attach or compensate with Shelve.
run unit_dem_acceptedUnattachedInFlight {
  some c: CardCycle, t: Tick | {
    liveCycleAt[c, t] and statusAt[c, t] = REQUESTED
    no demandOf[c, t]
    no o: AttachOcc + TargetOcc | committed[o]
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note, 2 Reference expect 1

// A STARTED member under a still-RELEASED demand: the production saga's partial-call window.
run unit_dem_startedBeforeCommitInFlight {
  some d: DemandItem, c: CardCycle, t: Tick | {
    demandStatusAt[d, t] = DS_RELEASED
    c in attachedLiveAt[d, t] and statusAt[c, t] = IN_PROCESS
    no o: StartProductionOcc | committed[o]
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 Tick, 9 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 1

// ── R1-amended BOUNDARY WITNESS: no uniqueness — two OPEN demands for ONE (Item, Station) pair
// in one tenant are LEGAL (single-OPEN, if wanted, is caller policy over `demandsFor`). ─────────
run unit_dem_twoOpenSameIdentityLegal {
  some disj a, b: DemandItem, t: Tick | {
    a.tenantId = b.tenantId
    demandStatusAt[a, t] = DS_OPEN and demandStatusAt[b, t] = DS_OPEN
    a.itemPin.subject = b.itemPin.subject and a.stationRef = b.stationRef
    a + b in demandsFor[a.itemPin.subject, a.stationRef, t]
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId, 2 Note, 2 Reference expect 1

// ── reason-precise refusal witnesses (one per Reason) ───────────────────────────────────────────
run unit_dem_demandStartedRefused {
  some o: CreateDemandOcc | refusedAtAdmission[o] and RDemandStarted in o.admission.because
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note, 2 Reference expect 1

run unit_dem_demandClosedRefused {
  some o: ReleaseOcc | refusedAtAdmission[o] and o.admission.because = RDemandClosed
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note, 2 Reference expect 1

run unit_dem_badStateRefused {
  some o: StartProductionOcc | refusedAtAdmission[o] and o.admission.because = RBadState
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note, 2 Reference expect 1

// RForeignRef guards the RECORD-carried refs only (holding/delivery) — the entity's
// stationRef is kernel-covered; the itemPin rides DemandItemPinTenancy (cross-tenant = unrepresentable).
run unit_dem_foreignRefRefused {
  some o: StartProductionOcc | refusedAtAdmission[o] and RForeignRef in o.admission.because
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 9 EntityId, 2 Note, 2 Reference expect 1

run unit_dem_foreignCycleRefused {
  some o: AddContributionOcc | refusedAtAdmission[o] and RForeignCycle in o.admission.because
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 2 KanbanCard, 0 InventoryItem, 9 EntityId, 2 Note, 2 Reference expect 1

run unit_dem_cycleHeldRefused {
  some o: AddContributionOcc | refusedAtAdmission[o] and RCycleHeld in o.admission.because
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 Tick, 12 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 1

// The gate refusal: attaching a cycle still REQUESTING (its Accept — the saga's first leg —
// has not committed) is refused with exactly RCycleIneligible.
run unit_dem_cycleIneligibleRefused {
  some o: AddContributionOcc | {
    refusedAtAdmission[o] and o.admission.because = RCycleIneligible
    statusAt[cyclesOf[o.contribution], o.tick] = REQUESTING
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId, 2 Note, 2 Reference expect 1

run unit_dem_cycleLiveRefused {
  some o: DetachWithdrawnOcc | refusedAtAdmission[o] and RCycleLive in o.admission.because
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId, 2 Note, 2 Reference expect 1

// (The name is the Dafny witness's pointer; since TN-004 the reason is RNotContribution: RNotAttached is declared, never raised.)
run unit_dem_notAttachedRefused {
  some o: RemoveContributionOcc | refusedAtAdmission[o] and RNotContribution in o.admission.because
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId, 2 Note, 2 Reference expect 1

run unit_dem_hasCardsRefused {
  some o: CancelOcc | refusedAtAdmission[o] and o.admission.because = RHasCards
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 EntityId, 2 Note, 2 Reference expect 1

run unit_dem_badAllocationRefused {
  some o: DistributeOcc | refusedAtAdmission[o] and RBadAllocation in o.admission.because
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 9 Tick, 9 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 1

// (`unit_dem_undistributedRefused` left with its reason: TN-004 row 11, dafny-domain MD-084 — a Complete is no longer refused
// for a holding that is not retired. What the released pools still hold is the placements' matter: the PR B section below.)

run unit_dem_notTerminalRefused {
  some o: DeleteDemandOcc | refusedAtAdmission[o] and o.admission.because = RNotTerminal
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note, 2 Reference expect 1

// An unattached REQUESTING cycle persists indefinitely (R6: attachment is NEVER automatic).
run unit_dem_unattachedRequestingLegal {
  some c: CardCycle, t: Tick | statusAt[c, t] = REQUESTING and no demandOf[c, t]
    and no o: demandOccKinds | committed[o]
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note, 2 Reference expect 1

// ── the §8.5.3 lattice row + provenance (DT-020 cut 5) — UNIT-dischargeable since kanban
// published poolProvenance: the cross-kind clause reasons from attach payloads to record
// bindings through the mock. Scope discipline: 2 of the OWN kind + 1 cycle; explicit
// abstract-parent pins (knowledge-base/pool-lattice-genesis-premise.md §3). ────────────────────
assert unit_dem_contract_holdingProvenance { holdingProvenance }
check unit_dem_contract_holdingProvenance for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 InventoryPool,
      8 Occurrence, 10 EntityId, 7 Tick, 8 Snapshot, 2 Note, 2 Reference expect 0

assert unit_dem_contract_holdingExclusive { holdingExclusiveWhileLive }
check unit_dem_contract_holdingExclusive for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 InventoryPool,
      8 Occurrence, 10 EntityId, 7 Tick, 8 Snapshot, 2 Note, 2 Reference expect 0

// The SAT companion (anti-vacuity): the premise HOLDS with a live demand holding its pool and
// a live MOCK cycle holding a distinct one (the cycle's binding now needs its committed
// StartProcessing — poolProvenance in the mock).
run unit_dem_latticeCompanion {
  demandPoolGenesis
  some t: Tick, d: DemandItem, c: CardCycle, disj p1, p2: InventoryPool | {
    liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p1
    liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p2
  }
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 InventoryPool,
      12 EntityId, 9 Tick, 10 Snapshot, 9 Occurrence, 2 Note, 2 Reference expect 1

// ── the ProductionDelivery subject (§8.1.2/§8.1.4, DT-020 build cut 3) ──────────────────────────
// Contract discharge — the §8.1.4 gates as theorems of createDeliveryViol:
assert unit_dem_contract_createDeliveryGated { createDeliveryGated }
check unit_dem_contract_createDeliveryGated for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 ProductionDelivery, 2 Note, 2 Reference expect 0

assert unit_dem_contract_deliveryTerminalRevoke { deliveryTerminalRevoke }
check unit_dem_contract_deliveryTerminalRevoke for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 ProductionDelivery, 2 Note, 2 Reference expect 0

// The composed accrual arc (§8.1.2 ATOMIC): CreateDelivery + its RecordProduction on the
// target's log — the F7 edge as one demand tx (two ticks under OneOccurrencePerTick).
run unit_dem_deliveryComposedArc {
  some c: CreateDeliveryOcc, r: RecordProductionOcc | {
    committed[c] and committed[r]
    r.delivery = c.subject.eId and r.subject.eId = c.subject.demandRef
    deliveryStatusAt[c.subject, c.tick] = PD_CREATED
    c.subject in contributionsFor[resolve[c.subject.demandRef] & DemandItem, c.tick]
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      9 Tick, 9 EntityId, 8 Snapshot, 2 Note, 2 Reference expect 1

// The composed reversal arc: Revoke + ExtractProduction; the delivery leaves the
// contributions fold forever (reversing-entry semantics — §8.1.1).
run unit_dem_deliveryRevokedArc {
  some v: RevokeDeliveryOcc, x: ExtractProductionOcc | {
    committed[v] and committed[x]
    x.delivery = v.subject.eId
    deliveryStatusAt[v.subject, v.tick] = PD_REVOKED
    v.subject not in contributionsFor[resolve[v.subject.demandRef] & DemandItem, v.tick]
  }
} for 10 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      12 Tick, 10 EntityId, 9 Snapshot, 2 Note, 2 Reference expect 1

// §8.1.4 refusal: a CreateDelivery whose target is not IN_PROCESS (here: still OPEN) —
// exactly RTargetNotInProcess. The OPEN→IN_PROCESS choreography is a composite's, not ours.
run unit_dem_targetNotInProcessRefused {
  some o: CreateDeliveryOcc | {
    refusedAtAdmission[o] and o.admission.because = RTargetNotInProcess
    demandStatusAt[resolve[o.subject.demandRef] & DemandItem, o.tick] = DS_OPEN
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      8 EntityId, 8 Snapshot, 2 Note, 2 Reference expect 1

// §8.1.4 item agreement refusal: the delivery denominated in the WRONG item — exactly
// RWrongItem (the pool module's reason reused; agreement is a Create guard, never a
// downstream pool-law violation).
run unit_dem_deliveryWrongItemRefused {
  some o: CreateDeliveryOcc | {
    refusedAtAdmission[o] and o.admission.because = RWrongItem
    demandStatusAt[resolve[o.subject.demandRef] & DemandItem, o.tick] = DS_IN_PROCESS
  }
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      9 EntityId, 8 Snapshot, 2 Note, 2 Reference expect 1

// M3 (DT-020 §8.5.3 / SPEARHEAD-D1 A′-2, MINESWEEPER model-deltas M3.1): pool-vs-demand item
// agreement on the RECORD side too. MF-003 (MP, 2026-10-16) narrows the arm to COMMITTED creates. A
// committed create has already passed the create-side arm (its pool agrees with the demand's item),
// and in this universe ids are keys and pins are static, so the record-side arm cannot fire here:
// the create-side arm SUBSUMES it. It stays for the runtime, where the pools can change between the
// two halves (the Dafny follower's witness `RecordWrongItem` exhibits that case). Was
// `run unit_dem_recordProductionWrongPoolItemRefused … expect 1`, satisfiable only because the arm
// read REFUSED creates, which is what made the honest retry below unrecordable.
assert unit_dem_recordProductionItemArmSubsumed {
  no r: RecordProductionOcc | RWrongItem in r.admission.because
}
check unit_dem_recordProductionItemArmSubsumed for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery, 1 InventoryPool,
      10 EntityId, 9 Snapshot, 2 Note, 2 Reference expect 0

// MF-003 (MP, 2026-10-16): the honest RETRY. A create naming a pool of another item is refused with
// RWrongItem; the retry (same delivery, naming a pool — which its committed create guard makes one that
// agrees; Copilot on PR #7) commits, and so does its RecordProduction.
// RED before the change: the record read the refused create's pool and was refused RWrongItem, and
// `createRecordsAtomically` then excluded the retry altogether (UNSAT).
run unit_dem_deliveryRetryAfterWrongPoolRecorded {
  some disj c1, c2: CreateDeliveryOcc, r: RecordProductionOcc | {
    refusedAtAdmission[c1] and c1.admission.because = RWrongItem
    committed[c2] and c2.subject = c1.subject and precedes[c1.tick, c2.tick]
    some resolve[c2.pool] & InventoryPool   // the retry NAMES a pool, so its committed guard proved the item agreement
    committed[r] and r.delivery = c2.subject.eId
  }
} for 10 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery, 2 InventoryPool,
      12 Tick, 11 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 1

// M3.2: the minted holding pool's itemPin always agrees with the demand's item — a THEOREM of
// the StartProduction effect (`StartProductionHoldingPoolPin`). RED before the fact: nothing
// constrained a resolved holding pool's itemPin, so the solver could freely disagree them.
assert unit_dem_holdingPoolPinMatchesItem {
  all o: StartProductionOcc, p: resolve[o.holding] & InventoryPool |
    committed[o] implies p.itemPin.subject = o.subject.itemPin.subject
}
check unit_dem_holdingPoolPinMatchesItem for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 InventoryPool,
      8 Occurrence, 10 EntityId, 7 Tick, 8 Snapshot, 2 Note, 2 Reference expect 0

// Revoke on an already-REVOKED delivery — exactly RDeliveryClosed (terminal §8.1.1).
run unit_dem_revokeRevokedRefused {
  some o: RevokeDeliveryOcc | refusedAtAdmission[o] and o.admission.because = RDeliveryClosed
    and some o.pre and pdPre[o].sStatus = PD_REVOKED
} for 10 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      13 Tick, 13 EntityId, 14 Snapshot, 13 Occurrence, 2 Note, 2 Reference expect 1
      // raised at the Alloy cut (2026-11-06): no verdict in 2 h 23 min at the old bounds; SAT in 166 s at these
      // (12 Occurrence = 2 Call + 10 rows, Snapshot 14 at the bound — each row brings its activation call)
      // census +1 across the board at DT-023 cut 7a: the trace's item-log fixture (the
      // committed CreateItemOcc behind the demand genesis guard) pushed the occurrence
      // count past the old for-8 default this deep witness sat exactly at

// ── DT-023 cut 8: gate at INCEPTION, never at PROPAGATION ──────────────────────────────────────

// PROPAGATION is ungated: a scan-derived demand (CreateWithCycle — the pin inherited from
// the triggering cycle, whose REQUEST was the gated inception) COMMITS even though its item
// has since RETIRED. This is the anti-deadlock half of the cut-8 ruling: the scan workflow
// must not strand on a mid-flight retirement.
run unit_dem_scanDerivedRetiredAllowed {
  some o: CreateWithContributionOcc, k: AcceptOcc, d: RetireItemOcc | {
    committed[o] and committed[k] and committed[d]
    k.cycle = cyclesOf[o.contribution] and precedes[k.tick, o.tick]
    d.subject = o.subject.itemPin.subject and precedes[d.tick, o.tick]
    not itemLiveAt[o.subject.itemPin.subject, o.tick]
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem,
      12 EntityId, 9 Tick, 9 Snapshot, 9 Occurrence, 2 Note, 2 Reference expect 1

// INCEPTION stays gated: a DIRECT create (the caller chooses the item — F6/queue-add) of a
// demand for a retired item refuses with exactly RRetiredRef.
run unit_dem_directCreateRetiredRefused {
  some o: CreateDemandOcc, d: RetireItemOcc | {
    committed[d]
    d.subject = o.subject.itemPin.subject and precedes[d.tick, o.tick]
    refusedAtAdmission[o] and o.admission.because = RRetiredRef
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem,
      10 EntityId, 7 Tick, 7 Snapshot, 7 Occurrence, 2 Note, 2 Reference expect 1

// ── DT-030 retire cut (2026-09-09): terminality ──────────────────────────────────────────────────
// Nothing commits on a demand item after its committed delete (the tombstone is the end of history).
assert unit_dem_nothingAfterRetire {
  all r: DeleteDemandOcc, o: CreateDemandOcc + CreateWithContributionOcc + AddContributionOcc + RemoveContributionOcc + EditContributionOcc + SetContributionNotesOcc + SetUserNotesOcc + SetWorkOrderOcc + SetFulfillmentNotesOcc + DetachWithdrawnOcc + ReleaseOcc + ReopenOcc + StartProductionOcc + RecordProductionOcc + ExtractProductionOcc + DistributeOcc + CompleteOcc + CancelOcc + DeleteDemandOcc | (committed[r] and committed[o] and o.subject = r.subject) implies not precedes[r.tick, o.tick]
}
check unit_dem_nothingAfterRetire for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 3 CardCycle, 2 KanbanCard, 0 InventoryItem, 9 Tick, 12 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 0

// ── COORDINATOR-Q527 (MP, 2026-10-15: the RBackdated family) — a COMPLETE is refused when its holding pool's newest
// write is dated after the COMPLETE's own stamp. RESTATED by TN-004 row 11 (dafny-domain MD-084, DT-016 PR B): Option B's
// other half, the RETIRED-holding gate with its reason RUndistributed, LEFT — the holding is released at rest, no retire is
// required (W3 is gone, W4 inverts). Commands pin `3 Instant` (before / equal / after).

// W1: the family's demand member — exactly RBackdatedHolding when the holding pool, RETIRED at the commit (so it is
// empty and no placement arm reads it), has its newest write dated AFTER the COMPLETE's own stamp.
run unit_dem_completeBackdatedHoldingRefused {
  some o: CompleteOcc, p: InventoryPool | {
    refusedAtAdmission[o] and o.admission.because = RBackdatedHolding
    resolve[dPre[o].sHolding] = p and poolRetiredAt[p, o.tick]
    some w: lastPoolWrite[p, o.tick] | earlierThan[o.at, w.at]
  }
} for 11 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 5 Instant,
      15 Tick, 14 EntityId, 16 Snapshot, 2 Note, 2 Reference expect 1

// W2: every committed pool write causally before a committed COMPLETE is dated at or before it (the A5
// condition as a published law — a theorem of the RBackdatedHolding arm and the pool's own trace law).
assert unit_dem_contract_completeStampedAfterHolding { completeStampedAfterHolding }
check unit_dem_contract_completeStampedAfterHolding for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 3 Instant,
      8 Occurrence, 10 EntityId, 8 Tick, 9 Snapshot, 2 Note, 2 Reference expect 0

// (W3, the check of `completeRequiresRetiredHolding`, left with the law: TN-004 row 11, dafny-domain MD-084.)

// W4, INVERTED (dafny-domain DemandTests.CompleteAgainstHolding as restated by PR B): an EMPTY and UNRETIRED holding pool
// no longer refuses the COMPLETE — it COMMITS. (The command was `unit_dem_completeUnretiredEmptyHoldingRefused`, exactly
// RUndistributed; the reason is gone, so the witness is restated as the commit it now is.)
run unit_dem_completeUnretiredEmptyHoldingCommits {
  some o: CompleteOcc, p: InventoryPool | {
    committed[o]
    resolve[dPre[o].sHolding] = p and no heldAt[p, o.tick] and not poolRetiredAt[p, o.tick]
  }
} for 9 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 3 Instant,
      13 Tick, 12 EntityId, 14 Snapshot, 2 Note, 2 Reference expect 1

// W5 (control): the ruled path commits — the holding pool retired EMPTY, dated before the COMPLETE, then COMPLETE.
run unit_dem_completeRetiredHoldingCommits {
  some o: CompleteOcc, p: InventoryPool, r: RetirePoolOcc | {
    committed[o] and committed[r]
    resolve[dPre[o].sHolding] = p and r.subject = p and precedes[r.tick, o.tick]
    earlierThan[r.at, o.at]
  }
} for 9 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 3 Instant,
      13 Tick, 12 EntityId, 14 Snapshot, 2 Note, 2 Reference expect 1

// W6 (control, the record's E7): the retire dated EXACTLY at the COMPLETE's stamp lets it commit (at-or-before).
run unit_dem_completeHoldingDatedAtCommits {
  some o: CompleteOcc, p: InventoryPool, r: RetirePoolOcc | {
    committed[o] and committed[r]
    resolve[dPre[o].sHolding] = p and r.subject = p and precedes[r.tick, o.tick]
    r.at = o.at
  }
} for 9 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 3 Instant,
      13 Tick, 12 EntityId, 14 Snapshot, 2 Note, 2 Reference expect 1

// ── QA704 Q4 (a), DT-009 Q27: the holding pool's item pin is a guard arm of StartProduction (reflects dafny-domain
// src/operations/demand/demand.dfy StartProductionViol, RWrongItem) ──
// A StartProduction naming a holding whose pool carries ANOTHER item's pin is refused with RWrongItem. RED before the arm:
// `StartProductionHoldingPoolPin` was a FACT over committed rows and no arm carried the reason, so the refusal was unrepresentable.
run unit_dem_startProductionWrongItemRefused {
  some o: StartProductionOcc | refusedAtAdmission[o] and RWrongItem in o.admission.because
    and some p: resolve[o.holding] & InventoryPool | p.itemPin.subject != o.subject.itemPin.subject
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 9 EntityId, 2 Note, 2 Reference expect 1
// The law is a THEOREM of the arm: a committed StartProduction's resolved holding pool carries the demand's item pin (M3.2).
check unit_dem_holdingPoolPinHolds {
  all o: StartProductionOcc | committed[o] implies
    (all p: resolve[o.holding] & InventoryPool | p.itemPin.subject = o.subject.itemPin.subject)
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 9 EntityId, 2 Note, 2 Reference expect 0

// ── QA704 Q2 (b) (MP, 2026-11-05; dafny-domain#33, MD-074): a named holding pool must EXIST and be LIVE ─────────────────────
// A StartProduction naming a holding that resolves to no live pool (no pool, or a pool retired before the act) is refused
// RNoSuchPool. RED before the arm: the reason atom does not exist; the old guard admitted the dangling holding (TN-001 S-08).
run unit_dem_startProductionNoSuchPoolRefused {
  some o: StartProductionOcc | some o.holding and not namedPoolLive[o.holding, o.tick]
    and refusedAtAdmission[o] and RNoSuchPool in o.admission.because
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 9 EntityId, 8 Occurrence, 8 Tick, 2 Note, 2 Reference expect 1
// The holding retired between two deliveries: a RecordProduction on the IN_PROCESS demand is refused RNoSuchPool (reading A: the
// delivery's genesis refuses the same condition, so the second Deliver refuses whole; this witness is the direct record).
run unit_dem_recordProductionHoldingRetiredRefused {
  some o: RecordProductionOcc, p: InventoryPool | liveAtOccD[o] and dPre[o].sStatus = DS_IN_PROCESS
    and p in resolve[dPre[o].sHolding] and poolRetiredAt[p, o.tick]
    and refusedAtAdmission[o] and RNoSuchPool in o.admission.because
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery, 1 InventoryPool,
      12 EntityId, 11 Tick, 10 Occurrence, 10 Snapshot, 2 Note, 2 Reference expect 1
// The delivery's genesis under the same condition is refused RNoSuchPool (the pair keeps one verdict).
run unit_dem_createDeliveryHoldingRetiredRefused {
  some c: CreateDeliveryOcc, d: resolve[c.subject.demandRef] & DemandItem, p: InventoryPool |
    demandStatusAt[d, c.tick] = DS_IN_PROCESS and p in resolve[demandStateAt[d, c.tick].sHolding] and poolRetiredAt[p, c.tick]
    and refusedAtAdmission[c] and RNoSuchPool in c.admission.because
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery, 1 InventoryPool,
      12 EntityId, 11 Tick, 10 Occurrence, 10 Snapshot, 2 Note, 2 Reference expect 1
// The laws are THEOREMS of the arms (Dafny StartedHoldingLive, RecordedHoldingLive): a committed act's holding is live at its tick.
check unit_dem_startedHoldingLive {
  all o: StartProductionOcc | (committed[o] and some o.holding) implies namedPoolLive[o.holding, o.tick]
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 9 EntityId, 8 Occurrence, 8 Tick, 2 Note, 2 Reference expect 0
check unit_dem_recordedHoldingLive {
  all o: RecordProductionOcc | (committed[o] and some dPre[o].sHolding) implies namedPoolLive[dPre[o].sHolding, o.tick]
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery, 1 InventoryPool, 10 EntityId, 9 Occurrence, 9 Tick, 2 Note, 2 Reference expect 0

// ══ TN-004, the demand's contributions (dafny-domain MD-076 to MD-080; PR A, on dafny-domain main at 0040544) ════════════════
// The FINDERS of the witnesses PR A added to dafny-domain src/operations/demand/tests/demand-tests.dfy, each named after the
// witness it finds an instance for. WRITTEN FIRST (test-first, TN-005 section 10): they name the contribution surface the
// module gains in the next commit — `Contribution` (`CardContribution`, `ExternalContribution`, keyed by `cid`), the state's
// `sContributions`, the kinds `CreateWithContributionOcc`, `AddContributionOcc`, `RemoveContributionOcc`,
// `EditContributionOcc`, `SetContributionNotesOcc`, `SetUserNotesOcc`, `SetWorkOrderOcc`, `SetFulfillmentNotesOcc`, the reads
// `contributionsAt` and `referenceOf`, and the reasons `RNoContribution`, `RContributionStarted`, `RDuplicateReference`,
// `RNotContribution`, `RNotExternal`. Until that commit this root does not compile: that is the first red.
// The references (an external reference, a card's reference override, a work order) are ONE inert value, `Reference`,
// pinned at 2 in every command (alloy/CLAUDE.md gotcha 7). A reference that is some card's serial is that `CardSerial`.
// SCOPES ARE FIRST ESTIMATES, NOT YET RUN. The two-kind sum (`ContributionsSum`) is in the confined root
// tests/unit/demand_quantity.als. PR B's eight witnesses (the placements, the freshness of the holding, Cancel's pool arm)
// follow when dafny-domain #35 merges.

// ── DemandTests.EmptyBirthThenRelease ──────────────────────────────────────────────────────────────────────────────────────
// A demand born with no contribution: its Release is refused with exactly RNoContribution.
run unit_dem_emptyReleaseRefused {
  some d: DemandItem, c: CreateDemandOcc, r: ReleaseOcc | {
    c.subject = d and r.subject = d and committed[c] and precedes[c.tick, r.tick]
    no dPre[r].sContributions
    refusedAtAdmission[r] and r.admission.because = RNoContribution
  }
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 0 Contribution, 6 EntityId, 2 Note, 2 Reference expect 1

// After ONE card contribution the Release commits (the card's Accept came first: call-first).
run unit_dem_releaseAfterCardContribution {
  some d: DemandItem, c: CreateDemandOcc, a: AddContributionOcc, r: ReleaseOcc | {
    c.subject = d and a.subject = d and r.subject = d
    committed[c] and committed[a] and committed[r]
    precedes[c.tick, a.tick] and precedes[a.tick, r.tick]
    a.contribution in CardContribution
    dPre[r].sContributions = a.contribution
    demandStatusAt[d, r.tick] = DS_RELEASED
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 Contribution, 9 Tick, 9 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 1

// After ONE external contribution the Release commits too: no card is needed.
run unit_dem_releaseAfterExternalContribution {
  some d: DemandItem, c: CreateDemandOcc, a: AddContributionOcc, r: ReleaseOcc | {
    c.subject = d and a.subject = d and r.subject = d
    committed[c] and committed[a] and committed[r]
    precedes[c.tick, a.tick] and precedes[a.tick, r.tick]
    a.contribution in ExternalContribution
    dPre[r].sContributions = a.contribution
    demandStatusAt[d, r.tick] = DS_RELEASED
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 1 Contribution,
      9 Tick, 9 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 1

// ── DemandTests.ContributionIdOnceAndReferenceUnique ───────────────────────────────────────────────────────────────────────
// A second attach under an id the demand's log already carried is refused with exactly RContributionStarted.
run unit_dem_contributionStartedRefused {
  some a1, a2: AddContributionOcc | {
    a1.subject = a2.subject and committed[a1] and precedes[a1.tick, a2.tick]
    a2.contribution.cid = a1.contribution.cid
    refusedAtAdmission[a2] and a2.admission.because = RContributionStarted
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 InventoryPool, 2 Contribution,
      10 Tick, 12 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 1

// Two external contributions under one reference: the second is refused with exactly RDuplicateReference.
run unit_dem_duplicateReferenceRefused {
  some a1, a2: AddContributionOcc | {
    a1.subject = a2.subject and committed[a1] and precedes[a1.tick, a2.tick]
    (a1.contribution + a2.contribution) in ExternalContribution
    a2.contribution.cid != a1.contribution.cid
    a2.contribution.externalReference = a1.contribution.externalReference
    refusedAtAdmission[a2] and a2.admission.because = RDuplicateReference
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 InventoryPool, 2 Contribution,
      10 Tick, 12 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 1

// A card contribution whose DEFAULT reference (its card's serial) equals a live external contribution's reference is refused
// the same: the uniqueness compares the references as read, not as stored.
run unit_dem_cardSerialClashRefused {
  some e, k: AddContributionOcc, cc: CardContribution | {
    e.subject = k.subject and committed[e] and precedes[e.tick, k.tick]
    e.contribution in ExternalContribution and k.contribution = cc
    no cc.referenceOverride
    e.contribution.externalReference = referenceOf[cc]
    refusedAtAdmission[k] and k.admission.because = RDuplicateReference
  }
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 2 Contribution,
      10 Tick, 12 EntityId, 12 Snapshot, 2 Note, 2 Reference expect 1

// ── DemandTests.CardSerialDefault ──────────────────────────────────────────────────────────────────────────────────────────
// A card contribution attached with no override keeps none in the state and READS its card's serial.
run unit_dem_cardSerialDefault {
  some a: AddContributionOcc, cc: CardContribution | {
    committed[a] and a.contribution = cc and no cc.referenceOverride
    cc in dPost[a].sContributions
    referenceOf[cc] = (cycles.(resolve[cc.cycleRef] & CardCycle)).serialNumber
    some referenceOf[cc]
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 Contribution, 9 Tick, 9 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 1

// Across a rollover of one card: attaching the successor cycle BEFORE the withdrawn one is detached is refused with exactly
// RDuplicateReference (both read the card's serial; the withdrawn entry is still in the state).
run unit_dem_rolloverBeforeDetachRefused {
  some w: WithdrawOcc, a2: AddContributionOcc, disj c1, c2: CardContribution | {
    committed[w] and precedes[w.tick, a2.tick]
    c1 in dPre[a2].sContributions and (resolve[c1.cycleRef] & CardCycle) = w.subject
    a2.contribution = c2 and c1.cycleRef != c2.cycleRef
    no c1.referenceOverride and no c2.referenceOverride
    referenceOf[c1] = referenceOf[c2]
    refusedAtAdmission[a2] and a2.admission.because = RDuplicateReference
  }
} for 10 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Contribution,
      13 Tick, 12 EntityId, 14 Snapshot, 12 Occurrence, 2 Note, 2 Reference expect 1

// After the detach the successor attaches, and reads the same serial: the default does not collide with an entry that left.
run unit_dem_rolloverAfterDetachCommits {
  some dt: DetachWithdrawnOcc, a2: AddContributionOcc, disj c1, c2: CardContribution | {
    dt.subject = a2.subject and committed[dt] and committed[a2] and precedes[dt.tick, a2.tick]
    dt.target = c1.cid and c1 in dPre[dt].sContributions
    a2.contribution = c2 and no c1.referenceOverride and no c2.referenceOverride
    referenceOf[c1] = referenceOf[c2]
  }
} for 11 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Contribution,
      14 Tick, 12 EntityId, 16 Snapshot, 13 Occurrence, 2 Note, 2 Reference expect 1

// ── DemandTests.ExternalPoolArms ───────────────────────────────────────────────────────────────────────────────────────────
// A committed external attach: its pool exists and is live, is in the demand's tenant and carries the demand's item.
run unit_dem_externalPoolAttached {
  some a: AddContributionOcc, e: ExternalContribution, p: InventoryPool | {
    committed[a] and a.contribution = e and p = resolve[e.cPool]
    poolLiveAt[p, a.tick] and p.tenantId = a.subject.tenantId
    p.itemPin.subject = a.subject.itemPin.subject
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 1 Contribution,
      9 Tick, 9 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 1

// The pool does not exist, or is retired: exactly RNoSuchPool.
run unit_dem_externalNoSuchPoolRefused {
  some a: AddContributionOcc, e: ExternalContribution | {
    a.contribution = e and not namedPoolLive[e.cPool, a.tick]
    refusedAtAdmission[a] and a.admission.because = RNoSuchPool
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 1 Contribution,
      9 Tick, 9 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 1

// The pool is another tenant's: RForeignRef is among the reasons.
run unit_dem_externalForeignPoolRefused {
  some a: AddContributionOcc, e: ExternalContribution, p: InventoryPool | {
    a.contribution = e and p = resolve[e.cPool] and p.tenantId != a.subject.tenantId
    refusedAtAdmission[a] and RForeignRef in a.admission.because
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 1 Contribution,
      9 Tick, 9 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 1

// The pool carries another item: exactly RWrongItem.
run unit_dem_externalWrongItemRefused {
  some a: AddContributionOcc, e: ExternalContribution, p: InventoryPool | {
    a.contribution = e and p = resolve[e.cPool] and p.itemPin.subject != a.subject.itemPin.subject
    refusedAtAdmission[a] and a.admission.because = RWrongItem
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 1 Contribution,
      9 Tick, 9 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 1

// The pool was already named by another external attach: exactly RPoolNotFresh (the kanban module's atom, reused).
run unit_dem_externalPoolNotFreshRefused {
  some a1, a2: AddContributionOcc | {
    committed[a1] and precedes[a1.tick, a2.tick]
    (a1.contribution + a2.contribution) in ExternalContribution
    a2.contribution.cPool = a1.contribution.cPool
    a2.contribution.cid != a1.contribution.cid
    a2.contribution.externalReference != a1.contribution.externalReference
    refusedAtAdmission[a2] and a2.admission.because = RPoolNotFresh
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 2 Contribution,
      10 Tick, 12 EntityId, 12 Snapshot, 2 Note, 2 Reference expect 1

// ── DemandTests.EditAndRemove ──────────────────────────────────────────────────────────────────────────────────────────────
// An edit of an external contribution sets the fields it carries (quantity and reference) and keeps the pool and the id.
run unit_dem_editExternalSetsFields {
  some ed: EditContributionOcc, disj e0, e1: ExternalContribution | {
    committed[ed] and some ed.newQuantity and some ed.newReference
    e0 in dPre[ed].sContributions and e0.cid = ed.target
    e1 in dPost[ed].sContributions and e1.cid = ed.target
    e1.quantity = ed.newQuantity and e1.externalReference = ed.newReference
    e1.quantity != e0.quantity and e1.externalReference != e0.externalReference
    e1.cPool = e0.cPool
    e0 not in dPost[ed].sContributions
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 2 Contribution,
      10 Tick, 10 EntityId, 12 Snapshot, 4 Quantity, 2 Note, 2 Reference expect 1

// An edit of a card contribution's reference sets the override, and the read follows it.
run unit_dem_editCardReference {
  some ed: EditContributionOcc, disj c0, c1: CardContribution | {
    committed[ed] and no ed.newQuantity and some ed.newReference
    c0 in dPre[ed].sContributions and c0.cid = ed.target and no c0.referenceOverride
    c1 in dPost[ed].sContributions and c1.cid = ed.target
    referenceOf[c1] = ed.newReference and referenceOf[c1] != referenceOf[c0]
    c1.cycleRef = c0.cycleRef
  }
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Contribution,
      10 Tick, 10 EntityId, 12 Snapshot, 2 Note, 2 Reference expect 1

// A quantity on a card contribution: exactly RNotExternal (a card's quantity is its cycle's).
run unit_dem_editQuantityOnCardRefused {
  some ed: EditContributionOcc, c0: CardContribution | {
    c0 in dPre[ed].sContributions and c0.cid = ed.target and some ed.newQuantity
    refusedAtAdmission[ed] and ed.admission.because = RNotExternal
  }
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 Contribution,
      10 Tick, 10 EntityId, 12 Snapshot, 2 Note, 2 Reference expect 1

// An edit after the Release: exactly RFrozen (the edit is a composition mutator).
run unit_dem_editFrozenRefused {
  some ed: EditContributionOcc | {
    dPre[ed].sStatus = DS_RELEASED and ed.target in dPre[ed].sContributions.cid
    refusedAtAdmission[ed] and ed.admission.because = RFrozen
  }
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 1 Contribution,
      10 Tick, 10 EntityId, 12 Snapshot, 2 Note, 2 Reference expect 1

// An edit naming no contribution of the demand: exactly RNotContribution.
run unit_dem_editUnknownRefused {
  some ed: EditContributionOcc | {
    dPre[ed].sStatus = DS_OPEN and ed.target not in dPre[ed].sContributions.cid
    refusedAtAdmission[ed] and ed.admission.because = RNotContribution
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 0 Contribution, 8 EntityId, 2 Note, 2 Reference expect 1

// Removing an external contribution whose pool holds an item: exactly RPoolNotEmpty (the pool module's atom, reused).
run unit_dem_removeExternalNotEmptyRefused {
  some rm: RemoveContributionOcc, e: ExternalContribution, p: InventoryPool | {
    e in dPre[rm].sContributions and e.cid = rm.target and p = resolve[e.cPool]
    some heldAt[p, rm.tick]
    refusedAtAdmission[rm] and rm.admission.because = RPoolNotEmpty
  }
} for 9 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 1 InventoryItem, 1 InventoryPool, 1 Contribution,
      12 Tick, 12 EntityId, 14 Snapshot, 11 Occurrence, 4 Quantity, 2 Note, 2 Reference expect 1

// Removing it while its pool is empty commits, and the entry is gone.
run unit_dem_removeExternalCommits {
  some rm: RemoveContributionOcc, e: ExternalContribution | {
    committed[rm] and e in dPre[rm].sContributions and e.cid = rm.target
    rm.target not in dPost[rm].sContributions.cid
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 1 Contribution,
      10 Tick, 10 EntityId, 12 Snapshot, 2 Note, 2 Reference expect 1

// ── DemandTests.FieldWrites ────────────────────────────────────────────────────────────────────────────────────────────────
// The three field kinds of an OPEN demand write what they carry, and each reads back from the state.
run unit_dem_fieldWrites {
  some d: DemandItem, u: SetUserNotesOcc, w: SetWorkOrderOcc, n: SetContributionNotesOcc, t: Tick | {
    u.subject = d and w.subject = d and n.subject = d
    committed[u] and committed[w] and committed[n]
    some u.notes and some w.workOrder and some n.notes
    notAfter[u.tick, t] and notAfter[w.tick, t] and notAfter[n.tick, t]
    demandStateAt[d, t].sUserNotes = u.notes
    demandStateAt[d, t].sWorkOrder = w.workOrder
    some c: demandStateAt[d, t].sContributions | c.cid = n.target and c.cUserNotes = n.notes
  }
} for 9 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 2 Contribution,
      12 Tick, 10 EntityId, 14 Snapshot, 2 Note, 2 Reference expect 1

// A write carrying nothing CLEARS the field.
run unit_dem_fieldClears {
  some u1, u2: SetUserNotesOcc | {
    u1.subject = u2.subject and committed[u1] and committed[u2] and precedes[u1.tick, u2.tick]
    some u1.notes and no u2.notes
    some dPre[u2].sUserNotes and no dPost[u2].sUserNotes
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 0 Contribution, 8 EntityId, 2 Note, 2 Reference expect 1

// The fulfillment notes are written on a RELEASED demand.
run unit_dem_fulfillmentNotesOnReleased {
  some f: SetFulfillmentNotesOcc | {
    committed[f] and some f.notes and dPre[f].sStatus = DS_RELEASED
    dPost[f].sFulfillmentNotes = f.notes
  }
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 1 Contribution,
      10 Tick, 10 EntityId, 12 Snapshot, 2 Note, 2 Reference expect 1

// ── DemandTests.NotesWindows ───────────────────────────────────────────────────────────────────────────────────────────────
// The user notes stay writable on a CLOSED demand, until its tombstone.
run unit_dem_userNotesOnClosedCommits {
  some u: SetUserNotesOcc | committed[u] and dPre[u].sStatus in (DS_COMPLETE + DS_CANCELED)
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 0 Contribution, 8 EntityId, 2 Note, 2 Reference expect 1

// After the tombstone the same write is refused with exactly RDemandClosed.
run unit_dem_userNotesAfterDeleteRefused {
  some dl: DeleteDemandOcc, u: SetUserNotesOcc | {
    dl.subject = u.subject and committed[dl] and precedes[dl.tick, u.tick]
    refusedAtAdmission[u] and u.admission.because = RDemandClosed
  }
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 0 Contribution, 10 Tick, 8 EntityId, 10 Snapshot, 2 Note, 2 Reference expect 1

// The work order is an OPEN-only field: on a RELEASED demand its write is refused with exactly RBadState.
run unit_dem_workOrderReleasedRefused {
  some w: SetWorkOrderOcc | {
    dPre[w].sStatus = DS_RELEASED
    refusedAtAdmission[w] and w.admission.because = RBadState
  }
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 1 Contribution,
      10 Tick, 10 EntityId, 12 Snapshot, 2 Note, 2 Reference expect 1

// The fulfillment notes close at StartProduction: on an IN_PROCESS demand the write is refused with exactly RBadState.
run unit_dem_fulfillmentNotesInProcessRefused {
  some f: SetFulfillmentNotesOcc | {
    dPre[f].sStatus = DS_IN_PROCESS
    refusedAtAdmission[f] and f.admission.because = RBadState
  }
} for 9 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 InventoryPool, 1 Contribution,
      12 Tick, 12 EntityId, 14 Snapshot, 11 Occurrence, 2 Note, 2 Reference expect 1

// ── DemandTests.DistributeExternalFill ─────────────────────────────────────────────────────────────────────────────────────
// A Distribute may name an external contribution among its fills: nothing is gated on it (it has no cycle to be READY).
run unit_dem_distributeExternalFill {
  some o: DistributeOcc, e: ExternalContribution | {
    committed[o] and e in dPre[o].sContributions and e.cid in o.fills
  }
} for 9 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 InventoryPool, 1 Contribution,
      12 Tick, 12 EntityId, 14 Snapshot, 11 Occurrence, 4 Quantity, 2 Note, 2 Reference expect 1

// ── DemandTests.CancelWithExternalOnly ─────────────────────────────────────────────────────────────────────────────────────
// A Cancel commits on an OPEN demand whose contributions are all external: RHasCards reads the card contributions only.
run unit_dem_cancelWithExternalOnly {
  some cn: CancelOcc | {
    committed[cn] and some dPre[cn].sContributions
    dPre[cn].sContributions in ExternalContribution
    demandStatusAt[cn.subject, cn.tick] = DS_CANCELED
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 1 Contribution,
      10 Tick, 10 EntityId, 12 Snapshot, 2 Note, 2 Reference expect 1

// ══ TN-004, PR B's surface (dafny-domain MD-081 to MD-087; DT-016 PR B, on dafny-domain main at 606c392) ═════════════════════
// The FINDERS of the eight witnesses PR B added to dafny-domain src/operations/demand/tests/demand-tests.dfy, each named after
// the witness it finds an instance for. WRITTEN FIRST (test-first, TN-005 section 12): they name the surface the module gains
// in the next commit — the Complete's `placements` (`Placement`: `PlaceAll.allAt`, `PlacePerPool.byPool`,
// `PlacePerItem.byLocator`), the reads `releasedPoolIds`, `heldByReleased` and `placedLocator`, and the reasons
// `RBadPlacement`, `RPlacementIncomplete`, `RUnplaced`. Until that commit this root does not compile: that is the first red.
// In every scenario the demand's one contribution is EXTERNAL (no card, so no cycle gate), and a StartProduction may name no
// holding. SCOPES: the log's four dimensions are pinned (`Occurrence`, `Tick`, `EntityId`, `Snapshot`) and the default is 5:
// a row costs one occurrence, each service's committed rows share one activation, each refusal adds one, a pool's genesis
// adds one, and the demand's item pin is one more (TN-005 section 11, the first batch's reading).

// ── DemandTests.StartProductionFreshness ───────────────────────────────────────────────────────────────────────────────────
// The holding a StartProduction names must be FRESH. The pool of the demand's own external contribution: exactly RPoolNotFresh.
run unit_dem_startProductionExternalPoolRefused {
  some sp: StartProductionOcc, e: ExternalContribution | {
    dPre[sp].sStatus = DS_RELEASED and e in dPre[sp].sContributions and sp.holding = e.cPool
    refusedAtAdmission[sp] and sp.admission.because = RPoolNotFresh
  }
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 1 Contribution, 0 Placement, 3 Instant,
      10 Occurrence, 11 Tick, 10 EntityId, 12 Snapshot, 2 Note, 2 Reference expect 1

// A holding another demand's committed StartProduction already named: exactly RPoolNotFresh (the demand log's own memory).
run unit_dem_startProductionUsedHoldingRefused {
  some disj s1, s2: StartProductionOcc | {
    committed[s1] and precedes[s1.tick, s2.tick] and s1.subject != s2.subject
    some s1.holding and s2.holding = s1.holding
    refusedAtAdmission[s2] and s2.admission.because = RPoolNotFresh
  }
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 3 InventoryPool, 2 Contribution, 0 Placement, 3 Instant,
      14 Occurrence, 15 Tick, 14 EntityId, 16 Snapshot, 2 Note, 2 Reference expect 1

// ── DemandTests.HoldingsAttachedOnce ───────────────────────────────────────────────────────────────────────────────────────
// Two demands in production on two fresh holdings: their two StartProduction rows name different pools.
run unit_dem_twoFreshHoldings {
  some disj s1, s2: StartProductionOcc | {
    committed[s1] and committed[s2] and s1.subject != s2.subject
    some s1.holding and some s2.holding and s1.holding != s2.holding
  }
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 4 InventoryPool, 2 Contribution, 0 Placement, 3 Instant,
      14 Occurrence, 15 Tick, 14 EntityId, 16 Snapshot, 2 Note, 2 Reference expect 1

// ── DemandTests.CompletePlacements ─────────────────────────────────────────────────────────────────────────────────────────
// One locator for everything: the Complete commits when the item its released pool holds already sits there (call-first),
// and the demand is no longer live, so nothing of it holds a pool (the release, derived).
run unit_dem_completePlacedForAll {
  some o: CompleteOcc, e: ExternalContribution, p: InventoryPool, x: InventoryItem | {
    committed[o] and o.placements in PlaceAll
    e in dPre[o].sContributions and p = resolve[e.cPool] and x in heldAt[p, o.tick]
    e.cPool -> x in heldByReleased[o]
    stateAt[x, o.tick].sLocator = o.placements.allAt
    demandStatusAt[o.subject, o.tick] = DS_COMPLETE and not liveDemandAt[o.subject, o.tick]
  }
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 1 InventoryItem, 1 InventoryPool, 1 Contribution, 1 Placement, 3 Instant,
      10 Occurrence, 11 Tick, 10 EntityId, 13 Snapshot, 2 Note, 2 Reference expect 1

// ── DemandTests.CompletePlacementForms ─────────────────────────────────────────────────────────────────────────────────────
// The per-pool form: the item sits at the locator given for its pool.
run unit_dem_completePlacedPerPool {
  some o: CompleteOcc, e: ExternalContribution, p: InventoryPool, x: InventoryItem | {
    committed[o] and o.placements in PlacePerPool
    e in dPre[o].sContributions and p = resolve[e.cPool] and x in heldAt[p, o.tick]
    stateAt[x, o.tick].sLocator = (o.placements.byPool)[e.cPool]
  }
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 1 InventoryItem, 1 InventoryPool, 1 Contribution, 1 Placement, 3 Instant,
      10 Occurrence, 11 Tick, 10 EntityId, 13 Snapshot, 2 Note, 2 Reference expect 1

// The per-item form: the item's id is in the set of the locator it sits at.
run unit_dem_completePlacedPerItem {
  some o: CompleteOcc, e: ExternalContribution, p: InventoryPool, x: InventoryItem | {
    committed[o] and o.placements in PlacePerItem
    e in dPre[o].sContributions and p = resolve[e.cPool] and x in heldAt[p, o.tick]
    x.eId in (o.placements.byLocator)[stateAt[x, o.tick].sLocator]
  }
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 1 InventoryItem, 1 InventoryPool, 1 Contribution, 1 Placement, 3 Instant,
      10 Occurrence, 11 Tick, 10 EntityId, 13 Snapshot, 2 Note, 2 Reference expect 1

// ── DemandTests.CompleteBadPlacements ──────────────────────────────────────────────────────────────────────────────────────
// A pool the demand does not release: exactly RBadPlacement (nothing is held, so no other placement arm speaks).
run unit_dem_completeForeignPoolPlacementRefused {
  some o: CompleteOcc, q: EntityId | {
    dPre[o].sStatus = DS_IN_PROCESS and o.placements in PlacePerPool
    some (o.placements.byPool)[q] and q not in releasedPoolIds[dPre[o]]
    refusedAtAdmission[o] and o.admission.because = RBadPlacement
  }
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 1 Contribution, 1 Placement, 3 Instant,
      10 Occurrence, 11 Tick, 10 EntityId, 12 Snapshot, 2 Note, 2 Reference expect 1

// An item no released pool holds: exactly RBadPlacement.
run unit_dem_completeItemNotHeldRefused {
  some o: CompleteOcc, i: EntityId | {
    dPre[o].sStatus = DS_IN_PROCESS and o.placements in PlacePerItem
    i in PhysicalLocator.(o.placements.byLocator) and no heldByReleased[o]
    refusedAtAdmission[o] and o.admission.because = RBadPlacement
  }
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 1 Contribution, 1 Placement, 3 Instant,
      10 Occurrence, 11 Tick, 10 EntityId, 12 Snapshot, 2 Note, 2 Reference expect 1

// A HELD item under two locators: RBadPlacement is among the reasons (the item then has no one locator, so
// RPlacementIncomplete speaks too — dafny-domain `PlacedLocator` gives none unless exactly one set names the item).
run unit_dem_completeItemTwiceRefused {
  some o: CompleteOcc, x: InventoryItem, disj l1, l2: PhysicalLocator | {
    dPre[o].sStatus = DS_IN_PROCESS and o.placements in PlacePerItem
    x in EntityId.(heldByReleased[o])
    x.eId in (o.placements.byLocator)[l1] and x.eId in (o.placements.byLocator)[l2]
    refusedAtAdmission[o] and RBadPlacement in o.admission.because
  }
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 1 InventoryItem, 1 InventoryPool, 1 Contribution, 1 Placement, 3 Instant,
      11 Occurrence, 12 Tick, 10 EntityId, 13 Snapshot, 2 Note, 2 Reference expect 1

// ── DemandTests.CompleteUnplaced ───────────────────────────────────────────────────────────────────────────────────────────
// A held item whose pool the per-pool placements do not name: exactly RPlacementIncomplete.
run unit_dem_completePoolMissingRefused {
  some o: CompleteOcc, e: EntityId, x: InventoryItem | {
    e -> x in heldByReleased[o] and o.placements in PlacePerPool and no (o.placements.byPool)[e]
    refusedAtAdmission[o] and o.admission.because = RPlacementIncomplete
  }
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 1 InventoryItem, 1 InventoryPool, 1 Contribution, 1 Placement, 3 Instant,
      11 Occurrence, 12 Tick, 10 EntityId, 13 Snapshot, 2 Note, 2 Reference expect 1

// A held item no locator's set names: exactly RPlacementIncomplete.
run unit_dem_completeItemMissingRefused {
  some o: CompleteOcc, e: EntityId, x: InventoryItem | {
    e -> x in heldByReleased[o] and o.placements in PlacePerItem
    x.eId not in PhysicalLocator.(o.placements.byLocator)
    refusedAtAdmission[o] and o.admission.because = RPlacementIncomplete
  }
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 1 InventoryItem, 1 InventoryPool, 1 Contribution, 1 Placement, 3 Instant,
      11 Occurrence, 12 Tick, 10 EntityId, 13 Snapshot, 2 Note, 2 Reference expect 1

// A held item that does not sit where the placements say, as of the tick: exactly RUnplaced.
run unit_dem_completeUnplacedRefused {
  some o: CompleteOcc, e: EntityId, x: InventoryItem | {
    e -> x in heldByReleased[o] and o.placements in PlaceAll
    stateAt[x, o.tick].sLocator != o.placements.allAt
    refusedAtAdmission[o] and o.admission.because = RUnplaced
  }
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 1 InventoryItem, 1 InventoryPool, 1 Contribution, 1 Placement, 3 Instant,
      11 Occurrence, 12 Tick, 10 EntityId, 13 Snapshot, 2 Note, 2 Reference expect 1

// ── DemandTests.ReleasedPoolsStayUsed ──────────────────────────────────────────────────────────────────────────────────────
// Released at rest is not fresh: after the Complete released an external contribution's pool (EMPTY throughout: no
// InventoryItem in scope, so the pool has no membership history and the refusal is the demand log's memory alone), a new
// demand's external attach of that pool is refused with exactly RPoolNotFresh.
run unit_dem_releasedExternalPoolStaysUsed {
  some o: CompleteOcc, a: AttachOcc, e: ExternalContribution | {
    committed[o] and precedes[o.tick, a.tick] and a.subject != o.subject
    e in dPre[o].sContributions
    a.contribution in ExternalContribution and a.contribution.cPool = e.cPool
    refusedAtAdmission[a] and a.admission.because = RPoolNotFresh
  }
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 2 Contribution, 1 Placement, 3 Instant,
      11 Occurrence, 12 Tick, 12 EntityId, 13 Snapshot, 2 Note, 2 Reference expect 1

// The same for the released HOLDING: a new demand's StartProduction on it is refused with exactly RPoolNotFresh.
run unit_dem_releasedHoldingStaysUsed {
  some o: CompleteOcc, sp: StartProductionOcc | {
    committed[o] and precedes[o.tick, sp.tick] and sp.subject != o.subject
    some dPre[o].sHolding and sp.holding = dPre[o].sHolding
    refusedAtAdmission[sp] and sp.admission.because = RPoolNotFresh
  }
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 3 InventoryPool, 2 Contribution, 1 Placement, 3 Instant,
      15 Occurrence, 16 Tick, 14 EntityId, 17 Snapshot, 2 Note, 2 Reference expect 1

// ── DemandTests.CancelPoolNotEmpty ─────────────────────────────────────────────────────────────────────────────────────────
// An OPEN demand whose external contribution's pool holds an item: its Cancel is refused with exactly RPoolNotEmpty
// (QA739 (a); with the pool empty the Cancel commits — unit_dem_cancelWithExternalOnly).
run unit_dem_cancelPoolNotEmptyRefused {
  some cn: CancelOcc, e: ExternalContribution, p: InventoryPool | {
    e in dPre[cn].sContributions and p = resolve[e.cPool] and some heldAt[p, cn.tick]
    refusedAtAdmission[cn] and cn.admission.because = RPoolNotEmpty
  }
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 1 InventoryItem, 1 InventoryPool, 1 Contribution, 0 Placement, 3 Instant,
      9 Occurrence, 10 Tick, 10 EntityId, 11 Snapshot, 2 Note, 2 Reference expect 1
