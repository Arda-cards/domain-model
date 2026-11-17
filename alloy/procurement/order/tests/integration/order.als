module procurement/order/tests/integration/order
// Reflects dafny-domain src/procurement/order/tests/order-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open procurement/order/order_implementation
open procurement/order/order_contracts
open operations/demand/demand_implementation                        // the demand stack for REAL
open reference_data/item/item_implementation
open reference_data/business_affiliate/business_affiliate_implementation
open resources/processing_network/processing_network_implementation
open resources/kanban_card/kanban_card_implementation

// (The SupplierReference CLOSURE fact DIED at DT-023 cut 7b: the handle dissolved into typed
// BA version pins — no orphan-closure obligation exists for typed occurrence references.)

/*
 * INTEGRATION suite for the order module (DT-018/DT-017): the two order logs composed with the
 * REAL demand implementation (chaining + guards + effects) and the real lower stacks. Gate
 * tier: a joint loads witness, the O2 Submit arc down the real ladder (cycle legs stay empty —
 * 0 CardCycle keeps the cone within budget; the demand↔kanban legs are demand's own
 * integration suite), the cancel-returns-to-queue arc, and the two refusals (RDemandHeld,
 * RFrozen) on the composed stack.
 */

// ── joint loads: the composed stack is satisfiable; refs resolve across the layers ──────────────
run int_ord_loads {
  some a: AddLineOcc, d: DemandItem | {
    committed[a]
    resolve[a.demand] = d
    some resolve[a.subject.orderRef] & Order
    demandStatusAt[d, a.tick] = DS_RELEASED
  }
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 1 InventoryPool, 0 Station,
      1 Contribution, 0 Placement, 12 Occurrence, 13 Tick, 13 EntityId, 14 Snapshot, 2 Note, 2 Reference, 2 ContributionId expect 1
      // re-scoped with the TN-004 projection (2026-11-13): a demand is RELEASED only with a live contribution
      // (RNoContribution), and with no card cycle here that is an EXTERNAL one, whose pool must exist (RNoSuchPool).
      // At "0 InventoryPool" and 8 occurrences this finder had no instance (UNSAT in 559 s in the night window of
      // 2026-11-13). The arc now carries the pool's Create, the contribution's attach and their calls.

// ── the O2 Submit arc on the REAL demand log: demand Create → Release (real chaining/effects),
// order AddLine attaches the RELEASED item, demand StartProduction (the saga's first leg — its
// REAL gate holds vacuously with no member cycles), then Submit commits on the C/OP gate. ──────
run int_ord_submitArc {
  some ord: Order, d: DemandItem,
       ki, kb, kp, kd, ko: Call,
       vi: CreateItemOcc, vb: CreateBaOcc, vp: CreatePoolOcc,
       dc: CreateDemandOcc, da: AddContributionOcc, dr: ReleaseOcc, dsp: StartProductionOcc,
       oc: CreateOrderOcc, a: AddLineOcc, s: SubmitOcc | {
    dc.subject = d and da.subject = d and dr.subject = d and dsp.subject = d
    oc.subject = ord and parentOf[a.subject] = ord and s.subject = ord
    committed[vi] and committed[vb] and committed[vp]
    committed[dc] and committed[da] and committed[dr] and committed[dsp]
    committed[oc] and committed[a] and committed[s]
    resolve[a.demand] = d
    // ONE order of the fifteen occurrences: a finder needs one history, not every interleaving of the fixtures
    vi.arche = ki and vb.arche = kb and vp.arche = kp
    (dc + da + dr + dsp).arche = kd and (oc + a + s).arche = ko
    precedes[ki.tick, vi.tick] and precedes[vi.tick, kb.tick] and precedes[kb.tick, vb.tick]
    precedes[vb.tick, kp.tick] and precedes[kp.tick, vp.tick] and precedes[vp.tick, kd.tick]
    precedes[kd.tick, dc.tick] and precedes[dc.tick, da.tick] and precedes[da.tick, dr.tick]
    precedes[dr.tick, ko.tick] and precedes[ko.tick, oc.tick] and precedes[oc.tick, a.tick]
    precedes[a.tick, dsp.tick] and precedes[dsp.tick, s.tick]
    orderStatusAt[ord, s.tick] = OS_SUBMITTED
    demandStatusAt[d, s.tick] = DS_IN_PROCESS
    d in servicedOf[ord, s.tick]
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 1 InventoryPool, 0 Station,
      1 Contribution, 0 Placement, 19 Tick, 17 EntityId, 19 Snapshot, 17 Occurrence, 2 Note, 2 Reference, 2 ContributionId expect 1
      // 17 occurrences: the arc COUNTS 15 on the real stacks, ten rows (the item's version, the vendor's version and the
      // pool's Create; the demand's Create, attach, Release and StartProduction; the order's Create, AddLine and Submit) and
      // one call per service (five). Two are spare.
      // THE ORDER IS PINNED (2026-11-14, a scope and symmetry read): the command names the fifteen and fixes one order of
      // their ticks. A finder needs one history, not every interleaving of the fixtures. Unpinned at this scope it had no
      // verdict in 1,800 s; pinned it is found in 285 s, and at the exact count of 15 in 795 s (measured at 4ee3a08).
      // re-scoped with the TN-004 projection (2026-11-13), as int_ord_loads: +1 pool, +1 contribution, +3 occurrences
      // (the pool's Create, its call, the contribution's attach)
      // census +2 EntityId / +2 Occurrence at DT-023 cut 8 (mirrors unit_ord_buildAndSubmit):
      // Submit requires a LINKED vendor, so the arc carries the BA Create fixture (PDEV-241 re-base)

// ── the cancel arc on the real stack: the hold dies with the order; the item is STILL RELEASED
// on its own (sovereign) log and back in the queue. ─────────────────────────────────────────────
run int_ord_cancelReturnsToQueue {
  some c: CancelOrderOcc, d: DemandItem, l: OrderLine | {
    committed[c]
    parentOf[l] = c.subject
    d in servicedAt[l, c.tick]
    no holdingLineOf[d, c.tick]
    demandStatusAt[d, c.tick] = DS_RELEASED       // demand knew nothing of the order (O3)
  }
} for 9 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 1 InventoryPool, 0 Station,
      1 Contribution, 0 Placement, 12 Occurrence, 14 Tick, 13 EntityId, 14 Snapshot, 2 Note, 2 Reference, 2 ContributionId expect 1
      // re-scoped with the TN-004 projection (2026-11-13), as int_ord_loads

// ── the two refusals on the composed stack ───────────────────────────────────────────────────────
// They replace the two contract checks this root held (`demandIndivisible`, `frozenOutsideDraft`), retired as checks of
// laws the reference model proves (dafny-domain `DemandIndivisible`, `FrozenOutsideDraftOrder`, `FrozenOutsideDraftLine`).
// A finder per refusal shows what a check could not show at its scope: on the REAL demand log and the real lower stacks,
// the guard still fires.

// Extension class 1: finder for OrderTests.AttachRefusals (RDemandHeld): a demand one live line services is refused to a
// second line. The arc is int_ord_loads' (the item's version, the pool, the demand's create and Release, the order, the
// line that takes the demand) plus the second line's genesis and its refused attach.
run int_ord_demandHeldRefused {
  some o: AttachDemandOcc | refusedAtAdmission[o] and o.admission.because = RDemandHeld
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 2 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 1 InventoryPool, 0 Station,
      1 Contribution, 0 Placement, 14 Occurrence, 15 Tick, 15 EntityId, 16 Snapshot, 2 Note, 2 Reference, 2 ContributionId expect 1

// Extension class 1: finder for OrderTests.FreezeRefusals (RFrozen): a line's genesis on an order that left draft is refused.
run int_ord_frozenRefused {
  some o: AddLineOcc | refusedAtAdmission[o] and o.admission.because = RFrozen
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 2 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 Contribution, 0 Placement, 12 Occurrence, 13 Tick, 12 EntityId, 12 Snapshot, 2 Note, 2 Reference, 2 ContributionId expect 1
