module operations/demand/tests/unit/delivery_retire

open operations/demand/demand_implementation
open operations/demand/demand_contracts
open reference_data/item/item_mock                            // lower layer as CONTRACT (DT-017)
open resources/processing_network/processing_network_mock    // Station stub as CONTRACT
open resources/kanban_card/kanban_card_mock                   // kanban as CONTRACT (DT-017)
open operations/demand/demand_types as dt                     // DIRECT (rule 10): the parameters below are alias-qualified
open meta/subject_log/lifecycle[dt/ProductionDelivery, dt/PDState] as pdlc   // the SHAPES for the delivery log (the cut's second instance)

/*
 * RED-FIRST witnesses for the production-delivery RETIRE kind (DT-030 M2 — a retire kind is mandatory for every
 * Universe-managed entity; Q24 (a): `RetireDeliveryOcc extends pdlc/RetireOcc`, refusals `RDeliveryClosed` (not started /
 * already retired) and `RNotTerminal` (status still PD_CREATED — the demand's two-step: Revoke first, then Retire).
 * Written and run RED at 1e79b89 BEFORE the sig lands (team-operations.md § Test-driven development; model-changes-sequence.md §9):
 * the root fails to parse on `RetireDeliveryOcc` / `pdlc`. One witness per behaviour and per branch of each pair.
 * Scopes: the demand unit root's delivery commands (1 ProductionDelivery; 11 Tick / 11 EntityId / 10 Snapshot / 10 Occurrence).
 */

// ── the act commits on a REVOKED delivery (terminal) and tombstones it ─────────────────────────
run unit_pdr_retireAfterRevoke {
  some o: RetireDeliveryOcc | committed[o] and pdPre[o].sStatus = PD_REVOKED and o.post = o.pre
} for 8 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      11 Tick, 11 EntityId, 10 Snapshot, 10 Occurrence expect 1

// complement: a committed retire never writes a new record (RetireEffect)
assert unit_pdr_retireIsTombstone { all o: RetireDeliveryOcc | committed[o] implies o.post = o.pre }
check unit_pdr_retireIsTombstone for 8 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      11 Tick, 11 EntityId, 10 Snapshot, 10 Occurrence expect 0

// ── refused while the delivery is still CREATED (not terminal) — the demand's two-step ─────────
run unit_pdr_retireNotTerminalRefused {
  some o: RetireDeliveryOcc | refusedAtAdmission[o] and o.admission.because = RNotTerminal
    and some o.pre and pdPre[o].sStatus = PD_CREATED
} for 8 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      11 Tick, 11 EntityId, 10 Snapshot, 10 Occurrence expect 1

// ── refused on a delivery that never started (no history) — the generic arm, the adopter's atom ─
run unit_pdr_retireNeverCreatedRefused {
  some o: RetireDeliveryOcc | refusedAtAdmission[o] and o.admission.because = RDeliveryClosed and no o.pre
} for 8 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      11 Tick, 11 EntityId, 10 Snapshot, 10 Occurrence expect 1

// ── refused twice: a second retire after a committed one ───────────────────────────────────────
run unit_pdr_retireTwiceRefused {
  some disj r1, r2: RetireDeliveryOcc | committed[r1] and r2.subject = r1.subject and precedes[r1.tick, r2.tick]
    and refusedAtAdmission[r2] and RDeliveryClosed in r2.admission.because
} for 8 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      11 Tick, 11 EntityId, 10 Snapshot, 10 Occurrence expect 1

// ── complement of the pair: a Revoke after a committed retire is refused (the log is closed) ───
run unit_pdr_revokeAfterRetireRefused {
  some r: RetireDeliveryOcc, v: RevokeDeliveryOcc | committed[r] and v.subject = r.subject and precedes[r.tick, v.tick]
    and refusedAtAdmission[v] and RDeliveryClosed in v.admission.because
} for 8 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      11 Tick, 11 EntityId, 10 Snapshot, 10 Occurrence expect 1

// ── the theorem: nothing commits on the delivery's log after a committed retire ────────────────
assert unit_pdr_nothingAfterRetire { pdlc/nothingAfterRetire }
check unit_pdr_nothingAfterRetire for 8 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      11 Tick, 11 EntityId, 10 Snapshot, 10 Occurrence expect 0
