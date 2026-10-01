module soak/sliced/demand_soak

/*
 * SOAK tier (DT-022 TQ-5): the demand lattice/provenance laws at GENEROUS scopes — see
 * kanban_soak.als for the tier's rationale. `make soak` only; never on the push path.
 */

open operations/demand/demand_implementation
open operations/demand/demand_contracts
open reference_data/item/item_mock
open resources/processing_network/processing_network_mock
open resources/kanban_card/kanban_card_mock

assert soak_dem_holdingProvenance { holdingProvenance }
check soak_dem_holdingProvenance for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 1 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool,
      11 Occurrence, 14 EntityId, 9 Tick, 11 Snapshot, 2 Note expect 0

// RETIRED (MP signoff 2026-08-27, DT-024 E7 ladder): `soak_dem_holdingExclusive` — the
// law is PROVEN INDUCTIVE in demand_holding_inductive.als (premise-conditioned base +
// step + law, state-local; both scope gates green 2026-08-27: W 1777s+45s, soak-matched
// 453s+49s), superseding this trace search. The provenance row above stays until its
// ladder verdict is formally ruled.

// CREATED-ONLY SLICE (DT-023 Q-D / DT-024, closing pass 7c): reference-data version
// dynamics are proven WIDE in soak/tests/reference_data_dynamics — this root reads
// reference data only through the pin/liveness API, so each subject carries exactly its
// Create and no Update/Delete atoms inflate the census (the lemma-then-slice retune).
fact CreatedOnlySlice {
  ItemOcc in CreateItemOcc
  BaOcc in CreateBaOcc
}
