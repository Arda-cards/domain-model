module soak/sliced/kanban_soak

/*
 * SOAK tier (DT-022 TQ-5 ruling; scaling-outlook to-do #5 — built 2026-08-08): the kanban
 * module's pool laws re-checked at GENEROUS scopes, probing past the gate's census-tuned
 * pins (the starved-scope folklore: a tuned check is sound only for its census — soak
 * widens the universe to hunt counterexamples the dev-loop scopes cannot represent).
 * Excluded from every regular tier; run via `make soak` (scheduled/overnight).
 */

open resources/kanban_card/kanban_card_implementation
open resources/kanban_card/kanban_card_contracts

assert soak_cyc_poolProvenance { poolProvenance }
check soak_cyc_poolProvenance for 6 but 5 Int, 3 Scalar, 5 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      4 CardCycle, 3 KanbanCard, 3 InventoryItem, 3 InventoryPool,
      11 Occurrence, 14 EntityId, 9 Tick, 11 Snapshot, 2 Note expect 0

// RETIRED (MP signoff 2026-08-27, DT-024 E7 ladder): `soak_cyc_poolExclusive` — the law
// is PROVEN INDUCTIVE in cycle_pool_inductive.als (base + step + law, state-local; both
// scope gates green 2026-08-27: W 975s+11s, soak-matched 353s+12s), superseding this
// trace search. The provenance row above stays until its ladder verdict is formally ruled.

// CREATED-ONLY SLICE (DT-023 Q-D / DT-024, closing pass 7c): reference-data version
// dynamics are proven WIDE in soak/tests/reference_data_dynamics — this root reads
// reference data only through the pin/liveness API, so each subject carries exactly its
// Create and no Update/Delete atoms inflate the census (the lemma-then-slice retune).
fact CreatedOnlySlice {
  ItemOcc in CreateItemOcc
  BaOcc in CreateBaOcc
}
