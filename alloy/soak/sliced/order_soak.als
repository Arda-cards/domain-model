module soak/sliced/order_soak

/*
 * SOAK tier (DT-022 TQ-5): the order freeze family at GENEROUS scopes — see
 * kanban_soak.als for the tier's rationale. NB the gate's older order checks ride `for 5`
 * DEFAULTS for the abstract parents (EntityId/Tick/Snapshot) — precisely the census this
 * tier exists to widen. `make soak` only; never on the push path.
 */

open procurement/order/order_implementation
open procurement/order/order_contracts
open operations/demand/demand_mock
open reference_data/item/item_mock
open reference_data/business_affiliate/business_affiliate_mock
open resources/processing_network/processing_network_mock
open resources/kanban_card/kanban_card_mock
open reference_data/staff/staff_mock

// RETIRED (MP signoff 2026-08-28, DT-024 E7 ladder window 2): `soak_ord_frozenOutsideDraft`,
// `soak_ord_supplierBindingFrozen`, `soak_ord_headerDetailFrozen` — each law is PROVEN
// INDUCTIVE as a per-occurrence rung (order_frozen_outside_draft_inductive.als,
// order_supplier_binding_inductive.als, order_header_detail_inductive.als: slice-faithful +
// base + step + law, state-local; both scope gates green 2026-08-27), which supersedes the
// trace searches at these scopes.
// RETIRED (MP signoff 2026-09-02, DT-024 E7 ladder window 3): `soak_ord_terminalClosure` — the last
// order soak row, never verified as a trace search (12h + ~17h orphaned without a verdict, twice), is
// PROVEN INDUCTIVE by Rung T (order_terminal_closure_inductive.als: slice-faithful + base + step + law,
// state-local; BOTH supersession gates green in window 3 — _step_w 21 s, _law_w 19 s, _step_s 16 s,
// _law_s 15 s, zero CTIs). Same two-gate standard and same edit shape as the freeze-family retirement.
// Was: `check soak_ord_terminalClosure for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition,
// 1 StateMachine, 0 Guard, 3 Order, 4 OrderLine, 2 DemandItem, … 11 Occurrence, 14 EntityId, 9 Tick,
// 13 Snapshot, 2 Note expect 0`.

// CREATED-ONLY SLICE (DT-023 Q-D / DT-024, closing pass 7c): reference-data version
// dynamics are proven WIDE in soak/tests/reference_data_dynamics — this root reads
// reference data only through the pin/liveness API, so each subject carries exactly its
// Create and no Update/Delete atoms inflate the census (the lemma-then-slice retune).
fact CreatedOnlySlice {
  ItemOcc in CreateItemOcc
  BaOcc in CreateBaOcc
  StaffOcc in CreateStaffOcc
}
