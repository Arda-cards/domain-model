module resources/inventory_item/tests/integration/inventory_item

open resources/inventory_item/inventory_item_implementation
open resources/inventory_item/inventory_item_types  // DIRECT (rule 10): `inventory_item_types/CreateOcc` — the module's own kind, disambiguated from the lifecycle family's `lc/CreateOcc` now in the transitive namespace (Tier B 793cfe0 parse red, 2026-09-09)
open resources/inventory_item/inventory_item_contracts
open reference_data/item/item_implementation       // the LOWER LAYER for real (DT-017 two-layer PoC)

/*
 * INTEGRATION suite for the InventoryItem module (DT-017): the real II log composed with the
 * REAL item stack (supplies, supplier chain, UoM laws as implementation facts, not assumptions).
 * This is the gate/soak tier — the unit tier (tests/unit/) runs the same implementation against
 * item's MOCK for the dev loop. Kept deliberately small: a joint loads witness (the composed
 * universe is satisfiable), a cross-layer resolution witness through the supplier chain, and a
 * re-discharge of two contract laws on the composed stack.
 */

// ── joint loads (guard-rail: the composed stack is satisfiable, no vacuity) ──────────────────────
// A committed Create on an item whose classifier resolves to a TRACKED Item under the full real
// item laws — the composition actually loads.
run int_ii_loads {
  some o: inventory_item_types/CreateOcc | committed[o]
    and some o.target.itemPin.subject.uom
    and liveAt[o.target, o.tick]
} for 5 but 3 Scalar, 5 Int expect 1

// ── cross-layer composition: the deep supplier chain resolves in one universe with a live log ───
run int_ii_supplyChainLoads {
  some ii: InventoryItem, i: Item, s: ItemSupply, t: Tick | {
    ii.itemPin.subject = i
    // the default supply is VERSION-CARRIED since DT-023 cut 7a: read it off the item's state
    resolve[itemStateAt[i, t].sDefaultSupply] = s
    some s.supplierPin   // the vendor VERSION pin (DT-023 cut 7b — was resolve[s.supplier.vendorRef])
    some o: inventory_item_types/CreateOcc | committed[o] and o.target = ii
  }
} for 6 but 3 Scalar, 5 Int, 11 EntityId, 8 Tick, 8 Snapshot, 8 Occurrence expect 1

// ── contract re-discharge on the composed stack (UNSAT = holds with the real lower layer) ───────
assert int_ii_contract_stateFunction { stateIsFunctionOnceStarted }
check int_ii_contract_stateFunction for 5 but 3 Scalar, 5 Int expect 0

assert int_ii_contract_closureIsTerminal { closureIsTerminal }
check int_ii_contract_closureIsTerminal for 5 but 3 Scalar, 5 Int expect 0
