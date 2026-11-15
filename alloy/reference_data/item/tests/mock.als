module reference_data/item/tests/mock
// Reflects dafny-domain src/reference-data/item/item-contract.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/kernel
open reference_data/item/item_mock                 // the item's contract AS ASSUMED by a consumer (DT-017); no implementation

/*
 * What a CONSUMER of the item may read. A root that opens the mock knows only `guarantees`: the mock has no effect fact
 * tying a committed write's payload to its record (`ItemEffects` is the implementation's), so a law the contract states
 * over payloads only says nothing of the records a consumer reads (MPBOT-399). The reference model states supplier-pin
 * soundness over both (`SupplierPinsSound` over `RowSupplies`: the payload and the state a committed row produced,
 * dafny-domain src/reference-data/item/item-contract.dfy).
 */

// Control: the mock admits a committed occurrence whose RECORD carries a supply row (so the finder below is not vacuous).
run unit_itemMock_recordCarriesSupply {
  some o: ItemOcc | committed[o] and some o.post.sSupplies
} for 6 but 2 RoleDetail, 4 Tick, 3 Snapshot, 3 Occurrence expect 1

// A committed occurrence whose RECORD holds a supply row with a pin and no vendor role selector: supplier-pin soundness
// (together or not at all) is broken in what a consumer reads. RED on the contract that ranges over payloads only.
run unit_itemMock_recordPinUnsound {
  some o: ItemOcc, s: ItemSupply | committed[o] and s in o.post.sSupplies and some s.supplierPin and no s.supplierRole
} for 6 but 2 RoleDetail, 4 Tick, 3 Snapshot, 3 Occurrence expect 0
