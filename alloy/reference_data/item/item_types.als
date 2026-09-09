module reference_data/item/item_types

// LOG-CARRIED since DT-023 cut 7a (MP ruling 2026-08-10; supersedes the QUASI-STATIC scope
// ruling of 2026-07-08): the Item rides the subject_log spine with the SIMPLE reference-data
// lifecycle — Create -> Live, Update -> Live, Delete -> Retired (terminal). WHY the log form:
// it resolves the standing reference irregularities — references become VERSION PINS
// (occurrence references into this log): the former `ItemDescriptorPin` device DISSOLVES into
// a pin, frozen holders (order line descriptor, receiving expected item) pin at their freeze,
// floating references read the current version at read time. The §7.1 "implementation MUST
// provide pinning" obligation is discharged BY CONSTRUCTION (runtime pin coordinate:
// (entityId, rId) — recorded-axis-exact).

/*
 * ITEM — TYPES (DT-017 four-file architecture: types / contracts / implementation / mock).
 * The naked signatures, the state record, the operation kinds, the Reason taxonomy, and the
 * read API of the item module: what any consumer may see. Laws are named predicates in
 * `item_contracts.als`; machinery in `item_implementation.als`; consumers' unit roots open
 * `item_mock.als`.
 *
 * IDENTITY vs STATE (DT-011: entity = identity + immutable structure; log = mutable state):
 * `uom` stays IDENTITY — the tracking mode never changes (DT-009: no mode change), so
 * consumers' `schemeOf`-style reads are version-independent. Supplies, the default supply,
 * and the card-issuance default are VERSIONED state (`ItemState`), folded per DT-023 Q-C:
 * a supply change IS an item version.
 *
 * The UoM vocabulary stays in uom.als as an INTERNAL VOCABULARY file opened here — so the
 * arity-4 collapse root can depend on it without paying this file's full cone (DT-017).
 */

open meta/profiles/domain_log        // PROFILE (DT-012): log anatomy + group/order premises
open meta/kernel                     // Scoped, EntityId, resolve
open meta/subject_log/subject_log[Item, ItemState] as ilog   // the log SPINE (DT-015 Q5)
open meta/subject_log/lifecycle[Item, ItemState] as lc   // the SHAPES: Create / Mutate / Retire (DT-030, 2026-09-09)
open reference_data/shared/lifecycle // RRetiredRef (DT-023)
open shared/values                   // Quantity, Money, Unit
open reference_data/item/uom         // UomScheme, Each, toEach, units (internal vocabulary, DT-009)
open reference_data/business_affiliate/business_affiliate_types   // BaOcc + BusinessRole — the supply rows' vendor PIN + role selector (DT-023 cut 7b)

// ── supply sources ───────────────────────────────────────────────────────────────────────────────
/** OrderMethod — how an item is ordered from a supplier. */
enum OrderMethod {
  UNKNOWN, PURCHASE_ORDER, EMAIL, PHONE, IN_STORE, ONLINE, RFQ, PRODUCTION, TASK, THIRD_PARTY, OTHER
}

/** ItemSupply — a supply source for an Item (vendor, order method, cost, lead time); a child
    entity FOLDED into the item's versioned state (DT-023 Q-C): rows are IMMUTABLE — changing
    a supply is replacing its row in the next ItemState — and membership is version-carried
    (`ItemState.sSupplies`). Keeps its own eId (the default-supply target). */
sig ItemSupply extends Scoped {
  supplierPin:     lone BaOcc,          // → BusinessAffiliate VERSION PIN (DT-023 cut 7b; was
                                        //   the denormalized SupplierReference handle) — absent
                                        //   = an unlinked supply row
  supplierRole:    lone BusinessRole,   // the VENDOR role selector within the pinned version
  orderMethod:     lone OrderMethod,
  orderQuantity:   lone Quantity,
  unitCost:        lone Money,
  averageLeadTime: lone Duration
}

// ── the entity: IDENTITY + immutable structure only (log-carried, DT-011) ───────────────────────
/** Item — reference-data master for a material/product (the TYPE); InventoryItems and supply
    records classify against it. Tenant-scoped. Identity carries only the immutable tracking
    mode; everything else rides the log (ItemState records + occurrences). */
sig Item extends Scoped {
  uom: lone UomScheme   // present ⟺ inventory-TRACKED (DT-009); immutable (no mode change)
}
fact ItemRefs { all i: Item | no i.dataRefs }
// The supply's vendor is a typed PIN since cut 7b — no soft EntityId refs remain.
fact ItemSupplyRefs { all s: ItemSupply | no s.dataRefs }

/** inventoryTracked — an Item is inventory-tracked iff it carries a UoM scheme (DT-009). */
pred inventoryTracked[i: Item] { some i.uom }

// (`itemCarriedSupplierRefs` — the SupplierReference closure export — DIED at cut 7b with the
// handle itself: pins are typed occurrence references, no orphan-closure obligation exists.)

// ── the state record ────────────────────────────────────────────────────────────────────────────
/** ItemState — one moment's versioned payload of an Item (a value; extensional): the folded
    supply content. The lifecycle (Live / Retired) is the LOG's shape since 2026-09-09 — live
    while the head is not a Retire — not a field. */
sig ItemState extends Snapshot {
  sSupplies:            set  ItemSupply,  // the folded children (Q-C)
  sDefaultSupply:       lone EntityId,    // soft ref → one of sSupplies
  sCardMinimumQuantity: lone Quantity     // card-issuance default (DT-022 TQ-4): pre-fills a
                                          //   new card's printed minimum, operator-overridable
                                          //   at mint; NO law reads it
}
// Value semantics: a state IS its fields.
fact ItemStateExtensional {
  all disj a, b: ItemState |
    a.sSupplies != b.sSupplies
    or a.sDefaultSupply != b.sDefaultSupply or a.sCardMinimumQuantity != b.sCardMinimumQuantity
}
// Record-carried refs are TYPED (soft; tenancy/containment are law-side — item_contracts C1).
fact ItemStateRefIntegrity {
  all s: ItemState | let d = resolve[s.sDefaultSupply] | some d implies d in ItemSupply
}

// ── the kinds — the reference-data lifecycle (DT-023 R1) ────────────────────────────────────────
/** ItemOcc — the item log's occurrence family; the PIN TYPE (DT-023 R3): a version pin is a
    reference to one of these atoms (the version it created). A SUBSET sig equal to the whole
    log: the kinds sit under the lifecycle SHAPES, so the family cannot be their `extends` parent. */
sig ItemOcc in ilog/SubjectOcc {}
fact ItemOccIsTheLog { ItemOcc = ilog/SubjectOcc }

/** ItemWriteOcc — the content-carrying kinds' shared payload (SET semantics — the
    UpdateOrderDetails precedent): the full versioned content each write states. A SUBSET sig
    carrying the fields (Create is a Create shape, Update a Mutate shape — one field each, no
    overload; the throwaway of 2026-09-09). */
sig ItemWriteOcc in ilog/SubjectOcc {
  supplies:            set  ItemSupply,
  defaultSupply:       lone EntityId,
  cardMinimumQuantity: lone Quantity
}
fact ItemWriteOccExtent {
  ItemWriteOcc = CreateItemOcc + UpdateItemOcc
  all o: ItemWriteOcc | o.bindings = o.subject + o.supplies + o.defaultSupply + o.cardMinimumQuantity
}

/** Create — births the Item with its initial content (live: the head is not a retire). */
sig CreateItemOcc extends lc/CreateOcc {}
/** Update — SETs the versioned content. */
sig UpdateItemOcc extends lc/MutateOcc {}
/** Retire — ends the Item's history (the tombstone; terminal; content carried forward). Was DeleteItemOcc; MP's word 2026-09-09. */
sig RetireItemOcc extends lc/RetireOcc {} { bindings = subject }

// ── the Reason taxonomy (module-sovereign atoms; RRetiredRef is shared via lifecycle) ───────────
one sig RItemExists, RItemNotCreated, RItemRetired extends Reason {}

// ── the read API ────────────────────────────────────────────────────────────────────────────────
/** itemStateAt — the item's versioned content as of `t` (LOCF; none before Create). */
fun itemStateAt[i: Item, t: Tick]: lone ItemState { ilog/recordAt[i, t] }
/** itemVersionAt — the item's CURRENT VERSION at `t`: the occurrence a new pin must
    reference (DT-023 Q-A "compatible and current"). */
fun itemVersionAt[i: Item, t: Tick]: lone ItemOcc { ilog/lastTouch[i, t] & ItemOcc }
/** itemLiveAt — the item exists and is Live at `t` (the reference-target guard read). */
pred itemLiveAt[i: Item, t: Tick] { lc/liveSubjectAt[i, t] }
/** pinsCurrentItem — `p` is the current version of its own item at `t` (pin currency). */
pred pinsCurrentItem[p: ItemOcc, t: Tick] { p = itemVersionAt[p.subject, t] }
/** itemPinnableAt — the D2 guard in one read: `p` is current at `t` AND its version is
    Live — the version a committed introducing occurrence may pin; anything else refuses
    with `RRetiredRef` (retired-current) or is unrepresentable (stale pin). */
pred itemPinnableAt[p: ItemOcc, t: Tick] { pinsCurrentItem[p, t] and p not in lc/RetireOcc }
