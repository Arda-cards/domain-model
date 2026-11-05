module resources/inventory_item/inventory_item_types

/*
 * INVENTORY ITEM — TYPES (DT-017 four-file architecture: types / contracts / implementation /
 * mock). Everything a consumer may SEE: the identity-only entity, the state record
 * (InventoryItemState), the REIFIED OBSERVABLES (`stateRel`, `liveTicks`) with their read API
 * (`stateAt`/`liveAt` — same signatures as the former occurrence-layer projections), the
 * PUBLIC OPERATION SURFACE (the fifteen Action kinds + Reason taxonomy + per-role read API —
 * MP ruling 2026-07-03: the Action sigs ARE the behavioral contract surface), and the
 * definitional facts that make the data well-formed. The module's LAWS about observable
 * behavior are named predicates in inventory_item_contracts.als; the machinery that realizes
 * them (guards, witnessing, chaining, effects, LOCF bridge) is inventory_item_implementation.als.
 *
 * Absorbs the former inventory_item.als (entity) + item_state.als (record) — strict renames,
 * 2026-07-03. The entity remains IDENTITY ONLY (DT-011): the observables are relations the
 * implementation DERIVES from the committed log; in consumer unit roots they are constrained
 * only by the contract (opening inventory_item_mock.als IS assuming it).
 */

open meta/profiles/domain_log                  // PROFILE (DT-012): log anatomy + group/order premises for the whole cone
open meta/kernel                               // Entity/Scoped, EntityId, resolve, refs
open meta/action/stateful                      // Snapshot (the record's supertype); Tick via the anatomy
open shared/values                             // Quantity (minQuantity, sActual), PhysicalLocator
open meta/keyed_value_algebra/keyed_order      // classify/Sign, lte, isZero (+ keyed_monoid: add, negate)
open reference_data/item/item_types            // Item — the primary classifier (TYPES only; laws by mock/implementation)

// ── module-local value / handle types ──────────────────────────────────────────────
/** LicensePlate — an InventoryItem's handling-unit identity (D9), distinct from `eId`;
    opaque; non-reusable, unique per tenant (we enforce global uniqueness here). Structure
    deferred (proposed topic). */
sig LicensePlate {}
/** SerialNumber — a product-instance individualizer (D10); opaque; unique within (tenant, Item).
    Presence ⇒ the item is "serialized" (all-or-nothing — an operation-level rule). */
sig SerialNumber {}
/** LotNumber — a lot/batch individualizer (D11); opaque; a state carries a SET (commingled
    provenance — not a per-unit discriminator, excluded from the cell key). */
sig LotNumber {}
/** Text — an opaque free-text value (a String); carries the AdjustProperties-editable
    descriptive attributes (notes, colorCode) on the state record. */
sig Text {}
/** Individualizer — generic placeholder for future individualizers (D3); serialNumber and
    lotNumbers are the concrete ones so far. */
sig Individualizer {}

// ── region value sets (the state record's enums) ─────────────────────────────────────────────
/** OperationalState — worthiness for consumption (DERIVED, D14): ENABLED vs DISABLED. */
enum OperationalState { ENABLED, DISABLED }
/** AvailabilityStatus — X.731 availability-status qualifier (DERIVED): DEGRADED. */
enum AvailabilityStatus { DEGRADED }
/** FillState — stock-fill level (D16): SEALED (operator-asserted as-intended), OPEN (working),
    EMPTY (zero; EMPTY ⟺ actual = 0 — a record fact). */
enum FillState { SEALED, OPEN, EMPTY }
/** AdministrativeState — authorization / hold (set by Lock/Unlock): UNLOCKED / LOCKED. */
enum AdministrativeState { UNLOCKED, LOCKED }

// ── the entity: IDENTITY + the reified observables ───────────────────────────────────────────
/** InventoryItem — the identity of a discrete amount of goods under a tenant, classified by an
    Item; its mutable payload lives on `InventoryItemState` records in the occurrence log,
    surfaced here as the derived observables `stateRel`/`liveTicks`. */
sig InventoryItem extends Scoped {
  itemPin:         one ItemOcc,           // → Item VERSION PIN (DT-023 R3; was itemRef: EntityId).
                                          //   Required, immutable (D1/G7). FLOATING reads go
                                          //   entity-wise via `.subject` (current-at-read);
                                          //   the pin records the version at genesis.
  licensePlate:    one LicensePlate,      // handling-unit identity (D9); immutable, globally unique
  serialNumber:    lone SerialNumber,     // D10 individualizer; immutable, persists (even through empty)
  minQuantity:     one Quantity,          // reorder threshold (default zero); not used by Fill
  individualizers: set Individualizer,    // D3 placeholder
  // — REIFIED OBSERVABLES (DT-017): derived by the implementation's bridge facts; constrained
  //   only by the contract in unit roots. Arity watch: stateRel is the module's one arity-3 field.
  stateRel:        Tick -> lone InventoryItemState,   // payload as of each tick (LOCF; tombstone once retired)
  liveTicks:       set Tick                           // the ticks at which the item EXISTS
}

/** isSerialized — the item carries a serial number (D10). */
pred isSerialized[ii: InventoryItem] { some ii.serialNumber }

// ── the read API (same signatures as the former occurrence-layer projections) ────────────────
/** stateAt — LOCF of records: ii's payload as of `t` (its tombstone once retired — check liveAt). */
fun stateAt[ii: InventoryItem, t: Tick]: lone InventoryItemState { ii.stateRel[t] }
/** liveAt — the existence projection: created, and the last touch did not retire it. */
pred liveAt[ii: InventoryItem, t: Tick] { t in ii.liveTicks }

// ── the state record (the mutable payload as a VALUE; DT-006) ─────────────────────────────────
/** InventoryItemState — one moment's mutable payload of an InventoryItem (a value; extensional). */
sig InventoryItemState extends Snapshot {
  sFill:       one  FillState,
  sAdmin:      one  AdministrativeState,
  sActual:     one  Quantity,
  sDegraded:   lone Quantity,
  sLots:       set  LotNumber,
  sLocator:    lone PhysicalLocator,
  sNotes:      lone Text,
  sColorCode:  lone Text,
  sExpiration: lone Int            // D17 placeholder (Int timestamp) — re-base on Instant with DT-001.03
}

// Value semantics: a state IS its fields — no two record atoms carry identical payloads.
fact StateExtensional {
  all disj a, b: InventoryItemState |
    a.sFill != b.sFill or a.sAdmin != b.sAdmin or a.sActual != b.sActual
    or a.sDegraded != b.sDegraded or a.sLots != b.sLots or a.sLocator != b.sLocator
    or a.sNotes != b.sNotes or a.sColorCode != b.sColorCode or a.sExpiration != b.sExpiration
}

// ── intra-snapshot invariants (DEFINITIONAL: what a well-formed state IS — value
//    well-formedness, like `nf[byUnit]` on Quantity; they hold at every tick for free.
//    Operation-level legality is guard-derived in the implementation.) ──────────────────────────
// G1/D12 — the non-negative cone.
fact SConeNonNegative {
  all s: InventoryItemState |
    classify[s.sActual.byUnit] in (ZERO + POSITIVE)
    and (some s.sDegraded implies classify[s.sDegraded.byUnit] in (ZERO + POSITIVE))
}
// D6/D16 — EMPTY ⟺ actual = 0.
fact SFillEmptyConsistency {
  all s: InventoryItemState | s.sFill = EMPTY iff isZero[s.sActual.byUnit]
}
// G3 — EMPTY ⟹ no qualifiers.
fact SEmptyHasNoQualifiers {
  all s: InventoryItemState | isZero[s.sActual.byUnit] implies (no s.sDegraded and no s.sLots)
}
// G4 — degraded (when present): strictly positive and ≤ actual.
fact SDegradedBelowActual {
  all s: InventoryItemState | some s.sDegraded implies
    (not isZero[s.sDegraded.byUnit] and lte[s.sDegraded.byUnit, s.sActual.byUnit])
}

// ── derived properties (the record-level twins of the entity's derived funs) ─────────────────────
/** sAvailableQty — the consumable amount = actual − degraded. */
fun InventoryItemState.sAvailableQty: Unit -> lone Scalar {
  add[this.sActual.byUnit, negate[this.sDegraded.byUnit]]
}
/** sOperationalState — DISABLED iff non-empty yet nothing available; else ENABLED. */
fun InventoryItemState.sOperationalState: one OperationalState {
  (isZero[this.sAvailableQty] and not isZero[this.sActual.byUnit]) => DISABLED else ENABLED
}

// ── definitional structural facts (all identity fields immutable — plain, non-temporal) ─────────
// The classifier is a PIN (typed, never dangles) — no soft dataRefs remain on the identity.
fact InventoryItemRefs { all ii: InventoryItem | no ii.dataRefs }

// Pin tenancy (DT-023): the kernel's isolation reaches only EntityId dataRefs, so the pin's
// in-tenant discipline is stated here — unrepresentable-style, exactly what kernel isolation
// gave the old soft ref.
fact ItemPinTenancy { all ii: InventoryItem | ii.itemPin.subject.tenantId = ii.tenantId }

// D9 / G5 — license plates are unique among items WITH COMMITTED HISTORY, and D10 / G6 — a present serialNumber is unique
// within (tenant, Item) among them: since QA704 Q4 (a) (DT-009 Q27) both are ARMS of the births (`identityViol` in the
// implementation: RLicensePlateTaken, RSerialTaken, on Create and on Split's new sibling) and THEOREMS over started items
// (tests/unit/inventory_item.als unit_occ_lpnUniqueAmongStarted, unit_occ_serialUniqueAmongStarted), as in dafny-domain
// src/resources/inventory-item/inventory-item.dfy. An item atom no birth committed is outside their reach. Non-reusability
// of a plate comes from the log's no-resurrection guard rather than a Retired axis.

// Tight by default — no orphan handle atoms tied to the IMMUTABLE identity. (LotNumber/Text are
// carried by state records/occurrence params, so their no-orphan rules live at the DAG sink,
// inventory_item_implementation.als; Quantity/PhysicalLocator are shared value objects,
// orphan-EXEMPT, D8.)
fact NoOrphanLicensePlate   { all x: LicensePlate   | x in InventoryItem.licensePlate }
fact NoOrphanSerialNumber   { all x: SerialNumber   | x in InventoryItem.serialNumber }
fact NoOrphanIndividualizer { all x: Individualizer | x in InventoryItem.individualizers }

// ═══ THE OPERATION SURFACE (public — MP ruling 2026-07-03, DT-017 L9 revised) ════════════════════
// The Action sigs ARE the behavioral contract surface: the operations exist to be used, so their
// kinds (name + typed bindings + per-role record fields) are TYPES-level from birth — a consumer
// may stage and reason about them. What stays in the implementation is their SEMANTICS (guards,
// witnessing, chaining, effects); per-kind semantic laws are published into the contract on
// demand (the L9 promotion rule applies to LAWS, not to the surface).

// ── Reason taxonomy (the refusal vocabulary — part of the operations' error channel) ─────────────
one sig RNotLive, RAlreadyExists, RLocked, RUnfit, REmpty, RNonPositive, ROverdraw,
        RSerialized, RNotApplicable, RIncompatible, RIncomparable, RInvalidUnit,
        RLicensePlateTaken,   // QA704 Q4 (a), DT-009 Q27: a birth whose plate an item with committed history bears (was the fact LicensePlateUnique)
        RSerialTaken,         // QA704 Q4 (a): a birth whose serial an item of the same (tenant, Item) with history bears (was SerialNumberUniquePerItem)
        RItemPinStale         // QA704 Q4 (a): a Create pinning an item version not current at its tick (was the fact ItemPinCurrency)
        extends Reason {}
// RIncomparable — the amounts are on incomparable unit bases (the partial order is silent): the
//   conservative-refusal convention; distinct from ROverdraw ("provably more than available").
// RInvalidUnit — a tracked Item's operation used a unit outside its UomScheme (DT-009).

// ── the kinds ─────────────────────────────────────────────────────────────────────────────────────
/** IIOcc — an InventoryItem operation occurrence; `target` is the primary subject (pre/post are its
    records). */
abstract sig IIOcc extends StatefulAction { target: one InventoryItem }

sig CreateOcc extends IIOcc { qty: one Quantity, exp: lone Int } { bindings = target + qty }
sig DeleteOcc extends IIOcc {} { bindings = target }
sig WriteOffOcc extends IIOcc {} { bindings = target }
sig ReplenishOcc extends IIOcc { delta: one Quantity, lots: set LotNumber, exp: lone Int }
  { bindings = target + delta + lots }
sig ConsumeOcc extends IIOcc { amount: one Quantity } { bindings = target + amount }
sig AdjustQuantityOcc extends IIOcc { good: one Quantity, degObs: lone Quantity }
  { bindings = target + good + degObs }
sig InspectOcc extends IIOcc { degObs: lone Quantity } { bindings = target + degObs }
sig RePackOcc extends IIOcc { gNew: lone Quantity, dNew: lone Quantity }
  { bindings = target + gNew + dNew }
sig MoveOcc extends IIOcc { dest: one PhysicalLocator } { bindings = target + dest }
sig LockOcc extends IIOcc {} { bindings = target }
sig UnlockOcc extends IIOcc {} { bindings = target }
sig SealOcc extends IIOcc {} { bindings = target }
sig UnsealOcc extends IIOcc {} { bindings = target }
sig SplitOcc extends IIOcc {
  nu: one InventoryItem, soGood: lone Quantity, soDeg: lone Quantity,
  nuPost: lone InventoryItemState                 // the new item's born record — present iff committed
} { bindings = target + nu + soGood + soDeg and nu != target }
sig MergeOcc extends IIOcc {
  absorbed: one InventoryItem,
  absPre: lone InventoryItemState                 // the absorbed's READ state (its tombstone if committed)
} { bindings = target + absorbed and absorbed != target }

fact NuPostIffCommitted { all o: SplitOcc | some o.nuPost iff committed[o] }

// ── touched items and their per-role records (read API over the kinds) ───────────────────────────
fun touches[o: IIOcc]: set InventoryItem { o.target + (o & SplitOcc).nu + (o & MergeOcc).absorbed }

/** retiringFor — o (if committed) ends ii's existence interval. */
pred retiringFor[o: IIOcc, ii: InventoryItem] {
  (o in DeleteOcc + WriteOffOcc and ii = o.target) or (o in MergeOcc and ii = (o & MergeOcc).absorbed)
}

/** postFor — the record o produced FOR ii (tombstone = the read state, for retired roles). */
fun postFor[o: IIOcc, ii: InventoryItem]: lone InventoryItemState {
  (ii = o.target) => o.post
  else (ii = (o & SplitOcc).nu) => (o & SplitOcc).nuPost
  else (ii = (o & MergeOcc).absorbed) => (o & MergeOcc).absPre
  else none
}
/** preFor — the record o read FOR ii (none for Split's `nu` — a fresh subject has no prior state). */
fun preFor[o: IIOcc, ii: InventoryItem]: lone InventoryItemState {
  (ii = o.target) => o.pre
  else (ii = (o & MergeOcc).absorbed) => (o & MergeOcc).absPre
  else none
}

/** schemeOf — the target's UomScheme, when its classifier is a TRACKED Item (the pin never
    dangles — DT-023; identity-carried `uom` makes the read version-independent). */
fun schemeOf[ii: InventoryItem]: lone UomScheme { ii.itemPin.subject.uom }

/** unitsOk — the amount's units are all configured in the target's scheme (vacuously true when the
    target is untracked or its classifier dangles) — DT-009's valid-UoM rule. */
pred unitsOk[m: Unit -> lone Scalar, ii: InventoryItem] {
  let sch = schemeOf[ii] | some sch implies m.univ in sch.units
}
