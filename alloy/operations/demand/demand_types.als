module operations/demand/demand_types

/*
 * DEMAND — TYPES (DT-016; DT-017 four-file architecture). The DemandItem is the
 * collection-and-collation shim between card-granularity demand signals and aggregate
 * production (DT-014 rung 2): an "Intent to Produce" a quantity of an Item at its
 * Production/Source Station. IDENTITY derives from (Item, Source Station) — but that pair is
 * NOT unique (R1 amended 2026-07-06: multiple DemandItems per pair coexist in different
 * states; whether multiple OPEN ones are allowed is CALLER POLICY, not a module law — the
 * collation decision belongs to whoever invokes CreateWithContribution/AddContribution). First module of
 * the operations/ domain.
 *
 * CONTRIBUTIONS (TN-004, 2026-11-05; reflects dafny-domain MD-076 to MD-080): a demand's composition is its set of
 * CONTRIBUTIONS — a card contribution names a card cycle, an external contribution carries its own reference, quantity
 * and pool. The stored, advisory intent (`sDemandQty`) and the membership (`sMembership`) are gone: the quantity is a
 * READ (the keyed sum of the live contributions, confined to demand_quantity.als) and the membership is DERIVED
 * (`attachedAt`: the cycles the card contributions name), so the order and the receiver read what they read before.
 *
 * PUBLIC OPERATION SURFACE (DT-017 L9): the kinds, the Reason taxonomy, and the read API
 * live here. Laws are named predicates in demand_contracts.als; machinery + pairing
 * enforcement in demand_implementation.als; consumers' unit roots open demand_mock.als.
 *
 * NAMING (Occ ruling (c) + flat-namespace survey): model sigs carry the `Occ` register marker;
 * product surfaces use the bare verb. Three kinds take collision-free model names —
 * `CreateDemandOcc`/`DeleteDemandOcc` (inventory_item owns CreateOcc/DeleteOcc in this cone) and
 * `StartProductionOcc` (the cycle log owns StartProcessingOcc; the name also carries the R8
 * Produce/Fulfill vocabulary). Statuses carry the DS_ prefix (the print machine's PS_ precedent —
 * the cycle log owns bare IN_PROCESS etc.).
 *
 * SEAM (R3, narrowed 2026-07-08): this module opens kanban_card_TYPES only (the four-file cut
 * landed); unit roots take the kanban MOCK, integration roots the real implementation.
 * inventory_pool rides that cone.
 */

open meta/profiles/timed_log                         // PROFILE (DT-012): P2 — log anatomy + group/order premises + the domain-time stamp (COORDINATOR-Q527: CompleteOcc is stamped)
open meta/kernel                                     // Scoped, EntityId, resolve
open meta/subject_log/subject_log[DemandItem, DemandState] as dlog   // the log SPINE (DT-015 Q5)
open meta/subject_log/lifecycle[DemandItem, DemandState] as lc     // the SHAPES: Create / Mutate / Retire (DT-030, 2026-09-09)
open meta/subject_log/subject_log[ProductionDelivery, PDState] as pdlog  // the SECOND subject (§8.1.2, DT-020 build cut 3)
open meta/subject_log/lifecycle[ProductionDelivery, PDState] as pdlc    // the SHAPES for the delivery log (DT-030 M2; cut 2, 2026-09-10)
open shared/values                                   // Quantity
open shared/note                                     // Note — the demand's and the contribution's notes (TN-004)
open shared/reference                                // Reference — external references and the work order (TN-004)
open reference_data/item/item_types                  // Item (collation-key target; TYPES only)
open resources/processing_network/processing_network_types   // Station (collation-key target; TYPES only)
open resources/kanban_card/kanban_card_types          // CardCycle + the cycle log surface + KanbanCard (TYPES — DT-017; the kanban four-file cut retired the INTERIM direct open, 2026-07-08)
open shared/backdating                               // RBackdated — the back-dating refusal family (COORDINATOR-Q527); this module's member is RBackdatedHolding

// ── the status vocabulary ───────────────────────────────────────────────────────────────────────
/** DemandStatus — the DemandItem lifecycle states (R5: MVP2 five states, plain enum; DS_ prefix
    = namespace mechanics, the product vocabulary is OPEN/RELEASED/IN_PROCESS/COMPLETE/CANCELED). */
abstract sig DemandStatus {}
one sig DS_OPEN, DS_RELEASED, DS_IN_PROCESS, DS_COMPLETE, DS_CANCELED extends DemandStatus {}

/** liveStatuses — the demand item is LIVE in these (R5); COMPLETE/CANCELED are terminal closure. */
fun liveStatuses: set DemandStatus { DS_OPEN + DS_RELEASED + DS_IN_PROCESS }

// ── the entity: IDENTITY ONLY (log-carried, DT-011) ─────────────────────────────────────────────
/** DemandItem — the production task: one collated "Intent to Produce" an Item at its
    Production/Source Station. Identity only; everything else rides the log (DemandState
    records + occurrences). */
sig DemandItem extends Scoped {
  itemPin:    one ItemOcc,    // → Item VERSION PIN (DT-023 R3; was itemRef): WHAT is produced
                              //   (immutable identity-structure); entity-wise reads via `.subject`
  stationRef: one EntityId    // → Station: the PRODUCTION/SOURCE station (never a destination)
}
fact DemandItemRefs { all d: DemandItem | d.dataRefs = d.stationRef }   // kernel isolation covers it
// Pin tenancy (DT-023): kernel isolation reaches only EntityId dataRefs — stated here instead.
fact DemandItemPinTenancy { all d: DemandItem | d.itemPin.subject.tenantId = d.tenantId }
fact DemandItemRefIntegrity {
  all d: DemandItem | let st = resolve[d.stationRef] | some st implies st in Station
}

// A REFERENCE as a contribution carries or reads it is `CardSerial + Reference`: a free `Reference`, or the text of some
// card's serial (a `CardSerial`). ONE space, so a card's default reference (its serial) and an external reference can be
// compared. Written out at each use: a field's bound comes from its declared type.

/** Contribution — one source of a demand's quantity (TN-004): a VALUE that carries its own id (`cid`, caller-minted at the
    attach and used once per demand) and an optional note. A state holds a set of them, at most one per id — the Alloy
    spelling of dafny-domain's `map<ContributionId, DemandContribution>` (MD-076). */
abstract sig Contribution {
  cid:        one  EntityId,   // the contribution's id: the key within its demand
  cUserNotes: lone Note        // the caller's note on this contribution
}
/** CardContribution — the contribution of a kanban card cycle: its quantity is the cycle's effective quantity, its reference
    the override given here or, by default, the card's serial (a READ — `referenceOf`; MD-077). */
sig CardContribution extends Contribution {
  cycleRef:          one  EntityId,   // → CardCycle (soft ref; `cycle` is the kanban log's alias fun in this cone)
  referenceOverride: lone (CardSerial + Reference)    // the caller's reference; absent ⇒ the card's serial is read
}
/** ExternalContribution — a contribution with no card: its own reference, its own quantity, and its own pool, which it
    holds exclusively while the demand is live. */
sig ExternalContribution extends Contribution {
  externalReference: one (CardSerial + Reference),    // the caller's reference: unique among the demand's contributions
  quantity:          one Quantity,    // the contributed quantity
  cPool:             one EntityId     // → InventoryPool: the contribution's own pool (fresh at the attach)
}
// Value semantics: a contribution IS its fields.
fact ContributionExtensional {
  all disj a, b: CardContribution |
    a.cid != b.cid or a.cUserNotes != b.cUserNotes or a.cycleRef != b.cycleRef or a.referenceOverride != b.referenceOverride
  all disj a, b: ExternalContribution |
    a.cid != b.cid or a.cUserNotes != b.cUserNotes or a.externalReference != b.externalReference
    or a.quantity != b.quantity or a.cPool != b.cPool
}

// ── the state record ────────────────────────────────────────────────────────────────────────────
/** DemandState — one moment's mutable payload of a DemandItem (a value; extensional). */
sig DemandState extends Snapshot {
  sStatus:           one  DemandStatus,   // where the task stands (R5)
  sContributions:    set  Contribution,   // the composition (TN-004): at most one contribution per id; may retain a
                                          //   card contribution whose cycle was withdrawn, until its DetachWithdrawn (R7)
  sHolding:          lone EntityId,       // → InventoryPool (R8): production deliveries accumulate here
  sUserNotes:        lone Note,           // the caller's notes on the demand: writable until the tombstone
  sWorkOrder:        lone Reference,      // the work-order number: an OPEN-only field
  sFulfillmentNotes: lone Note            // the fulfillment notes: writable while OPEN or RELEASED
}

// Value semantics: a state IS its fields.
fact DemandStateExtensional {
  all disj a, b: DemandState |
    a.sStatus != b.sStatus or a.sContributions != b.sContributions or a.sHolding != b.sHolding
    or a.sUserNotes != b.sUserNotes or a.sWorkOrder != b.sWorkOrder or a.sFulfillmentNotes != b.sFulfillmentNotes
}
// The contributions of a state are keyed by their id (the map's key).
fact ContributionsKeyedById { all s: DemandState | all disj a, b: s.sContributions | a.cid != b.cid }
// A contribution value exists only where something carries it: a state, or an attach (a refused one included).
fact NoOrphanContribution { all c: Contribution | c in DemandState.sContributions + AttachOcc.contribution }

// Record-carried refs are TYPED (soft — dangling/cross-Universe allowed; tenancy is guard-side).
fact DemandRefIntegrity {
  all s: DemandState | (let h = resolve[s.sHolding] | some h implies h in InventoryPool)
  all c: CardContribution     | let k = resolve[c.cycleRef] | some k implies k in CardCycle
  all c: ExternalContribution | let p = resolve[c.cPool] | some p implies p in InventoryPool
}

// ── the SECOND subject: ProductionDelivery (§8.1.2, DT-020 build cut 3) ─────────────────────────
/** ProductionDelivery — the materialized record of ONE production-process output contributing
    inventory to a DemandItem (DT-020 §8.1/§8.1.1, re-homed HERE §8.1.2 as the module's second
    subject: the intersection reified PROCESS-GENERICALLY — receiving is one producing process;
    manufacturing runs, kitting, transfers reuse this surface). Decomposes the process↔demand
    m:n into two functional legs (1:N source→PDs, M:1 PDs→demand). Identity + immutable
    structure only: the one MANDATORY target leg, the contributed quantity (immutable at Create
    — corrections are Revoke + recreate, reversing-entry semantics §8.1.1), and the OPAQUE
    source handle (§8.1.3: reconciliation-only — NO LAW reads it; the typed, law-bearing
    provenance is process-owned, the producing process's `sDeliveries`). */
sig ProductionDelivery extends Scoped {
  demandRef:    one  EntityId,        // → DemandItem — the one MANDATORY leg (same module)
  quantity:     one  Quantity,        // contributed; immutable at Create
  sourceHandle: lone PDSourceHandle   // opaque reconciliation metadata (the R7 rId-stamping precedent)
}
/** PDSourceHandle — the §8.1.3 reconciliation handle: idempotency plumbing for the producing
    process's append; opaque, nominal, never resolved or interpreted by any law. */
sig PDSourceHandle {}
fact PDRefs { all pd: ProductionDelivery | pd.dataRefs = pd.demandRef }   // kernel isolation covers it
fact PDRefIntegrity {
  all pd: ProductionDelivery | let d = resolve[pd.demandRef] | some d implies d in DemandItem
}
fact NoOrphanPDSourceHandle { all h: PDSourceHandle | h in ProductionDelivery.sourceHandle }

/** PDStatus — Create-immutable then terminal Revoke (§8.1.1): a REVOKED delivery contributes
    NOTHING and stays forever (audit preserved — reversing-entry semantics). */
abstract sig PDStatus {}
one sig PD_CREATED, PD_REVOKED extends PDStatus {}
/** PDState — one moment's status of a delivery (a value; extensional). */
sig PDState extends Snapshot { sStatus: one PDStatus }
fact PDStateExtensional { all disj a, b: PDState | a.sStatus != b.sStatus }

// ── the kinds (product-register names in comments) ─────────────────────────────────────────────
/** Create — start a demand task with no contribution yet (births the DemandItem OPEN; TN-004: the quantity is read from the
    contributions, so the genesis carries none). */
sig CreateDemandOcc extends lc/CreateOcc {} { bindings = subject }   // item/station ride the ENTITY (immutable structure), not the payload
/** AttachOcc — the two kinds that attach a contribution share the field, `contribution` declared ONCE so union quantifiers
    over them stay unambiguous. A SUBSET sig: CreateWithContribution is a Create shape and AddContribution a Mutate shape, so no
    `extends` parent can hold both (the MemberOcc precedent of 2026-09-09). */
sig AttachOcc in dlog/SubjectOcc { contribution: one Contribution }
/** TargetOcc — the kinds that name an EXISTING contribution by its id share the field `target` (the same device). */
sig TargetOcc in dlog/SubjectOcc { target: one EntityId }
/** NotesOcc — the three kinds that write a note share the field `notes`; none given CLEARS the note (the same device). */
sig NotesOcc in dlog/SubjectOcc { notes: lone Note }
fact ContributionOccExtents {
  AttachOcc = CreateWithContributionOcc + AddContributionOcc
  TargetOcc = RemoveContributionOcc + EditContributionOcc + SetContributionNotesOcc + DetachWithdrawnOcc
  NotesOcc  = SetUserNotesOcc + SetFulfillmentNotesOcc + SetContributionNotesOcc
  all o: AttachOcc | o.bindings = o.subject + o.contribution
  all o: RemoveContributionOcc + DetachWithdrawnOcc | o.bindings = o.subject + o.target
  all o: EditContributionOcc | o.bindings = o.subject + o.target + o.newQuantity + o.newReference
  all o: SetContributionNotesOcc | o.bindings = o.subject + o.target + o.notes
  all o: SetUserNotesOcc + SetFulfillmentNotesOcc | o.bindings = o.subject + o.notes
}
/** CreateWithContribution — start a task from its first contribution (births + attaches). For a card contribution this is
    C/OP call-first: the caller invokes the cycle's Accept FIRST, and this commit is the saga's gate. */
sig CreateWithContributionOcc extends lc/CreateOcc {}
/** AddContribution — attach a further contribution, under the freeze (a card: C/OP call-first, after the cycle's Accept; an
    external one: its pool must be live, in tenant, of the demand's item, and fresh). */
sig AddContributionOcc extends lc/MutateOcc {}
/** RemoveContribution — detach a contribution, under the freeze (a card: C/OP call-first, after the cycle's Shelve; an
    external one: only while its pool is empty). */
sig RemoveContributionOcc extends lc/MutateOcc {}
/** EditContribution — set a contribution's fields, under the freeze: the quantity (an external contribution only) and the
    reference (an external one's own, a card one's override). A field not given is left as it is. */
sig EditContributionOcc extends lc/MutateOcc { newQuantity: lone Quantity, newReference: lone (CardSerial + Reference) }
/** SetContributionNotes — write a contribution's note; NOT under the freeze, admitted until the demand's tombstone. */
sig SetContributionNotesOcc extends lc/MutateOcc {}
/** SetUserNotes — write the demand's user notes; admitted in every status, until the tombstone. */
sig SetUserNotesOcc extends lc/MutateOcc {}
/** SetWorkOrder — write the work-order number; OPEN only. None given clears it. */
sig SetWorkOrderOcc extends lc/MutateOcc { workOrder: lone Reference } { bindings = subject + workOrder }
/** SetFulfillmentNotes — write the fulfillment notes; while OPEN or RELEASED. */
sig SetFulfillmentNotesOcc extends lc/MutateOcc {}
/** DetachWithdrawn — reconcile a card contribution whose cycle was withdrawn (R7: the system reaction to the
    cycle-withdrawal notification — CONVERGENT/NOTIFICATION; the same kind is the manual repair). Names the contribution's id. */
sig DetachWithdrawnOcc extends lc/MutateOcc {}
/** Release — hand to the station; the freeze instant (R5). */
sig ReleaseOcc extends lc/MutateOcc {} { bindings = subject }
/** Reopen — take back a release (R5, PDEV-215; members are still REQUESTED — R8). */
sig ReopenOcc extends lc/MutateOcc {} { bindings = subject }
/** StartProduction — begin the production run (R8): DS_RELEASED → DS_IN_PROCESS, attaches the
    holding pool. C/OP call-first: the caller moves each live member cycle → IN_PROCESS (cycle
    StartProcessing) first; this commit GATES on all of them being there. */
sig StartProductionOcc extends lc/MutateOcc { holding: lone EntityId } { bindings = subject + holding }
/** RecordProduction — record a production delivery (⟲, R8; §8.1.2 re-based): `delivery` now
    references the ProductionDelivery ENTITY (the reified contribution — was the transient
    delivery pool pre-§8.1.2); the delivery pool's merge into the holding pool stays pool-log/
    runtime territory. Committed ONLY as the demand-side half of the ATOMIC Create composition
    (compose-don't-subsume — CreateComposesWithRecord in the implementation): the listener
    chain (ProductionRecorded → the order's receiptAccrues) rides THIS kind, untouched. */
sig RecordProductionOcc extends lc/MutateOcc { delivery: lone EntityId } { bindings = subject + delivery }
/** ExtractProduction — the demand-side extraction pairing Revoke (⟲, §8.1.2): reverses the
    recorded contribution on the target's log (the fulfillment fold ignores REVOKED deliveries;
    the holding pool's content movement is runtime, watched by the I3-family probe). Committed
    ONLY as the demand-side half of the ATOMIC Revoke composition. The listener chain
    (ProductionRevoked → the order's receiptReverses COMPENSATING posting) rides THIS kind
    (cut 9, MP 2026-08-14 — the received quantity is financially binding). */
sig ExtractProductionOcc extends lc/MutateOcc { delivery: lone EntityId } { bindings = subject + delivery }
/** Distribute — allocate accumulated production (⟲, R8): a DATA-DRIVEN distribution matrix
    (per-contribution quantities, keyed by the contribution's id — TN-004) + the caller's fullness assertion `fills` (intent-capturing — the
    keyed-Quantity partial order may be INDETERMINATE). C/OP call-first: the caller moves each
    fill → READY (cycle CompleteProcessing) first; this commit gates on fills being READY. */
sig DistributeOcc extends lc/MutateOcc { allocation: EntityId -> lone Quantity, fills: set EntityId }
  { bindings = subject + allocation.Quantity + EntityId.allocation + fills }
/** Placement — where the items a Complete releases go (TN-004 rows 12 to 14; dafny-domain MD-082 `Placement`): one locator
    for all, one per released pool, or one per item. A VALUE carried by the Complete. Call-first: the items were MOVED
    before the Complete is called; its arms CHECK, the Complete never moves. */
abstract sig Placement {}
/** PlaceAll — one locator for everything the released pools hold (dafny-domain `ForAll`). */
sig PlaceAll extends Placement { allAt: one PhysicalLocator }
/** PlacePerPool — one locator per released pool, keyed by the pool's id (dafny-domain `PerPool`). */
sig PlacePerPool extends Placement { byPool: EntityId -> lone PhysicalLocator }
/** PlacePerItem — one locator per item: each locator's set of inventory-item ids (dafny-domain `PerItem`). */
sig PlacePerItem extends Placement { byLocator: PhysicalLocator -> EntityId }
// Value semantics: a placement IS its fields, and exists only where a Complete carries it (a refused one included).
fact PlacementExtensional {
  all disj a, b: PlaceAll     | a.allAt != b.allAt
  all disj a, b: PlacePerPool | a.byPool != b.byPool
  all disj a, b: PlacePerItem | a.byLocator != b.byLocator
}
fact NoOrphanPlacement { all p: Placement | p in CompleteOcc.placements }
/** Complete — declare the production run done (R8), naming where the released items sit (`placements`, TN-004 rows 12 to
    14): every live member SETTLED, the holding pool's newest write dated at or before this commit's own stamp (A5), and
    every item the released pools hold already at its placed locator. C/OP call-first: the caller settles each
    still-IN_PROCESS member first — inventory → CompleteProcessing (READY), none → ProductionFailure (REQUESTING, back in
    the queue) — and MOVES the items; this commit gates on both. The released pools (the holding and each external
    contribution's) are released AT REST by the status alone: no retire is required (TN-004 row 11, dafny-domain MD-084;
    COORDINATOR-Q527 Option B's retired-holding gate left). The resulting quantity MAY differ from the intent (R3b
    advisory). STAMPED (`CompleteTimed`): the one demand kind carrying the domain-time stamp, read against the holding
    pool's writes. */
sig CompleteOcc extends lc/MutateOcc { placements: one Placement } { bindings = subject + placements }
fact CompleteTimed { CompleteOcc in Timed }   // COORDINATOR-Q527: the stamp the A5 condition compares
/** Cancel — abandon an OPEN task (R5: guard requires NO attached cycles — RHasCards). */
sig CancelOcc extends lc/MutateOcc {} { bindings = subject }
/** Delete — delete/retire the closed task (R7: terminal Delete/Retire; tombstoned, II precedent). */
sig DeleteDemandOcc extends lc/RetireOcc {} { bindings = subject }   // the Retire shape; the NAME stays (MP, row 5)

// ── the kinds — ProductionDelivery subject (§8.1.2, cut 3) ─────────────────────────────────────
/** CreateDelivery — PD genesis, the F7 accrual edge's demand-side commit (§8.1.2 ATOMIC:
    target guards + the PD row + the RecordProduction effect in ONE demand commit; the I3
    quantity band is RUNTIME enforcement + probe — the pool-content fold stays out of the
    model, the standing arity-4 exclusion). `pool` carries the delivery's SPLIT POOL
    (caller-supplied) for the §8.1.4 item-agreement guard — deliberately an OCCURRENCE
    binding, not an entity field (D5 ruled the entity shape without it). RE-BASED (M3,
    DT-020 §8.5.3 / SPEARHEAD-D1 A′-2, MINESWEEPER model-deltas M3): was
    `item: lone EntityId`, a caller-ASSERTED Item compared directly to the demand's item;
    with typed pools (I3a) the caller supplies the POOL instead and the guard reads its
    `itemPin` — the pool's pin is authoritative, no separate item assertion needed. */
sig CreateDeliveryOcc extends pdlc/CreateOcc { pool: lone EntityId } { bindings = subject + pool }
/** RevokeDelivery — terminal reversal (§8.1.1 reversing-entry): the delivery contributes
    nothing from here on; corrections are Revoke + recreate. The caller (the producing
    process) checks its OWN source state per ordinary call-first; the content clause
    (holding ≥ contributed) is RUNTIME + probe (the I3 exclusion). Pairs ATOMICALLY with
    ExtractProduction on the target's log. */
sig RevokeDeliveryOcc extends pdlc/MutateOcc {} { bindings = subject }   // a status transition (terminal on the ladder), NOT the retire
/** RetireDelivery — the delivery's RETIRE kind (DT-030 M2: mandatory for every Universe-managed entity; Q24 (a)): the
    end of the delivery's history after its Revoke — the demand's two-step (Complete/Cancel then Delete) on the second
    subject. Admitted only on a REVOKED delivery (`RNotTerminal` while CREATED); refused `RDeliveryClosed` when never
    created or already retired (the family's arm). Effect: the tombstone (`pdlc/RetireEffect`). Runtime code `RETIRE`
    (D13 §6). Revoke stays a Mutate: REVOKED is a status, not the end of history. */
sig RetireDeliveryOcc extends pdlc/RetireOcc {} { bindings = subject }

/** demandMutators — the composition mutators under the R5 freeze (OPEN-only, RFrozen). SetContributionNotes is NOT one. */
fun demandMutators: set dlog/SubjectOcc {
  AddContributionOcc + RemoveContributionOcc + EditContributionOcc + DetachWithdrawnOcc
}
/** demandOccKinds — ALL demand occurrence kinds (the module family, alias-free for roots). Renamed from demandKinds 2026-07-08: `kind` binds to OCCURRENCE, never the module/entity (interaction-terminology section occurrence-kind). */
fun demandOccKinds: set dlog/SubjectOcc { dlog/SubjectOcc }
/** pdOccKinds — the ProductionDelivery subject's kinds (§8.1.2). */
fun pdOccKinds: set pdlog/SubjectOcc { pdlog/SubjectOcc }

// ── refusal reasons ─────────────────────────────────────────────────────────────────────────────
// (No uniqueness reason: multiple DemandItems per (Item, Source Station) are legal — R1 amended;
// single-OPEN, if wanted, is CALLER policy.)
one sig RDemandStarted,     // create: this subject already has committed history (genesis-once)
        RDemandClosed,      // the subject is not live (never started, or COMPLETE/CANCELED/deleted)
        RFrozen,            // composition/intent mutator outside OPEN (R5 freeze family)
        RBadState,          // lifecycle transition from the wrong status (Release/Reopen/StartProduction/…)
        RForeignRef,        // a resolved item/station/holding ref is in another tenant
        RForeignCycle,      // a resolved member cycle is in another tenant
        RCycleHeld,         // attach: the cycle is already held by a live DemandItem (indivisibility)
        RCycleIneligible,   // the member cycle is not at the saga step's expected state (C/OP
                            //   call-first: the CYCLE operation happens first, the demand commit is
                            //   the gate — dangling/closed/wrong-status refuse conservatively)
        RCycleLive,         // DetachWithdrawn: the cycle is still live (nothing to reconcile)
        RNotAttached,       // (declared, no longer raised: TN-004 replaced it by RNotContribution; dafny-domain MD-079 keeps the atom)
        RHasCards,          // cancel with attached cycles (R5)
        RBadAllocation,     // distribute: allocation keys / fills outside the live membership (R8)
        RBadPlacement,        // complete: the placements name a pool the demand does not release, an item no released pool
                              //   holds, or an item under two locators (TN-004 row 13)
        RPlacementIncomplete, // complete: a held item the placements give no locator (TN-004 row 13)
        RUnplaced,            // complete: a held item does not sit, as of the tick, where the placements say (row 14, call-first)
                              // (RUndistributed LEFT with the retired-holding gate: TN-004 row 11, dafny-domain MD-084)
        RNotTerminal,       // delete: the subject is not COMPLETE/CANCELED
        RNoContribution,    // release: the demand has no live contribution (TN-004)
        RContributionStarted, // attach: this demand's log already carried the contribution's id (used once, a removed id included)
        RDuplicateReference,  // attach/edit: another contribution of this demand reads the same reference
        RNotContribution,   // remove/edit/notes/detach: the id names no contribution of this demand
        RNotExternal        // edit: a quantity given for a card contribution (its quantity is its cycle's)
        extends Reason {}
// REUSED for the external contribution's pool (TN-004; the kanban and pool modules' atoms, dafny-domain MD-079):
// RPoolNotFresh (the pool was already named by an attach — and, since PR B, the HOLDING a StartProduction names was
// already used, MD-083), RPoolNotEmpty (remove while the pool holds an item — and, since PR B, CANCEL while an external
// contribution's pool holds one, MD-085), RNoSuchPool, RWrongItem.
// The PD subject's reasons (§8.1.2/§8.1.4; cut 3). RWrongItem is REUSED from the pool module
// (same semantic — item disagreement; the order module's reuse precedent).
one sig RDeliveryStarted,      // create-delivery: this PD already has committed history (genesis-once)
        RDeliveryClosed,       // revoke: the delivery is not live — never created, or already
                               //   REVOKED (terminal — §8.1.1; the RDemandClosed/ROrderClosed shape)
        RTargetNotInProcess    // create-delivery (§8.1.4): the target DemandItem is not IN_PROCESS —
                               //   COMPLETE/tombstoned/dangling targets refuse conservatively; the
                               //   OPEN→IN_PROCESS StartProduction choreography belongs to a service
                               //   composite OUTSIDE the model (A4 caller-responsibility)
        extends Reason {}
/** RBackdatedHolding — the RBackdated family's demand member (COORDINATOR-Q527 A5, MP 2026-10-15): COMPLETE refused
    because the holding pool's newest committed write is dated AFTER the COMPLETE's own stamp — accepting it would record
    a completion earlier in domain time than the content history it closes. Runtime: `DemandReason`, the same name (#327). */
one sig RBackdatedHolding extends RBackdated {}

// ── the read API (per-role; L9) ─────────────────────────────────────────────────────────────────
/** dPre / dPost — an occurrence's records, TYPED (the DT-017 Snapshot field-name collision fix:
    `sStatus` is ambiguous against CycleState in this cone). */
fun dPre [o: dlog/SubjectOcc]: lone DemandState { o.pre  & DemandState }
fun dPost[o: dlog/SubjectOcc]: lone DemandState { o.post & DemandState }
/** cyclesOf — the card cycles a set of contributions names, RESOLVED (soft refs may dangle out of scope). */
fun cyclesOf[cs: set Contribution]: set CardCycle {
  { k: CardCycle | some c: cs & CardContribution | resolve[c.cycleRef] = k }
}
/** liveContributionsOf — the contributions that COUNT at `t`: every external one, and a card one while its cycle is live. */
fun liveContributionsOf[cs: set Contribution, t: Tick]: set Contribution {
  (cs & ExternalContribution) + { c: cs & CardContribution | some k: CardCycle | resolve[c.cycleRef] = k and liveCycleAt[k, t] }
}
/** preMemberCycles — the LIVE resolved cycles of the card contributions as an operation reads them (pre-record). */
fun preMemberCycles[o: dlog/SubjectOcc]: set CardCycle {
  { c: cyclesOf[dPre[o].sContributions] | liveCycleAt[c, o.tick] }
}
/** preLiveContributionIds — the ids of the contributions live as an operation reads them (Distribute's keys and fills). */
fun preLiveContributionIds[o: dlog/SubjectOcc]: set EntityId {
  liveContributionsOf[dPre[o].sContributions, o.tick].cid
}
/** demandStateAt — LOCF of records: the demand item's payload as of `t`. */
fun demandStateAt[d: DemandItem, t: Tick]: lone DemandState { dlog/recordAt[d, t] }
/** demandStatusAt — the demand item's lifecycle status as of `t`. */
fun demandStatusAt[d: DemandItem, t: Tick]: lone DemandStatus { demandStateAt[d, t].sStatus }
/** liveDemandAt — live = STARTED and in a live status (R5: OPEN/RELEASED/IN_PROCESS;
    status-derived, unlike the cycle log's tombstone closure). NB the `some` conjunct is
    load-bearing: `in` is subset, so an empty read would be vacuously "live" without it. */
pred liveDemandAt[d: DemandItem, t: Tick] {
  some s: demandStateAt[d, t] | s.sStatus in liveStatuses
}
/** deletedAt — the terminal task has been deleted/retired (R7; tombstone, II precedent). */
pred deletedAt[d: DemandItem, t: Tick] {
  some o: DeleteDemandOcc | committed[o] and o.subject = d and notAfter[o.tick, t]
}
/** contributionsAt — the demand's contributions as of `t` (a withdrawn card's entry included, until its detach). */
fun contributionsAt[d: DemandItem, t: Tick]: set Contribution { demandStateAt[d, t].sContributions }
/** liveContributionsAt — the contributions that count at `t` (TN-004: the quantity sums these). */
fun liveContributionsAt[d: DemandItem, t: Tick]: set Contribution { liveContributionsOf[contributionsAt[d, t], t] }
/** attachedAt — the MEMBERSHIP, derived (dafny-domain MD-080): the cycles the card contributions name, RESOLVED. */
fun attachedAt[d: DemandItem, t: Tick]: set CardCycle { cyclesOf[contributionsAt[d, t]] }
/** attachedLiveAt — membership ∩ live cycles: the EFFECTIVE composition (R7). */
fun attachedLiveAt[d: DemandItem, t: Tick]: set CardCycle {
  { c: attachedAt[d, t] | liveCycleAt[c, t] }
}
/** retiredMembersAt — membership ∖ live cycles: the R7 frozen-state dangle. RECONCILED-class
    surface — non-empty drives the UI indication; never a violation. */
fun retiredMembersAt[d: DemandItem, t: Tick]: set CardCycle {
  attachedAt[d, t] - attachedLiveAt[d, t]
}
// ── the released pools and the placements (TN-004 rows 11 to 14; dafny-domain MD-082, MD-084) ───
/** releasedPoolIds — the pool ids a Complete of a demand in state `s` releases (dafny-domain `ReleasedPoolsAt`): the
    holding, if any, and every external contribution's pool. */
fun releasedPoolIds[s: DemandState]: set EntityId { s.sHolding + (s.sContributions & ExternalContribution).cPool }
/** heldByReleased — the (pool id, item) pairs the released pools hold as a Complete reads them (dafny-domain
    `HeldByReleasedAt`). */
fun heldByReleased[o: CompleteOcc]: EntityId -> InventoryItem {
  { e: releasedPoolIds[dPre[o]], x: InventoryItem | some p: resolve[e] & InventoryPool | x in heldAt[p, o.tick] }
}
/** placedLocators — every locator the placements give an item held by pool `e`: `PlaceAll`'s one, `PlacePerPool`'s for the
    pool, `PlacePerItem`'s locators whose set names the item's id. */
fun placedLocators[pl: Placement, e: EntityId, x: InventoryItem]: set PhysicalLocator {
  (pl & PlaceAll).allAt + e.((pl & PlacePerPool).byPool) + ((pl & PlacePerItem).byLocator).(x.eId)
}
/** placedLocator — THE locator the placements give the item, when there is exactly one (dafny-domain `PlacedLocator`: none
    when nothing names the item, and none when two locators' sets do — that case is the guard's RBadPlacement). */
fun placedLocator[pl: Placement, e: EntityId, x: InventoryItem]: lone PhysicalLocator {
  (one placedLocators[pl, e, x]) => placedLocators[pl, e, x] else none
}
/** contributionHolds — a LIVE demand's external contribution `c` names the pool id `e` at `t` (dafny-domain
    `ContributionHolds`): the pool lattice's fourth holder kind. */
pred contributionHolds[d: DemandItem, c: ExternalContribution, e: EntityId, t: Tick] {
  liveDemandAt[d, t] and c in contributionsAt[d, t] and c.cPool = e
}
/** demandOf — the derived INVERSE of membership (R2: the cycle carries no back-pointer). */
fun demandOf[c: CardCycle, t: Tick]: set DemandItem {
  { d: DemandItem | liveDemandAt[d, t] and c in attachedAt[d, t] }
}
/** demandsFor — the live DemandItems for an (Item, Source Station) identity pair: the CALLER's
    read for its collation policy (single-OPEN, round-robin, …) — the module does NOT enforce
    uniqueness (R1 amended). */
fun demandsFor[i: Item, station: EntityId, t: Tick]: set DemandItem {
  { d: DemandItem | liveDemandAt[d, t] and d.itemPin.subject = i and d.stationRef = station }
}

// ── the effective quantity (R7: FIXED AT GENESIS) ───────────────────────────────────────────────
/** genesisOf — the cycle's committed genesis occurrence (≤1 by the cycle log's RAlreadyStarted). */
fun genesisOf[c: CardCycle]: lone RequestOcc { { r: RequestOcc | committed[r] and r.cycle = c } }
/** effectiveQtyMap — the member's contribution as a keyed map: the genesis `qtyOverride` if given,
    else the owning card's `nominalQuantity` AT ANY TIME (safe: both are immutable — R7). Empty
    map = no stated quantity (the keyed zero). */
fun effectiveQtyMap[c: CardCycle]: Unit -> lone Scalar {
  some genesisOf[c].qtyOverride => genesisOf[c].qtyOverride.byUnit else (cycles.c).nominalQuantity.byUnit
}
/** qtyMap — a lone Quantity as its keyed map (none = the keyed zero; the kit's uniform encoding). */
fun qtyMap[q: Quantity]: Unit -> lone Scalar { q.byUnit }
/** contributionQtyMap — ONE contribution's quantity as a keyed map: an external one's own, a card one's cycle's effective
    quantity (empty when the cycle does not resolve). The SUM over the live contributions is demand_quantity.als's. */
fun contributionQtyMap[c: Contribution]: Unit -> lone Scalar {
  (c in ExternalContribution) => c.quantity.byUnit else effectiveQtyMap[cyclesOf[c]]
}

// ── the reference (TN-004: unique among a demand's contributions, AS READ) ──────────────────────
/** referenceOf — a contribution's EFFECTIVE reference: an external one's own; a card one's override, or by default its
    card's serial (dafny-domain MD-077: the default is a read over the card, never stored). Empty when a card
    contribution has no override and its cycle does not resolve. */
fun referenceOf[c: Contribution]: lone (CardSerial + Reference) {
  (c in ExternalContribution) => c.externalReference
  else ((some c.referenceOverride) => c.referenceOverride else (cycles.(cyclesOf[c])).serialNumber)
}

// ── the PD read API (§8.1.2; per-role, L9) ──────────────────────────────────────────────────────
/** pdPre / pdPost — a PD occurrence's records, TYPED (the DT-017 collision fix, per subject). */
fun pdPre [o: pdlog/SubjectOcc]: lone PDState { o.pre  & PDState }
fun pdPost[o: pdlog/SubjectOcc]: lone PDState { o.post & PDState }
/** deliveryStatusAt — the delivery's status as of `t` (none before genesis). */
fun deliveryStatusAt[pd: ProductionDelivery, t: Tick]: lone PDStatus {
  pdlog/recordAt[pd, t].sStatus
}
/** contributionsFor — the LIVE (CREATED, un-revoked) deliveries targeting `d` as of `t`: the
    M:1 functional leg the fulfillment fold rolls up (SET-level here; the quantity fold is
    read-side/metrics territory — the I3 exclusion). */
fun contributionsFor[d: DemandItem, t: Tick]: set ProductionDelivery {
  { pd: ProductionDelivery | pd.demandRef = d.eId and deliveryStatusAt[pd, t] = PD_CREATED }
}
