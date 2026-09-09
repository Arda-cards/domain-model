module procurement/order/order_types

/*
 * ORDER — TYPES (DT-018; DT-017 four-file architecture). The Order is the AGREEMENT DOCUMENT at
 * the boundary of a Source station (DT-014 rung 3): it collates released demand — DemandItems —
 * into a single-supplier commitment, is negotiated through submission and (possibly WAIVED)
 * acknowledgment, and closes as material arrives through receiving. First module of the
 * procurement/ domain; the runtime rides the operations COMPONENT (component ≠ domain).
 *
 * TWO SUBJECTS on the log spine — the Order and its OrderLines (each `open` of subject_log
 * mints its OWN spine: olog and llog below are independent chaining laws and read APIs). The
 * composition is ENTITY-CARRIED ON THE CHILD (O5): a line's `orderRef` is immutable
 * identity-structure; `linesOf` is a derived read; NO record-side line set exists.
 *
 * PUBLIC OPERATION SURFACE (DT-017 L9): the 17 kinds, the Reason taxonomy, and the read API
 * live here. Laws are named predicates in order_contracts.als; machinery in
 * order_implementation.als; consumers' unit roots open order_mock.als.
 *
 * NAMING (Occ ruling (c) + flat-namespace survey): model sigs carry the `Occ` register marker;
 * product surfaces use the bare verb. Collision-dodging model names: CreateOrderOcc /
 * CancelOrderOcc / CloseOrderOcc / DeleteOrderOcc / AnnotateOrderOcc (demand owns
 * CreateDemandOcc / CancelOcc / DeleteDemandOcc in this cone; Close/Annotate take the
 * subject-qualified form for symmetry with their line twins). Statuses carry the OS_ prefix
 * (the DS_/PS_ precedent); OS_CANCELED is the en-US single-L spelling (the DS_CANCELED
 * precedent). REASONS: five atoms are REUSED from the demand vocabulary in this cone (RFrozen,
 * RBadState, RForeignRef, RNotAttached, RNotTerminal — same meaning one rung up); the
 * order-specific ones are declared below.
 *
 * MODEL SIMPLIFICATIONS (documented, not modeled — design doc §4): orderNumber (identity is the
 * atom; the number is a runtime writer policy), line rank/document ordering, currency/terms,
 * LINE notes-as-occurrence-payloads (AnnotateLineOcc — the order-line record carries no note
 * field yet; PDEV-516 will ride the shared Note mechanism at its own ruling), the supplier
 * snapshot's field-level detail (an opaque atom + an overrides marker suffice for the
 * freeze/reset laws — only the NAME is first-class, because Submit's RNoSupplier and F8's
 * "all fields but the name" need it).
 *
 * ORDER-LEVEL notes ARE record fields since cut 6 (DT-022 TQ-7(c), MP 2026-08-07): sNotes
 * (vendor-facing, frozen at Submit) + sInternalNotes (internal, editable at ANY time — the
 * one deliberate exemption from every freeze; history rides the log). The same cut added
 * sPriority (TQ-7(a): ordered vocabulary, UNDEFINED default, frozen at Submit) and sAssignee
 * (TQ-7(b): → StaffMember, frozen at Submit).
 */

open meta/profiles/domain_log                        // PROFILE (DT-012): log anatomy + group/order premises
open meta/kernel                                     // Scoped, EntityId, resolve
open meta/subject_log/subject_log[Order, OrderState] as olog          // the ORDER log spine
open meta/subject_log/subject_log[OrderLine, OrderLineState] as llog  // the LINE log spine
open meta/subject_log/lifecycle[Order, OrderState] as lco             // the ORDER log's SHAPES (DT-030, 2026-09-09)
open meta/subject_log/lifecycle[OrderLine, OrderLineState] as lcl     // the LINE log's SHAPES
open shared/values                                   // Quantity (+ keyed-map add/negate)
open shared/note                                     // Note (sNotes/sInternalNotes — record-carried; pin `2 Note`)
open operations/demand/demand_types                  // DemandItem + statuses + reads (TYPES only)
open reference_data/item/item_types                  // Item + ItemOcc pins + itemLiveAt (DT-023; previously transitive via demand_types)
open reference_data/business_affiliate/business_affiliate_types      // BaOcc + BusinessRole — the binding's vendor PIN + role selector (DT-023 cut 7b; was SupplierReference [F8/O6])
open reference_data/staff/staff_types                // StaffOcc — the assignee VERSION PIN (DT-023 cut 7c; was the sAssignee soft ref, DT-022 TQ-7(b))

// ── the status vocabulary ───────────────────────────────────────────────────────────────────────
/** OrderStatus — the FOUR stored states (O7); CONFIRMED and RECEIVING are DERIVED READINGS over
    SUBMITTED (see confirmedReadingAt / receivingReadingAt), never stored transitions. */
abstract sig OrderStatus {}
one sig OS_DRAFT, OS_SUBMITTED, OS_CLOSED, OS_CANCELED extends OrderStatus {}

/** liveOrderStatuses — the order is LIVE in these; CLOSED/CANCELED are terminal closure. */
fun liveOrderStatuses: set OrderStatus { OS_DRAFT + OS_SUBMITTED }

/** OrderLineStatus — the line's closure facet (F7: lines close ONLY by act; "short" is derived). */
abstract sig OrderLineStatus {}
one sig L_OPEN, L_CLOSED extends OrderLineStatus {}

/** OrderPriority — the order's vendor-expediting priority (DT-022 TQ-7(a), MP 2026-08-08):
    a fixed ORDERED vocabulary, UNDEFINED < LOW < NORMAL < HIGH < URGENT (declaration order;
    easy to add/remove values later — no law reads the order today). OP_UNDEFINED is the
    SEEDED DEFAULT at Create; the field freezes at Submit (vendor communication — the
    "re-submitting" workflow that would re-open it is out of scope this version). */
abstract sig OrderPriority {}
one sig OP_UNDEFINED, OP_LOW, OP_NORMAL, OP_HIGH, OP_URGENT extends OrderPriority {}

// ── the supplier binding (F8/O6) ────────────────────────────────────────────────────────────────
/** SupplierName — the vendor's name: the ONE first-class snapshot field (Submit requires it —
    RNoSupplier; F8: the only field overrides may NOT touch). */
sig SupplierName {}
/** SupplierData — the OPAQUE snapshot/override content (field-level detail is runtime — §4). */
sig SupplierData {}
/** SupplierBinding — snapshot + vendor VERSION PIN + per-order overrides (F8): chooseable and
    overridable while DRAFT; `ResetToSupplier` discards `overrides`; FROZEN at Submit. The
    vendor link is a BA version pin + role selector since DT-023 cut 7b (the SupplierReference
    handle DISSOLVED) — both lone, so an unlinked, name-only supplier stays legal (PDEV-241).
    The frozen binding freezes the PIN: what was agreed with the vendor is the pinned version. */
sig SupplierBinding {
  name:       lone SupplierName,     // may be the ONLY content (PDEV-241)
  vendorPin:  lone BaOcc,            // → BusinessAffiliate VERSION PIN (DT-023 R3)
  vendorRole: lone BusinessRole,     // the VENDOR role selector within the pinned version
  base:       one  SupplierData,     // the snapshot taken at choose time
  overrides:  lone SupplierData      // present iff any field is overridden (F8)
}
// Value semantics: a binding IS its fields.
fact SupplierBindingExtensional {
  all disj a, b: SupplierBinding |
    a.name != b.name or a.vendorPin != b.vendorPin or a.vendorRole != b.vendorRole
    or a.base != b.base or a.overrides != b.overrides
}
// Pin-target agreement is DEFINITIONAL (the ItemLinePinAgrees precedent): pin and selector
// come TOGETHER (DT-023 cut 8, the PDEV-241 re-base: every present vendor reference points
// to a real BusinessAffiliate BEARING a VENDOR role — "name-only" means a minimal
// BusinessAffiliate, never a role-less link), and the selector is a VENDOR role of the
// PINNED version. Tenancy stays guard-side.
fact SupplierBindingPinAgrees {
  all b: SupplierBinding {
    some b.vendorPin iff some b.vendorRole
    some b.vendorRole implies roleSelectorAgrees[b.vendorPin, b.vendorRole, VENDOR]
  }
}

// ── the line's item reference — IDENTITY + READ-TIME EFFECTIVE VERSION (cut 10, PDEV-1536) ──────
// The line carries the item's IDENTITY only (`itemRef`); the EFFECTIVE version is DERIVED at
// read time (`effectiveItemAt`): the item log's CURRENT version while the parent order is
// un-submitted, FROZEN at the version current at the parent's Submit tick afterward (MP ruling
// 2026-08-13, the propagation-semantics refinement: "the line refers to the most current version
// of the Item while not submitted (identified by eId), and to the frozen record after submission
// (identified by [eId, rId]); the other fields are a denormalization of the effective Item").
// The model keeps NO denormalized state — the runtime's C/NOTIF refresh listener, its sync
// occurrence kind, and the heal probe are pure implementation with no model representation.
// This supersedes the cut-7a genesis-frozen VERSION pin (`itemPin: lone ItemOcc` +
// `LinePinCurrency`), which froze the WRONG version whenever the item was edited during DRAFT;
// the cut-7a dissolution of the descriptor apparatus (`sItemData` + `ItemLinePinAgrees` +
// `lineDescriptorFrozen` + `RNoDescriptor`) stands. Runtime coordinate after Submit: (eId, rId).

// ── the confirmation facet (F3) ─────────────────────────────────────────────────────────────────
/** Disposition — the vendor's per-line answer; WAIVED = an acknowledgment recorded WITHOUT an
    explicit vendor answer (the F3 auto-confirm, trusting the user act). */
abstract sig Disposition {}
one sig DISP_ACCEPTED, DISP_CHANGED, DISP_BACKORDERED, DISP_REJECTED, DISP_SUBSTITUTED, DISP_WAIVED
  extends Disposition {}

/** Confirmation — the vendor's answer on a line (requested vs confirmed — the X12 855 lesson);
    notes ride the occurrence payload, not the record. */
sig Confirmation {
  disposition:  one  Disposition,
  confirmedQty: lone Quantity
}
fact ConfirmationExtensional {
  all disj a, b: Confirmation | a.disposition != b.disposition or a.confirmedQty != b.confirmedQty
}

// ── the entities: IDENTITY + IMMUTABLE STRUCTURE (O5) ───────────────────────────────────────────
/** Order — the agreement document. Identity only; everything mutable rides the log. (The
    orderNumber is a documented simplification — runtime writer policy, no law touches it.) */
sig Order extends Scoped {}
fact OrderRefs { all o: Order | no o.dataRefs }   // the supplier binding is RECORD-carried

/** OrderLine — a structure WITH IDENTITY (the UBL lesson): immutable parent + immutable
    optional item. A line with no item is FREE-FORM: documentary only — no demand pairing, no
    received tracking (F7 flag 3). Changing a line's item = Remove + Add (O5). */
sig OrderLine extends Scoped {
  orderRef: one  EntityId,   // → Order: the parent (lines never move — O5); entity-carried composition
  itemRef:  lone EntityId    // → Item IDENTITY (cut 10 — was the cut-7a version pin): WHAT is
                             //   ordered; the effective VERSION is `effectiveItemAt` (read-time
                             //   derivation, frozen at Submit); absent = free-form
}
// Both refs are EntityId dataRefs, so kernel cross-tenant isolation covers them — the cut-7a
// `LineItemPinTenancy` side-fact DISSOLVED with the typed pin (cut 10).
fact OrderLineRefs { all l: OrderLine | l.dataRefs = l.orderRef + l.itemRef }
fact OrderLineRefIntegrity {
  all l: OrderLine | let o = resolve[l.orderRef] | some o implies o in Order
  all l: OrderLine | let i = resolve[l.itemRef]  | some i implies i in Item
}

// ── the state records ───────────────────────────────────────────────────────────────────────────
/** OrderState — one moment's mutable payload of an Order (a value; extensional). */
sig OrderState extends Snapshot {
  sStatus:   one OrderStatus,     // where the document stands (F5/O7: the stored core)
  sSupplier: one SupplierBinding, // the F8 binding (frozen at Submit)
  sPriority: one OrderPriority,   // vendor-expediting priority (TQ-7(a)); OP_UNDEFINED default; frozen at Submit
  sAssignee: lone StaffOcc,       // → StaffMember VERSION PIN (DT-023 cut 7c; was a soft
                                  //   EntityId ref): the accountable owner (TQ-7(b));
                                  //   floats pre-Submit (each details write re-pins
                                  //   current); frozen at Submit (headerDetailFrozen)
  sNotes:    lone Note,           // procurement ↔ VENDOR communication (TQ-7(c)); frozen at Submit
  sInternalNotes: set Note        // INTERNAL notes (TQ-7(c)): editable at ANY time — the one
                                  //   deliberate exemption from every freeze; history = the log
}
fact OrderStateExtensional {
  all disj a, b: OrderState |
    a.sStatus != b.sStatus or a.sSupplier != b.sSupplier or a.sPriority != b.sPriority
    or a.sAssignee != b.sAssignee or a.sNotes != b.sNotes or a.sInternalNotes != b.sInternalNotes
}
// (OrderAssigneeRefIntegrity DISSOLVED at DT-023 cut 7c: the assignee is a TYPED staff
// version pin — soft-ref typing is unrepresentable; tenancy stays guard-side.)
// (OrderSupplierRefIntegrity DISSOLVED at DT-023 cut 7b: the binding's vendor link is a TYPED
// pin + selector — soft-ref typing clauses are unrepresentable; agreement is the definitional
// SupplierBindingPinAgrees above; tenancy stays guard-side — supplierRefViol.)

/** OrderLineState — one moment's mutable payload of an OrderLine (a value; extensional). */
sig OrderLineState extends Snapshot {
  sQuantity:     lone Quantity,        // requested (buyer facet)
  sConfirmation: lone Confirmation,    // the vendor's answer (F3); none until acknowledged
  sReceived:     lone Quantity,        // STORED, incrementally maintained (F9); none = the keyed zero
  sLineStatus:   one  OrderLineStatus, // L_OPEN / L_CLOSED (closure by act — F7)
  sDemand:       set  EntityId,        // → DemandItem: the serviced demand (O3: the HOLDER carries the refs)
  sInternalNotes: set Note             // INTERNAL notes on the line (TQ-7(c) one rung down; 2026-09-09: was parked on the
                                       //   kernel's inert `Occurrence.note` — a point defect; editable in any domain state)
  // (sItemData DISSOLVED at DT-023 cut 7a; the effective item version is DERIVED at read time
  //  since cut 10 — `effectiveItemAt`, frozen at Submit.)
}
fact OrderLineStateExtensional {
  all disj a, b: OrderLineState |
    a.sQuantity != b.sQuantity or a.sConfirmation != b.sConfirmation or a.sReceived != b.sReceived
    or a.sLineStatus != b.sLineStatus or a.sDemand != b.sDemand or a.sInternalNotes != b.sInternalNotes
}
// Record-carried refs are TYPED (soft — dangling allowed; tenancy is guard-side).
fact OrderLineDemandRefIntegrity {
  all s: OrderLineState | all m: s.sDemand | let d = resolve[m] | some d implies d in DemandItem
}

// ── the kinds — ORDER subject (product-register names in comments) ──────────────────────────────
/** Create — start an order (births DRAFT; seeds the supplier binding — name may be the only
    content, PDEV-241). */
sig CreateOrderOcc extends lco/CreateOcc { supplier: one SupplierBinding }
  { bindings = subject + supplier }
/** UpdateSupplier — choose/override the supplier while composing (F8). */
sig UpdateSupplierOcc extends lco/MutateOcc { supplier: one SupplierBinding }
  { bindings = subject + supplier }
/** ResetToSupplier — discard the per-order overrides (F8). */
sig ResetToSupplierOcc extends lco/MutateOcc {} { bindings = subject }
/** Submit — commit: freeze + snapshot + transmit (the freeze instant — F5). C/OP call-first
    (O2): the caller drives demand.StartProduction per serviced item FIRST (demand's own service
    op carries its member-cycle legs); this commit GATES on every serviced item IN_PROCESS. */
sig SubmitOcc extends lco/MutateOcc {} { bindings = subject }
/** Close — order done, by act (requires every live line closed). */
sig CloseOrderOcc extends lco/MutateOcc {} { bindings = subject }
/** Cancel — abandon while composing (DRAFT-ONLY — O4: post-submission cancellation retracts
    vendor commitments; a parked seam, not a casual operation). */
sig CancelOrderOcc extends lco/MutateOcc {} { bindings = subject }
/** UpdateOrderDetails — SET the DRAFT-mutable header details as one facet cluster (TQ-7,
    cut 6): the payload IS the new cluster (the Receiver-header SET precedent — absent
    priority ⇒ OP_UNDEFINED, absent assignee/notes ⇒ cleared). DRAFT-only (the F5 family). */
sig UpdateOrderDetailsOcc extends lco/MutateOcc {
  priority: lone OrderPriority, assignee: lone StaffOcc, notes: lone Note
} { bindings = subject + priority + assignee + notes }
/** Annotate — SET the order's INTERNAL notes (any live-or-terminal state — TQ-7(c):
    editable at ANY time; the payload IS the new note set, so add/edit/remove are all this
    one act; history rides the log). Since cut 6 the notes land on the RECORD
    (sInternalNotes) — the pre-cut-6 payload-only reading is superseded. */
sig AnnotateOrderOcc extends lco/MutateOcc { notes: set Note } { bindings = subject + notes }
/** Delete — retire the closed order (the Retire shape: the tombstone; lines retire with it at runtime). The NAME stays (MP, row 5). */
sig DeleteOrderOcc extends lco/RetireOcc {} { bindings = subject }

// ── the kinds — LINE subject ────────────────────────────────────────────────────────────────────
/** AddLine — line genesis: from a DemandItem, from an Item, or free-form (F6). The on-the-fly
    card-less DemandItem for a naked-item line is the CALLER's demand-side Create — order-side
    this is just genesis + attach. orderRef/itemRef ride the ENTITY (identity only — the
    effective version is the read-time derivation `effectiveItemAt`, cut 10); the item is
    guarded live on this arm (RRetiredRef — line-add is a new-commitment point, D3). */
sig AddLineOcc extends lcl/CreateOcc { qty: lone Quantity, demand: lone EntityId }
  { bindings = subject + qty + demand }   // the descriptor pin rides the line IDENTITY (DT-023 cut 7a)
/** UpdateLine — edit the requested quantity (SET; the item is immutable — O5). */
sig UpdateLineOcc extends lcl/MutateOcc { qty: one Quantity } { bindings = subject + qty }
/** LineDemandOcc — the abstract parent of the demand-addressing line kinds (`demand` declared
    once — the MemberOcc precedent). */
abstract sig LineDemandOcc extends lcl/MutateOcc { demand: one EntityId }   // both children are mutations: `extends` still holds
/** AttachDemand — service a further DemandItem (C/OP gate order-side: item observed RELEASED,
    not held; NO demand-side operation pairs with attach — O3). */
sig AttachDemandOcc extends LineDemandOcc {} { bindings = subject + demand }
/** DetachDemand — stop servicing an item (it is simply back in the queue; pairs with nothing). */
sig DetachDemandOcc extends LineDemandOcc {} { bindings = subject + demand }
/** RemoveLine — retire a line while composing (the Retire shape: the tombstone, terminal). TWO ACTS since 2026-09-09
    (MP's word): a line still servicing a demand refuses `RDemandAttached` — the caller DETACHES first (`DetachDemandOcc`,
    which puts the demand back in the queue), then removes. The NAME stays (MP, row 5). */
sig RemoveLineOcc extends lcl/RetireOcc {} { bindings = subject }
/** RecordAcknowledgment — the vendor's answer, or the WAIVED auto-confirm (F3). */
sig RecordAcknowledgmentOcc extends lcl/MutateOcc { confirmation: one Confirmation }
  { bindings = subject + confirmation }
/** RecordReceipt — the accrual posting (F7/F9: the C/NOTIF reaction to demand
    RecordProduction notifications; the SAME kind is the manual repair / probe re-drive).
    Incremental: sReceived += qty — pairwise, no fold anywhere. */
sig RecordReceiptOcc extends lcl/MutateOcc { qty: one Quantity } { bindings = subject + qty }
/** ReverseReceipt — the accrual's COMPENSATING posting (F9b, MP ruling 2026-08-14: the received
    quantity is FINANCIALLY BINDING — it is what incurs cost when the order closes — so a revoked
    delivery must decrement it, unlike purely operational effects; the C/NOTIF reaction to demand
    Revoke/ExtractProduction notifications; the SAME kind is the manual repair / probe re-drive).
    Incremental: sReceived −= qty — pairwise, the ledger's reversing entry (corrections are never
    edits). Dedup (one reversal per revoked delivery) is runtime idempotency machinery — the
    accrual precedent: no law reads a delivery identity here. */
sig ReverseReceiptOcc extends lcl/MutateOcc { qty: one Quantity } { bindings = subject + qty }
/** CloseLine — line done, BY DECREE (F7: full receipt makes closure available, never actual;
    "short" = the derived reading open ≠ 0 at the close tick). */
sig CloseLineOcc extends lcl/MutateOcc {} { bindings = subject }
/** AnnotateLine — SET the line's INTERNAL notes (a Mutate: the payload IS the new note set — the order's cut-6 shape one
    rung down; TQ-7(c): any DOMAIN state, closed lines included; never after the line's retire — MP 2026-09-09, the
    point-defect fix: the note no longer rides the kernel's inert `Occurrence.note`). */
sig AnnotateLineOcc extends lcl/MutateOcc { notes: set Note } { bindings = subject + notes }

// (`orderCarriedSupplierRefs` — the SupplierReference closure export — DIED at DT-023 cut 7b
// with the handle itself: the binding's vendor link is a typed pin + selector, no
// orphan-closure obligation exists.)

/** orderStructuralMutators — the ORDER-subject mutators under the F5 freeze (DRAFT-only).
    AnnotateOrderOcc is deliberately NOT here — internal notes are editable at any time
    (TQ-7(c)). */
fun orderStructuralMutators: set olog/SubjectOcc {
  UpdateSupplierOcc + ResetToSupplierOcc + UpdateOrderDetailsOcc
}
/** lineStructuralMutators — the LINE-subject mutators under the F5 freeze (the parent order
    must be DRAFT; includes line genesis). */
fun lineStructuralMutators: set llog/SubjectOcc {
  AddLineOcc + UpdateLineOcc + AttachDemandOcc + DetachDemandOcc + RemoveLineOcc
}
/** orderOccKinds / lineOccKinds — the module families, alias-free for roots. */
fun orderOccKinds: set olog/SubjectOcc { olog/SubjectOcc }
fun lineOccKinds:  set llog/SubjectOcc { llog/SubjectOcc }

// ── refusal reasons (order-specific; five shared atoms reused from the demand vocabulary) ───────
one sig ROrderStarted,      // create: this order already has committed history (genesis-once)
        ROrderClosed,       // the order is not live (never started, or CLOSED/CANCELED/deleted)
        RLineStarted,       // add-line: this line already has committed history (genesis-once)
        RLineClosed,        // the line is unusable (never started, removed, or L_CLOSED)
        RNoLines,           // submit: no live lines
        RNoSupplier,        // submit: the supplier binding carries no name (PDEV-241 floor)
        RDemandHeld,        // attach: the demand item is already serviced by a live line (demandIndivisible)
        RDemandIneligible,  // attach/submit C/OP gate: the demand item is dangling, not live,
                            //   not at the expected saga state (RELEASED for attach; IN_PROCESS at submit),
                            //   or not denominated in the line's item (C3b, MP 2026-07-10 — wrong
                            //   item, or a free-form target line: an empty itemRef resolution can never agree)
        RLinesOpen,         // close: a live line is still L_OPEN
        RNoDemand           // record-receipt: the line is free-form (no received tracking — F7)
        extends Reason {}
/** RDemandAttached — RemoveLine on a line still servicing a demand (two acts: detach first — MP 2026-09-09). */
one sig RDemandAttached extends Reason {}
        // (RNoDescriptor RETIRED at DT-023 cut 7a: the descriptor pin is the line IDENTITY —
        //  a missing or extra pin is no longer a caller error but a different line kind.)

// ── the read API (per-role; L9) ─────────────────────────────────────────────────────────────────
/** oPre / oPost / lPre / lPost — an occurrence's records, TYPED (the DT-017 Snapshot
    field-name collision fix, per subject). */
fun oPre [o: olog/SubjectOcc]: lone OrderState { o.pre  & OrderState }
fun oPost[o: olog/SubjectOcc]: lone OrderState { o.post & OrderState }
fun lPre [o: llog/SubjectOcc]: lone OrderLineState { o.pre  & OrderLineState }
fun lPost[o: llog/SubjectOcc]: lone OrderLineState { o.post & OrderLineState }

/** orderStateAt / orderStatusAt — LOCF reads of the order log. */
fun orderStateAt [o: Order, t: Tick]: lone OrderState { olog/recordAt[o, t] }
fun orderStatusAt[o: Order, t: Tick]: lone OrderStatus { orderStateAt[o, t].sStatus }
/** liveOrderAt — started and in a live status (status-derived; NB the `some` conjunct — the
    demand precedent: `in` is subset, an empty read would be vacuously live). */
pred liveOrderAt[o: Order, t: Tick] {
  some s: orderStateAt[o, t] | s.sStatus in liveOrderStatuses
}
/** orderDeletedAt — the terminal order has been deleted/retired (tombstone). */
pred orderDeletedAt[o: Order, t: Tick] {
  some d: DeleteOrderOcc | committed[d] and d.subject = o and notAfter[d.tick, t]
}

/** lineStateAt / lineStatusAt — LOCF reads of the line log. */
fun lineStateAt [l: OrderLine, t: Tick]: lone OrderLineState { llog/recordAt[l, t] }
fun lineStatusAt[l: OrderLine, t: Tick]: lone OrderLineStatus { lineStateAt[l, t].sLineStatus }
/** lineRemovedAt — a committed RemoveLine tombstone exists at-or-before `t`. */
pred lineRemovedAt[l: OrderLine, t: Tick] {
  some r: RemoveLineOcc | committed[r] and r.subject = l and notAfter[r.tick, t]
}
/** startedLineAt / startedOrderAt — spine reads exported by name (module aliases are
    file-local; the sibling files and roots read through these). */
pred startedLineAt [l: OrderLine, t: Tick] { llog/startedAt[l, t] }
pred startedOrderAt[o: Order, t: Tick]     { olog/startedAt[o, t] }
/** liveLineAt — started and not removed (L_CLOSED lines are still LIVE — closure is a facet,
    removal is retirement). */
pred liveLineAt[l: OrderLine, t: Tick] { startedLineAt[l, t] and not lineRemovedAt[l, t] }

/** parentOf — the line's order (entity-carried composition, O5). */
fun parentOf[l: OrderLine]: lone Order { resolve[l.orderRef] & Order }
/** linesOf — the ENTITY composition read (no record-side line set exists — O5). */
fun linesOf[o: Order]: set OrderLine { { l: OrderLine | parentOf[l] = o } }
/** liveLinesOf — the order's live (started, unremoved) lines. */
fun liveLinesOf[o: Order, t: Tick]: set OrderLine { { l: linesOf[o] | liveLineAt[l, t] } }
/** retiredLinesOf — the removed lines (audit surface; their history stays on the log). */
fun retiredLinesOf[o: Order, t: Tick]: set OrderLine {
  { l: linesOf[o] | startedLineAt[l, t] and lineRemovedAt[l, t] }
}
/** freeForm — the line orders no Item: documentary only (F6/F7). */
pred freeForm[l: OrderLine] { no l.itemRef }

/** lineFreezeTick — the parent order's freeze instant at-or-before `t` (the committed Submit's
    tick; at most one — Submit fires once, DRAFT → SUBMITTED). Empty while un-submitted. */
fun lineFreezeTick[l: OrderLine, t: Tick]: lone Tick {
  { k: Tick | some s: SubmitOcc | committed[s] and s.subject = parentOf[l] and s.tick = k and notAfter[k, t] }
}
/** effectiveItemAt — the line's EFFECTIVE item version at `t` (cut 10, PDEV-1536 — the ruled
    read-time derivation): the item log's CURRENT version while the parent is un-submitted;
    FROZEN at the version current at the parent's Submit tick afterward. Empty for a free-form
    or dangling reference. Only Submit changes the retrieval rule — no stored version, no
    denormalized state, nothing to keep in sync model-side. */
fun effectiveItemAt[l: OrderLine, t: Tick]: lone ItemOcc {
  some lineFreezeTick[l, t]
    => itemVersionAt[resolve[l.itemRef] & Item, lineFreezeTick[l, t]]
    else itemVersionAt[resolve[l.itemRef] & Item, t]
}

/** servicedAt — a line's serviced DemandItems, RESOLVED (soft refs may dangle out of scope). */
fun servicedAt[l: OrderLine, t: Tick]: set DemandItem {
  { d: DemandItem | some m: lineStateAt[l, t].sDemand | resolve[m] = d }
}
/** servicedOf — every DemandItem serviced by the order's LIVE lines (Submit's gate domain). */
fun servicedOf[o: Order, t: Tick]: set DemandItem {
  { d: DemandItem | some l: liveLinesOf[o, t] | d in servicedAt[l, t] }
}
/** holdingLineOf — the derived INVERSE of servicing (O3: the demand side carries no back-pointer;
    "is this item spoken for?" is THIS read). ≤1 by demandIndivisible. THE HOLD DIES WITH THE
    ORDER (scenario 6/O4: cancel — or close — returns the serviced items to the queue; no
    line-by-line choreography), hence the parent-liveness conjunct. */
fun holdingLineOf[d: DemandItem, t: Tick]: set OrderLine {
  { l: OrderLine | liveLineAt[l, t] and liveOrderAt[parentOf[l], t] and d in servicedAt[l, t] }
}

/** effectiveLineQty — confirmed-else-requested, as a keyed map (the reconciliation read). */
fun effectiveLineQty[s: OrderLineState]: Unit -> lone Scalar {
  some s.sConfirmation.confirmedQty => qtyMap[s.sConfirmation.confirmedQty] else qtyMap[s.sQuantity]
}
/** openOf — the derived open quantity: confirmed-else-requested − sReceived (pairwise; MAY go
    negative — over-receipt is admissible, the advisory stance F9). */
fun openOf[l: OrderLine, t: Tick]: Unit -> lone Scalar {
  add[effectiveLineQty[lineStateAt[l, t]], negate[qtyMap[lineStateAt[l, t].sReceived]]]
}

/** confirmedReadingAt — the O7 derived CONFIRMED reading: SUBMITTED and every live line has a
    recorded answer (incl. WAIVED). May be transient — a reading, never a transition. */
pred confirmedReadingAt[o: Order, t: Tick] {
  orderStatusAt[o, t] = OS_SUBMITTED
  all l: liveLinesOf[o, t] | some lineStateAt[l, t].sConfirmation
}
/** receivingReadingAt — the O7 derived RECEIVING reading: SUBMITTED and material has arrived
    (trumps CONFIRMED in the product's status view). */
pred receivingReadingAt[o: Order, t: Tick] {
  orderStatusAt[o, t] = OS_SUBMITTED
  some l: liveLinesOf[o, t] | some qtyMap[lineStateAt[l, t].sReceived]
}
