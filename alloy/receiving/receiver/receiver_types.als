module receiving/receiver/receiver_types

/*
 * RECEIVER — TYPES (DT-020; DT-017 four-file architecture). The receiving CAPTURE surface
 * (DT-014 rung 4): the Receiver is a mutable bitemporal document on the Order/OrderLine
 * pattern (§8.2 — MP ruling 2026-07-21), mostly INFORMATION RECORDING — its ReceivingLines
 * are determined by the receiving process, not by the Receiver's contents. First module of
 * the receiving/ domain.
 *
 * THREE SUBJECTS on the log spine — the Receiver, its ReceivingLines, and the
 * OrderAttributions (§8.3.3: the attribution is an ENTITY with its own log — the third
 * subject; procurement/order set the two-subject precedent). Composition is ENTITY-CARRIED
 * ON THE CHILD for the lines (the O5 precedent: `receiverRef` immutable, `linesOfReceiver`
 * derived) and RECORD-CARRIED ON THE HOLDER for the attributions (§8.3.1: the line carries
 * `sAttributions`; the attribution carries NO back-ref — held-and-ignorant).
 *
 * THE TWO LAYERS (§8.2 RQ-1 layer split): the capture layer (Receiver + lines,
 * mutable-while-live, frozen by the explicit Complete cascade) and the distribution layer
 * (ProductionDelivery, re-homed to operations/demand §8.1.2 — referenced here only through
 * the line's owner-carried `sDeliveries`, §8.1.3 P2). They meet at RL_RECEIVED without
 * conflict: the captured-facts cluster freezes there; `sDeliveries` stays append-only until
 * RL_DISTRIBUTED (field-scoped freeze).
 *
 * PUBLIC OPERATION SURFACE (DT-017 L9): the 13 kinds, the Reason taxonomy, and the read API
 * live here. Laws are named predicates in receiver_contracts.als; machinery + the same-module
 * pairing facts in receiver_implementation.als; consumers' unit roots open receiver_mock.als.
 *
 * NAMING (Occ ruling (c) + flat-namespace survey): model sigs carry the `Occ` register
 * marker; product surfaces use the bare verb. This cone includes the ORDER module's kinds
 * (AddLineOcc, CloseLineOcc, …) and DEMAND's (CompleteOcc, DistributeOcc), so the receiving
 * kinds take collision-free model names: CreateReceiverOcc / UpdateReceiverOcc /
 * CompleteReceiverOcc; AddReceivingLineOcc / UpdateReceivingLineOcc / AppendAttributionOcc /
 * RemoveAttributionOcc / ReceiveLineOcc / RecordDeliveryOcc / ReleaseLineOcc (the line's
 * `Complete([locator])` — the model name avoids reading as the order's CloseLineOcc twin,
 * and demand owns CompleteOcc; the PRODUCT verb stays "Complete"); AttachAttributionOcc /
 * RecordActualOcc / DetachAttributionOcc. Statuses carry the RV_/RL_ prefixes (the
 * DS_/OS_/PS_ precedent).
 *
 * REASONS: nine atoms are REUSED from this cone with the same semantics one module over
 * (RFrozen, RBadState, RForeignRef, RBadAllocation, RNotAttached from demand; RLineStarted,
 * RLineClosed from order; RWrongItem, RAlreadyMember from the pool; RPoolInUse, RForeignPool
 * from kanban); the receiving-specific atoms are declared below.
 *
 * MODEL SIMPLIFICATIONS (documented, not modeled — design doc §4): receiverNumber (identity
 * is the atom; the number is a runtime writer policy — the orderNumber precedent); notes
 * (occurrence payloads, never record fields — the order precedent); the pre-freeze RUNNING
 * received count (capture-window accumulation is service/UI convenience; the STORED
 * `sReceivedQty` is authoritative from the Receive freeze — §8.4.1: the accepted count is
 * final only there; the capture-window SET rides UpdateReceivingLineOcc); the put-away move
 * bundled in ReleaseLine's `locator` parameter (an ITEM-level move in the resources module —
 * the payload is carried, the move itself is the caller's composite leg, §8.2.1).
 */

open meta/profiles/domain_log                        // PROFILE (DT-012): log anatomy + group/order premises
open meta/kernel                                     // Scoped, EntityId, resolve
open meta/subject_log/subject_log[Receiver, ReceiverState] as rvlog          // the RECEIVER log spine
open meta/subject_log/subject_log[ReceivingLine, ReceivingLineState] as rllog // the LINE log spine
open meta/subject_log/subject_log[OrderAttribution, AttributionState] as oalog // the ATTRIBUTION log spine
open shared/values                                   // Quantity, PhysicalLocator
open shared/note                                     // Note (sNote/sInternalNotes — record-carried; pin `2 Note`)
open meta/keyed_value_algebra/keyed_order            // lte — the Σ-invariant comparisons (§8.3.3 d)
open reference_data/item/item_types                  // Item — the expected-item target (TYPES only)
open reference_data/business_affiliate/business_affiliate_types  // BusinessRole(CARRIER) + BusinessAffiliate — the carrier handles
open resources/inventory_item/inventory_pool         // InventoryPool (+ InventoryItem transitively) — sPool / sBirthPins targets
open operations/demand/demand_types                  // ProductionDelivery + DemandItem (+ CardCycle transitively) — sDeliveries + the lattice reads
open procurement/order/order_types                   // OrderLine — the attribution's downward target (TYPES only)

// ── the status vocabulary ───────────────────────────────────────────────────────────────────────
/** ReceiverStatus — the capture document's two states (§8.2): editable while the receiving
    process runs; COMPLETE by an explicit operator act (the capture-finalization cascade —
    capture ENDS, distribution may continue). */
abstract sig ReceiverStatus {}
one sig RV_EDITING, RV_COMPLETE extends ReceiverStatus {}

/** ReceivingLineStatus — the ruled three-state line machine (§8.2/§8.3): RECEIVING (capture,
    mutable), RECEIVED (captured facts frozen; pool attached; distribution runs), DISTRIBUTED
    (released — custody ends, pool detached). */
abstract sig ReceivingLineStatus {}
one sig RL_RECEIVING, RL_RECEIVED, RL_DISTRIBUTED extends ReceivingLineStatus {}

// ── the carrier pin + header values (§8.2 field list) ───────────────────────────────────────────
// (`CarrierReference` — the denormalized handle — DISSOLVED at DT-023 cut 7b into the
// pin + role-selector pair on the state record and header payloads: sCarrierPin/sCarrierRole
// and carrierPin/carrierRole. Captured facts freeze the PIN — the carrier as it was at
// capture; a retired carrier's past deliveries keep reading their pinned version.)
/** BillOfLading — the shipment document identity (opaque capture value; field-level detail is
    runtime). */
sig BillOfLading {}
/** OperatorName — the responsible receiving operator as CAPTURED INFORMATION (§8.2 — distinct
    from occurrence-level Principal provenance, which records who performed each act
    regardless; opaque capture value). */
sig OperatorName {}
/** OffManifest — the §8.4.2 operator assertion, a presence marker (the D5 `Bool?` rendered as
    a `lone` flag): PRESENT = "this material is NOT on the vendor's manifest" — the
    exceptional-path input; ABSENT = not asserted (the benign default). No law reads it; the
    line classification reading does. */
one sig OffManifest {}

/** RejectionReason — WHY material was refused at the dock (DT-022 TQ-2, MP 2026-08-07:
    Option (b) — a SINGLE reason per line, with RR_OTHER_MULTIPLE as the general relief
    valve for mixed/unlisted causes; the free-form clarification rides the line's `sNote`).
    INERT like sStatedQty — captured evidence for reporting (vendor scorecards, claims);
    no law reads it. A reason with no rejected quantity is legal-but-meaningless (the
    inert-evidence posture). Model enum first; promotable to reference data if tenants
    need extensibility. */
abstract sig RejectionReason {}
one sig RR_DAMAGED, RR_QUALITY, RR_PAPERWORK, RR_OVERAGE_REFUSED, RR_OTHER_MULTIPLE
  extends RejectionReason {}

// The carried-values closure (modeling-conventions §6 — the PDSourceHandle precedent; scope
// hygiene: these atoms exist only where carried). BillOfLading/OperatorName appear on records
// AND on header-occurrence payloads (a refused create legally carries them). The carrier's
// closure fact died with the handle (pins are typed occurrence references).
fact NoOrphanBillOfLading     { all b: BillOfLading     | b in ReceiverState.sBillOfLading + ReceiverHeaderOcc.bol }
fact NoOrphanOperatorName     { all n: OperatorName     | n in ReceiverState.sOperator + ReceiverHeaderOcc.operator }

// ── the entities: IDENTITY + IMMUTABLE STRUCTURE ────────────────────────────────────────────────
/** Receiver — the capture document's identity: one receiving episode at ONE materialization
    Location. `locator` is NORMATIVE (§8.2.1): the dock ≡ this locator — every line's
    inventory is born located here; a shipment landing at two docks takes two Receivers. */
sig Receiver extends Scoped {
  locator: one PhysicalLocator     // NORMATIVE (§8.2.1) — immutable, set at Create
}
fact ReceiverRefs { all r: Receiver | no r.dataRefs }   // the locator is a VALUE; header refs are RECORD-carried

/** ReceivingLine — a line of the capture document, OWNED by its Receiver (composition —
    entity-carried on the child, the O5 precedent: lines never move). Everything else rides
    the log: the expected item is RECORD-carried (§8.3.2 — optional at creation, resolved by
    the clerk no later than Receive), so it lives on ReceivingLineState, not here. */
sig ReceivingLine extends Scoped {
  receiverRef: one EntityId        // → Receiver: the parent (composition)
}
fact ReceivingLineRefs { all l: ReceivingLine | l.dataRefs = l.receiverRef }
fact ReceivingLineRefIntegrity {
  all l: ReceivingLine | let r = resolve[l.receiverRef] | some r implies r in Receiver
}

/** OrderAttribution — the commercial leg (§8.3.3, entity form): attributes a line's receipt
    to ONE OrderLine. `expected` lives in the IDENTITY — frozen at attach BY CONSTRUCTION
    (no freeze law needed); `sActual` rides the log, set-once by the line's Receive. NO
    back-ref to the line (§8.3.1 held-and-ignorant) and NO reconciliation handle (same
    module — that machinery was the price of the cross-module P2 seam). */
sig OrderAttribution extends Scoped {
  orderLineRef: one EntityId,      // → OrderLine (downward; the order module stays ignorant)
  expected:     one Quantity       // the planning facet — IDENTITY placement = the freeze
}
fact OrderAttributionRefs { all a: OrderAttribution | a.dataRefs = a.orderLineRef }
fact OrderAttributionRefIntegrity {
  all a: OrderAttribution | let l = resolve[a.orderLineRef] | some l implies l in OrderLine
}

// ── the state records ───────────────────────────────────────────────────────────────────────────
/** ReceiverState — one moment's header payload of a Receiver (a value; extensional). The
    header fields are the §8.2 capture set; all editable while EDITING, frozen at COMPLETE. */
sig ReceiverState extends Snapshot {
  sStatus:       one  ReceiverStatus,
  sBillOfLading: lone BillOfLading,
  sCarrierPin:   lone BaOcc,          // → BusinessAffiliate VERSION PIN (DT-023 cut 7b; was
                                      //   the CarrierReference handle) — frozen with the
                                      //   captured facts: the carrier AS IT WAS at capture
  sCarrierRole:  lone BusinessRole,   // the CARRIER role selector within the pinned version
  sOperator:     lone OperatorName,
  sInternalNotes: set Note           // INTERNAL notes (DT-022 TQ-7(c) shared mechanism —
                                     //   settles the D5 sNotes gap): editable at ANY time,
                                     //   the one deliberate exemption from the header
                                     //   freeze AND the terminal law; history = the log
}
fact ReceiverStateExtensional {
  all disj a, b: ReceiverState |
    a.sStatus != b.sStatus or a.sBillOfLading != b.sBillOfLading
    or a.sCarrierPin != b.sCarrierPin or a.sCarrierRole != b.sCarrierRole
    or a.sOperator != b.sOperator
    or a.sInternalNotes != b.sInternalNotes
}
// Pin-target agreement was DEFINITIONAL; since QA704 Q4 (a) (DT-009 Q27) it is the RCarrierPinUnsound ARM of the header
// writes (receiver_implementation carrierPinViol) and this pred is its THEOREM over committed writes: pin and
// selector come TOGETHER (DT-023 cut 8 — a carrier link always names its CARRIER role),
// and the selector is a CARRIER role of the PINNED version. Tenancy stays guard-side
// (carrierTenancyViol).
pred receiverCarrierPinAgrees {
  all o: ReceiverHeaderOcc | committed[o] implies {
    some o.carrierPin iff some o.carrierRole
    some o.carrierRole implies roleSelectorAgrees[o.carrierPin, o.carrierRole, CARRIER]
  }
}

/** ReceivingLineState — one moment's payload of a ReceivingLine (a value; extensional). The
    CAPTURED-FACTS cluster (§8.3.4/§8.3.5 — frozen at RL_RECEIVED): sExpectedItem,
    sExpectedQty, sStatedQty, sOffManifest, sReceivedQty, sRejectedQty, sBirthPins,
    sAttributions. The LIVE operational refs: sPool (attached at Receive, detached at
    release) and sDeliveries (append-only until RL_DISTRIBUTED — §8.1.3 field-scoped). */
sig ReceivingLineState extends Snapshot {
  sStatus:       one  ReceivingLineStatus,
  sExpectedItem: lone ItemOcc,       // → Item VERSION PIN (DT-023 R3; §8.3.2: optional at creation;
                                     //   floating in the capture window — each write re-pins current —
                                     //   FROZEN with the captured facts at Receive)
  sExpectedQty:  lone Quantity,      // the ORDER's position (open qty at creation; absent = blind)
  sStatedQty:    lone Quantity,      // the VENDOR's claim (§8.3.4 — optional, INERT: no law reads it)
  sReceivedQty:  lone Quantity,      // OUR count of ACCEPTED material (§8.3.5; none = the keyed zero)
  sRejectedQty:  lone Quantity,      // refused at the dock, never born (§8.3.5; present = rejection happened)
  sOffManifest:  lone OffManifest,   // the §8.4.2 operator assertion (exceptional path only)
  sRejectionReason: lone RejectionReason, // WHY the dock refused (DT-022 TQ-2 — inert
                                     //   evidence; lands AT Receive with the final counts)
  sNote:         lone Note,          // the operator's free-form receiving-time clarification
                                     //   (DT-022 TQ-2 qual. 2 — the shared Note mechanism;
                                     //   lands AT Receive; frozen with the captured facts)
  sBirthPins:    set  EntityId,      // → InventoryItem: the born items, PINNED at the line's own
                                     //   Receive tick (§8.3.5/§7 note 3: against a log-carried
                                     //   target the log itself expresses the pin — the pinned
                                     //   view is `birthPinViewOf`, the state AT the Receive tick)
  sPool:         lone EntityId,      // → InventoryPool: LIVE operational truth (§8.2.1 — custody
                                     //   is the DERIVED reading "pool attached to a live line")
  sDeliveries:   set  EntityId,      // → ProductionDelivery (§8.1.3 P2: owner-carried, append-only)
  sAttributions: set  EntityId       // → OrderAttribution (§8.3.1: owner-carried; membership
                                     //   frozen at RL_RECEIVED; the members' own logs stay live)
}
fact ReceivingLineStateExtensional {
  all disj a, b: ReceivingLineState |
    a.sStatus != b.sStatus or a.sExpectedItem != b.sExpectedItem
    or a.sExpectedQty != b.sExpectedQty or a.sStatedQty != b.sStatedQty
    or a.sReceivedQty != b.sReceivedQty or a.sRejectedQty != b.sRejectedQty
    or a.sOffManifest != b.sOffManifest or a.sRejectionReason != b.sRejectionReason
    or a.sNote != b.sNote or a.sBirthPins != b.sBirthPins
    or a.sPool != b.sPool or a.sDeliveries != b.sDeliveries or a.sAttributions != b.sAttributions
}
// Record-carried refs are TYPED (soft — dangling/cross-Universe allowed; tenancy is guard-side).
fact ReceivingLineStateRefIntegrity {
  all s: ReceivingLineState {
    (let p = resolve[s.sPool]         | some p implies p in InventoryPool)
    all b: s.sBirthPins    | let ii = resolve[b] | some ii implies ii in InventoryItem
    all d: s.sDeliveries   | let pd = resolve[d] | some pd implies pd in ProductionDelivery
    all m: s.sAttributions | let a  = resolve[m] | some a  implies a in OrderAttribution
  }
}

/** AttributionState — one moment's payload of an OrderAttribution (a value; extensional).
    NO status field — the phase is derivable (started / actual-recorded / detached). */
sig AttributionState extends Snapshot { sActual: lone Quantity }
fact AttributionStateExtensional { all disj a, b: AttributionState | a.sActual != b.sActual }

// ── the kinds — RECEIVER subject (product-register names in comments) ───────────────────────────
/** ReceiverHeaderOcc — the abstract parent of the header-writing kinds: the §8.2 header
    payload declared ONCE (SET semantics — the payload IS the new header, the AdjustQty
    precedent; absent = cleared). */
abstract sig ReceiverHeaderOcc extends rvlog/SubjectOcc {
  carrierPin:  lone BaOcc,           // → BA VERSION PIN (DT-023 cut 7b; was CarrierReference)
  carrierRole: lone BusinessRole,    // the CARRIER role selector within the pinned version
  bol:      lone BillOfLading,
  operator: lone OperatorName
}
/** Create — start a receiving episode (births EDITING; the locator rides the ENTITY —
    immutable, NORMATIVE §8.2.1). */
sig CreateReceiverOcc extends ReceiverHeaderOcc {} { bindings = subject + carrierPin + carrierRole + bol + operator }
/** Update — edit the header while capturing (every edit an occurrence — audit free; §8.2). */
sig UpdateReceiverOcc extends ReceiverHeaderOcc {} { bindings = subject + carrierPin + carrierRole + bol + operator }
/** Complete — END CAPTURE by explicit operator act (§8.2): the capture-finalization cascade
    is the CALLER's composite (drive each not-yet-finalized line's Receive first — the
    demand-Complete-settles-members shape, same-module); this commit GATES on no child line
    still RL_RECEIVING. Distribution may continue after (lines RL_RECEIVED stay serviceable). */
sig CompleteReceiverOcc extends rvlog/SubjectOcc {} { bindings = subject }
/** Annotate — SET the Receiver's INTERNAL notes (any state, including RV_COMPLETE —
    DT-022 TQ-7(c): internal notes are editable at ANY time, the one deliberate exemption
    from the header freeze and the terminal law; the payload IS the new note set, history
    rides the log). */
sig AnnotateReceiverOcc extends rvlog/SubjectOcc { notes: set Note } { bindings = subject + notes }

// ── the kinds — LINE subject ────────────────────────────────────────────────────────────────────
/** AddLine — line genesis (S3prep-A): from scratch (blind when no expected qty — the
    Undetermined reading) or from an OrderLine — in which case the line is born WITH its
    OrderAttribution in one atomic receiving-module act (§8.3.1: `attribution` names the
    atom whose AttachAttribution genesis pairs with this commit — the same-module pairing,
    enforced in the implementation). */
sig AddReceivingLineOcc extends rllog/SubjectOcc {
  item:        lone ItemOcc,     // → Item VERSION PIN (DT-023 R3; optional at creation — §8.3.2)
  expectedQty: lone Quantity,    // the order's open quantity at creation (absent = blind)
  attribution: lone EntityId     // → OrderAttribution (present ⟺ order-connected birth)
} { bindings = subject + item + expectedQty + attribution }
/** UpdateLine — SET the capture-window expectation/evidence cluster (§8.3.2 item resolution,
    §8.3.4 stated facet, §8.4.2 off-manifest assertion, the running received count; SET
    semantics — the payload IS the new cluster). */
sig UpdateReceivingLineOcc extends rllog/SubjectOcc {
  item:        lone ItemOcc,
  expectedQty: lone Quantity,
  statedQty:   lone Quantity,
  receivedQty: lone Quantity,
  offManifest: lone OffManifest
} { bindings = subject + item + expectedQty + statedQty + receivedQty + offManifest }
/** LineAttributionOcc — the abstract parent of the membership-editing kinds (`attribution`
    declared once — the MemberOcc precedent). */
abstract sig LineAttributionOcc extends rllog/SubjectOcc { attribution: one EntityId }
/** AttachAttribution(line side) — append an attribution to the membership (an ordinary
    pre-RECEIVED capture edit — §8.3.3 sub-ruling; pairs with the attribution's genesis). */
sig AppendAttributionOcc extends LineAttributionOcc {} { bindings = subject + attribution }
/** DetachAttribution(line side) — remove a member pre-RECEIVED (pairs with the attribution's
    tombstone; the delete-recreate escape hatch rides this pair). */
sig RemoveAttributionOcc extends LineAttributionOcc {} { bindings = subject + attribution }
/** Receive — THE FREEZE (§8.4.1 single genesis): one atomic act — items born LOCATED at
    Receiver.locator (the caller's resources-side legs precede this commit, call-first),
    the line's pool attached (BORN WITH the line's act — §8.5.3 ownership-by-genesis; no
    custody machinery), `sBirthPins` stamped from the genesis call's returned birth records,
    the attribution `sActual` fan-out committed (the same-module pairing), captured facts
    frozen. `receivedQty` is the FINAL accepted count (genesis births exactly it — §8.3.5);
    a fully-rejected line (receivedQty none, rejectedQty present) births nothing and
    attaches no pool (ReceiveBirthsPooled below). `allocation` is the CALLER-SUPPLIED
    actual split (the Distribute data-driven-matrix precedent; pro-rata is service-level). */
sig ReceiveLineOcc extends rllog/SubjectOcc {
  receivedQty: lone Quantity,               // the ACCEPTED count (none = the keyed zero)
  rejectedQty: lone Quantity,               // refused at the dock (§8.3.5)
  rejectionReason: lone RejectionReason,    // WHY (DT-022 TQ-2 — with the final counts; inert)
  lineNote:    lone Note,                   // the operator's clarification (TQ-2 qual. 2; inert)
  pool:        lone EntityId,               // → InventoryPool — the line's pool, minted in this act
  birthPins:   set  EntityId,               // → InventoryItem — the born items (pin ≡ this tick)
  allocation:  EntityId -> lone Quantity    // attribution → actual (caller-supplied split)
} { bindings = subject + receivedQty + rejectedQty + rejectionReason + lineNote + pool + birthPins + allocation.Quantity + EntityId.allocation }
/** RecordDelivery — the line's own commit closing the distribute C/OP (§8.1.3): after the
    demand-side PD.Create (the caller's first leg), append the PD ref to `sDeliveries` —
    IDEMPOTENT by set semantics (a retry's re-append is a no-op append, never a refusal). */
sig RecordDeliveryOcc extends rllog/SubjectOcc { delivery: one EntityId } { bindings = subject + delivery }
/** Complete([locator]) — RELEASE the line (§8.2.1/C3: a caller act, never automatic): custody
    ends (the derived reading — the pool detaches; it persists, user-manipulable, never
    re-held §8.5.1); the locator parameter is an optional bundled put-away move (an
    item-level move, the caller's composite leg — items may simply remain at the dock). */
sig ReleaseLineOcc extends rllog/SubjectOcc { putAway: lone PhysicalLocator } { bindings = subject + putAway }

// ── the kinds — ATTRIBUTION subject (§8.3.3) ────────────────────────────────────────────────────
/** AttachAttribution — attribution genesis: born inside the line's own attach act (ownership
    by genesis — composed atomically with AddReceivingLine's attribution arm or with a
    line-side AppendAttribution; the pairing facts are the implementation's rendering of the
    ONE receiving-module tx). The `expected` facet rides the ENTITY. */
sig AttachAttributionOcc extends oalog/SubjectOcc {} { bindings = subject }
/** RecordActual — the set-once actual facet, driven by the line's Receive (§8.3.3 b/c: ONE
    atomic fan-out across the line log and the attribution logs — the pairing fact; never a
    standalone act). Post-RECEIVED corrections are recorded-axis territory (out of model). */
sig RecordActualOcc extends oalog/SubjectOcc { actual: one Quantity } { bindings = subject + actual }
/** DetachAttribution — the pre-RECEIVED tombstone (pairs with the line-side Remove; the
    membership freeze itself rides the LINE's guard — this subject stays line-ignorant). */
sig DetachAttributionOcc extends oalog/SubjectOcc {} { bindings = subject }

// ── definitional capture (the refused-vs-unrepresentable distinction) ───────────────────────────
/** Births and the pool arrive TOGETHER (§8.4.1/§8.5.3): the composite mints the pool exactly
    when genesis births items — the caller never supplies one without the other, so a
    mismatch is UNREPRESENTABLE (a type-level fact, not a Reason; the ItemLinePinAgrees
    precedent). */
fact ReceiveBirthsPooled { all o: ReceiveLineOcc | some o.pool iff some o.birthPins }

/** receiverHeaderMutators — the header-editing kinds under the §8.2 freeze (EDITING-only). */
fun receiverHeaderMutators: set rvlog/SubjectOcc { UpdateReceiverOcc }
/** lineCaptureMutators — the capture-window mutators under the RL_RECEIVING freeze (§8.3). */
fun lineCaptureMutators: set rllog/SubjectOcc {
  UpdateReceivingLineOcc + AppendAttributionOcc + RemoveAttributionOcc
}
/** rvOccKinds / rlOccKinds / oaOccKinds — the module families, alias-free for roots. */
fun rvOccKinds: set rvlog/SubjectOcc { rvlog/SubjectOcc }
fun rlOccKinds: set rllog/SubjectOcc { rllog/SubjectOcc }
fun oaOccKinds: set oalog/SubjectOcc { oalog/SubjectOcc }

// ── refusal reasons (receiving-specific; nine atoms reused from this cone — header note) ────────
one sig RReceiverStarted,    // create: this receiver already has committed history (genesis-once)
        RReceiverClosed,     // the receiver is unusable (never started, or a dangling parent ref)
        RLinesReceiving,     // receiver complete: a child line is still RL_RECEIVING (the
                             //   RLinesOpen precedent — the caller's cascade legs come first)
        RNoItem,             // receive: births require the expected item RESOLVED by now (§8.3.2)
        ROverAttributed,     // attach: Σ expected(attributions) would exceed sExpectedQty (§8.3.3 d)
        ROverAllocated,      // receive: Σ allocation would exceed the accepted count (§8.3.3 d)
        RActualRecorded,     // record-actual: the set-once facet is already present (§8.3.3 b)
        RAttributionStarted, // attach: this attribution already has committed history (genesis-once)
        RAttributionClosed,  // the attribution is unusable (never started, or detached)
        RCarrierPinUnsound,  // QA704 Q4 (a), DT-009 Q27: a header write whose carrier pin and role selector do not come together or agree (was the fact ReceiverCarrierPinAgrees)
        RCarrierPinStale     // QA704 Q4 (a): a header write pinning a carrier version not current at the write (was the fact CarrierPinCurrency); RItemPinStale on the line writes is the item log's atom, reused
        extends Reason {}

// ── the read API (per-role; L9) ─────────────────────────────────────────────────────────────────
/** rvPre / rvPost / rlPre / rlPost / oaPre / oaPost — an occurrence's records, TYPED (the
    DT-017 Snapshot field-name collision fix, per subject). */
fun rvPre [o: rvlog/SubjectOcc]: lone ReceiverState { o.pre  & ReceiverState }
fun rvPost[o: rvlog/SubjectOcc]: lone ReceiverState { o.post & ReceiverState }
fun rlPre [o: rllog/SubjectOcc]: lone ReceivingLineState { o.pre  & ReceivingLineState }
fun rlPost[o: rllog/SubjectOcc]: lone ReceivingLineState { o.post & ReceivingLineState }
fun oaPre [o: oalog/SubjectOcc]: lone AttributionState { o.pre  & AttributionState }
fun oaPost[o: oalog/SubjectOcc]: lone AttributionState { o.post & AttributionState }

/** receiverStateAt / receiverStatusAt — LOCF reads of the receiver log. */
fun receiverStateAt [r: Receiver, t: Tick]: lone ReceiverState { rvlog/recordAt[r, t] }
fun receiverStatusAt[r: Receiver, t: Tick]: lone ReceiverStatus { receiverStateAt[r, t].sStatus }

/** rlStateAt / rlStatusAt — LOCF reads of the line log (rl-prefixed: the order module owns
    `lineStateAt` in this cone). */
fun rlStateAt [l: ReceivingLine, t: Tick]: lone ReceivingLineState { rllog/recordAt[l, t] }
fun rlStatusAt[l: ReceivingLine, t: Tick]: lone ReceivingLineStatus { rlStateAt[l, t].sStatus }

/** oaStateAt — LOCF read of the attribution log. */
fun oaStateAt[a: OrderAttribution, t: Tick]: lone AttributionState { oalog/recordAt[a, t] }
/** attributionDetachedAt — a committed Detach tombstone exists at-or-before `t`. */
pred attributionDetachedAt[a: OrderAttribution, t: Tick] {
  some d: DetachAttributionOcc | committed[d] and d.subject = a and notAfter[d.tick, t]
}
/** liveAttributionAt — started and not detached. */
pred liveAttributionAt[a: OrderAttribution, t: Tick] {
  oalog/startedAt[a, t] and not attributionDetachedAt[a, t]
}

/** parentReceiverOf — the line's Receiver (entity-carried composition). */
fun parentReceiverOf[l: ReceivingLine]: lone Receiver { resolve[l.receiverRef] & Receiver }
/** linesOfReceiver — the ENTITY composition read (no record-side line set exists). */
fun linesOfReceiver[r: Receiver]: set ReceivingLine { { l: ReceivingLine | parentReceiverOf[l] = r } }

/** attributionsAt — the line's attribution members, RESOLVED (soft refs may dangle). */
fun attributionsAt[l: ReceivingLine, t: Tick]: set OrderAttribution {
  { a: OrderAttribution | some m: rlStateAt[l, t].sAttributions | resolve[m] = a }
}

/** receiveTickOf — the line's Receive instant: the PIN COORDINATE of its birth pins (§7 note:
    against a log-carried target, `recordAt` at this tick IS the pinned view — at most one by
    the RL_RECEIVING-only guard). */
fun receiveTickOf[l: ReceivingLine]: lone Tick {
  { t: Tick | some o: ReceiveLineOcc | committed[o] and o.subject = l and o.tick = t }
}
/** birthPinViewOf — the RECEIPT-TIME reading of a born item: its state AT the line's Receive
    tick, immune to the item's later history (§8.3.5 — the audit pin; the item's live state
    remains readable through the ordinary `stateAt`). */
fun birthPinViewOf[l: ReceivingLine, ii: InventoryItem]: lone InventoryItemState {
  stateAt[ii, receiveTickOf[l]]
}

// ── the classification readings (§8.4.2, derived — stored NOWHERE) ─────────────────────────────
/** lineOrderDrivenAt — order linkage present (attributions live on the membership). */
pred lineOrderDrivenAt[l: ReceivingLine, t: Tick] { some rlStateAt[l, t].sAttributions }
/** lineUnexpectedAt — no linkage + the operator's explicit off-manifest assertion. */
pred lineUnexpectedAt[l: ReceivingLine, t: Tick] {
  no rlStateAt[l, t].sAttributions and some rlStateAt[l, t].sOffManifest
}
/** lineBlindAt — no linkage otherwise (manifest-backed — the benign, normal case; note
    `sStatedQty` plays NO part: pure evidence, never a classifier — §8.4.2). */
pred lineBlindAt[l: ReceivingLine, t: Tick] {
  rllog/startedAt[l, t] and no rlStateAt[l, t].sAttributions and no rlStateAt[l, t].sOffManifest
}

// ── the fulfillment readings (§8.3 RQ-2a, derived over (ExpectedQty, ReceivedQty, status)) ─────
/** lineUndeterminedAt — no expectation: precisely the blind-receiving case. */
pred lineUndeterminedAt[l: ReceivingLine, t: Tick] {
  rllog/startedAt[l, t] and no rlStateAt[l, t].sExpectedQty
}
/** linePartiallyReceivedAt — expectation present ∧ received strictly below it. */
pred linePartiallyReceivedAt[l: ReceivingLine, t: Tick] {
  let s = rlStateAt[l, t] | some s.sExpectedQty
    and lte[qtyMap[s.sReceivedQty], qtyMap[s.sExpectedQty]]
    and qtyMap[s.sReceivedQty] != qtyMap[s.sExpectedQty]
}
/** lineFullyReceivedAt — RECEIVED ∧ expectation met exactly (the deliberate asymmetry:
    mid-process equality is NOT "fully received" — the judgment is made only at the freeze). */
pred lineFullyReceivedAt[l: ReceivingLine, t: Tick] {
  let s = rlStateAt[l, t] | s.sStatus in RL_RECEIVED + RL_DISTRIBUTED
    and some s.sExpectedQty and qtyMap[s.sReceivedQty] = qtyMap[s.sExpectedQty]
}
/** lineOverReceivedAt — expectation present ∧ received strictly above it. */
pred lineOverReceivedAt[l: ReceivingLine, t: Tick] {
  let s = rlStateAt[l, t] | some s.sExpectedQty
    and lte[qtyMap[s.sExpectedQty], qtyMap[s.sReceivedQty]]
    and qtyMap[s.sReceivedQty] != qtyMap[s.sExpectedQty]
}
