module operations/demand/demand_types

/*
 * DEMAND — TYPES (DT-016; DT-017 four-file architecture). The DemandItem is the
 * collection-and-collation shim between card-granularity demand signals and aggregate
 * production (DT-014 rung 2): an "Intent to Produce" a quantity of an Item at its
 * Production/Source Station. IDENTITY derives from (Item, Source Station) — but that pair is
 * NOT unique (R1 amended 2026-07-06: multiple DemandItems per pair coexist in different
 * states; whether multiple OPEN ones are allowed is CALLER POLICY, not a module law — the
 * collation decision belongs to whoever invokes CreateWithCycle/AddCycle). First module of
 * the operations/ domain.
 *
 * PUBLIC OPERATION SURFACE (DT-017 L9): the 15 kinds, the Reason taxonomy, and the read API
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

open meta/profiles/domain_log                        // PROFILE (DT-012): log anatomy + group/order premises
open meta/kernel                                     // Scoped, EntityId, resolve
open meta/subject_log/subject_log[DemandItem, DemandState] as dlog   // the log SPINE (DT-015 Q5)
open meta/subject_log/lifecycle[DemandItem, DemandState] as lc     // the SHAPES: Create / Mutate / Retire (DT-030, 2026-09-09)
open meta/subject_log/subject_log[ProductionDelivery, PDState] as pdlog  // the SECOND subject (§8.1.2, DT-020 build cut 3)
open shared/values                                   // Quantity
open reference_data/item/item_types                  // Item (collation-key target; TYPES only)
open resources/processing_network/processing_network_types   // Station (collation-key target; TYPES only)
open resources/kanban_card/kanban_card_types          // CardCycle + the cycle log surface + KanbanCard (TYPES — DT-017; the kanban four-file cut retired the INTERIM direct open, 2026-07-08)

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

// ── the state record ────────────────────────────────────────────────────────────────────────────
/** DemandState — one moment's mutable payload of a DemandItem (a value; extensional). */
sig DemandState extends Snapshot {
  sStatus:    one  DemandStatus,   // where the task stands (R5)
  sDemandQty: lone Quantity,       // the stored, ADVISORY intent total (R3b): no cone, may float free of the members' sum
  sMembership: set EntityId,       // → CardCycle (soft refs; DEMAND-SIDE ONLY — R2; may retain withdrawn cycles — R7)
  sHolding:   lone EntityId        // → InventoryPool (R8): production deliveries accumulate here; must be EMPTY at Complete
}

// Value semantics: a state IS its fields.
fact DemandStateExtensional {
  all disj a, b: DemandState |
    a.sStatus != b.sStatus or a.sDemandQty != b.sDemandQty or a.sMembership != b.sMembership
    or a.sHolding != b.sHolding
}

// Record-carried refs are TYPED (soft — dangling/cross-Universe allowed; tenancy is guard-side).
fact DemandRefIntegrity {
  all s: DemandState {
    (let h = resolve[s.sHolding] | some h implies h in InventoryPool)
    all m: s.sMembership | let c = resolve[m] | some c implies c in CardCycle
  }
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

// ── the kinds — the 15 operations (product-register names in comments) ─────────────────────────
/** Create — start a card-less demand task (births the DemandItem OPEN, seeds the intent). */
sig CreateDemandOcc extends lc/CreateOcc { qty: lone Quantity }
  { bindings = subject + qty }   // item/station ride the ENTITY (immutable structure), not the payload
/** MemberOcc — the member-addressing kinds' shared field, `member` declared ONCE so union quantifiers over
    these kinds stay unambiguous. A SUBSET sig since 2026-09-09: CreateWithCycle is a Create shape, the other
    three are Mutate shapes, so no `extends` parent can hold all four (the throwaway of that day: two
    declarations of one field are refused over a union receiver; one field on a subset sig is not). */
sig MemberOcc in dlog/SubjectOcc { member: one EntityId }
fact MemberOccExtent {
  MemberOcc = CreateWithCycleOcc + AddCycleOcc + RemoveCycleOcc + DetachWithdrawnOcc
  all o: CreateWithCycleOcc | o.bindings = o.subject + o.qty + o.member
  all o: AddCycleOcc + RemoveCycleOcc + DetachWithdrawnOcc | o.bindings = o.subject + o.member
}
/** CreateWithCycle — start a task from its first demand signal (births + attaches; C/OP
    call-first: the caller invokes the cycle's Accept FIRST, this commit is the saga's gate). */
sig CreateWithCycleOcc extends lc/CreateOcc { qty: lone Quantity }
/** AddCycle — collate a further signal (C/OP call-first, after the cycle's Accept). */
sig AddCycleOcc extends lc/MutateOcc {}
/** RemoveCycle — return a signal to the queue (C/OP call-first, after the cycle's Shelve). */
sig RemoveCycleOcc extends lc/MutateOcc {}
/** DetachWithdrawn — reconcile a withdrawn attachment (R7: the system reaction to the
    cycle-withdrawal notification — CONVERGENT/NOTIFICATION; the same kind is the manual repair). */
sig DetachWithdrawnOcc extends lc/MutateOcc {}
/** AdjustQty — SET the intent total (R3b). */
sig AdjustQtyOcc extends lc/MutateOcc { qty: one Quantity } { bindings = subject + qty }
/** ResetQty — snap the intent to the attached sum (THE arity-4 entrant — Σ semantics CONFINED to
    demand_reset.als + its dedicated root; elsewhere the effect frames everything else and leaves
    sDemandQty unconstrained — R3b confinement). */
sig ResetQtyOcc extends lc/MutateOcc {} { bindings = subject }
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
    (per-member quantities) + the caller's fullness assertion `fills` (intent-capturing — the
    keyed-Quantity partial order may be INDETERMINATE). C/OP call-first: the caller moves each
    fill → READY (cycle CompleteProcessing) first; this commit gates on fills being READY. */
sig DistributeOcc extends lc/MutateOcc { allocation: EntityId -> lone Quantity, fills: set EntityId }
  { bindings = subject + allocation.Quantity + EntityId.allocation + fills }
/** Complete — declare the production run done (R8): requires the holding pool EMPTY and every
    live member SETTLED. C/OP call-first: the caller settles each still-IN_PROCESS member first —
    inventory → CompleteProcessing (READY), none → ProductionFailure (REQUESTING, back in the
    queue); this commit gates on no member left IN_PROCESS. The resulting quantity MAY differ
    from the intent (R3b advisory). */
sig CompleteOcc extends lc/MutateOcc {} { bindings = subject }
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
sig CreateDeliveryOcc extends pdlog/SubjectOcc { pool: lone EntityId } { bindings = subject + pool }
/** RevokeDelivery — terminal reversal (§8.1.1 reversing-entry): the delivery contributes
    nothing from here on; corrections are Revoke + recreate. The caller (the producing
    process) checks its OWN source state per ordinary call-first; the content clause
    (holding ≥ contributed) is RUNTIME + probe (the I3 exclusion). Pairs ATOMICALLY with
    ExtractProduction on the target's log. */
sig RevokeDeliveryOcc extends pdlog/SubjectOcc {} { bindings = subject }

/** demandMutators — the composition/intent mutators under the R5 freeze (OPEN-only, RFrozen). */
fun demandMutators: set dlog/SubjectOcc {
  AddCycleOcc + RemoveCycleOcc + AdjustQtyOcc + ResetQtyOcc + DetachWithdrawnOcc
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
        RNotAttached,       // remove/detach: the cycle is not a member
        RHasCards,          // cancel with attached cycles (R5)
        RBadAllocation,     // distribute: allocation keys / fills outside the live membership (R8)
        RUndistributed,     // complete: the holding pool still has content (R8)
        RNotTerminal        // delete: the subject is not COMPLETE/CANCELED
        extends Reason {}
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

// ── the read API (per-role; L9) ─────────────────────────────────────────────────────────────────
/** dPre / dPost — an occurrence's records, TYPED (the DT-017 Snapshot field-name collision fix:
    `sStatus`/`sMembership` are ambiguous against CycleState in this cone). */
fun dPre [o: dlog/SubjectOcc]: lone DemandState { o.pre  & DemandState }
fun dPost[o: dlog/SubjectOcc]: lone DemandState { o.post & DemandState }
/** preMemberCycles — the LIVE resolved member cycles as an operation reads them (pre-record). */
fun preMemberCycles[o: dlog/SubjectOcc]: set CardCycle {
  { c: CardCycle | (some m: dPre[o].sMembership | resolve[m] = c) and liveCycleAt[c, o.tick] }
}
/** preLiveMemberRefs — the member REFS whose cycles are live as an operation reads them. */
fun preLiveMemberRefs[o: dlog/SubjectOcc]: set EntityId {
  { m: dPre[o].sMembership | some c: CardCycle | resolve[m] = c and liveCycleAt[c, o.tick] }
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
/** attachedAt — the membership refs RESOLVED to cycles (soft refs may dangle out of scope). */
fun attachedAt[d: DemandItem, t: Tick]: set CardCycle {
  { c: CardCycle | some m: demandStateAt[d, t].sMembership | resolve[m] = c }
}
/** attachedLiveAt — membership ∩ live cycles: the EFFECTIVE composition (R7). */
fun attachedLiveAt[d: DemandItem, t: Tick]: set CardCycle {
  { c: attachedAt[d, t] | liveCycleAt[c, t] }
}
/** retiredMembersAt — membership ∖ live cycles: the R7 frozen-state dangle. RECONCILED-class
    surface — non-empty drives the UI indication; never a violation. */
fun retiredMembersAt[d: DemandItem, t: Tick]: set CardCycle {
  attachedAt[d, t] - attachedLiveAt[d, t]
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
