module resources/kanban_card/kanban_card_types

/*
 * KanbanCard + CardCycle — TYPES (DT-017 four-file cut, 2026-07-08; content consolidated from
 * the pre-cut kanban_card.als / card_cycle.als / cycle_state.als / cycle_occurrences.als):
 * the entities, the CycleState record, the status vocabularies, the reified LifecycleConfig,
 * the PUBLIC OPERATION SURFACE (the eleven cycle kinds + the Reason taxonomy — L9), and the
 * read API. Guards, effects, chaining, and the print machine live in
 * kanban_card_implementation.als; the published laws in kanban_card_contracts.als.
 *
 * SPINE (ported 2026-07-08): the cycle log now rides `meta/subject_log[CardCycle, CycleState]`
 * — the spine that was EXTRACTED from this log's hand-built original (DT-015 Q5). The kind
 * subject field is therefore `subject`; the alias `fun cycle` preserves every existing
 * `o.cycle` read (receiver syntax), so consumers and suites are unchanged.
 */

open meta/profiles/domain_log                 // PROFILE (DT-012): the log anatomy (StatefulAction, Tick, verdicts)
open meta/kernel                              // Scoped, Entity, EntityId, resolve
open shared/values                            // Quantity, PhysicalLocator
open meta/state_machine/machine               // State/Signal (the print vocabulary's parents)
open reference_data/item/item_types           // Item (soft-ref target; TYPES only — DT-017)
open resources/processing_network/processing_network_types  // Loop (soft-ref target; TYPES only — DT-017) [KC-MH-5]
open resources/inventory_item/inventory_pool  // InventoryPool — the sPool soft-ref target
open meta/subject_log/subject_log[CardCycle, CycleState] as clog
open meta/subject_log/lifecycle[CardCycle, CycleState] as lc      // the SHAPES: Create / Mutate / Retire (DT-030 M2; cut 2, 2026-09-10)

// ── the operational status vocabulary (a plain enum — the op machine retired at DT-015 B) ──────
/** KanbanCardStatus — the operational lifecycle states. The 8 CORE states are cycle states;
    AVAILABLE is the CARD-level "no live cycle" condition (KC-MH-6) — kept in the vocabulary for
    card-level prose/readings, unrepresentable on cycle records (a CycleState fact). */
abstract sig KanbanCardStatus {}
one sig AVAILABLE, REQUESTING, REQUESTED, IN_PROCESS, READY,
        FULFILLING, FULFILLED, IN_USE, DEPLETED extends KanbanCardStatus {}

// ── the cycle entity: IDENTITY ONLY (immutable for the cycle's whole existence) ─────────────────
/** CardCycle — the identity of one circuit of a KanbanCard; child of KanbanCard (the parent owns
    it). Its mutable payload is the `CycleState` record; the ASSOCIATION between the two is the
    occurrence log (`clog` — the subject_log spine), read back as `stateOfCycleAt[c, t]`. */
sig CardCycle extends Scoped {
  sourcedBy:  lone EntityId,     // the sourcing document — UNTYPED stub until DT-014 rung 3 (Orders) types it
  precededBy: lone CardCycle     // the prior cycle [KC-MH-1: DIRECT ref — flipped from soft for clean acyclicity]
}

// dataRefs = the cycle's outgoing soft references. The BIN is RECORD-carried (CycleState.sPool)
// — not an entity dataRef; typing lives with the record, tenancy with the attach guard.
fact CardCycleRefs { all c: CardCycle | c.dataRefs = c.sourcedBy }

// [KC-MH-2] ordering — acyclic and LINEAR (each cycle ≤1 successor; the `lone` field gives ≤1
// predecessor). With the same-card constraint below, a card's cycles form a single chain.
fact PrecededByAcyclic { no c: CardCycle | c in c.^precededBy }
fact PrecededByLinear  { all p: CardCycle | lone precededBy.p }   // ≤ 1 successor

// ── the state record ────────────────────────────────────────────────────────────────────────────
/** CycleState — one moment's mutable payload of a CardCycle (a value; extensional). */
sig CycleState extends Snapshot {
  sStatus:          one  KanbanCardStatus,   // operational state (core 8 — fact below)
  sLocator:         lone PhysicalLocator,    // where the card is (VALUE ref). Absent = position not
                                             //   operationally tracked on this leg. NB currently
                                             //   DORMANT: no operation writes it yet — the writer
                                             //   arrives with Receiving/moves (DT-014 rung 4)
  sPool:            lone EntityId,           // → InventoryPool (KD12 revised 2026-07-03): the
                                             //   cycle's EXCLUSIVELY-held pool while it lives;
                                             //   absent = the demand leg; attached at
                                             //   StartProcessing (residue allowed); persists into
                                             //   DEPLETED (present-but-empty ≠ detached); dismissed
                                             //   implicitly when the cycle closes
  sQuantityOverride: lone Quantity           // per-cycle override of the card's nominalQuantity
}

// Value semantics: a state IS its fields.
fact CycleStateExtensional {
  all disj a, b: CycleState |
    a.sStatus != b.sStatus or a.sLocator != b.sLocator
    or a.sPool != b.sPool or a.sQuantityOverride != b.sQuantityOverride
}

// The bin ref is TYPED (soft — dangling/cross-Universe allowed): a resolved sPool is an InventoryPool.
// (Tenancy is occurrence-side — the attach guard — since a record cannot know its cycle's tenant.)
fact CyclePoolIntegrity {
  all s: CycleState | let p = resolve[s.sPool] | some p implies p in InventoryPool
}

// KC-MH-6 as a record fact: a cycle state is always one of the 8 core states.
fact CycleStateIsCore { all s: CycleState | s.sStatus != AVAILABLE }

// ── the canonical REGION ORDER over the core states (KD8) — the forward-skip guard's yardstick ──
/** regionRank — the canonical progression position of each core state (REQUESTING first). */
fun regionRank[st: KanbanCardStatus]: one Int {
  st = REQUESTING => 1 else st = REQUESTED => 2 else st = IN_PROCESS => 3
  else st = READY => 4 else st = FULFILLING => 5 else st = FULFILLED => 6
  else st = IN_USE => 7 else st = DEPLETED => 8 else 0   // AVAILABLE: unranked (unreachable on records)
}
/** regionBefore — `a` strictly precedes `b` on the canonical progression. */
pred regionBefore[a, b: KanbanCardStatus] { regionRank[a] < regionRank[b] }
/** regionBetween — `m` sits strictly between `a` and `b` on the progression. */
pred regionBetween[m, a, b: KanbanCardStatus] { regionBefore[a, m] and regionBefore[m, b] }

// ── per-deployment lifecycle configuration (KQ-S9 — reified, not hard-coded) ────────────────────
/** LifecycleConfig — which core statuses this deployment uses; inactive ones are SKIPPED. */
one sig LifecycleConfig { active: set KanbanCardStatus }
fact ConfigWellFormed { LifecycleConfig.active in (KanbanCardStatus - AVAILABLE) }

// ── the kinds — the PUBLIC operation surface (one per Operation, `<Operation>Occ`; L9) ──────────
/** CycleOcc — a CardCycle operation occurrence on the spine; `subject` is the cycle (pre/post are
    its CycleState records — the spine's SubjectOccRecords). */
sig CycleOcc in clog/SubjectOcc {}                 // the WHOLE cycle log, read by kind family (a SUBSET sig since cut 2: the kinds
fact CycleOccIsTheLog { CycleOcc = clog/SubjectOcc }   //   extend the lifecycle SHAPES, and a sig cannot extend two parents)
/** cycle — the reading alias for the spine's `subject` field (receiver syntax: `o.cycle`). */
fun cycle[o: CycleOcc]: one CardCycle { o.subject }

sig RequestOcc            extends lc/CreateOcc { qtyOverride: lone Quantity } { bindings = subject + qtyOverride }   // the GENESIS (Create shape)
// `AcceptOcc` / `StartProcessingOcc` / `ShelveOcc` cite the claim chain's RESERVE / ACT_RESERVE (`arche`) when the act is a
// demand saga's leg (DT-029 E6, chain A) — kanban stays HOLDER-BLIND: the citation discipline is the demand module's fact
// (`operations/demand/demand_claim.als`, `CycleCitations`), never a kanban law.
sig AcceptOcc             extends lc/MutateOcc {} { bindings = subject }
sig ShelveOcc             extends lc/MutateOcc {} { bindings = subject }
sig StartProcessingOcc    extends lc/MutateOcc { pool: one EntityId } { bindings = subject + pool }   // ATTACHES the pool (exclusive while the cycle lives).
  // M1 annotation (DT-020 §8.5.3 / SPEARHEAD-D1 A′-2, MINESWEEPER model-deltas M1): `pool` is
  // the pool the act MINTS for this cycle (ownership-by-genesis) — NEVER a pre-existing pool
  // being attached. See `startViol` (kanban_card_implementation.als) for the freshness guard
  // this annotation implies.
sig CompleteProcessingOcc extends lc/MutateOcc {} { bindings = subject }
sig FulfillOcc            extends lc/MutateOcc {} { bindings = subject }
sig ReceiveOcc            extends lc/MutateOcc {} { bindings = subject }   // status-only: material arrivals are PoolAddOcc events on the attached pool
sig UseOcc                extends lc/MutateOcc {} { bindings = subject }
sig DepleteOcc            extends lc/MutateOcc {} { bindings = subject }   // the ladder's LAST forward status — a transition, not the retire (Q24)
sig WithdrawOcc           extends lc/RetireOcc {} { bindings = subject }   // the ABANDON — the existing tombstone, now a Retire shape (Q24 (a))
/** RetireCycleOcc — the COMPLETION retire (Q24 (a); DT-030 M2): the cycle finished its trip and its history closes. Admitted on a
    cycle open at a COMPLETABLE status (or refused `RCardInCirculation` mid-trip: a cycle mid-trip is withdrawn or it finishes);
    refused `RClosed` when never started or already withdrawn / retired. Effect: the tombstone (`lc/RetireEffect`). Runtime code
    `RETIRE` (D13 §6); `WITHDRAW` keeps its own code. The rollover's closure of the predecessor (a successor's genesis) stays as it
    is until Q25 rules whether it writes this row. */
sig RetireCycleOcc        extends lc/RetireOcc {} { bindings = subject }
sig ProductionFailureOcc  extends lc/MutateOcc {} { bindings = subject }   // IN_PROCESS → REQUESTING (2nd sanctioned backward, R8): the run closed with no inventory for this cycle; the pool DETACHES (back to the demand leg)

/** targetOf — the operation's CANONICAL target status (none for the closing Withdraw). */
fun targetOf[o: CycleOcc]: lone KanbanCardStatus {
  o in RequestOcc => REQUESTING else o in AcceptOcc => REQUESTED
  else o in ShelveOcc => REQUESTING else o in StartProcessingOcc => IN_PROCESS
  else o in CompleteProcessingOcc => READY else o in FulfillOcc => FULFILLING
  else o in ReceiveOcc => FULFILLED else o in UseOcc => IN_USE
  else o in DepleteOcc => DEPLETED
  else o in ProductionFailureOcc => REQUESTING else none
}

/** cycleForwardOps — the strictly-forward kinds (the forward-skip guard family). */
fun cycleForwardOps: set CycleOcc {
  AcceptOcc + StartProcessingOcc + CompleteProcessingOcc + FulfillOcc + ReceiveOcc + UseOcc + DepleteOcc
}

// ── refusal reasons (the taxonomy — public surface) ─────────────────────────────────────────────
one sig RClosed,            // the cycle is not live (never started, withdrawn, or rolled over)
        RBackward,          // target is not strictly forward on the region order
        RInactiveTarget,    // the deployment does not use the target status
        RSkippedActive,     // the jump skips a status the deployment DOES use
        RAlreadyStarted,    // genesis on a cycle that already has committed history
        RCardInCirculation, // genesis while the predecessor cycle is mid-trip (open at a NON-completable status)
        RNotRequested,      // Shelve from a status other than REQUESTED
        RPoolInUse,         // attach: another LIVE cycle currently holds this pool (exclusivity)
        RForeignPool,       // attach: the pool must be in the cycle's tenant
        RPoolWrongItem,     // attach: the pool's Item must be the card's demanded Item (homogeneity — DT-015 R1)
        RPoolNotFresh,      // attach: `o.pool` already has committed pool-log history strictly
                            //   before `o.tick` (M1, DT-020 §8.5.3 — ownership-by-genesis: a
                            //   minted pool is fresh; a used pool is never re-attached)
        RNotInProcess       // ProductionFailure from a status other than IN_PROCESS (R8)
        extends Reason {}

// ── the read API (the projections / notifications surface) ─────────────────────────────────────
/** lastCycleTouch — the latest committed occurrence on `c` at-or-before `t` (the spine's read). */
fun lastCycleTouch[c: CardCycle, t: Tick]: lone CycleOcc { clog/lastTouch[c, t] }
/** stateOfCycleAt — LOCF of records: the cycle's payload as of `t`. */
fun stateOfCycleAt[c: CardCycle, t: Tick]: lone CycleState { clog/recordAt[c, t] }
/** statusAt — the cycle's operational status as of `t`. */
fun statusAt[c: CardCycle, t: Tick]: lone KanbanCardStatus { stateOfCycleAt[c, t].sStatus }
/** closedStrictlyBefore — the cycle was closed before `t`: withdrawn, or its successor's genesis
    committed (the rollover closes the predecessor). */
pred closedStrictlyBefore[c: CardCycle, t: Tick] {
  (some w: lc/RetireOcc | committed[w] and w.subject = c and precedes[w.tick, t])   // withdrawn OR retired (cut 2)
  or (some r: RequestOcc | committed[r] and r.subject.precededBy = c and precedes[r.tick, t])
}
/** closedAt — the cycle is closed as of `t` (withdrawn or rolled over). */
pred closedAt[c: CardCycle, t: Tick] {
  (some w: lc/RetireOcc | committed[w] and w.subject = c and notAfter[w.tick, t])   // withdrawn OR retired (cut 2)
  or (some r: RequestOcc | committed[r] and r.subject.precededBy = c and notAfter[r.tick, t])
}
/** liveCycleAt — started and open as of `t` (the SQ-8 "live" reading). */
pred liveCycleAt[c: CardCycle, t: Tick] { some lastCycleTouch[c, t] and not closedAt[c, t] }

/** completableStatuses — the statuses from which a cycle may be ROLLED OVER by its successor's
    genesis (MP ruling 2026-07-08): once INVENTORY ASSOCIATION IS COMPLETE (READY and beyond),
    any real-world event may flush that inventory (damage, fire, consumption off the books), so
    the new demand signal MUST be admissible — the system cannot insist on the remaining
    statuses being walked. Mid-trip is different in kind: through IN_PROCESS the card is under
    the control of the PRODUCING PROCESS, which remedies issues internally until it completes
    (→ READY) or gives up (→ ProductionFailure) — no end-of-cycle is needed from there. Effect
    on an attached pool: implicit release (exclusivity counts LIVE holders only —
    `poolExclusiveWhileLive`); the pool's items stay at their last known locators (the pool is
    informational, never a locator writer). */
fun completableStatuses: set KanbanCardStatus { READY + FULFILLING + FULFILLED + IN_USE + DEPLETED }
/** rolloverEligible — the predecessor does not block a successor's genesis: already closed, or
    STARTED and open at a completable status (the genesis itself then closes it as COMPLETED —
    rollover). The `some` conjunct is load-bearing: an unstarted predecessor has empty statusAt
    and `∅ in S` is vacuously true (the subset trap, solver-limits) — without it a genesis
    could close a predecessor that never started, breaking closure terminality. */
pred rolloverEligible[c: CardCycle, t: Tick] {
  closedStrictlyBefore[c, t]
  or (some statusAt[c, t] and statusAt[c, t] in completableStatuses)
}

/** completedAt / abandonedAt — the SQ-8 "done" readings, DERIVED from how the cycle closed:
    completed = rolled over (successor genesis, no withdraw); abandoned = withdrawn. Disjoint —
    a withdrawn-then-re-requested predecessor reads ABANDONED only.
    PRECONDITION (guard-dependence): these readings are faithful only over histories admitted
    under `rolloverEligible` — the genesis guard (RCardInCirculation) is what makes
    "rolled over ⇒ completed" sound. On a history containing a committed MID-TRIP rollover
    (inadmissible here, but producible by a runtime deployed without the guard) the honest
    reading is ABANDONED, which this derivation cannot express. The runtime additionally
    STORES the reading at closure (`cycle_closure`, operations PR #288) as a read-side
    denormalization from the status the cycle actually held; under the guard the stored and
    derived readings coincide (deployment ruling 2026-08-20: the storing increment never
    deploys without the guard increment). */
pred completedAt[c: CardCycle, t: Tick] {
  (some r: RequestOcc | committed[r] and r.subject.precededBy = c and notAfter[r.tick, t])
  and (no w: WithdrawOcc | committed[w] and w.subject = c)
}
pred abandonedAt[c: CardCycle, t: Tick] {
  some w: WithdrawOcc | committed[w] and w.subject = c and notAfter[w.tick, t]
}

// ── print vocabulary (the durable artifact — KD3; the machine itself is implementation) ─────────
/** KanbanCardPrintStatus — print/physical-artifact state (PS_-prefixed; UNKNOWN omitted). */
abstract sig KanbanCardPrintStatus extends State {}
one sig PS_NOT_PRINTED, PS_PRINTED, PS_LOST, PS_DEPRECATED, PS_RETIRED extends KanbanCardPrintStatus {}
/** KanbanCardPrintEventType — event driving the print lifecycle (PE_-prefixed). */
abstract sig KanbanCardPrintEventType extends Signal {}
one sig PE_PRINT, PE_REPRINT, PE_LOST, PE_DEPRECATE, PE_RETIRE, PE_DESTROY, PE_UNMARK, PE_NONE
        extends KanbanCardPrintEventType {}
/** KanbanCardPrintEvent — embedded snapshot of the card's last print event. */
sig KanbanCardPrintEvent { type: one KanbanCardPrintEventType }

/** CardSerial — the card's natural identifier, unique within a tenant (opaque). Named distinctly
    from inventory_item's `SerialNumber` (product-instance individualizer) to avoid a cross-module
    type clash; the field stays `serialNumber`. */
sig CardSerial {}

// ── the static card ─────────────────────────────────────────────────────────────────────────────
/** KanbanCard — the static container + the aggregate root of its CardCycles (KD13). */
sig KanbanCard extends Scoped {
  // identity & durable configuration (administrative edits only)
  serialNumber:    one CardSerial,               // CardSerial: distinct from inventory_item's SerialNumber
  itemPin:         one ItemOcc,                  // → Item VERSION PIN (DT-023 R3; was itemRef):
                                                 //   print-immutable classifier; entity-wise reads
                                                 //   via `.subject`; mint-time currency is runtime
                                                 //   (cards have no mint kind in the model)
  nominalQuantity: lone Quantity,                // durable target (overridable per cycle — CycleState.sQuantityOverride)
  loopRef:         lone EntityId,                // → Loop [KC-MH-5 / KD11]
  // the physical/print artifact (durable; spans cycles)
  printStatus:     lone KanbanCardPrintStatus,
  lastPrintEvent:  lone KanbanCardPrintEvent,
  // cycle aggregation (parent→child, ≙ Item.supplies)
  cycles:          set CardCycle                 // direct containment (no back-ref)
}

// Outgoing soft references (cycles is a direct relation, kept in-tenant by CardCycleOwnership;
// the item classifier is a PIN — typed, never dangles — since DT-023 cut 7a).
fact KanbanCardRefs { all k: KanbanCard | k.dataRefs = k.loopRef }

// Pin tenancy (DT-023): kernel isolation reaches only EntityId dataRefs — stated here instead.
fact CardItemPinTenancy { all k: KanbanCard | k.itemPin.subject.tenantId = k.tenantId }

// A resolved loop handle is a Loop (dangling allowed — soft ref; Loop stays EntityId until 7c).
fact LoopRefIntegrity { all k: KanbanCard | let l = resolve[k.loopRef] | some l implies l in Loop }

// Serial numbers are unique within a tenant.
fact SerialNumberUniqueInTenant {
  all disj a, b: KanbanCard | a.tenantId = b.tenantId implies a.serialNumber != b.serialNumber
}

// ── parent→child aggregation & ordering (≙ ItemSupplyOwnership, lives in the parent) ────────────
// Each cycle belongs to exactly one card; children inherit the tenant.
fact CardCycleOwnership {
  all c: CardCycle | one k: KanbanCard | c in k.cycles
  all k: KanbanCard, c: k.cycles | c.tenantId = k.tenantId
}
// [KC-MH-2] the precededBy chain stays within the card's own cycles (siblings), and each card has a
// single chain (one head) — so a card's cycles are one totally-ordered, non-overlapping series.
fact PrecededByWithinCard {
  all k: KanbanCard, c: k.cycles | some c.precededBy implies c.precededBy in k.cycles
}
fact OneChainPerCard { all k: KanbanCard | lone { c: k.cycles | no c.precededBy } }

// Tight by default: no orphan card-local value/handle atoms.
fact NoOrphanSerialNumber   { all s: CardSerial         | s in KanbanCard.serialNumber }
fact NoOrphanPrintEvent     { all e: KanbanCardPrintEvent  | e in KanbanCard.lastPrintEvent }

// ── card-level log readings ─────────────────────────────────────────────────────────────────────
/** currentCycleAt — the card's live (open) cycle as of `t`. `lone` by the published
    one-live-cycle-per-card law (kanban_card_contracts.als). */
fun currentCycleAt[k: KanbanCard, t: Tick]: set CardCycle {
  { c: k.cycles | liveCycleAt[c, t] }
}
/** cardInCirculationAt — the card has a live cycle as of `t`. AVAILABLE (KC-MH-6) ⟺ NOT in
    circulation. */
pred cardInCirculationAt[k: KanbanCard, t: Tick] { some currentCycleAt[k, t] }
