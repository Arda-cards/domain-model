module operations/demand/demand_claim

/*
 * DEMAND — THE CYCLE CLAIM CHAIN (chain A; DT-029 E6; DT-027 §6.1 / §7 the additive arm). The demand item OWNS a
 * HOLD-semantics intent chain keyed by the CARD CYCLE it claims: `addCycle` / `createWithCycle` RESERVE the cycle,
 * kanban's `accept` cites the RESERVE (`arche` on the AcceptOcc — the causal signature of its immediate cause), the
 * demand CONFIRMs from the citation and attaches in the SAME transaction; a hold ends by a RELEASE (the cycle moved
 * otherwise under the hold — withdrawn, shelved by a third party, deleted: SPEARHEAD-D7 Option A) or by the CLOSE-mode
 * sub-intent (`shelve`); `startProcessing` is the KEEP-mode sub-intent. WHO HOLDS a cycle is read from the chain head;
 * membership is the denormalization (`membershipMirrorsHeadAt`, witnessed — the runtime's holding-reconciliation probe
 * repairs membership FROM the heads).
 *
 * ATTRIBUTION IS BY CITATION (the additive arm — `accept` has eight production UI call sites, STOREFRONT d3cd0c6): an
 * uncited accept holds nothing and reads MOVED_OTHERWISE; the exclusive-arm premise `takeOnlyByClaimants` of the D3 rung
 * is NOT assumed here.
 *
 * CONFINED MODULE (the demand_reset.als / demand_movement.als precedent, C-2 of the D6 brief): opened ONLY by its
 * dedicated root (tests/unit/demand_claim.als) and by system roots — never by demand_types. `demandOf` stays the
 * membership read in demand_types; `claimHolderOf` (the head read) lives here with the law relating the two. Phase III
 * ships neither the claim log nor a citing accept path (SPEARHEAD, 2026-09-03T20:13:53Z: "the claim log is out" — a
 * scope decision under D3/D5); this module is the DESIGN the P3-I4 saga is written against, seated nowhere this phase.
 */

open operations/demand/demand_implementation                          // the demand kinds + guards + the demand log (real machinery)
open operations/demand/demand_types as dt   // rule 10: the parameter below was resolving through a transitive open
open meta/subject_log/subject_log[dt/DemandItem, dt/DemandState] as dlog    // re-opened: aliases do not propagate (I-4)
open resources/kanban_card/kanban_card_types as kt                   // aliased: EVERY open parameter is qualified (B-mov's first execution;
open meta/intent_log/semantics as sem                                 //   MINESWEEPER: an unqualified parameter is safe only by accident of scope)
open meta/intent_log/intent_log[kt/CardCycle, sem/HoldSem] as claim   // the claim chain: keyed by the cycle, HOLD semantics

// ── the acts under a hold (the sub-intents; LC-IL-08 / LC-IL-09) ─────────────────────────────────────────────────
/** CycleAct — what the demand does to a cycle it holds: START keeps the hold (the run begins; KEEP), SHELVE closes it
    (the cycle returns to the queue and the demand lets go; CLOSE — one ACT_CONFIRM ends the hold). */
abstract sig CycleAct {}
one sig A_START, A_SHELVE extends CycleAct {}

// ── the instance: spine + attribution (E2 / E2b: the view law is the PARTITION; the HELD rule is ours, below) ──
fact ClaimSpine       { claim/spineAdopted }
fact ClaimAttribution { claim/citationView }

// ── the owner-side bindings (D6 brief B-1..B-5) ────────────────────────────────────────────────────────────────
fact ClaimBindings {
  all o: claim/HolderOcc     | o.holder in DemandItem.eId                     // the holder is a demand
  all o: claim/ReserveOcc    | o.ownerVersion in dlog/SubjectOcc              // the acting demand version (owner_rid)
  all r: claim/IntentRec     | r.iVersion in dlog/SubjectOcc
  all r: claim/IntentRec     | some r.iAct implies r.iAct in CycleAct
  all o: claim/CitingOcc     | o.peerRid in CycleOcc                          // the kanban row the act produced
  all o: claim/ActReserveOcc | (o.act = A_START and o.mode = sem/AM_KEEP) or (o.act = A_SHELVE and o.mode = sem/AM_CLOSE)
  all o: claim/TransferOcc   | o.from in DemandItem.eId and o.to in DemandItem.eId and o.toVersion in dlog/SubjectOcc   // present, no verb (I4)
  all o: claim/HolderOcc | some d: DemandItem | o.holder = d.eId and o.subject.tenantId = d.tenantId   // B-5 tenancy
}
/** ClaimOrigins — a claim row's immediate cause, if it has one, is a row of the demand's own log (a re-drive's probe
    has no row: a claim RESERVE self-mints in the I4 design — Q8's duplicate-cause refusal is the pattern's, unwitnessed
    here because no originator row exists to cite). */
fact ClaimOrigins { all o: claim/IntentOcc | o.arche != o implies o.arche in dlog/SubjectOcc }
/** ClaimLanding — the landing a CONFIRM / ACT_CONFIRM RECORDS is a citer of the intent it settles: a committed peer row citing that
    intent, strictly earlier; and a committed RESERVE's acting demand version is a committed row. Run 1 at 4c35606 (note §8.1): the
    pattern's `citers` counts every committed non-intent Action of ANY log — an ITEM-log row citing the RESERVE let the CONFIRM commit with
    no accept, its `peerRid` a later REFUSED cycle row, the RESERVE's `ownerVersion` a REFUSED demand row: references bound by KIND alone
    where the runtime binds by a committed row (a refused act writes no row). With `ClaimBindings` (`peerRid in CycleOcc`) and
    `CycleCitations` (a cycle row citing a RESERVE is an accept on that cycle) this is the missing link of `heldImpliesAcceptLanded`.
    The foreign citer itself stays legal here — D-2's blindness, and contexts do leak across hops (DT-030) — it just is not OUR landing.
    Consequence made explicit (R-g): a GENESIS leg's CONFIRM has no legal citer under `CycleCitations` until a genesis citation rule exists. */
fact ClaimLanding {
  all o: claim/CitingOcc  | committed[o] implies
    (o.peerRid in claim/citers[claim/settledIntent[o]] and precedes[(o.peerRid & CycleOcc).tick, o.tick])
  all o: claim/ReserveOcc | committed[o] implies committed[o.ownerVersion & dlog/SubjectOcc]
}

// ── the peer rows' citation discipline — law A's shape, scoped to THIS chain's citers ────────────────────────────
/** CycleCitations — a kanban row that cites one of OUR intent rows is on that intent's cycle, cites a COMMITTED row, and
    is the kind the intent expects: an accept cites the opener (a RESERVE); a start-processing / shelve cites the pending
    ACT_RESERVE of its own act (the LEVEL rule — the immediate cause). Genesis and every other kanban kind never cite
    this chain (nobody's leg here). Never "every kanban citation is ours": kanban stays holder-blind. */
fact CycleCitations {
  all o: CycleOcc | o.arche in claim/IntentOcc implies
    (let i = o.arche & claim/IntentOcc | {
      committed[i] and i.subject = o.subject
      o in AcceptOcc + StartProcessingOcc + ShelveOcc
      o in AcceptOcc          implies i in claim/ReserveOcc
      o in StartProcessingOcc implies (i in claim/ActReserveOcc and (i & claim/ActReserveOcc).act = A_START)
      o in ShelveOcc          implies (i in claim/ActReserveOcc and (i & claim/ActReserveOcc).act = A_SHELVE)
    })
}

// ── the residuals (D-2: the applier's split when no committed peer row cites the intent) ───────────────────────
/** cycleResidualAt — HOLD level. ABSENT before the cycle's genesis; a closed cycle (withdrawn / rolled over) is gone;
    REQUESTING reads differently by phase (read STRICTLY BEFORE `t`, `heldBefore` — run 1's mismatch 1): at RESERVED our accept has not landed (UNMOVED — retry), UNDER THE HOLD a third
    party shelved it back (MOVED_OTHERWISE — SPEARHEAD-D7 Option A: the hold is void, RELEASE + detach, never a re-accept
    from under a hold); REQUESTED uncited (a UI accept) and IN_PROCESS-and-beyond are moved under someone else's act.
    UNDER THE HOLD OUR ACCEPT HAS LANDED (MINESWEEPER's chain A review, R-a): a held phase is entered only by a committed
    CONFIRM at RESERVED (`EffectWitness`; transfers and acts need a held prePhase), `confirmViol` refuses an uncited CONFIRM
    (RNotLanded) and the adopted `citationLands` reads a committed one as cited — a committed accept STRICTLY precedes it.
    So "the head cites nothing of ours" at a held tick is a LATER row, never our own accept in flight; the derivation is
    pinned by `heldImpliesAcceptLanded` (checked, `dem_heldImpliesAcceptLanded`), not by the remedy. */
/** heldBefore — a hold is in force STRICTLY BEFORE `t`: the chain's latest committed row before `t` left a held phase. Equal to
    `claim/heldAt` (as-of) at every probe tick, where no intent row sits at `t`; at a view row's OWN tick it reads "before me" — the
    RELEASE's own post-phase (I_FREE) never reaches the residual that decides the RELEASE. Run 1 at 4c35606 found the as-of read:
    `dem_thirdPartyShelveUnderHoldReleases` was UNSAT because the held arm read the RELEASE's own I_FREE and yielded UNMOVED
    (MINESWEEPER's E2 boundary-tick warning, caught by a witness). */
pred heldBefore[c: CardCycle, t: Tick] {
  let h = { r: claim/IntentOcc | committed[r] and r.subject = c and precedes[r.tick, t]
             and (no r2: claim/IntentOcc | committed[r2] and r2.subject = c and precedes[r.tick, r2.tick] and precedes[r2.tick, t]) } |
    some h and claim/iPost[h].iPhase in sem/heldPhases
}
fun cycleResidualAt[c: CardCycle, t: Tick]: one sem/PeerView {
  (no stateOfCycleAt[c, t])           => sem/PV_ABSENT
  else closedAt[c, t]                 => sem/PV_MOVED_OTHERWISE
  else (statusAt[c, t] = REQUESTING)  => (heldBefore[c, t] => sem/PV_MOVED_OTHERWISE else sem/PV_UNMOVED)
  else sem/PV_MOVED_OTHERWISE
}
/** actResidualAt — ACT level (THE LEVEL RULE's residual): both acts under the hold need the cycle at REQUESTED (a start
    goes REQUESTED → IN_PROCESS, a shelve REQUESTED → REQUESTING) — still there, UNMOVED (retry); anywhere else, someone
    moved it (the act cannot land). */
fun actResidualAt[c: CardCycle, t: Tick]: one sem/PeerView {
  (no stateOfCycleAt[c, t])                                 => sem/PV_ABSENT
  else (not closedAt[c, t] and statusAt[c, t] = REQUESTED)  => sem/PV_UNMOVED
  else sem/PV_MOVED_OTHERWISE
}

// ── the views: the residual half + THE HELD RULE (E2b / DT-029 Q9; the exemplar's shape) ────────────────────────
/** cycleHeadCitesAt — the cycle's latest committed row at `t` cites a row of the hold the cycle is under (the opener or
    a sub-intent after it): the cycle is STILL held by this claim. A later third-party row (a withdraw, a stranger's
    shelve) is the head and cites nothing of ours → the residual → a RELEASE ends the hold. `cited` cannot say this: it
    is monotone. Owed by every HOLD-chain seat with its theorem check (`dem_heldViewHeadBased`, E5 S-3). */
pred cycleHeadCitesAt[c: CardCycle, t: Tick] {
  let h = lastCycleTouch[c, t], r = claim/openerBefore[c, t] |
    some h and some r and h.arche in claim/IntentOcc and (h.arche & claim/IntentOcc).subject = c and notAfter[r.tick, h.arche.tick]
}
fact ClaimViews {
  all o: claim/ConfirmOcc + claim/ReleaseOcc       | not claim/cited[o] implies o.peerView = cycleResidualAt[o.subject, o.tick]
  all o: claim/ActConfirmOcc + claim/ActReleaseOcc | not claim/cited[o] implies o.peerView = actResidualAt[o.subject, o.tick]
  all o: claim/ConfirmOcc + claim/ReleaseOcc | claim/prePhase[o] = sem/I_HELD implies
    o.peerView = (cycleHeadCitesAt[o.subject, o.tick] => sem/PV_MOVED_BY_THIS else cycleResidualAt[o.subject, o.tick])   // THE HELD RULE
}

// ── the reads (A-1: the classifier `redrive(claimHead, cycleView)` reads these two) and the detector (A-5) ────────
/** claimHolderOf — WHO holds the cycle: the chain head while the intent is live, nobody otherwise. */
fun claimHolderOf[c: CardCycle, t: Tick]: lone EntityId { claim/liveAt[c, t] => claim/holderAt[c, t] else none }
/** cycleViewAt — the HOLD-level peer view the re-drive reads: under the hold, the head rule; before it, the citation. */
fun cycleViewAt[c: CardCycle, t: Tick]: one sem/PeerView {
  claim/heldAt[c, t] => (cycleHeadCitesAt[c, t] => sem/PV_MOVED_BY_THIS else cycleResidualAt[c, t])
  else (claim/citedAt[c, t] => sem/PV_MOVED_BY_THIS else cycleResidualAt[c, t])
}
/** actViewAt — the ACT-level peer view while a sub-intent pends. */
fun actViewAt[c: CardCycle, t: Tick]: one sem/PeerView { claim/actCitedAt[c, t] => sem/PV_MOVED_BY_THIS else actResidualAt[c, t] }
/** lateAccept — a committed accept whose cited RESERVE's chain reads FREE at the accept's tick: the intent was RELEASEd
    before the act landed (R1 broken by a timeout read as a refusal) — the late-act detector for the claim chain. */
pred lateAccept[o: AcceptOcc] { committed[o] and o.arche in claim/ReserveOcc and claim/phaseAt[o.subject, o.tick] = sem/I_FREE }

// ── the saga's transaction boundary (I4: CONFIRM + attach in ONE transaction; the hold's end + detach in ONE) ────
/** SagaCoupling — the model's "same transaction" is ADJACENCY (`adjacentCommit`, the inventory transfer precedent):
    (a) a committed attach by demand `d` of cycle `c` is the immediately-next committed occurrence after `d`'s CONFIRM on
    `c`; (b) a committed remove follows `d`'s RELEASE or its CLOSE-mode ACT_CONFIRM (the shelve) on `c`; (c) a committed
    detach-withdrawn follows `d`'s RELEASE on `c`. The converse (every CONFIRM is followed by its attach) is the saga's
    liveness, not stated: a crash between the two is the lost-ack window the re-drive closes (`dem_lostAckRedrive`). */
fact SagaCoupling {
  all o: AddCycleOcc + CreateWithCycleOcc | committed[o] implies
    some f: claim/ConfirmOcc | committed[f] and f.subject in resolve[o.member] and f.holder = o.subject.eId and adjacentCommit[f, o]
  all o: RemoveCycleOcc | committed[o] implies
    some e: claim/ReleaseOcc + claim/ActConfirmOcc | committed[e] and (e in claim/ReleaseOcc or claim/closingAct[e])
      and e.subject in resolve[o.member] and e.holder = o.subject.eId and adjacentCommit[e, o]
  all o: DetachWithdrawnOcc | committed[o] implies
    some e: claim/ReleaseOcc | committed[e] and e.subject in resolve[o.member] and e.holder = o.subject.eId and adjacentCommit[e, o]
}

// ── the laws (theorems of the instance + the pattern's guards; checked in the root) ─────────────────────────────
/** membershipMirrorsHeadAt — at a QUIESCENT tick the membership is exactly what the heads say (S-8; D6 L-1 / L-2).
    WITNESSED, not a theorem: between a peer moving otherwise and the saga's RELEASE + detach the two disagree by design
    — the runtime's reconciliation probe repairs membership FROM the heads (instance policy). */
pred membershipMirrorsHeadAt[t: Tick] {
  all d: DemandItem, c: CardCycle | (c in attachedLiveAt[d, t]) iff (claimHolderOf[c, t] = d.eId)
}
/** cycleIndivisibleFromChain — wherever membership mirrors the heads, `cycleIndivisible` (demand_contracts C1) is a
    THEOREM of the chain's `oneLiveHolderPerKey` (LC-IL-02): one head, one holder, one demand. */
pred cycleIndivisibleFromChain { all t: Tick | membershipMirrorsHeadAt[t] implies (all c: CardCycle | lone demandOf[c, t]) }
/** attachRequiresHeld — a committed attach finds the claim chain HELD by this demand at its tick (the C/OP gate reads
    the head, not only the cycle's REQUESTED status — theorem of SagaCoupling (a) + the CONFIRM's effect). */
pred attachRequiresHeld {
  all o: AddCycleOcc + CreateWithCycleOcc | committed[o] implies
    (let c = resolve[o.member] & CardCycle | claim/phaseAt[c, o.tick] = sem/I_HELD and claim/holderAt[c, o.tick] = o.subject.eId)
}
/** detachRequiresReleased — a committed remove / detach-withdrawn finds the chain FREE at its tick (theorem of
    SagaCoupling (b) / (c) + the RELEASE's and the closing ACT_CONFIRM's effects). */
pred detachRequiresReleased {
  all o: RemoveCycleOcc + DetachWithdrawnOcc | committed[o] implies claim/phaseAt[resolve[o.member] & CardCycle, o.tick] = sem/I_FREE
}
/** confirmedAcceptCited — a committed CONFIRM's RESERVE has a citing accept (LC-IL-03 read through E2). */
pred confirmedAcceptCited { all o: claim/ConfirmOcc | committed[o] implies claim/cited[o] }
/** heldImpliesAcceptLanded — at every held tick a committed accept citing the hold's opener strictly precedes `t` (R-a):
    the residual's MOVED_OTHERWISE arm under the hold never classifies our own accept in flight. Theorem of the CONFIRM guard
    (RNotLanded) + `citationLands` + the held-phase entry effects; non-vacuous by `dem_claimArc` (reaches I_HELD). */
pred heldImpliesAcceptLanded {
  all c: CardCycle, t: Tick | claim/heldAt[c, t] implies
    (some a: AcceptOcc | committed[a] and a.subject = c and a.arche = claim/openerBefore[c, t] and precedes[a.tick, t])
}
/** releasedClaimUncited — a committed RELEASE at RESERVED has no citing accept before it (LC-IL-04 read through E2; named apart
    from demand_movement's `releasedReserveUncited` so a system root may open both confined modules;
    at HELD a RELEASE may follow a cited accept — E2b's whole point, `dem_withdrawnUnderHoldReleases`). */
pred releasedClaimUncited { all o: claim/ReleaseOcc | (committed[o] and claim/prePhase[o] = sem/I_RESERVED) implies not claim/cited[o] }
/** claimGuarantees — what a consumer may assume of the chain. */
pred claimGuarantees { confirmedAcceptCited and releasedClaimUncited and attachRequiresHeld and detachRequiresReleased and cycleIndivisibleFromChain }
