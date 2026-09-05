module conventions/intent_log/intent_log

/*
 * CONVENTION EXEMPLAR — THE INTENT-LOG PATTERN (DT-027, SAMWISE; origin SPEARHEAD-D3, chartered by
 * MINESWEEPER-Q6, 2026-08-28). Canon: the demand cycle-claim log ruled for P3-I4 (chain A) and the
 * identity-keyed pool movements ruled in SAMWISE-S1 (chain B).
 *
 * THE CONVENTION: a module that must produce an effect in a PEER module's log ("two logs, one
 * fact") first appends RESERVE to an intent log it OWNS whose subject IS the contended peer
 * entity, acts on the peer ONCE (call-first), then appends CONFIRM (citing the peer's committed
 * row) or RELEASE (on the peer's TYPED refusal — never on a timeout). Competing intents are forks
 * on one chain; the peer keeps NO holder knowledge; recovery is the re-drive function of two heads
 * (meta/intent_log `redrive`). What the module `meta/intent_log/intent_log[Key, Sem]` cannot know
 * — and this exemplar shows — is the ATTRIBUTION LAW binding each CONFIRM / RELEASE's `peerView`
 * to the real peer head. Since DT-029 E2 BOTH arms attribute BY CITATION — the peer row's `arche` names the
 * intent it fulfils and the module derives moved-by-this from it (`claim/citationView`, adopted); what the
 * exemplar still supplies is the RESIDUAL split (absent / unmoved / moved-otherwise when not cited). The arms
 * differ in the peer's transition, not in attribution:
 *   - the EXCLUSIVE arm (HOLD chain): the peer act is a transition only one taker can make (`take` on a free
 *     Cart); an UNCITED take (the UI's) reads moved-OTHERWISE on a TAKEN cart — DT-027 §7's uncited-accept
 *     cell — so the owner RELEASEs and detaches instead of confirming; the named PREMISE `takeOnlyByClaimants`
 *     (takes cite their live claim) is what the exclusive-arm LAW rides, never attribution;
 *   - the ADDITIVE arm (MOVEMENT chain): the peer act stacks (`pour` into a Vat) and the peer head cannot
 *     tell one pour from another — only the citation can (`arche` = the RESERVE it fulfils; the runtime's
 *     `arche_id` column + partial unique index, SAMWISE-S1); a late pour citing a RELEASEd intent is
 *     DETECTABLE, and a reversal is itself a new movement intent naming the row it reverses.
 *
 * THE CAST: a Porter (owner) claims Carts (exclusive peer, HOLD) and pours into Vats (additive
 * peer, MOVEMENT). Carts and Vats keep their own logs and never mention porters. Both peers share
 * this file for compactness; in core models they live in DIFFERENT modules and the peer act is a
 * request/reply operation — the design doc carries the mapping.
 */

open meta/profiles/domain_log
open meta/kernel
open meta/subject_log/subject_log[Cart, CartRec] as clog
open meta/subject_log/subject_log[Vat, VatRec] as vlog
open meta/intent_log/semantics as sem              // aliased: the open-parameters below are qualified
open meta/intent_log/intent_log[Cart, sem/HoldSem] as claim   // chain 1: the cart CLAIM (HOLD)
open meta/intent_log/intent_log[Vat, sem/MoveSem]  as pour    // chain 2: the vat POUR (MOVEMENT)

// ── the owner ───────────────────────────────────────────────────────────────────────────────────
/** Porter — the owner: claims carts and pours into vats; identity only (its own log is elided —
    the exemplar reads the porter's holdings FROM THE CLAIM HEAD, the customer's law). */
sig Porter extends Scoped {}
fact PorterRefs { all p: Porter | no p.dataRefs }
/** PorterVersion — an opaque acting version of a porter (`owner_rid`). */
sig PorterVersion {}
/** cartsOf — THE HOLDER DERIVATION: a porter's carts are exactly the carts whose claim head
    names it. No membership record exists to drift. */
fun cartsOf[p: Porter, t: Tick]: set Cart { { c: Cart | claim/holderAt[c, t] = p.eId } }

// ── peer 1: the Cart (exclusive) ────────────────────────────────────────────────────────────────
abstract sig CartStatus {}
one sig C_FREE, C_TAKEN, C_LOADED, C_RETIRED extends CartStatus {}
/** Cart — the exclusive peer: free / taken / retired; knows nothing about who took it. */
sig Cart extends Scoped {}
fact CartRefs { all c: Cart | no c.dataRefs }
sig CartRec extends Snapshot { cStat: one CartStatus }
fact CartRecExtensional { all disj a, b: CartRec | a.cStat != b.cStat }

/** CartAct — the act MARKERS a sub-intent names (the binding is a marker atom, never the act's
    occurrence — which does not exist yet at ACT_RESERVE time, and never the kind SET). */
abstract sig CartAct {}
one sig A_LOAD, A_PARK extends CartAct {}

sig AddCartOcc extends clog/SubjectOcc {} { bindings = subject }   // genesis → FREE
sig TakeOcc    extends clog/SubjectOcc {} { bindings = subject }   // FREE → TAKEN (the exclusive act)
sig LoadOcc    extends clog/SubjectOcc {} { bindings = subject }   // TAKEN → LOADED (an act UNDER the hold: a KEEP sub-intent)
sig ParkOcc    extends clog/SubjectOcc {} { bindings = subject }   // TAKEN/LOADED → FREE (the inverse act; as a sub-intent: CLOSE — ends the hold)
sig RetireOcc  extends clog/SubjectOcc {} { bindings = subject }   // → RETIRED (a peer-side transition the owner cannot prevent)

fun cartStatusAt[c: Cart, t: Tick]: lone CartStatus { clog/recordAt[c, t].cStat }
fun cPre[o: clog/SubjectOcc]: lone CartRec { o.pre & CartRec }
fun cPost[o: clog/SubjectOcc]: lone CartRec { o.post & CartRec }

one sig RCartStarted, RCartUnborn, RCartBusy, RCartFree, RCartGone, RCartNotTaken extends Reason {}
fun addCartViol[o: AddCartOcc]: set Reason { (some clog/priorOn[o]) => RCartStarted else none }
fun takeViol[o: TakeOcc]: set Reason {
  ((no o.pre) => RCartUnborn else none)
  + ((cPre[o].cStat = C_TAKEN) => RCartBusy else none)
  + ((cPre[o].cStat = C_RETIRED) => RCartGone else none)
  + (clog/archeDuplicate[o] => sem/RDuplicateArche else none)   // the idempotent callee on the cart log too (DT-029 Q8: the module fact needs the typed refusal wherever rows cite)
}
fun loadViol[o: LoadOcc]: set Reason {
  ((no o.pre) => RCartUnborn else none)
  + ((cPre[o].cStat != C_TAKEN) => RCartNotTaken else none)
  + (clog/archeDuplicate[o] => sem/RDuplicateArche else none)
}
fun parkViol[o: ParkOcc]: set Reason {
  ((no o.pre) => RCartUnborn else none)
  + ((cPre[o].cStat = C_FREE) => RCartFree else none)
  + ((cPre[o].cStat = C_RETIRED) => RCartGone else none)
  + (clog/archeDuplicate[o] => sem/RDuplicateArche else none)
}
fun retireViol[o: RetireOcc]: set Reason {
  ((no o.pre) => RCartUnborn else none) + ((cPre[o].cStat = C_RETIRED) => RCartGone else none)
}
fact CartAdmission {
  all o: AddCartOcc | (o.admission = Accepted iff no addCartViol[o]) and (o.admission in Rejected implies o.admission.because = addCartViol[o])
  all o: TakeOcc    | (o.admission = Accepted iff no takeViol[o])    and (o.admission in Rejected implies o.admission.because = takeViol[o])
  all o: LoadOcc    | (o.admission = Accepted iff no loadViol[o])    and (o.admission in Rejected implies o.admission.because = loadViol[o])
  all o: ParkOcc    | (o.admission = Accepted iff no parkViol[o])    and (o.admission in Rejected implies o.admission.because = parkViol[o])
  all o: RetireOcc  | (o.admission = Accepted iff no retireViol[o])  and (o.admission in Rejected implies o.admission.because = retireViol[o])
}
fact CartEffects {
  all o: AddCartOcc | committed[o] implies cPost[o].cStat = C_FREE
  all o: TakeOcc    | committed[o] implies cPost[o].cStat = C_TAKEN
  all o: LoadOcc    | committed[o] implies cPost[o].cStat = C_LOADED
  all o: ParkOcc    | committed[o] implies cPost[o].cStat = C_FREE
  all o: RetireOcc  | committed[o] implies cPost[o].cStat = C_RETIRED
}
fact CartSpine { clog/chained and clog/commitAlwaysAccepts }

// ── peer 2: the Vat (additive) ──────────────────────────────────────────────────────────────────
/** Vat — the additive peer: a level that pours stack onto; the head cannot say who poured. */
sig Vat extends Scoped {}
fact VatRefs { all v: Vat | no v.dataRefs }
sig VatRec extends Snapshot { vLevel: one Int }
fact VatRecExtensional { all disj a, b: VatRec | a.vLevel != b.vLevel }

sig AddVatOcc extends vlog/SubjectOcc {} { bindings = subject }   // genesis → level 0
/** PourOcc — the additive act. `arche` — the ORIGIN identity every occurrence carries since DT-029 E1
    (kernel-typed `one Occurrence` since ruling A, no field of its own here) — is bound to the RESERVE the pour fulfils (the
    runtime `arche_id` = the RESERVE's rId, SAMWISE-S1); `reverses` names the pour this pour undoes, if any. */
sig PourOcc extends vlog/SubjectOcc { amount: one Int, reverses: lone PourOcc }   // typed to the kind (B-mov's P4 finding, 2026-09-04:
                                                                                   //   `lone univ` cost |PourOcc|×|univ| bits per command,
                                                                                   //   +58–64 % primary on the receiver canary; `lone PourOcc` is
                                                                                   //   N² — derived bound N²+2N+3 per command, one kind). The
                                                                                   //   discipline stays `ArcheIdentity`'s second clause; the type
                                                                                   //   is not the discipline (the `& PourOcc` reads there are now identity).
  { bindings = subject + amount + arche + reverses }

fun vatLevelAt[v: Vat, t: Tick]: lone Int { vlog/recordAt[v, t].vLevel }
fun vPre[o: vlog/SubjectOcc]: lone VatRec { o.pre & VatRec }
fun vPost[o: vlog/SubjectOcc]: lone VatRec { o.post & VatRec }

one sig RVatStarted, RVatUnborn extends Reason {}
fun addVatViol[o: AddVatOcc]: set Reason { (some vlog/priorOn[o]) => RVatStarted else none }
fun pourViol[o: PourOcc]: set Reason {
  ((no o.pre) => RVatUnborn else none)
  + (vlog/archeDuplicate[o] => sem/RDuplicateArche else none)   // the idempotent callee: a re-sent origin is refused, typed (DT-029 E1)
}
fact VatAdmission {
  all o: AddVatOcc | (o.admission = Accepted iff no addVatViol[o]) and (o.admission in Rejected implies o.admission.because = addVatViol[o])
  all o: PourOcc   | (o.admission = Accepted iff no pourViol[o])   and (o.admission in Rejected implies o.admission.because = pourViol[o])
}
fact VatEffects {
  all o: AddVatOcc | committed[o] implies vPost[o].vLevel = 0
  all o: PourOcc   | committed[o] implies vPost[o].vLevel = plus[vPre[o].vLevel, o.amount]
}
fact VatSpine { vlog/chained and vlog/commitAlwaysAccepts }
/** The vat rows' citation discipline: only the ACT (`pour`) cites — genesis is nobody's leg (a genesis row citing a
    movement intent read as the movement landing: the E2 self-check found it). */
fact VatCitations { all o: AddVatOcc | o.arche = o }

// ── the two intent chains: spine adoption + owner-side bindings ─────────────────────────────────
fact ClaimSpine { claim/spineAdopted }
fact PourSpine  { pour/spineAdopted }
fact ClaimAttribution { claim/citationView }   // DT-029 E2: moved-by-this = a committed peer row cites the intent
fact PourAttribution  { pour/citationView }
fact OwnerBindings {
  all o: claim/HolderOcc | o.holder in Porter.eId           // per instance: a union over two instances' `holder` is ambiguous (knowledge-base)
  all o: pour/HolderOcc  | o.holder in Porter.eId
  all o: claim/TransferOcc | o.from in Porter.eId and o.to in Porter.eId and o.toVersion in PorterVersion
  all o: claim/ReserveOcc | o.ownerVersion in PorterVersion
  all o: pour/ReserveOcc  | o.ownerVersion in PorterVersion
  all o: claim/CitingOcc | o.peerRid in clog/SubjectOcc
  all o: pour/CitingOcc  | o.peerRid in PourOcc
  all r: claim/IntentRec | r.iVersion in PorterVersion
  all r: pour/IntentRec  | r.iVersion in PorterVersion
  all o: claim/ActReserveOcc | (o.act = A_LOAD and o.mode = sem/AM_KEEP) or (o.act = A_PARK and o.mode = sem/AM_CLOSE)   // the two acts under a hold: load KEEPs, park CLOSEs
  all r: claim/IntentRec | some r.iAct implies r.iAct in CartAct
  no pour/ActReserveOcc and no pour/TransferOcc   // MOVEMENT chains carry no sub-intents
}

// ── ARM 1 — the EXCLUSIVE arm (cart claim): the citation attributes; the residual is supplied here ──
/** The cart rows' citation discipline (the counterpart of `ArcheIdentity` for vats): a cart row cites a row of the
    CLAIM chain on its own cart, or nothing — never a pour intent, never another cart's claim (a cart row citing a
    vat's RESERVE would read as that movement landing: the E2 self-check found exactly that). Takes cite the claim's
    opener; acts under the hold cite the pending ACT_RESERVE. */
fact CartCitations {
  all o: TakeOcc + LoadOcc + ParkOcc | o.arche != o implies
    (o.arche in claim/IntentOcc and (o.arche & claim/IntentOcc).subject = o.subject)
  all o: AddCartOcc + RetireOcc | o.arche = o
}
/** takeOnlyByClaimants — THE EXCLUSIVE-ARM PREMISE of the law `takenCartsAreClaimed` (assume when: the peer
    act is performed only by owners holding a live reservation AND cites it — the runtime's `accept` carrying
    the claim's `arche_id`). A NAMED ASSUMPTION, never a fact: a breach — a bare or uncited `take` — stays
    representable, and E2 makes it READ as moved-otherwise instead of moved-by-this (`conv_il_uncitedTake…`).
    Strengthened at E2 with the citation: without it an uncited take at RESERVED lets the owner RELEASE and
    leaves a TAKEN cart with no holder — the very hazard the citation exists to expose. */
pred takeOnlyByClaimants {
  all o: TakeOcc | committed[o] implies
    (claim/phaseAt[o.subject, o.tick] = sem/I_RESERVED and o.arche = claim/openerBefore[o.subject, o.tick])
}
/** cartResidualAt — the RESIDUAL split the applier supplies when NO committed peer row cites the intent
    (D-2): ABSENT before genesis, UNMOVED when free (the peer went back), otherwise MOVED_OTHERWISE — taken
    by someone else (the uncited take, DT-027 §7's uncited-accept cell) or retired. */
fun cartResidualAt[c: Cart, t: Tick]: one sem/PeerView {
  (no clog/recordAt[c, t])           => sem/PV_ABSENT
  else (cartStatusAt[c, t] = C_FREE)  => sem/PV_UNMOVED
  else sem/PV_MOVED_OTHERWISE
}
/** actResidualAt — THE LEVEL RULE's residual: while a sub-intent is pending and its act is UNCITED, the cart
    reads UNMOVED if it still sits in the act's precondition state (retry — `load` needs TAKEN, `park` needs
    TAKEN or LOADED) and MOVED_OTHERWISE if it does not (someone else moved it; the act cannot land). */
fun actResidualAt[c: Cart, act: univ, t: Tick]: one sem/PeerView {
  (no clog/recordAt[c, t])                => sem/PV_ABSENT
  else (act = A_LOAD)                      => ((cartStatusAt[c, t] = C_TAKEN) => sem/PV_UNMOVED else sem/PV_MOVED_OTHERWISE)
  else ((cartStatusAt[c, t] in C_TAKEN + C_LOADED) => sem/PV_UNMOVED else sem/PV_MOVED_OTHERWISE)
}
/** The saga discipline, residual half (the moved-by-this half is `claim/citationView`): every claim CONFIRM /
    RELEASE reads the cart as it is at its tick — at the HOLD level, and at the ACT level for ACT_CONFIRM /
    ACT_RELEASE. */
fact ClaimViews {
  all o: claim/ConfirmOcc + claim/ReleaseOcc | not claim/cited[o] implies o.peerView = cartResidualAt[o.subject, o.tick]
  all o: claim/ActConfirmOcc + claim/ActReleaseOcc | not claim/cited[o] implies o.peerView = actResidualAt[o.subject, claim/iPre[o].iAct, o.tick]
  all o: claim/ConfirmOcc + claim/ReleaseOcc | claim/prePhase[o] = sem/I_HELD implies
    o.peerView = (cartHeadCitesAt[o.subject, o.tick] => sem/PV_MOVED_BY_THIS else cartResidualAt[o.subject, o.tick])   // THE HELD RULE (E2b)
}
/** cartHeadCitesAt — THE HELD RULE's reading (DT-029 Q9 / E2b): the cart's latest committed row at `t` cites a row of
    the hold the cart is under (the opener or a sub-intent after it) — the peer is STILL held by this claim. A later
    third-party row (a retire, a stranger's park) is the head and cites nothing of ours → the residual → a RELEASE ends
    the hold. `cited` cannot say this: it is monotone. Every HOLD-chain seat owes this rule + its theorem check. */
pred cartHeadCitesAt[c: Cart, t: Tick] {
  let h = clog/lastTouch[c, t], r = claim/openerBefore[c, t] |
    some h and some r and h.arche in claim/IntentOcc and (h.arche & claim/IntentOcc).subject = c and notAfter[r.tick, h.arche.tick]
}

// ── ARM 2 — the ADDITIVE arm (vat pour): the citation attributes; the residual is UNMOVED ───────────
/** reserveOf / poursCiting — the exemplar's names for the module's readings (DT-029 E2 moved them in):
    the RESERVE a pour-chain view settles, and the committed pours citing an intent. */
fun reserveOf[o: pour/ViewOcc]: lone pour/ReserveOcc { pour/settledIntent[o] & pour/ReserveOcc }
fun poursCiting[r: pour/ReserveOcc]: set PourOcc { pour/citers[r] & PourOcc }
/** The residual for an additive peer: there is no "otherwise" (another owner's pour does not touch this
    intent) and vats are not minted by porters (no ABSENT) — an uncited view reads UNMOVED. */
fact PourViews { all o: pour/ViewOcc | not pour/cited[o] implies o.peerView = sem/PV_UNMOVED }
/** The peer-row citation discipline (the runtime's `arche_id` column): a pour's arche is a committed RESERVE
    on this vat (strict precedence is the kernel's `ArcheOriginPrecedes`; the cast is needed because `subject`
    is per-instantiation — knowledge-base §3). Uniqueness per (arche, vat) is no longer stated here: it is
    a THEOREM of the `archeDuplicate` refusal in `pourViol` (`conv_il_archeUniquePerVat`), per (arche, subject)
    by construction. Keying is PER LEG (SAMWISE-S1 as ruled): a pour cites its OWN vat's RESERVE; a multi-vat movement
    is N+1 leg intents whose RESERVEs share one ORIGINATOR — that is where one origin spans subjects. */
fact ArcheIdentity {
  all p: PourOcc | p.arche != p implies
    (p.arche in pour/ReserveOcc and committed[p.arche & pour/ReserveOcc] and (p.arche & pour/ReserveOcc).subject = p.subject)
  all p: PourOcc | some p.reverses implies (p.reverses in PourOcc and committed[p.reverses & PourOcc] and (p.reverses & PourOcc).subject = p.subject
                                            and precedes[(p.reverses & PourOcc).tick, p.tick] and p.amount = minus[0, (p.reverses & PourOcc).amount])
}
/** lateAct — the DETECTOR: a committed pour whose cited RESERVE's chain reads FREE at the pour's tick
    (the intent was RELEASEd before the act landed — rule R1 broken by a timeout read as a refusal),
    unless a committed reversal names it. */
pred lateAct[p: PourOcc] {
  committed[p] and p.arche != p and pour/phaseAt[p.subject, p.tick] = sem/I_FREE
  and no q: PourOcc | committed[q] and q.reverses = p
}

// ── the exemplar's laws ─────────────────────────────────────────────────────────────────────────
/** takenCartsAreClaimed — under the exclusive-arm premise (takes cite their live claim), a TAKEN cart is
    always held on the claim chain: the peer's exclusive state is credited to exactly the claim holder. */
pred takenCartsAreClaimed {
  takeOnlyByClaimants implies
    all c: Cart, t: Tick | cartStatusAt[c, t] = C_TAKEN implies some claim/holderAt[c, t]
}
/** holdingsReadTheHead — a porter's carts are exactly the claim heads naming it (definitional:
    there is no second record to disagree). */
pred holdingsReadTheHead {
  all p: Porter, c: Cart, t: Tick | (c in cartsOf[p, t]) iff claim/holderAt[c, t] = p.eId
}
/** confirmedPourCited — a committed pour CONFIRM's reservation has exactly one committed pour
    citing it (the additive arm's attribution + the unique index). */
pred confirmedPourCited {
  all o: pour/ConfirmOcc | committed[o] implies one poursCiting[reserveOf[o]]
}
/** releasedReserveUncited — under rule R1 (RELEASE only on a typed refusal, i.e. no pour landed),
    a committed pour RELEASE's reservation has no pour citing it BEFORE the release — a pour
    citing it AFTER is the late act the detector names. */
pred releasedReserveUncited {
  all o: pour/ReleaseOcc | committed[o] implies no p: poursCiting[reserveOf[o]] | precedes[p.tick, o.tick]
}
/** guarantees — the exemplar's promise. */
pred guarantees { takenCartsAreClaimed and holdingsReadTheHead and confirmedPourCited and releasedReserveUncited }
