module conventions/intent_log/tests/intent_log

open conventions/intent_log/intent_log as il
open meta/intent_log/semantics as sem
// Identical parameters re-open the SAME instances the exemplar built (the DT-024 rule): a root
// cannot see a library's alias for a parametric instance, so it re-opens them under the same names.
open meta/intent_log/intent_log[il/Cart, sem/HoldSem] as claim
open meta/intent_log/intent_log[il/Vat, sem/MoveSem]  as pour
open meta/subject_log/subject_log[il/Vat, il/VatRec] as vlog   // the vat's own log too (E1: its archeUniquePerSubject is checked below)

/*
 * Root for the INTENT-LOG exemplar (DT-027). Tiny scopes; command prefix `conv_il_*`. Verifies the
 * two attribution arms and the crash-window story the pattern exists for: the loser of a race
 * is refused before the peer is touched, the lost acknowledgement is recovered by CONFIRM without
 * a second act, a late additive act is detectable and its reversal is not re-detected, and the
 * owner's holdings are read from the claim head.
 */

// ── ARM 1 (cart claim, HOLD) ────────────────────────────────────────────────────────────────────
/** The full arc: RESERVE → take → CONFIRM; the porter's holdings read the head. */
run conv_il_claimArc {
  some p: Porter, c: Cart, r: claim/ReserveOcc, k: TakeOcc, f: claim/ConfirmOcc | {
    committed[r] and committed[k] and committed[f]
    r.subject = c and k.subject = c and f.subject = c and r.holder = p.eId and f.holder = p.eId and k.arche = r
    precedes[r.tick, k.tick] and precedes[k.tick, f.tick]
    c in cartsOf[p, f.tick] and claim/phaseAt[c, f.tick] = sem/I_HELD
    takeOnlyByClaimants
  }
} for 5 but 5 Int, 2 Porter, 1 Cart, 0 Vat, 2 PorterVersion, 7 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 1

/** Crash window 2 is LEGAL and recoverable: take committed, CONFIRM never appended; the re-drive
    verdict at (RESERVED, moved-by-this) is CONFIRM — no second take. */
run conv_il_lostAckWindow {
  some c: Cart, r: claim/ReserveOcc, k: TakeOcc, t: Tick | {
    committed[r] and committed[k] and r.subject = c and k.subject = c and precedes[r.tick, k.tick] and k.arche = r
    no f: claim/ConfirmOcc | committed[f]
    notAfter[k.tick, t] and claim/phaseAt[c, t] = sem/I_RESERVED and claim/citedAt[c, t]
    claim/redrive[claim/phaseAt[c, t], sem/PV_MOVED_BY_THIS] = sem/RD_CONFIRM
    takeOnlyByClaimants
  }
} for 5 but 5 Int, 1 Porter, 1 Cart, 0 Vat, 1 PorterVersion, 6 Tick, 5 Occurrence, 7 Snapshot, 6 EntityId expect 1

/** The race: two porters reserve one cart; the second is refused RKeyTaken and the cart is taken once. */
run conv_il_raceSerialized {
  some c: Cart, disj a, b: claim/ReserveOcc | {
    committed[a] and refusedAtAdmission[b] and b.admission.because = sem/RKeyTaken
    a.subject = c and b.subject = c and a.holder != b.holder and precedes[a.tick, b.tick]
    lone k: TakeOcc | committed[k] and k.subject = c
    takeOnlyByClaimants
  }
} for 5 but 5 Int, 2 Porter, 1 Cart, 0 Vat, 2 PorterVersion, 6 Tick, 5 Occurrence, 7 Snapshot, 8 EntityId expect 1

/** The peer moves otherwise under a hold (retired): the verdict is RELEASE + detach (the R7 shape). */
run conv_il_retiredUnderHold {
  some c: Cart, f: claim/ConfirmOcc, x: RetireOcc, t: Tick | {
    committed[f] and committed[x] and f.subject = c and x.subject = c and precedes[f.tick, x.tick]
    notAfter[x.tick, t] and claim/phaseAt[c, t] = sem/I_HELD
    claim/redrive[claim/phaseAt[c, t], cartResidualAt[c, t]] = sem/RD_RELEASE_DETACH   // retired: the residual says moved-otherwise
    takeOnlyByClaimants
  }
} for 5 but 5 Int, 1 Porter, 1 Cart, 0 Vat, 1 PorterVersion, 7 Tick, 6 Occurrence, 8 Snapshot, 6 EntityId expect 1

/** KEEP act under the hold: HELD → ACT_RESERVE(load, KEEP) → load → ACT_CONFIRM (view = LOADED) → HELD again. */
run conv_il_loadUnderHold {
  some c: Cart, f: claim/ConfirmOcc, a: claim/ActReserveOcc, k: LoadOcc, b: claim/ActConfirmOcc | {
    committed[f] and committed[a] and committed[k] and committed[b]
    f.subject = c and a.subject = c and k.subject = c and b.subject = c and a.act = A_LOAD and k.arche = a
    precedes[f.tick, a.tick] and precedes[a.tick, k.tick] and precedes[k.tick, b.tick]
    claim/phaseAt[c, b.tick] = sem/I_HELD and claim/holderAt[c, b.tick] = f.holder
    takeOnlyByClaimants
  }
} for 6 but 5 Int, 1 Porter, 1 Cart, 0 Vat, 1 PorterVersion, 8 Tick, 7 Occurrence, 9 Snapshot, 6 EntityId expect 1

/** CLOSE act under the hold (the shelve leg): ACT_RESERVE(park, CLOSE) → park → ONE ACT_CONFIRM that ends
    the hold — the cart is FREE and unheld at that row; no tick reads "held, cart gone back". */
run conv_il_parkClosesHold {
  some c: Cart, f: claim/ConfirmOcc, a: claim/ActReserveOcc, k: ParkOcc, b: claim/ActConfirmOcc | {
    committed[f] and committed[a] and committed[k] and committed[b]
    f.subject = c and a.subject = c and k.subject = c and b.subject = c and a.act = A_PARK and k.arche = a
    precedes[f.tick, a.tick] and precedes[a.tick, k.tick] and precedes[k.tick, b.tick]
    claim/phaseAt[c, k.tick] = sem/I_ACTING
    claim/phaseAt[c, b.tick] = sem/I_FREE and no claim/holderAt[c, b.tick] and cartStatusAt[c, b.tick] = C_FREE
    takeOnlyByClaimants
  }
} for 6 but 5 Int, 1 Porter, 1 Cart, 0 Vat, 1 PorterVersion, 8 Tick, 7 Occurrence, 9 Snapshot, 6 EntityId expect 1

/** DT-027 §7's UNCITED-ACCEPT cell made a theorem (DT-029 E2): a take that does NOT cite the live reservation
    (the UI's eight call sites) reads moved-OTHERWISE, so the owner's verdict at RESERVED is RELEASE — never a
    CONFIRM crediting a stranger's take. No premise assumed. */
run conv_il_uncitedTakeMovedOtherwise {
  some c: Cart, r: claim/ReserveOcc, k: TakeOcc, t: Tick | {
    committed[r] and committed[k] and r.subject = c and k.subject = c and precedes[r.tick, k.tick] and k.arche = k
    notAfter[k.tick, t] and claim/phaseAt[c, t] = sem/I_RESERVED and not claim/citedAt[c, t]
    cartResidualAt[c, t] = sem/PV_MOVED_OTHERWISE
    claim/redrive[claim/phaseAt[c, t], cartResidualAt[c, t]] = sem/RD_RELEASE
    no f: claim/ConfirmOcc | committed[f]
  }
} for 5 but 5 Int, 1 Porter, 1 Cart, 0 Vat, 1 PorterVersion, 6 Tick, 5 Occurrence, 7 Snapshot, 6 EntityId expect 1

assert conv_il_takenCartsAreClaimed { takenCartsAreClaimed }
check conv_il_takenCartsAreClaimed for 5 but 5 Int, 2 Porter, 2 Cart, 0 Vat, 2 PorterVersion, 6 Tick, 6 Occurrence, 8 Snapshot, 10 EntityId expect 0

assert conv_il_holdingsReadTheHead { holdingsReadTheHead }
check conv_il_holdingsReadTheHead for 5 but 5 Int, 2 Porter, 2 Cart, 0 Vat, 2 PorterVersion, 6 Tick, 6 Occurrence, 8 Snapshot, 10 EntityId expect 0

// ── ARM 2 (vat pour, MOVEMENT) ──────────────────────────────────────────────────────────────────
/** The movement arc: RESERVE → pour citing it → CONFIRM (moved-by-this by the citation); the key frees. */
run conv_il_pourArc {
  some v: Vat, r: pour/ReserveOcc, p: PourOcc, f: pour/ConfirmOcc | {
    committed[r] and committed[p] and committed[f]
    r.subject = v and p.subject = v and f.subject = v and p.arche = r
    precedes[r.tick, p.tick] and precedes[p.tick, f.tick]
    pour/phaseAt[v, f.tick] = sem/I_DONE
  }
} for 5 but 5 Int, 1 Porter, 0 Cart, 1 Vat, 1 PorterVersion, 6 Tick, 5 Occurrence, 7 Snapshot, 6 EntityId expect 1

/** Two pours by two sagas: the additive head cannot tell them apart, the citations can. */
run conv_il_twoPoursAttributed {
  some v: Vat, disj r1, r2: pour/ReserveOcc, disj p1, p2: PourOcc | {
    committed[r1] and committed[r2] and committed[p1] and committed[p2]
    r1.subject = v and r2.subject = v and p1.subject = v and p2.subject = v
    p1.arche = r1 and p2.arche = r2
  }
} for 6 but 5 Int, 2 Porter, 0 Cart, 1 Vat, 2 PorterVersion, 8 Tick, 7 Occurrence, 9 Snapshot, 8 EntityId expect 1

/** The LATE ACT is detectable: a pour citing a reservation already RELEASEd (R1 broken upstream). */
run conv_il_lateActDetected {
  some v: Vat, r: pour/ReserveOcc, l: pour/ReleaseOcc, p: PourOcc | {
    committed[r] and committed[l] and committed[p]
    r.subject = v and l.subject = v and p.subject = v and p.arche = r
    precedes[r.tick, l.tick] and precedes[l.tick, p.tick]
    lateAct[p]
  }
} for 5 but 5 Int, 1 Porter, 0 Cart, 1 Vat, 1 PorterVersion, 6 Tick, 5 Occurrence, 7 Snapshot, 6 EntityId expect 1

/** The reversal is NOT re-detected: a reversing pour under its own new intent names the late row,
    and the detector excludes the reversed row. */
run conv_il_reversalExcluded {
  some v: Vat, r: pour/ReserveOcc, l: pour/ReleaseOcc, p: PourOcc, r2: pour/ReserveOcc, q: PourOcc | {
    committed[r] and committed[l] and committed[p] and committed[r2] and committed[q]
    r.subject = v and l.subject = v and p.subject = v and r2.subject = v and q.subject = v
    p.arche = r and q.arche = r2 and q.reverses = p
    precedes[r.tick, l.tick] and precedes[l.tick, p.tick] and precedes[p.tick, r2.tick] and precedes[r2.tick, q.tick]
    not lateAct[p] and not lateAct[q]
  }
} for 7 but 5 Int, 1 Porter, 0 Cart, 1 Vat, 2 PorterVersion, 9 Tick, 8 Occurrence, 10 Snapshot, 6 EntityId expect 1

assert conv_il_confirmedPourCited { confirmedPourCited }
check conv_il_confirmedPourCited for 5 but 5 Int, 2 Porter, 0 Cart, 1 Vat, 2 PorterVersion, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0

assert conv_il_releasedReserveUncited { releasedReserveUncited }
check conv_il_releasedReserveUncited for 5 but 5 Int, 2 Porter, 0 Cart, 1 Vat, 2 PorterVersion, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0

/** The IDEMPOTENT CALLEE (DT-029 E1): a second pour re-sending an origin already committed on the vat is
    refused RDuplicateArche at admission; the first pour stands (the lost-reply retry lands exactly once). */
run conv_il_duplicatePourRefused {
  some v: Vat, r: pour/ReserveOcc, disj p, q: PourOcc | {
    committed[r] and committed[p] and refusedAtAdmission[q] and q.admission.because = sem/RDuplicateArche
    r.subject = v and p.subject = v and q.subject = v and p.arche = r and q.arche = r
    precedes[r.tick, p.tick] and precedes[p.tick, q.tick]
  }
} for 5 but 5 Int, 1 Porter, 0 Cart, 1 Vat, 1 PorterVersion, 6 Tick, 5 Occurrence, 7 Snapshot, 6 EntityId expect 1

// ── E2b (DT-029 Q9): a hold ENDS by RELEASE once the peer moved otherwise; while the peer is ours it cannot ──
/** The missing witness: after a cited take and a CONFIRM, a third party RETIRES the cart; the owner's RELEASE at HELD
    COMMITS, reading the peer as moved-otherwise (the head is the retire, citing nothing of ours). */
run conv_il_releaseAfterRetireUnderHold {
  some c: Cart, k: TakeOcc, f: claim/ConfirmOcc, x: RetireOcc, r: claim/ReleaseOcc | {
    committed[k] and committed[f] and committed[x] and committed[r]
    k.subject = c and f.subject = c and x.subject = c and r.subject = c
    precedes[k.tick, f.tick] and precedes[f.tick, x.tick] and precedes[x.tick, r.tick]
    claim/prePhase[r] = sem/I_HELD and r.peerView = sem/PV_MOVED_OTHERWISE
    takeOnlyByClaimants
  }
} for 5 but 5 Int, 1 Porter, 1 Cart, 0 Vat, 1 PorterVersion, 8 Tick, 7 Occurrence, 8 Snapshot, 6 EntityId expect 1
/** While the cart is still ours (the cited take is the head), a RELEASE at HELD is refused RLanded — the hold ends by
    the CLOSE act (park), never by abandoning a held cart. */
run conv_il_releaseAtHeldWhileOursRefused {
  some c: Cart, k: TakeOcc, f: claim/ConfirmOcc, r: claim/ReleaseOcc | {
    committed[k] and committed[f]
    k.subject = c and f.subject = c and r.subject = c
    precedes[k.tick, f.tick] and precedes[f.tick, r.tick]
    claim/prePhase[r] = sem/I_HELD and r.admission in Rejected and sem/RLanded in r.admission.because
    takeOnlyByClaimants
  }
} for 5 but 5 Int, 1 Porter, 1 Cart, 0 Vat, 1 PorterVersion, 7 Tick, 6 Occurrence, 8 Snapshot, 6 EntityId expect 1
/** THE HELD-RULE THEOREM CHECK (E5 S-3, MINESWEEPER's Q5 point): a seat that forgets its HELD rule turns this SAT. */
assert conv_il_heldViewHeadBased {
  all o: claim/ConfirmOcc + claim/ReleaseOcc | claim/prePhase[o] = sem/I_HELD implies
    ((o.peerView = sem/PV_MOVED_BY_THIS) iff cartHeadCitesAt[o.subject, o.tick])
}
check conv_il_heldViewHeadBased for 5 but 5 Int, 2 Porter, 2 Cart, 0 Vat, 2 PorterVersion, 7 Tick, 7 Occurrence, 8 Snapshot, 8 EntityId expect 0

/** Uniqueness per (arche, vat) is a THEOREM of the refusal in the guard — the seat check E5 names. */
assert conv_il_archeUniquePerVat { vlog/archeUniquePerSubject }
check conv_il_archeUniquePerVat for 5 but 5 Int, 2 Porter, 0 Cart, 1 Vat, 2 PorterVersion, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0

assert conv_il_guarantees { il/guarantees }
check conv_il_guarantees for 5 but 5 Int, 2 Porter, 1 Cart, 1 Vat, 2 PorterVersion, 6 Tick, 6 Occurrence, 8 Snapshot, 10 EntityId expect 0
