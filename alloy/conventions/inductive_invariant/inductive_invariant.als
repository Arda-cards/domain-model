module conventions/inductive_invariant/inductive_invariant

/*
 * CONVENTION EXEMPLAR — THE INDUCTIVE-INVARIANT PROOF (the E7 idiom, DT-024).
 * Canon: the receiving lattice row's proof (soak/sliced/receiver_pool_inductive, 2026-08-24)
 * — the first exclusivity law discharged by state-local checks instead of trace soaking.
 *
 * THE CONVENTION: a time-indexed law over log-carried state ("at any tick, at most one live
 * holder per resource; holders of different kinds never collide") need not be proven by
 * searching whole traces — whose cost scales with TRACE LENGTH. Instead:
 *   1. name an INDUCTIVE INVARIANT: per-kind PROVENANCE (a held resource is EXACTLY some
 *      committed attach act's payload) ∧ own-kind LONE-HOLDER;
 *   2. prove the invariant INDUCTIVE: base (empty history) + step (ANY single real
 *      occurrence preserves it from an ARBITRARY well-formed pre-state);
 *   3. prove the LAW from the invariant STATE-LOCALLY: provenance turns record bindings
 *      into act payloads, and the GENESIS PREMISE (each holder kind mints its resource
 *      inside its own act — a named ASSUMPTION, never a fact) makes the payload sets
 *      pairwise disjoint; `resolve = eId.id` + `EntityIdIsKey` close the argument.
 * Arbitrary pre-states come from a HAVOC SEED KIND declared in the ROOT (frame-free,
 * always committed, strictly before every real occurrence) — sound exactly because the
 * module's admission/effect witnessing is PER-KIND, so seeds are swept only by `chained`
 * (`commitAlwaysAccepts` left with the second gate, TN-003 row 9). Faithfulness asserts tie the root's per-tick slices to the
 * PUBLISHED laws, and vacuity runs prove the obligations range over non-empty
 * configurations. The full apparatus, obligations, and scope-perimeter semantics are in
 * the root: tests/inductive_invariant.als.
 *
 * THE EXEMPLAR: Pegs contended by two holder kinds — a Cubby (grab/drop/tag) and a Hanger
 * (hang/unhang). Grab and Hang name their peg in their own act (the mint); the guard's
 * availability clause refuses a busy peg; the cross-kind law is derived, never stored.
 */

open meta/profiles/domain_log
open meta/kernel
open meta/subject_log/subject_log[Cubby, CubbyRec] as cblog
open meta/subject_log/subject_log[Hanger, HangerRec] as hglog

// ── the contended resource and the two holder subjects ──────────────────────────────────────────
/** Peg — the contended resource; holders reference it by EntityId (soft ref). */
sig Peg extends Scoped {}
fact PegRefs { all p: Peg | no p.dataRefs }

/** Cubby — holder kind 1: holds at most one peg in its record. */
sig Cubby extends Scoped {}
fact CubbyRefs { all c: Cubby | no c.dataRefs }

/** Hanger — holder kind 2: holds at most one peg in its record. */
sig Hanger extends Scoped {}
fact HangerRefs { all h: Hanger | no h.dataRefs }

/** CubbyRec — the cubby's log-carried payload: the held peg, or none. */
sig CubbyRec extends Snapshot { cPeg: lone EntityId }
fact CubbyRecExtensional { all disj a, b: CubbyRec | a.cPeg != b.cPeg }
fact CubbyRecRefIntegrity { all r: CubbyRec | let p = resolve[r.cPeg] | some p implies p in Peg }

/** HangerRec — the hanger's log-carried payload: the held peg, or none. */
sig HangerRec extends Snapshot { hPeg: lone EntityId }
fact HangerRecExtensional { all disj a, b: HangerRec | a.hPeg != b.hPeg }
fact HangerRecRefIntegrity { all r: HangerRec | let p = resolve[r.hPeg] | some p implies p in Peg }

// ── the kinds ───────────────────────────────────────────────────────────────────────────────────
sig MakeCubbyOcc  extends cblog/SubjectOcc {}                        { bindings = subject }
sig GrabOcc       extends cblog/SubjectOcc { peg: lone EntityId }    { bindings = subject + peg }
sig DropOcc       extends cblog/SubjectOcc {}                        { bindings = subject }
/** TagOcc — a pure carry kind: touches the record without moving the peg (the frame case
    the provenance step must survive). */
sig TagOcc        extends cblog/SubjectOcc {}                        { bindings = subject }

sig MakeHangerOcc extends hglog/SubjectOcc {}                        { bindings = subject }
sig HangOcc       extends hglog/SubjectOcc { peg: lone EntityId }    { bindings = subject + peg }
sig UnhangOcc     extends hglog/SubjectOcc {}                        { bindings = subject }

fact CubbyChaining  { cblog/chained }
fact HangerChaining { hglog/chained }

// ── the reasons ─────────────────────────────────────────────────────────────────────────────────
one sig RUnborn,     // any mutator before genesis
        RRebirth,    // a second genesis on the same subject
        RPegBusy,    // grab/hang: the peg is currently held by ANY holder of either kind
        RBareDrop    // drop/unhang with nothing held
        extends Reason {}

// ── read API ────────────────────────────────────────────────────────────────────────────────────
fun cPre  [o: cblog/SubjectOcc]: lone CubbyRec  { o.pre  & CubbyRec }
fun cPost [o: cblog/SubjectOcc]: lone CubbyRec  { o.post & CubbyRec }
fun hPre  [o: hglog/SubjectOcc]: lone HangerRec { o.pre  & HangerRec }
fun hPost [o: hglog/SubjectOcc]: lone HangerRec { o.post & HangerRec }
/** cubbyAt / hangerAt — LOCF reads of the two logs. */
fun cubbyAt [c: Cubby,  t: Tick]: lone CubbyRec  { cblog/recordAt[c, t] }
fun hangerAt[h: Hanger, t: Tick]: lone HangerRec { hglog/recordAt[h, t] }

// ── admission (reason-precise, per kind — see the reason_precise_refusals exemplar) ─────────────
fun makeCubbyViol[o: MakeCubbyOcc]: set Reason { (some cblog/priorOn[o]) => RRebirth else none }
fun grabViol[o: GrabOcc]: set Reason {
  ((no o.pre) => RUnborn else none)
  + ((some p: resolve[o.peg] & Peg |
        (some c: Cubby - o.subject | resolve[cubbyAt[c, o.tick].cPeg] = p)
        or (some h: Hanger | resolve[hangerAt[h, o.tick].hPeg] = p))
     => RPegBusy else none)
}
fun dropViol[o: DropOcc]: set Reason {
  ((no o.pre) => RUnborn else none) + ((some o.pre and no cPre[o].cPeg) => RBareDrop else none)
}
fun tagViol[o: TagOcc]: set Reason { (no o.pre) => RUnborn else none }
fun makeHangerViol[o: MakeHangerOcc]: set Reason { (some hglog/priorOn[o]) => RRebirth else none }
fun hangViol[o: HangOcc]: set Reason {
  ((no o.pre) => RUnborn else none)
  + ((some p: resolve[o.peg] & Peg |
        (some c: Cubby | resolve[cubbyAt[c, o.tick].cPeg] = p)
        or (some h: Hanger - o.subject | resolve[hangerAt[h, o.tick].hPeg] = p))
     => RPegBusy else none)
}
fun unhangViol[o: UnhangOcc]: set Reason {
  ((no o.pre) => RUnborn else none) + ((some o.pre and no hPre[o].hPeg) => RBareDrop else none)
}

fact AdmissionWitness {
  all o: MakeCubbyOcc  | (o.admission = Accepted iff no makeCubbyViol[o])  and (o.admission in Rejected implies o.admission.because = makeCubbyViol[o])
  all o: GrabOcc       | (o.admission = Accepted iff no grabViol[o])       and (o.admission in Rejected implies o.admission.because = grabViol[o])
  all o: DropOcc       | (o.admission = Accepted iff no dropViol[o])       and (o.admission in Rejected implies o.admission.because = dropViol[o])
  all o: TagOcc        | (o.admission = Accepted iff no tagViol[o])        and (o.admission in Rejected implies o.admission.because = tagViol[o])
  all o: MakeHangerOcc | (o.admission = Accepted iff no makeHangerViol[o]) and (o.admission in Rejected implies o.admission.because = makeHangerViol[o])
  all o: HangOcc       | (o.admission = Accepted iff no hangViol[o])       and (o.admission in Rejected implies o.admission.because = hangViol[o])
  all o: UnhangOcc     | (o.admission = Accepted iff no unhangViol[o])     and (o.admission in Rejected implies o.admission.because = unhangViol[o])
}

// ── effects (committed) — per-kind frames; ONLY Grab/Hang set the peg ───────────────────────────
fact EffectWitness {
  all o: MakeCubbyOcc  | committed[o] implies no cPost[o].cPeg
  all o: GrabOcc       | committed[o] implies cPost[o].cPeg = o.peg
  all o: DropOcc       | committed[o] implies no cPost[o].cPeg
  all o: TagOcc        | committed[o] implies cPost[o].cPeg = cPre[o].cPeg
  all o: MakeHangerOcc | committed[o] implies no hPost[o].hPeg
  all o: HangOcc       | committed[o] implies hPost[o].hPeg = o.peg
  all o: UnhangOcc     | committed[o] implies no hPost[o].hPeg
}

// ── the published laws ──────────────────────────────────────────────────────────────────────────
/** cubbyPegProvenance — a cubby-held peg is EXACTLY some committed Grab's payload on that
    cubby (the load-bearing invariant conjunct; a theorem of the frames). */
pred cubbyPegProvenance {
  all c: Cubby, t: Tick | some cubbyAt[c, t].cPeg implies
    (some o: GrabOcc | committed[o] and o.subject = c and notAfter[o.tick, t]
       and cubbyAt[c, t].cPeg = o.peg)
}
/** hangerPegProvenance — the hanger-side mirror. */
pred hangerPegProvenance {
  all h: Hanger, t: Tick | some hangerAt[h, t].hPeg implies
    (some o: HangOcc | committed[o] and o.subject = h and notAfter[o.tick, t]
       and hangerAt[h, t].hPeg = o.peg)
}
/** pegLoneCubby / pegLoneHanger — own-kind lone holder (guard-derived, unconditional). */
pred pegLoneCubby  { all t: Tick, p: Peg | lone { c: Cubby  | resolve[cubbyAt[c, t].cPeg]  = p } }
pred pegLoneHanger { all t: Tick, p: Peg | lone { h: Hanger | resolve[hangerAt[h, t].hPeg] = p } }

/** pegMintDisjoint — THE GENESIS PREMISE (assume when: each holder kind mints its peg
    inside its own act). A NAMED ASSUMPTION, never a fact — a mint-discipline breach stays
    representable (premise false). */
pred pegMintDisjoint {
  all disj a, b: GrabOcc | (committed[a] and committed[b]) implies no (a.peg & b.peg)
  all disj a, b: HangOcc | (committed[a] and committed[b]) implies no (a.peg & b.peg)
  all a: GrabOcc, b: HangOcc | (committed[a] and committed[b]) implies no (a.peg & b.peg)
}

/** pegExclusiveAcrossKinds — the derived CROSS-KIND law: under the premise, no peg is
    simultaneously cubby-held and hanger-held. Never stored; proven from provenance ×2 +
    the premise, state-locally. */
pred pegExclusiveAcrossKinds {
  pegMintDisjoint implies
    all t: Tick, p: Peg |
      (some c: Cubby | resolve[cubbyAt[c, t].cPeg] = p) implies
        (no h: Hanger | resolve[hangerAt[h, t].hPeg] = p)
}

/** guarantees — the exemplar's full promise. */
pred guarantees {
  cubbyPegProvenance and hangerPegProvenance
  and pegLoneCubby and pegLoneHanger
  and pegExclusiveAcrossKinds
}
