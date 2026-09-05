module conventions/inductive_invariant/tests/inductive_invariant

/*
 * THE INDUCTIVE-INVARIANT APPARATUS — the root half of the convention (the library holds
 * the domain and the published laws; the root holds the proof machinery, because havoc
 * seeds and per-tick slices are VERIFICATION scaffolding, never module surface).
 *
 * Obligations (all four + faithfulness + vacuity — the E7 chain in miniature):
 *   conv_ii_slice_faithful — the per-tick law slices ∧-compose to the published laws.
 *   conv_ii_prov_faithful  — likewise for the provenance conjunct (ties root to contract).
 *   conv_ii_base           — the invariant at the first tick (havoc-free).
 *   conv_ii_step           — ANY single real occurrence preserves the invariant from an
 *                            ARBITRARY well-formed pre-state (the havoc seeds supply them).
 *   conv_ii_law            — invariant ∧ genesis premise ⇒ the law, STATE-LOCALLY.
 *   two SAT vacuity guards — the obligations range over non-empty configurations.
 * Together: base + step give the invariant at every tick of every real trace; law converts
 * it. The law's assurance now scales with STATE size, not trace length: at scope U the
 * proof covers every trace whose per-tick states fit in U — the occurrence/tick dimension
 * drops out of the perimeter.
 */

open conventions/inductive_invariant/inductive_invariant as ii
open meta/subject_log/subject_log[ii/Cubby, ii/CubbyRec] as cblog
open meta/subject_log/subject_log[ii/Hanger, ii/HangerRec] as hglog

// ── the havoc seeds — arbitrary pre-states, one kind per log ────────────────────────────────────
/** Frame-free, always-committed: the post is an arbitrary well-formed record, so pre-states
    range over ALL states, not just reachable ones. Sound because the library's witnessing
    is per-kind. */
sig HavocCubbyOcc  extends cblog/SubjectOcc {} { bindings = subject }
sig HavocHangerOcc extends hglog/SubjectOcc {} { bindings = subject }
fact HavocDiscipline {
  all v: HavocCubbyOcc + HavocHangerOcc | v.admission = Accepted
  all v: HavocCubbyOcc,  o: cblog/SubjectOcc - HavocCubbyOcc  | precedes[v.tick, o.tick]
  all v: HavocHangerOcc, o: hglog/SubjectOcc - HavocHangerOcc | precedes[v.tick, o.tick]
}
pred seedAt[t: Tick] { some v: HavocCubbyOcc + HavocHangerOcc | v.tick = t }

// ── per-tick slices of the published laws ───────────────────────────────────────────────────────
pred cubbyProvAt[t: Tick] {
  all c: Cubby | some cubbyAt[c, t].cPeg implies
    (some o: GrabOcc | committed[o] and o.subject = c and notAfter[o.tick, t]
       and cubbyAt[c, t].cPeg = o.peg)
}
pred hangerProvAt[t: Tick] {
  all h: Hanger | some hangerAt[h, t].hPeg implies
    (some o: HangOcc | committed[o] and o.subject = h and notAfter[o.tick, t]
       and hangerAt[h, t].hPeg = o.peg)
}
pred loneCubbyAt[t: Tick]  { all p: Peg | lone { c: Cubby  | resolve[cubbyAt[c, t].cPeg]  = p } }
pred loneHangerAt[t: Tick] { all p: Peg | lone { h: Hanger | resolve[hangerAt[h, t].hPeg] = p } }

/** The candidate inductive invariant: provenance ×2 ∧ lone-holder ×2. */
pred iiInv[t: Tick] { cubbyProvAt[t] and hangerProvAt[t] and loneCubbyAt[t] and loneHangerAt[t] }

/** The published law at a fixed tick. */
pred lawSliceAt[t: Tick] {
  loneCubbyAt[t] and loneHangerAt[t]
  pegMintDisjoint implies
    all p: Peg | (some c: Cubby | resolve[cubbyAt[c, t].cPeg] = p) implies
      (no h: Hanger | resolve[hangerAt[h, t].hPeg] = p)
}

// ── obligations ─────────────────────────────────────────────────────────────────────────────────
assert conv_ii_slice_faithful {
  (all t: Tick | lawSliceAt[t]) iff (pegLoneCubby and pegLoneHanger and pegExclusiveAcrossKinds)
}
assert conv_ii_prov_faithful { (all t: Tick | cubbyProvAt[t]) iff cubbyPegProvenance }
assert conv_ii_base { (not seedAt[first]) implies iiInv[first] }
assert conv_ii_step {
  all t: Tick - last | let t2 = next[t] |
    (iiInv[t] and not seedAt[t2]) implies iiInv[t2]
}
assert conv_ii_law { all t: Tick | iiInv[t] implies lawSliceAt[t] }

check conv_ii_slice_faithful for 5 but 5 Int, 2 Cubby, 1 Hanger, 2 Peg, 8 EntityId, 6 Tick, 6 Occurrence, 8 Snapshot expect 0
check conv_ii_prov_faithful  for 5 but 5 Int, 2 Cubby, 1 Hanger, 2 Peg, 8 EntityId, 6 Tick, 6 Occurrence, 8 Snapshot expect 0
check conv_ii_base           for 5 but 5 Int, 2 Cubby, 1 Hanger, 2 Peg, 8 EntityId, 6 Tick, 6 Occurrence, 8 Snapshot expect 0
check conv_ii_step           for 5 but 5 Int, 2 Cubby, 1 Hanger, 2 Peg, 8 EntityId, 6 Tick, 6 Occurrence, 8 Snapshot expect 0
check conv_ii_law            for 5 but 5 Int, 2 Cubby, 1 Hanger, 2 Peg, 8 EntityId, 6 Tick, 6 Occurrence, 8 Snapshot expect 0

// ── vacuity guards — the checks range over non-empty, law-relevant configurations ───────────────
/** A seeded peg-holding cubby state coexisting with a later committed Grab. */
run conv_ii_seededGrab {
  some v: HavocCubbyOcc | committed[v] and some cPost[v].cPeg
  some o: GrabOcc | committed[o]
} for 5 but 5 Int, 2 Cubby, 1 Hanger, 2 Peg, 8 EntityId, 6 Tick, 6 Occurrence, 8 Snapshot expect 1

/** The cross-kind antecedent is realizable: a cubby-held peg beside a live hanger record. */
run conv_ii_crossAntecedent {
  some t: Tick, c: Cubby | some resolve[cubbyAt[c, t].cPeg] & Peg
  some v: HavocHangerOcc | committed[v] and some hPost[v].hPeg
} for 5 but 5 Int, 2 Cubby, 1 Hanger, 2 Peg, 8 EntityId, 6 Tick, 6 Occurrence, 8 Snapshot expect 1
