module meta/occurrence/tests/occurrence
// Reflects dafny-domain src/meta/tests/trace-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/occurrence/occurrence

/*
 * The MINIMAL core (DT-011): occurrences carry only their causal position. The domain-time stamp and
 * the two-clock bridge live in the `timed` extension (tests/timed.als). `Occurrence` is abstract, so
 * a concrete test subtype is introduced here.
 */

/** TestOcc — a concrete occurrence for exercising the log anatomy. */
sig TestOcc extends Occurrence {}

// The core loads: a causally ordered pair exists.
run unit_occ_loads {
  some disj a, b: TestOcc | occPrecedes[a, b]
} for 4 expect 1

// Occurrences inherit a strict TOTAL causal order (from one-per-tick + the Tick total order).
assert unit_occ_total { all disj a, b: TestOcc | occPrecedes[a, b] or occPrecedes[b, a] }
check unit_occ_total for 5 expect 0

// One occurrence per tick (the linearization fact is in force).
assert unit_occ_onePerTick { all disj a, b: TestOcc | a.tick != b.tick }
check unit_occ_onePerTick for 5 expect 0

// The note seat: an occurrence may carry a free-text annotation of the act itself (plain
// String — zero universe cost in commands without literals; MP ruling 2026-08-10).
run unit_occ_noteWitness {
  some o: TestOcc | o.note = "expedited at the vendor's request"
} for 4 but exactly 1 String expect 1

// The note is genuinely optional — a noted and an un-noted occurrence coexist.
run unit_occ_noteOptional {
  some disj a, b: TestOcc | some a.note and no b.note
} for 4 but exactly 1 String expect 1

// The ORIGIN seat (DT-029 E1, total since ruling A): a self-initiated occurrence cites itself — the one spelling of "no caller".
run unit_occ_archeSelfInitiated {
  some o: TestOcc | o.arche = o and o in selfInitiated
} for 4 expect 1

// A cited origin is strictly earlier than the occurrence citing it.
assert unit_occ_archeOriginPrecedes { all o: TestOcc | o.arche != o implies occPrecedes[o.arche, o] }
check unit_occ_archeOriginPrecedes for 5 expect 0

// Proper cycles are unrepresentable: the only loop is the self-initiated one (a theorem of strict precedence).
assert unit_occ_archeNoProperCycle { all o: TestOcc | o in o.^arche implies o.arche = o }
check unit_occ_archeNoProperCycle for 5 expect 0

// The field is total: every occurrence has an origin, itself or an earlier one (a theorem of `one`).
assert unit_occ_archeTotal { all o: TestOcc | one o.arche and (o.arche = o or occPrecedes[o.arche, o]) }
check unit_occ_archeTotal for 5 expect 0

// A citing occurrence and its self-initiated origin coexist: the walk `a.*arche` ends at the self-loop.
run unit_occ_archeCitesSelfInitiated {
  some disj a, b: TestOcc | a.arche = b and b.arche = b and b in a.^arche
} for 4 expect 1
