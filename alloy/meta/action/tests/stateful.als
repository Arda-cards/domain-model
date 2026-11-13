module meta/action/tests/stateful
// Reflects dafny-domain src/meta/tests/trace-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/action/stateful

/*
 * Suite for the OPTIONAL snapshot-carrying extension (DT-006 build prep). Exercises the anatomy
 * only — chaining and transition witnessing are domain concerns (the InventoryItem build);
 * ex17 demonstrates the full pattern on the Hotel cast.
 */

/** SOp — a concrete stateful kind with free outcome, to exercise the anatomy. */
sig SOp extends StatefulAction {} { no bindings }

// A committed stateful action carries its result snapshot (what its Effect produced).
run unit_stateful_committedCarriesAfter {
  some a: SOp | committed[a] and some a.pre and some a.post
} for 4 expect 1

// A CREATION shape is representable: committed, no prior state to read, a result produced.
run unit_stateful_creationShape {
  some a: SOp | committed[a] and no a.pre and some a.post
} for 4 expect 1

// A refused action carries reasons and NO result (it produced nothing).
run unit_stateful_refusedProducesNothing {
  some a: SOp | not committed[a] and some refusalReasons[a] and no a.post
} for 4 expect 1

// The law both ways, as impossibility guards (PostOnlyIfCommitted):
run unit_stateful_committedWithoutAfterImpossible {
  some a: StatefulAction | committed[a] and no a.post
} for 4 expect 0
run unit_stateful_refusedWithAfterImpossible {
  some a: StatefulAction | not committed[a] and some a.post
} for 4 expect 0
