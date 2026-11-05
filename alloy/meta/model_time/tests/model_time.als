module meta/model_time/tests/model_time
// Reflects dafny-domain src/meta/tests/model-time-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/model_time/model_time

/*
 * The model-time axis is a genuine strict total order on `Tick`. SAT = a witnessing instance;
 * UNSAT (check) = the order property holds in every instance. `util/ordering[Tick]` pins Tick to the
 * exact scope, so `for N` means exactly N ticks.
 */

// A non-trivial strictly-increasing chain of three ticks exists.
run unit_mt_chain {
  some disj a, b, c: Tick | precedes[a, b] and precedes[b, c]
} for 4 expect 1

// Total: any two distinct ticks are causally comparable.
assert unit_mt_total { all disj a, b: Tick | precedes[a, b] or precedes[b, a] }
check unit_mt_total for 6 expect 0

// Strict: `precedes` is irreflexive and asymmetric.
assert unit_mt_strict {
  (no a: Tick | precedes[a, a]) and
  (all a, b: Tick | precedes[a, b] implies not precedes[b, a])
}
check unit_mt_strict for 6 expect 0

// Transitive.
assert unit_mt_transitive {
  all a, b, c: Tick | (precedes[a, b] and precedes[b, c]) implies precedes[a, c]
}
check unit_mt_transitive for 6 expect 0

// `follows` is the converse of `precedes`; `notAfter` is `precedes` or equal.
assert unit_mt_vocabulary {
  all a, b: Tick |
    (follows[a, b] iff precedes[b, a]) and
    (notAfter[a, b] iff (precedes[a, b] or a = b))
}
check unit_mt_vocabulary for 6 expect 0
