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
