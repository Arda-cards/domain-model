module meta/action/tests/attributed
// Reflects dafny-domain src/meta/tests/trace-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/action/attributed

/*
 * The opt-in actor stamp (DT-011): a kind opts in with one fact; un-opted kinds carry no principal
 * (and, cone-wise, a model with no Attributed kinds carries no kernel at all).
 */

/** AOp — a kind opted into provenance. */
sig AOp extends Action {} { no bindings }
fact AOpAttributed { AOp in Attributed }

/** BOp — a kind left un-attributed (membership free). */
sig BOp extends Action {} { no bindings }

// An attributed committed action carries its actor.
run unit_attr_committedHasActor { some a: AOp | committed[a] and some a.by } for 4 expect 1

// Mixed logs are representable: an action outside Attributed carries no actor.
run unit_attr_mixedLog { some b: BOp | b not in Attributed and no b.by } for 4 expect 1

// Every opted-in action has exactly one actor (the field multiplicity, as a law).
assert unit_attr_oneActor { all a: AOp | one a.by }
check unit_attr_oneActor for 5 expect 0
