module shared/certainty/tests/certainty
// Reflects dafny-domain src/shared/certainty/tests/certainty-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open shared/certainty/certainty

// Three ordered levels exist.
run unit_cert_levels { #CertaintyLevel = 3 } for 3 expect 1

// Decay can move strictly down (HIGH → MEDIUM/LOW); holding (no time passed) is allowed.
run unit_cert_canDecayStrictly { some c, s: CertaintyLevel | computedFrom[c, s] and c != s } for 3 expect 1
run unit_cert_canHold { some s: CertaintyLevel | computedFrom[s, s] } for 3 expect 1
