module shared/certainty/tests/certainty
// Reflects dafny-domain src/shared/certainty/tests/certainty-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open shared/certainty/certainty

// Three ordered levels exist.
run unit_cert_levels { #CertaintyLevel = 3 } for 3 expect 1

// The order is a strict ascending chain LOW < MEDIUM < HIGH.
check unit_cert_order {
  lteC[LOW, MEDIUM] and lteC[MEDIUM, HIGH] and lteC[LOW, HIGH]
  and not lteC[MEDIUM, LOW] and not lteC[HIGH, MEDIUM]
} for 3 expect 0

// Decay never RAISES certainty: a computed level is at-or-below its operation-supplied start.
check unit_cert_decayNeverRaises {
  all c, s: CertaintyLevel | computedFrom[c, s] implies lteC[c, s]
} for 3 expect 0

// LOW is the floor — it cannot decay further.
check unit_cert_floorIsLowest { atOrBelow[LOW] = LOW } for 3 expect 0

// Decay can move strictly down (HIGH → MEDIUM/LOW); holding (no time passed) is allowed.
run unit_cert_canDecayStrictly { some c, s: CertaintyLevel | computedFrom[c, s] and c != s } for 3 expect 1
run unit_cert_canHold { some s: CertaintyLevel | computedFrom[s, s] } for 3 expect 1
