module meta/keyed_value_algebra/tests/scalar_int
// Reflects dafny-domain src/meta/tests/scalar-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/keyed_value_algebra/scalar_int
open util/integer

// Concrete bounded fixed-point arithmetic (SCALE=1 ⇒ integers). `for 5 int` = bitwidth 5 (−16..15).
// The RING laws hold on the bounded carrier even with wraparound (ℤ/2^bw is a commutative ring); the
// ORDER is sound only in-range (constrain, don't forbid); DIVISION is truncating (lossy).

// ── Ring laws (UNSAT = hold) — true even with wraparound: ℤ/2^bw is a commutative ring with unit ──
check int_addAssoc { all a, b, c: Int | fadd[fadd[a, b], c] = fadd[a, fadd[b, c]] } for 5 int expect 0
check int_addComm  { all a, b: Int | fadd[a, b] = fadd[b, a] } for 5 int expect 0
check int_addId    { all a: Int | fadd[a, fZero] = a } for 5 int expect 0
check int_addInv   { all a: Int | fadd[a, fneg[a]] = fZero } for 5 int expect 0
check int_mulComm  { all a, b: Int | fmul[a, b] = fmul[b, a] } for 5 int expect 0
check int_mulId    { all a: Int | fmul[a, fOne] = a } for 5 int expect 0
check int_distrib  { all a, b, c: Int | fmul[a, fadd[b, c]] = fadd[fmul[a, b], fmul[a, c]] } for 5 int expect 0

// ── Order: sound only within range (the recommended "constrain to prevent overflow" practice) ──
// Positive + positive stays positive when both summands are bounded away from the overflow edge.
check int_posClosed_bounded {
  all a, b: Int | (gt[a, 0] and gt[b, 0] and lt[a, 8] and lt[b, 8]) implies gt[fadd[a, b], 0]
} for 5 int expect 0
// Without that bound, wraparound breaks the order — a counterexample EXISTS (e.g. 15 + 1 = −16).
run int_orderBreaksOnOverflow {
  some a, b: Int | gt[a, 0] and gt[b, 0] and not gt[fadd[a, b], 0]
} for 5 int expect 1

// ── Division: bounded, truncating (limited precision) ──
// Truncation is real: some a/b·b ≠ a (e.g. 7/2 = 3, 3·2 = 6 ≠ 7).
run int_divTruncates {
  some a, b: Int | b != 0 and rem[a, b] != 0 and fmul[fdiv[a, b], b] != a
} for 5 int expect 1
// When b divides a exactly (in range), division is the inverse of multiplication.
run int_divExactRecovers {
  some a, b: Int | b != 0 and a != 0 and rem[a, b] = 0 and fmul[fdiv[a, b], b] = a
} for 5 int expect 1
