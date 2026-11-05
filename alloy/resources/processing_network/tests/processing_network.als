module resources/processing_network/tests/processing_network
// Reflects dafny-domain src/resources/processing-network/tests/processing-network-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/kernel
open resources/processing_network/processing_network_implementation

/*
 * Satisfiability suite for the STUB module (DT-017 static degenerate: the laws are axioms, so the
 * obligation is joint SAT witnesses + impossibility guards, not discharge proofs).
 */

// A station network loads: a loop between two stations of one tenant.
run unit_pnet_coherent {
  some l: Loop | some l.source and some l.sink
} for 4 expect 1

// Two stations in ONE tenant coexist — the DT-016 two-station reality (Procurement source,
// Shop Floor sink) is witness configuration, not schema.
run unit_pnet_twoStationsOneTenant {
  some disj a, b: Station | a.tenantId = b.tenantId
} for 4 expect 1

// A degenerate self-loop is impossible (loopWellFormed).
run unit_pnet_selfLoopImpossible {
  some l: Loop | l.source = l.sink
} for 4 expect 0

// A loop crossing tenants is impossible (loopWellFormed).
run unit_pnet_crossTenantLoopImpossible {
  some l: Loop | l.source.tenantId != l.tenantId or l.sink.tenantId != l.tenantId
} for 4 expect 0

// ── DT-023 cut 7c: the retirement LATCH (own atoms — R2 structural independence) ───────────────

// The retirement boundary is expressible: a station live at one tick, retired at a later one
// — what the (deferred) consumer guards will read at the Loop build-out.
run unit_pnet_retirementBoundary {
  some s: Station, t1, t2: Tick {
    precedes[t1, t2]
    stationLiveAt[s, t1] and not stationLiveAt[s, t2]
  }
} for 4 but 4 Tick expect 1

// An unretired station is live at EVERY tick (the latch's benign default).
check unit_pnet_unretiredAlwaysLive {
  all s: Station, t: Tick | no s.retiredAt implies stationLiveAt[s, t]
} for 4 but 4 Tick expect 0
