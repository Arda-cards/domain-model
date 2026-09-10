module resources/inventory_item/tests/pool_lifecycle

open resources/inventory_item/inventory_pool as ip            // aliased (rule 10): the parameters below are qualified
open meta/subject_log/lifecycle[ip/InventoryPool, ip/PoolState] as lc   // the SHAPES for the pool log (the cut's adoption)
open meta/subject_log/affirm[ip/InventoryPool, ip/PoolState] as aff     // the AFFIRM act on the pool log (Q43: the module's promised first adopter)

/*
 * RED-FIRST witnesses for the inventory pool under the lifecycle family (Q29: `CreatePoolOcc extends lc/CreateOcc` enters
 * the model — the model catching up to the runtime's CREATE; Q24 (a) + Q17: `RetirePoolOcc extends lc/RetireOcc`, refused
 * `RPoolClosed` (not started / already retired) and `RPoolNotEmpty` (some LIVE member — a pool retires EMPTY: members
 * transfer out first, the line's two-act pattern). Consequence the family forces (ShapeAdmission): every membership
 * operation is a Mutate shape and needs a started, unretired pool — an add on a never-created pool is refused (`RPoolClosed`).
 * Run RED at 1e79b89 before any sig lands: the root fails to parse on `CreatePoolOcc` / `RetirePoolOcc` / the three atoms / `lc`.
 * Scopes: inventory_pool.als (static cone; no steps); Occurrence/Snapshot pinned for the three-row histories.
 */

// ── genesis: a committed create starts the pool empty ──────────────────────────────────────────
run unit_plc_createStartsEmpty {
  some o: CreatePoolOcc | committed[o] and no heldAt[o.pool, o.tick] and not lc/startedBefore[o]
} for 6 but 2 Scalar, 3 Int, 6 Tick, 6 Occurrence, 6 Snapshot expect 1

// complement: genesis on a started pool is refused (genesis-once)
run unit_plc_createTwiceRefused {
  some disj a, b: CreatePoolOcc | committed[a] and b.subject = a.subject and precedes[a.tick, b.tick]
    and refusedAtAdmission[b] and b.admission.because = RPoolStarted
} for 6 but 2 Scalar, 3 Int, 6 Tick, 6 Occurrence, 6 Snapshot expect 1

// ── an add on a pool that was never created is refused — the family's word on the mutators ─────
run unit_plc_addBeforeCreateRefused {
  some o: PoolAddOcc | refusedAtAdmission[o] and RPoolClosed in o.admission.because and no o.pre
} for 6 but 2 Scalar, 3 Int, 6 Tick, 6 Occurrence, 6 Snapshot expect 1

// complement: after a committed create, an add commits (the existing witness survives with a genesis)
run unit_plc_addAfterCreateCommits {
  some c: CreatePoolOcc, o: PoolAddOcc | committed[c] and o.subject = c.subject and precedes[c.tick, o.tick]
    and committed[o] and o.item in heldAt[o.pool, o.tick]
} for 6 but 2 Scalar, 3 Int, 6 Tick, 6 Occurrence, 6 Snapshot expect 1

// ── retire an EMPTY started pool: commits, tombstones ──────────────────────────────────────────
run unit_plc_retireEmptyCommits {
  some o: RetirePoolOcc | committed[o] and no o.pre.holds and o.post = o.pre
} for 6 but 2 Scalar, 3 Int, 6 Tick, 6 Occurrence, 6 Snapshot expect 1

// complement (Q17): a LIVE member refuses the retire — RPoolNotEmpty
run unit_plc_retireNotEmptyRefused {
  some o: RetirePoolOcc | refusedAtAdmission[o] and o.admission.because = RPoolNotEmpty and some o.pre.holds
} for 6 but 2 Scalar, 3 Int, 6 Tick, 6 Occurrence, 6 Snapshot expect 1

// ── refused on a never-created pool, and twice ─────────────────────────────────────────────────
run unit_plc_retireNeverCreatedRefused {
  some o: RetirePoolOcc | refusedAtAdmission[o] and RPoolClosed in o.admission.because and no o.pre
} for 6 but 2 Scalar, 3 Int, 6 Tick, 6 Occurrence, 6 Snapshot expect 1

run unit_plc_retireTwiceRefused {
  some disj a, b: RetirePoolOcc | committed[a] and b.subject = a.subject and precedes[a.tick, b.tick]
    and refusedAtAdmission[b] and RPoolClosed in b.admission.because
} for 6 but 2 Scalar, 3 Int, 6 Tick, 6 Occurrence, 6 Snapshot expect 1

// ── complement of the pair: an add after a committed retire is refused ─────────────────────────
run unit_plc_addAfterRetireRefused {
  some r: RetirePoolOcc, o: PoolAddOcc | committed[r] and o.subject = r.subject and precedes[r.tick, o.tick]
    and refusedAtAdmission[o] and RPoolClosed in o.admission.because
} for 6 but 2 Scalar, 3 Int, 6 Tick, 6 Occurrence, 6 Snapshot expect 1

// ── the theorem ────────────────────────────────────────────────────────────────────────────────
assert unit_plc_nothingAfterRetire { lc/nothingAfterRetire }
check unit_plc_nothingAfterRetire for 6 but 2 Scalar, 3 Int, 6 Tick, 6 Occurrence, 6 Snapshot expect 0

// ── Q43: the pool adopts `affirm` (red-first: parse fails on `aff` / `AffirmPoolOcc` until the adoption lands) ────
// ── affirm on a live pool whose affirmed version IS the current record: commits, post = pre ───
run unit_plc_affirmCurrentCommits {
  some o: AffirmPoolOcc | committed[o] and o.affirmed = o.pre and o.post = o.pre
} for 6 but 2 Scalar, 3 Int, 6 Tick, 6 Occurrence, 6 Snapshot expect 1

// complement: a stale affirmation (the affirmed version is not the current record) → RStaleAffirmation
run unit_plc_affirmStaleRefused {
  some o: AffirmPoolOcc | refusedAtAdmission[o] and o.admission.because = RStaleAffirmation and some o.pre and o.affirmed != o.pre
} for 6 but 2 Scalar, 3 Int, 6 Tick, 6 Occurrence, 6 Snapshot expect 1

// ── never created → the adopter's closed atom; retired → the same atom ─────────────────────────
run unit_plc_affirmNeverCreatedRefused {
  some o: AffirmPoolOcc | refusedAtAdmission[o] and RPoolClosed in o.admission.because and no o.pre
} for 6 but 2 Scalar, 3 Int, 6 Tick, 6 Occurrence, 6 Snapshot expect 1

run unit_plc_affirmAfterRetireRefused {
  some r: RetirePoolOcc, o: AffirmPoolOcc | committed[r] and o.subject = r.subject and precedes[r.tick, o.tick]
    and refusedAtAdmission[o] and RPoolClosed in o.admission.because
} for 6 but 2 Scalar, 3 Int, 6 Tick, 6 Occurrence, 6 Snapshot expect 1

// ── the affirm never writes a new record ───────────────────────────────────────────────────────
assert unit_plc_affirmIsInert { all o: AffirmPoolOcc | committed[o] implies o.post = o.pre }
check unit_plc_affirmIsInert for 6 but 2 Scalar, 3 Int, 6 Tick, 6 Occurrence, 6 Snapshot expect 0
