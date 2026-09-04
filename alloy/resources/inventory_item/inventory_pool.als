module resources/inventory_item/inventory_pool

/*
 * InventoryPool — a Scoped aggregate of InventoryItems that all classify under ONE Item. It resolves the
 * tension between (a) an InventoryItem as a *homogeneous* amount of goods and (b) needing to discriminate
 * InventoryItems that share an Item but differ in attributes (lot, expiry, locator, …): a consumer
 * references a single `one`/`lone` pool, while the pool holds the discriminating *set* internally — so the
 * `one`-vs-`set` duality is NOT forced on the consuming modules.
 *
 * LOG-CARRIED (2026-07-02 — MP review; the v1 `var items` predated DT-011's one-carrier decision):
 * membership is now the occurrence-log pattern of the rest of this module — the entity is identity
 * only; the held set lives on `PoolState` records carried by `PoolAddOcc`/`PoolRemoveOcc`; the
 * current view is the LOCF projection `heldAt`. Homogeneity and same-tenant are now GUARD-derived
 * theorems (witnessed refusals: `RWrongItem`/`RWrongTenant`), not standing `always` facts. Pool
 * occurrences share the one causal Tick order with the InventoryItem occurrences.
 *
 * SPINE (ported 2026-07-17 — DT-015 R2, the last row of the Q5 refactor review): the membership
 * log now rides `meta/subject_log[InventoryPool, PoolState]` — the spine EXTRACTED from this
 * log's hand-built original (with the II and CardCycle logs). The kind subject field is
 * therefore `subject`; the alias `fun pool` preserves every existing `o.pool` read (receiver
 * syntax), so consumers and suites are unchanged; `heldAt` is a wrapper over the spine's
 * `recordAt`.
 *
 * Still v1 scope: membership only — no liveness coupling to members (a retired member is a
 * modeling question deferred with reservations). Inventory counts remain DERIVED, never stored —
 * the counting machinery is the metrics package (`resources/inventory_item/metrics.als`, DT-007);
 * a pool-scoped count cell lands there on demand. Consumers (KanbanCard, …) are NOT retrofitted.
 *
 * Future (not modeled): recursive pools (pool-of-pools or leaf items); default/back-fill attributes;
 * lock/unlock the set as a unit; reservations against the set.
 */

open meta/profiles/domain_log                    // PROFILE (DT-012): the log anatomy (StatefulAction, Tick, verdicts)
open meta/kernel                                 // Scoped, Entity, EntityId, resolve
open reference_data/item/item_types            // Item — the membership classifier (TYPES; laws via root mock/impl)
open resources/inventory_item/inventory_item_types     // InventoryItem (+ transitively keyed algebra, values)
open meta/subject_log/subject_log[InventoryPool, PoolState] as plog

/** InventoryPool — the IDENTITY of a tenant-scoped set of InventoryItems under one Item; its
    membership lives on PoolState records in the occurrence log. */
sig InventoryPool extends Scoped {
  itemPin: one ItemOcc              // → Item VERSION PIN (DT-023 R3; was itemRef): constrains
                                    //   membership (immutable); entity-wise reads via `.subject`.
                                    //   Genesis is runtime-side (no create kind), so pin CURRENCY
                                    //   anchors at the minting process — as of M2a (DT-020
                                    //   §8.5.3 / SPEARHEAD-D1 A′-2) THREE minting holders:
                                    //   ReceivingLine at Receive, DemandItem at StartProduction
                                    //   (the holding pool) and again at delivery split, and
                                    //   CardCycle at StartProcessing (kanban_card M1). Annotation
                                    //   only — no law change: the runtime carries the pin as a
                                    //   floating ItemReference refreshed by the Item channel (R3);
                                    //   here only typing + tenancy.
}

// The classifier is a PIN (typed, never dangles) — no soft dataRefs remain on the identity.
fact InventoryPoolRefs { all p: InventoryPool | no p.dataRefs }

// Pin tenancy (DT-023): kernel isolation reaches only EntityId dataRefs — stated here instead.
fact PoolPinTenancy { all p: InventoryPool | p.itemPin.subject.tenantId = p.tenantId }

// ── the state record ─────────────────────────────────────────────────────────────────────────────
/** PoolState — one moment's membership of a pool (a value; extensional). */
sig PoolState extends Snapshot { holds: set InventoryItem }
fact PoolStateExtensional { all disj a, b: PoolState | a.holds != b.holds }

// ── the kinds ────────────────────────────────────────────────────────────────────────────────────
/** PoolOcc — a pool-membership operation occurrence on the spine; `subject` is the pool (pre/post
    are its PoolState records — the spine's SubjectOccRecords). */
abstract sig PoolOcc extends plog/SubjectOcc {}
/** pool — the reading alias for the spine's `subject` field (receiver syntax: `o.pool`). */
fun pool[o: PoolOcc]: one InventoryPool { o.subject }

sig PoolAddOcc    extends PoolOcc { item: one InventoryItem, reverses: lone PoolOcc } { bindings = subject + item + arche + reverses }
sig PoolRemoveOcc extends PoolOcc { item: one InventoryItem, reverses: lone PoolOcc } { bindings = subject + item + arche + reverses }
// B-mov (DT-029 E6 / SAMWISE-S1 as ruled, 2026-09-03): every movement row binds its causal signature `arche` (kernel field;
// the caller's RESERVE row id, or itself when self-minted — MP's Q7 rule: every row an act writes carries the act's `arche`)
// and `reverses` — the row this movement UNDOES (a reversal is a NEW context: it carries its own `arche`; S1 item 2).
// `reverses` is typed `lone PoolOcc`, never `lone univ`: a field over `univ` is a |PoolOcc| × |univ| relation and inflated every
// root opening this module by ~60 % primary vars (the receiver canary, B-mov's P4 falsified 2026-09-04); `ReversalDiscipline`
// constrains it to the inverse kind anyway, so the type costs nothing and the matrix is |PoolOcc|². The type is NOT the
// discipline: `lone PoolOcc` is not `lone <inverse kind>`, so `ReversalDiscipline` stays LOAD-BEARING for the inverse-kind half
// (`unit_pool_reversalWrongKindImpossible` still proves it) — MINESWEEPER's read of f72191e, 2026-09-04.
/** PoolTransferOcc — M2b (DT-020 §8.5.3 / SPEARHEAD-D1 A′-2): the ONE kind that moves an
    InventoryItem between pools (ownership-by-genesis — items move between pools, pools never
    re-attach). `subject` (the spine field, read via `pool[o]`/`o.pool`) is the SOURCE pool
    (`from`); atomic remove-then-add. `to` is the destination. This is the model seat of R2 —
    "take inventory from Inventory-at-Rest into a new DemandItem without receiving". */
sig PoolTransferOcc extends PoolOcc { item: one InventoryItem, to: one InventoryPool, reverses: lone PoolOcc }
  { bindings = subject + item + to + arche + reverses }
/** ReversalDiscipline — B-mov: `reverses` names a COMMITTED row on the SAME pool, EARLIER, of the INVERSE kind and the same
    item — an add reversing a remove, a remove reversing an add, a transfer reversing a transfer whose `to` is this one's
    source and whose source is this one's `to`. The late-movement detector (the owner's module) excludes rows named by a
    committed reversal, so a repair never trips its own detector (DT-027 §7). */
fact ReversalDiscipline {
  all o: PoolAddOcc    | some o.reverses implies (o.reverses in PoolRemoveOcc and committed[o.reverses & PoolRemoveOcc]
                                                  and (o.reverses & PoolRemoveOcc).subject = o.subject and (o.reverses & PoolRemoveOcc).item = o.item
                                                  and precedes[(o.reverses & PoolRemoveOcc).tick, o.tick])
  all o: PoolRemoveOcc | some o.reverses implies (o.reverses in PoolAddOcc and committed[o.reverses & PoolAddOcc]
                                                  and (o.reverses & PoolAddOcc).subject = o.subject and (o.reverses & PoolAddOcc).item = o.item
                                                  and precedes[(o.reverses & PoolAddOcc).tick, o.tick])
  all o: PoolTransferOcc | some o.reverses implies (o.reverses in PoolTransferOcc and committed[o.reverses & PoolTransferOcc]
                                                  and (o.reverses & PoolTransferOcc).to = o.subject and (o.reverses & PoolTransferOcc).subject = o.to
                                                  and (o.reverses & PoolTransferOcc).item = o.item and precedes[(o.reverses & PoolTransferOcc).tick, o.tick])
}

// ── refusal reasons ──────────────────────────────────────────────────────────────────────────────
one sig RWrongItem, RWrongTenant, RAlreadyMember, RNotMember,
        RHeldElsewhere,  // M2b (DT-020 §8.5.3): add refused — the item is already held by ANOTHER
                         //   live pool (poolMembershipExclusive: at most one pool per item per tick)
        RSameTarget,     // M2b: transfer refused — `to` names the same pool as `from` (no-op move)
        RDuplicateOrigin // B-mov (DT-029 E5 S-2 / S1 item 3): a movement citing an `arche` a COMMITTED row on this pool
                         //   already carries — the idempotent callee's typed refusal ("already landed"); the runtime's
                         //   typed duplicate refusal. LOCAL atom: this module opens no pattern layer, and the pattern's
                         //   `RDuplicateArche` would clash in the flat namespace with a root that opens both.
        extends Reason {}

// ── the spine adoption: chaining (unconditional — a refused occurrence still read the real
// membership) + v1 result policy ────────────────────────────────────────────────────────────────
fact PoolChaining      { plog/chained }
// (no o.pre = the pool has no committed history: membership reads empty — `none.holds = none`.)

// ── reason-precise admission guards (Accepted ⟺ ∅; because = EXACTLY the set) ────────────────────
fun poolAddViol[o: PoolAddOcc]: set Reason {
  ((o.item.itemPin.subject != o.pool.itemPin.subject) => RWrongItem else none)
  + ((o.item.tenantId != o.pool.tenantId) => RWrongTenant   else none)
  + ((o.item in o.pre.holds)              => RAlreadyMember else none)
  // M2b (DT-020 §8.5.3 / SPEARHEAD-D1 A′-2): poolMembershipExclusive as a GUARD-DERIVED
  // theorem — an add is refused if the item is currently held by ANY OTHER pool at this
  // tick (RAlreadyMember above only catches the SAME pool).
  + ((some q: InventoryPool - o.pool | o.item in heldAt[q, o.tick]) => RHeldElsewhere else none)
  + (plog/archeDuplicate[o] => RDuplicateOrigin else none)   // B-mov: a re-sent origin on this pool is refused, typed (the module FACT `ArcheUnique` needs the refusal — Q8)
}
fun poolRemoveViol[o: PoolRemoveOcc]: set Reason {
  ((o.item not in o.pre.holds) => RNotMember else none)
  + (plog/archeDuplicate[o] => RDuplicateOrigin else none)   // B-mov
}
/** poolTransferViol — M2b: RSameTarget (a no-op move), RNotMember (the item isn't at the
    SOURCE — `subject`/`from`), RWrongItem/RWrongTenant judged at the DESTINATION (`to`) — the
    same item-agreement shape `poolAddViol` uses, since the destination gain IS an ordinary
    add (`transferPairing`). */
fun poolTransferViol[o: PoolTransferOcc]: set Reason {
  ((o.to = o.subject) => RSameTarget else none)
  + ((o.item not in o.pre.holds) => RNotMember else none)
  + ((o.item.itemPin.subject != o.to.itemPin.subject) => RWrongItem else none)
  + ((o.item.tenantId != o.to.tenantId) => RWrongTenant else none)
  + (plog/archeDuplicate[o] => RDuplicateOrigin else none)   // B-mov
}
fact PoolAdmissionWitness {
  all o: PoolAddOcc      | (o.admission = Accepted iff no poolAddViol[o])      and (o.admission in Rejected implies o.admission.because = poolAddViol[o])
  all o: PoolRemoveOcc   | (o.admission = Accepted iff no poolRemoveViol[o])   and (o.admission in Rejected implies o.admission.because = poolRemoveViol[o])
  all o: PoolTransferOcc | (o.admission = Accepted iff no poolTransferViol[o]) and (o.admission in Rejected implies o.admission.because = poolTransferViol[o])
}
// No result policy in v1 (mirrors the InventoryItem log).
fact PoolCommitAccepts { plog/commitAlwaysAccepts }

// ── effects ──────────────────────────────────────────────────────────────────────────────────────
fact PoolEffectWitness {
  all o: PoolAddOcc      | committed[o] implies o.post.holds = o.pre.holds + o.item
  all o: PoolRemoveOcc   | committed[o] implies o.post.holds = o.pre.holds - o.item
  all o: PoolTransferOcc | committed[o] implies o.post.holds = o.pre.holds - o.item   // the SOURCE half
}

/** adjacentCommit — `b` is the very NEXT COMMITTED occurrence causally after `a` (nothing
    committed sits between them). SAME-TICK PAIRING IS IMPOSSIBLE in this model:
    `meta/occurrence`'s `OneOccurrencePerTick` fact is GLOBAL (at most one Occurrence atom per
    tick across the WHOLE model, not per subject-log) — two distinct occurrence atoms can never
    share a tick. ADJACENCY (ticks are global, so "nothing committed between" is exactly what
    atomicity means here) is the model-consistent rendering of the M2 spec's "at the same tick"
    / "same tick" wording for `transferPairing` and `splitInPool` below (team-lead ruling,
    2026-08-28, on the STOP raised for this exact obstacle). */
pred adjacentCommit[a, b: Occurrence] {
  precedes[a.tick, b.tick] and no c: Occurrence | committed[c] and precedes[a.tick, c.tick] and precedes[c.tick, b.tick]
}

/** transferPairing — M2b: a committed PoolTransferOcc's DESTINATION gain is a matching
    PoolAddOcc on `o.to`, the immediately-next COMMITTED occurrence (`adjacentCommit`) — so
    `heldAt` stays a single projection (the paired PoolAddOcc's OWN effect, above) and
    `poolMembershipExclusive` still discharges through the ordinary add guard. The transfer's
    OWN guard (`poolTransferViol`) already judges `RWrongItem`/`RWrongTenant` at the
    DESTINATION — the same clauses the paired add's guard evaluates — and the item was JUST
    removed from every other pool (this transfer's own source effect), so the paired add's
    `RAlreadyMember`/`RHeldElsewhere` cannot fire: the pairing is always admissible once the
    transfer itself is. */
fact TransferPairing {
  all o: PoolTransferOcc | committed[o] implies
    (some a: PoolAddOcc | committed[a] and a.pool = o.to and a.item = o.item and adjacentCommit[o, a]
       and a.arche = o.arche)   // Q7 = A (MP, 2026-09-03): the paired half carries the transfer's causal signature — one act, one
                                //   `arche` on both rows; adjacency stays as the model's "same transaction"; when the transfer is
                                //   self-minted the pair cites the transfer row itself (it IS the add's immediate cause)
}

/** splitInPool — M2b composite (a DERIVED predicate, not a kind): a committed SplitOcc whose
    new sibling (`nu`) is PoolAdd'ed into the SAME pool that already held the split target, as
    the immediately-next COMMITTED occurrence (`adjacentCommit` — same OneOccurrencePerTick
    reasoning as `transferPairing` above). Witnesses that a split residue stays co-located with
    its origin without any pool-side re-attach machinery. */
pred splitInPool[s: SplitOcc, a: PoolAddOcc] {
  committed[s] and committed[a] and a.item = s.nu and adjacentCommit[s, a]
  and s.target in heldAt[a.pool, s.tick]
  and a.arche = s.arche   // Q7 = A inherits: the residue's add carries the split's causal signature
}

// ── the projections (wrappers over the spine's reads — public surface preserved) ────────────────
/** lastPoolTouch — the latest committed occurrence on `p` at-or-before `t`. */
fun lastPoolTouch[p: InventoryPool, t: Tick]: lone PoolOcc { plog/lastTouch[p, t] }
/** heldAt — the pool's membership as of `t` (empty before any committed history). */
fun heldAt[p: InventoryPool, t: Tick]: set InventoryItem { plog/recordAt[p, t].holds }

// M2c (DT-020 §8.5.3/§8.2.1, SPEARHEAD-D1 A′-2): "AT REST" IS THE POOL'S CUSTODY READING —
// a pool CANNOT know who holds it (the DAG requirement: this module sees no ReceivingLine /
// DemandItem / CardCycle), so "at rest" (no live holder among the three kinds) is DERIVED,
// never a stored pool-side state (§8.2.1: "Bin ≠ Pool" — items carry their own location and
// availability). The predicate itself (`atRestAt`) is defined at the COMPOSITION level, where
// all three holder kinds are visible: `tests/pool_lattice.als` (the existing root that already
// composes ReceivingLine/DemandItem/CardCycle over their MOCKS for the global exclusivity row).
