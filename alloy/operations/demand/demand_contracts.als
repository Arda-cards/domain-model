module operations/demand/demand_contracts

/*
 * DEMAND — CONTRACTS (DT-016/DT-017). The module's laws as NAMED predicates — curated few and
 * strong. CROSS-LOG LAWS DECLARE THEIR CONSISTENCY CLASS per the kit matrix (adopted 2026-07-06,
 * MP): same module + Operation → ATOMIC · same module + Notification → CONVERGENT/NOTIFICATION ·
 * different module + Operation → CONVERGENT/OPERATION · different module + Notification →
 * CONVERGENT/NOTIFICATION · human-resolvable → RECONCILED. Deployment plays NO role.
 *
 * Demand ↔ kanban interactions are DIFFERENT-MODULE Operations → **CONVERGENT/OPERATION**, with
 * the CALL-FIRST saga shape: the caller invokes the CYCLE operation first (Accept / Shelve /
 * StartProcessing / CompleteProcessing / ProductionFailure), reads its response, and only then
 * commits the demand operation — whose admission GUARD is the saga's commit gate (it reads the
 * member cycles' CURRENT states). Consequences the model embraces:
 *  - IN-FLIGHT INTERMEDIATES ARE LEGAL (suite boundary witnesses): an accepted-but-unattached
 *    cycle, a started member under a still-RELEASED demand, a settled member before Complete.
 *  - CONVERGENCE IS THE CALLER'S: retry the demand commit, or COMPENSATE with existing cycle
 *    kinds (Shelve un-accepts; ProductionFailure un-starts). No new compensation kinds needed.
 *  - The COMMIT-GATE laws below are guard-derived THEOREMS ("a committed demand operation saw
 *    its members at the expected saga state"); the QUIESCENCE law (`demandCyclesAlignedAt`) is
 *    t-parameterized — witnessed on settled traces and watched at runtime by the law probe,
 *    NEVER a global fact (that would outlaw the legal in-flight states).
 *
 * The R7 withdrawal reaction is CONVERGENT/NOTIFICATION; the frozen-state dangle is RECONCILED
 * (surfaced by `retiredMembersAt`, never a violation — a suite boundary witness). There is NO
 * uniqueness law for the (Item, Source Station) identity pair (R1 amended 2026-07-06): the
 * collation policy — which eligible cycle joins which DemandItem, and whether multiple OPEN
 * items per pair are allowed — is the CALLER's, served by the `demandsFor` read.
 */

open operations/demand/demand_types

// POOL MOVEMENTS (chain B-mov) and THE CYCLE CLAIM (chain A): the confined chain modules `demand_movement.als` and
// `demand_claim.als` and their roots LEFT THE TREE on 2026-11-05 (removed 2026-11-05: the intent chains and the saga are postponed, TN-003 row 2 / DT-015 D4; the Dafny tree is the reference model). The citation discipline they carried is the causal
// tree's (every row cites the activation that wrote it, DT-015 D1); membership stays the denormalisation below.

// `cycleIndivisible` below was a THEOREM of the retired claim chain wherever membership mirrored the heads; it stands on
// its own as the membership law. `demandOf` stays the
// membership read here — the head read `claimHolderOf` lives there. Re-run that root with any change here.

// ── C1 · cycle indivisibility (R1/R3) — single-log law ──────────────────────────────────────────
/** A cycle belongs to at most one live DemandItem at any moment (`demandOf` is at most one) —
    the module-owned INTEGRITY half of collation (the policy half is the caller's). */
pred cycleIndivisible { all t: Tick, c: CardCycle | lone demandOf[c, t] }

// ── C2 · the freeze family (R5) — single-log law ────────────────────────────────────────────────
/** Composition mutators (attach, remove, edit, detach) commit only in OPEN (Release is the freeze instant). */
pred frozenOutsideOpen {
  all o: demandMutators | committed[o] implies dPre[o].sStatus = DS_OPEN
}

// ── C3 · the saga commit gates (R3/R8) — CONVERGENT/OPERATION, call-first ───────────────────────
/** A committed attach saw its member ACCEPTED (cycle at REQUESTED — the prior cycle-side Accept
    is the saga's first leg; refusal flows back on ITS response). */
pred attachRequiresAccepted {
  all o: AttachOcc | (committed[o] and o.contribution in CardContribution) implies
    statusAt[cyclesOf[o.contribution], o.tick] = REQUESTED
}
/** A committed remove saw its member SHELVED back to the queue (cycle at REQUESTING). */
pred removeRequiresShelved {
  all o: RemoveContributionOcc, c: dPre[o].sContributions & CardContribution |
    (committed[o] and c.cid = o.target) implies statusAt[cyclesOf[c], o.tick] = REQUESTING
}
/** A committed StartProduction saw EVERY live member already IN_PROCESS (the caller's
    cycle-side StartProcessing calls preceded the commit). */
pred startProductionRequiresStarted {
  all o: StartProductionOcc | committed[o] implies
    (all c: preMemberCycles[o] | statusAt[c, o.tick] = IN_PROCESS)
}
/** A committed Distribute saw every asserted-full member already READY (the caller's
    CompleteProcessing calls preceded the commit; fullness itself is the caller's judgment —
    the keyed partial order may be indeterminate, R8). */
pred distributeRequiresReady {
  all o: DistributeOcc | committed[o] implies
    (all c: dPre[o].sContributions & CardContribution | c.cid in o.fills implies statusAt[cyclesOf[c], o.tick] = READY)
}
/** A committed Complete saw every live member SETTLED — none still IN_PROCESS (each settled by
    the caller: inventory → CompleteProcessing/READY, none → ProductionFailure/REQUESTING). The
    content ↔ branch correspondence is the caller's obligation, watched by the runtime probe —
    deliberately not a guard (it needs the pool-content fold). */
pred completeRequiresSettled {
  all o: CompleteOcc | committed[o] implies
    (no c: preMemberCycles[o] | statusAt[c, o.tick] = IN_PROCESS)
}

// ── C4 · the quiescence law (C/OP) — t-parameterized, NEVER a global fact ───────────────────────
/** demandCyclesAlignedAt — the demand ↔ cycle logs are settled at `t`: every live REQUESTED
    cycle is attached to a live demand (no attach saga mid-flight), no live demand holds a
    REQUESTING member (no remove saga mid-flight), and a RELEASED demand's live members all wait
    at REQUESTED (no production saga mid-flight). Holds at saga boundaries; legally FALSE
    in-flight — the runtime law probe watches it as the C/OP watchdog. */
pred demandCyclesAlignedAt[t: Tick] {
  all c: CardCycle | (liveCycleAt[c, t] and statusAt[c, t] = REQUESTED) implies some demandOf[c, t]
  all d: DemandItem | liveDemandAt[d, t] implies
    (no c: attachedLiveAt[d, t] | statusAt[c, t] = REQUESTING)
  all d: DemandItem | demandStatusAt[d, t] = DS_RELEASED implies
    (all c: attachedLiveAt[d, t] | statusAt[c, t] = REQUESTED)
}

// ── C5 · closure (R8; TN-004 rows 11 to 14, dafny-domain MD-082 and MD-084) — single-log laws ───
// `completeRequiresDistributed` and `completeRequiresRetiredHolding` LEFT with COORDINATOR-Q527 Option B's retired-holding
// gate (DT-016 PR B): a Complete no longer requires its holding retired or empty. The released pools are released AT REST
// by the status alone, and what they still hold is checked against the Complete's placements.
/** holdersReleasedAtComplete — after a committed Complete or Cancel the demand is not live, so neither it nor any of its
    contributions holds a pool: the release is DERIVED from the status (dafny-domain `HoldersReleasedAtComplete`). */
pred holdersReleasedAtComplete {
  all o: CompleteOcc + CancelOcc | committed[o] implies {
    not liveDemandAt[o.subject, o.tick]
    no c: ExternalContribution, e: EntityId | contributionHolds[o.subject, c, e, o.tick]
  }
}
/** completedItemsPlaced — the call-first law of the placements: every item a released pool held when a Complete committed
    has a locator under its placements and sits there as of the tick (dafny-domain `CompletedItemsPlaced`; a theorem of
    the RPlacementIncomplete and RUnplaced arms). The locator is the inventory-item module's read (`stateAt`). */
pred completedItemsPlaced {
  all o: CompleteOcc | committed[o] implies
    (all e: EntityId, x: InventoryItem | e -> x in heldByReleased[o] implies
       (some placedLocator[o.placements, e, x] and stateAt[x, o.tick].sLocator = placedLocator[o.placements, e, x]))
}
/** completeStampedAfterHolding — COORDINATOR-Q527 A5 in causal terms: every committed write of the holding pool causally
    before a committed Complete is dated at or before the Complete's own stamp. A theorem of the `RBackdatedHolding` arm
    (which reads the NEWEST write) and the pool's trace law `poolStampsMonotone`. */
pred completeStampedAfterHolding {
  all o: CompleteOcc, p: resolve[dPre[o].sHolding] & InventoryPool, w: poolWriteKinds |
    (committed[o] and committed[w] and w.subject = p and precedes[w.tick, o.tick]) implies atOrBefore[w.at, o.at]
}

// ── C6 · the withdrawal reaction (R7) — CONVERGENT/NOTIFICATION ─────────────────────────────────
/** The reaction kind reconciles: a committed DetachWithdrawn removes the withdrawn card's contribution and nothing
    else (TN-004: there is no stored intent to decrement — the quantity is read from the live contributions, and the
    withdrawn card had already left them). The quiescence reading ("no withdrawn
    member in an OPEN demand at quiescence") is the runtime law probe's job — in-flight
    intermediates are LEGAL (suite boundary witness), the emitter cannot fix a miss, the
    listener (this kind) restores. */
pred withdrawnDetachReconciles {
  all o: DetachWithdrawnOcc | committed[o] implies {
    dPost[o].sContributions = { c: dPre[o].sContributions | c.cid != o.target }
  }
}

// ── C8 · the ProductionDelivery subject (§8.1.2/§8.1.4, DT-020 build cut 3) ─────────────────────
/** A committed CreateDelivery saw its target IN_PROCESS and its POOL agreed with the target's
    item (§8.1.4 — both typed refusals at the guard; the OPEN→IN_PROCESS StartProduction
    choreography belongs to a service composite OUTSIDE the model, A4 caller-responsibility;
    item agreement here rather than as a downstream pool-homogeneity violation). RE-BASED (M3,
    DT-020 §8.5.3 / SPEARHEAD-D1 A′-2): was a direct `o.item = ...eId` equality against a
    caller-asserted Item; now the resolved pool's pin (vacuously true when `o.pool` doesn't
    resolve — a dangling ref carries no item claim to check). ATOMIC. */
pred createDeliveryGated {
  all o: CreateDeliveryOcc | committed[o] implies {
    demandStatusAt[resolve[o.subject.demandRef] & DemandItem, o.tick] = DS_IN_PROCESS
    (let p = resolve[o.pool] & InventoryPool | some p implies
       p.itemPin.subject = (resolve[o.subject.demandRef] & DemandItem).itemPin.subject)
  }
}
/** Create COMPOSES with RecordProduction (§8.1.2 compose-don't-subsume — ONE atomic demand
    commit; the model renders the tx as a both-or-neither pairing): every committed
    CreateDelivery has exactly one committed RecordProduction recording IT on its own target's
    log, and vice versa. The listener chain (ProductionRecorded → the order's receiptAccrues)
    rides the RecordProduction half UNTOUCHED. NOT in `guarantees` (the demandCyclesAlignedAt
    precedent, L9): no mock consumer relies on the pairing — the order's listener treats
    RecordProduction as its notification source regardless of PD reification, and putting it
    in the mock would force PD machinery into every consumer universe. Enforced by the
    implementation's composition facts; discharged in THIS module's suites. */
pred createRecordsAtomically {
  all c: CreateDeliveryOcc | committed[c] implies
    (one r: RecordProductionOcc | committed[r] and r.delivery = c.subject.eId)
  all r: RecordProductionOcc | committed[r] implies
    (one c: CreateDeliveryOcc | committed[c] and c.subject.eId = r.delivery
       and r.subject.eId = c.subject.demandRef)
}
/** Revoke COMPOSES with ExtractProduction — the symmetric §8.1.2 pair (same non-publication
    rationale). The content clause (holding ≥ contributed) is RUNTIME enforcement + probe —
    the standing I3 arity-4 exclusion. */
pred revokeExtractsAtomically {
  all v: RevokeDeliveryOcc | committed[v] implies
    (one x: ExtractProductionOcc | committed[x] and x.delivery = v.subject.eId)
  all x: ExtractProductionOcc | committed[x] implies
    (one v: RevokeDeliveryOcc | committed[v] and v.subject.eId = x.delivery
       and x.subject.eId = v.subject.demandRef)
}
/** Once REVOKED, forever REVOKED (SL-4; §8.1.1 reversing-entry semantics: the terminal record
    is kept, the delivery contributes NOTHING — `contributionsFor` excludes it forever). */
pred deliveryTerminalRevoke {
  all pd: ProductionDelivery, t1, t2: Tick |
    (notAfter[t1, t2] and deliveryStatusAt[pd, t1] = PD_REVOKED)
      implies deliveryStatusAt[pd, t2] = PD_REVOKED
}

// ── C9 · the exclusivity-lattice row (§8.5.3, DT-020 cut 4) — checks-not-facts ──────────────────
/** demandPoolGenesis — the §8.5.3 GENESIS PREMISE at demand's visibility (assume when: pools
    are minted inside their holder's own attach act — the ownership-by-genesis runtime
    discipline, monitored by the §8.5.3 integrity monitoring / PDEV-1424): no pool is named
    by two committed pool-attaching acts among the kinds demand can see (cycle
    StartProcessing, demand StartProduction). A NAMED PREMISE — never a fact: a discipline
    breach stays representable, and a weakened guard stays refusable (the R1 distinction).
    FOUR clauses since TN-004 (dafny-domain `DemandPoolGenesis`, DT-016 PR B): the fourth says a cycle's StartProcessing
    and an external attach never name one pool — the order "attach, then StartProcessing" is what no demand guard can
    refuse; the other order is RPoolNotFresh. */
pred demandPoolGenesis {
  all disj a, b: StartProcessingOcc | (committed[a] and committed[b]) implies no (a.pool & b.pool)
  all disj a, b: StartProductionOcc | (committed[a] and committed[b]) implies no (a.holding & b.holding)
  all a: StartProcessingOcc, b: StartProductionOcc |
    (committed[a] and committed[b]) implies no (a.pool & b.holding)
  all a: StartProcessingOcc, b: AttachOcc |
    (committed[a] and committed[b] and b.contribution in ExternalContribution) implies no (a.pool & b.contribution.cPool)
}
/** holdingProvenance — a demand item's holding pool is EXACTLY the pool its committed
    StartProduction named (DT-020 cut 5, the kanban poolProvenance twin — same L9 publication
    rationale: upper layers reason from attach-act payloads to record bindings). A theorem of
    the StartProduction effect + the sameHolding frames. */
pred holdingProvenance {
  all d: DemandItem, t: Tick | some demandStateAt[d, t].sHolding implies
    (some o: StartProductionOcc | committed[o] and o.subject = d and notAfter[o.tick, t]
       and demandStateAt[d, t].sHolding = o.holding)
}
/** holdingExclusiveWhileLive — the demand LATTICE ROW (§8.5.3): under the genesis premise,
    time-indexed over live holders, a holding pool is held by at most one LIVE demand and is
    never simultaneously a LIVE cycle's pool (the kinds demand can see; kanban's own row is
    `poolExclusiveWhileLive`, receiving's is `linePoolExclusiveWhileLive`, and the global
    pairwise row is dafny-domain's `PoolLattice.PoolLatticeGlobal`; the system tier keeps its
    finders, QA761). Guard-and-genesis-derived THEOREM —
    discharged at the UNIT tier since kanban published `poolProvenance` (cut 5; the cross-kind
    clause reasons from the attach payload to the record binding through it — before that
    publication the discharge needed kanban's real effects, the cut-4 integration-tier
    interim). */
pred holdingExclusiveWhileLive {
  demandPoolGenesis implies {
    all t: Tick, p: InventoryPool {
      lone { d: DemandItem | liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p }
      (some d: DemandItem | liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p)
        implies (no c: CardCycle | liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p)
    }
  }
}
/** holdingAttachedOnce — two committed StartProductions naming a holding name different pools, on any demands
    (dafny-domain `HoldingAttachedOnce`, MD-083: the freshness arm's theorem, so the premise's own clause for holdings is
    derivable). Stated for consumers and finders; NOT in `guarantees`: it was left out while a law joined the mock's promise
    only after a bounded check, and its scenario was too large for one in the unit root. Witness: unit_dem_twoFreshHoldings. */
pred holdingAttachedOnce {
  all disj a, b: StartProductionOcc | (committed[a] and committed[b]) implies no (a.holding & b.holding)
}
/** contributionFrom — the fourth holder's PROVENANCE (dafny-domain `ContributionFrom`; the `holdingProvenance` twin, the
    same L9 publication rationale): a live demand's external contribution naming a pool was attached by a committed attach
    of THAT demand, under that id, naming that pool (an edit keeps the id and the pool). What an upper layer reads to go
    from a held pool to the attach row — the receiving row `lineContributionPoolDisjoint` does. */
pred contributionFrom {
  all d: DemandItem, t: Tick, c: ExternalContribution, e: EntityId | contributionHolds[d, c, e, t] implies
    (some a: AttachOcc | committed[a] and a.subject = d and notAfter[a.tick, t]
       and a.contribution in ExternalContribution and a.contribution.cid = c.cid and a.contribution.cPool = e)
}
/** contributionPoolExclusiveWhileLive — the demand lattice row's FOURTH holder (TN-004; dafny-domain MD-086:
    `ContributionPoolExclusiveWhileLive`, `ContributionPoolNotAHolding`, `ContributionPoolNotACyclePool`): at every moment
    a pool is named by at most one external contribution of at most one LIVE demand, it is no live demand's holding, and
    — under the genesis premise (its fourth clause) — no live cycle's pool. Counted by OWNERS: a contribution is a value,
    so two demands holding equal contributions hold one atom. */
pred contributionPoolExclusiveWhileLive {
  all t: Tick, p: InventoryPool {
    lone { d: DemandItem | some c: ExternalContribution | contributionHolds[d, c, c.cPool, t] and resolve[c.cPool] = p }
    all d: DemandItem | lone { c: ExternalContribution | contributionHolds[d, c, c.cPool, t] and resolve[c.cPool] = p }
    (some d: DemandItem, c: ExternalContribution | contributionHolds[d, c, c.cPool, t] and resolve[c.cPool] = p) implies {
      no d2: DemandItem | liveDemandAt[d2, t] and resolve[demandStateAt[d2, t].sHolding] = p
      demandPoolGenesis implies (no k: CardCycle | liveCycleAt[k, t] and resolve[stateOfCycleAt[k, t].sPool] = p)
    }
  }
}

// ── C10 · the contributions (TN-004; reflects dafny-domain MD-076 to MD-080) — single-log laws ──
// Each is a LEMMA of the reference model (dafny-domain src/operations/demand/demand-contract.dfy), proven there for every
// log. They are stated here so consumers and finders can name them. They are NOT in `guarantees`. TN-005 D4 let a predicate
// join the mock's promise only after one bounded check against the guards as written here; the project owner's ruling
// QA779 (a), 2026-11-12, retired such checks, so which of these laws the mock promises is the classification's question.
/** releasedHasContribution — a committed Release saw at least one LIVE contribution (Dafny `ReleasedHasContribution`). */
pred releasedHasContribution {
  all o: ReleaseOcc | committed[o] implies some liveContributionsOf[dPre[o].sContributions, o.tick]
}
/** contributionIdOnce — a contribution id is attached at most ONCE on a demand's log, a removed id included (Dafny
    `ContributionIdOnce`). */
pred contributionIdOnce {
  all disj a, b: AttachOcc |
    (committed[a] and committed[b] and a.subject = b.subject) implies a.contribution.cid != b.contribution.cid
}
/** referenceUniquePerDemand — at every moment two contributions of one demand read different references (Dafny
    `ReferenceUniquePerDemand`; "read": a card's default is its card's serial). */
pred referenceUniquePerDemand {
  all d: DemandItem, t: Tick | all disj a, b: contributionsAt[d, t] |
    (some referenceOf[a] and some referenceOf[b]) implies referenceOf[a] != referenceOf[b]
}
/** contributionPoolMatchesItem — a committed external attach's pool is live, in the demand's tenant and carries the demand's
    item (Dafny `ContributionPoolMatchesItem` with its tenancy sibling). */
pred contributionPoolMatchesItem {
  all o: AttachOcc, e: ExternalContribution | (committed[o] and o.contribution = e) implies
    (some p: resolve[e.cPool] & InventoryPool |
       poolLiveAt[p, o.tick] and p.tenantId = o.subject.tenantId and p.itemPin.subject = o.subject.itemPin.subject)
}
/** contributionPoolAttachedOnce — no pool is named by two committed external attaches, of any demands (Dafny
    `ContributionPoolAttachedOnce`: the freshness arm's theorem). */
pred contributionPoolAttachedOnce {
  all disj a, b: AttachOcc |
    (committed[a] and committed[b] and (a.contribution + b.contribution) in ExternalContribution)
      implies a.contribution.cPool != b.contribution.cPool
}
/** notesWritableUntilRetire — a committed notes write (the demand's, or a contribution's) precedes the demand's tombstone
    (Dafny `NotesWritableUntilRetire`). */
pred notesWritableUntilRetire {
  all o: SetUserNotesOcc + SetContributionNotesOcc, dl: DeleteDemandOcc |
    (committed[o] and committed[dl] and dl.subject = o.subject) implies precedes[o.tick, dl.tick]
}

// ── C7 · terminal closure (SL-4 instance, R5/R7) — single-log law ───────────────────────────────
/** Once COMPLETE/CANCELED, forever closed: no later tick shows a live status (Delete/Retire
    keeps the terminal record — tombstoned retirement, II precedent). */
pred terminalClosure {
  all d: DemandItem, t1, t2: Tick |
    (notAfter[t1, t2]
       and (some s: demandStateAt[d, t1] | s.sStatus in DS_COMPLETE + DS_CANCELED))
      implies demandStatusAt[d, t2] in DS_COMPLETE + DS_CANCELED
}

// ── the promise ─────────────────────────────────────────────────────────────────────────────────
/** guarantees — the module's full promise: the conjunction of the published laws.
    (`demandCyclesAlignedAt` is deliberately NOT here — it is t-parameterized quiescence, not an
    invariant.) */
pred guarantees {
  cycleIndivisible
  and frozenOutsideOpen
  and attachRequiresAccepted
  and removeRequiresShelved
  and startProductionRequiresStarted
  and distributeRequiresReady
  and completeRequiresSettled
  and holdersReleasedAtComplete        // TN-004 row 11 (MD-084): the release at Complete and Cancel, derived; Dafny HoldersReleasedAtComplete
  and completedItemsPlaced             // TN-004 row 14 (MD-082): the placements' call-first law; Dafny CompletedItemsPlaced
  and completeStampedAfterHolding      // COORDINATOR-Q527 A5: the stamp condition in causal terms
  and withdrawnDetachReconciles
  and terminalClosure
  and createDeliveryGated       // §8.1.4 (vacuous in PD-free consumer universes)
  and deliveryTerminalRevoke    // §8.1.1 (likewise vacuous without PDs)
  and holdingProvenance         // cut 5 (the kanban poolProvenance twin; L9 publication)
  and holdingExclusiveWhileLive // §8.5.3 lattice row (premise-conditional; unit-tier discharge since cut 5)
  and contributionFrom          // the fourth holder's provenance (TN-004, dafny-domain ContributionFrom)
  and contributionPoolExclusiveWhileLive // the row's fourth holder (TN-004, MD-086; its cycle clause premise-conditional); Dafny ContributionPoolExclusiveWhileLive
  // createRecordsAtomically / revokeExtractsAtomically: deliberately NOT here — see C8.
}
