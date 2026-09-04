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

// POOL MOVEMENTS (chain B-mov, DT-029 E6 / SAMWISE-S1 / MINESWEEPER-Q7 = A): the demand's movement legs — merge,
// extract, transfer — ride a MOVEMENT-semantics intent chain keyed by the pool, governed by the CONFINED module
// `demand_movement.als` and verified in its own root `tests/unit/demand_movement.als` (C-2 cone confinement, the
// demand_reset.als precedent). An edit to THIS module's laws propagates into that root's cone (it opens the real
// implementation) — re-run it with any change here. No law below reads the chain; none may without opening it.

// THE CYCLE CLAIM (chain A, DT-029 E6 / DT-027 §6.1 the additive arm): the demand's claim on a cycle rides a
// HOLD-semantics intent chain keyed by the cycle, governed by the CONFINED module `demand_claim.als` and verified in
// its own root `tests/unit/demand_claim.als` (the same confinement, for the same reason). `cycleIndivisible` below is a
// THEOREM of that chain wherever membership mirrors the heads (`cycleIndivisibleFromChain`); `demandOf` stays the
// membership read here — the head read `claimHolderOf` lives there. Re-run that root with any change here.

// ── C1 · cycle indivisibility (R1/R3) — single-log law ──────────────────────────────────────────
/** A cycle belongs to at most one live DemandItem at any moment (`demandOf` is at most one) —
    the module-owned INTEGRITY half of collation (the policy half is the caller's). */
pred cycleIndivisible { all t: Tick, c: CardCycle | lone demandOf[c, t] }

// ── C2 · the freeze family (R5) — single-log law ────────────────────────────────────────────────
/** Composition/intent mutators commit only in OPEN (Release is the freeze instant). */
pred frozenOutsideOpen {
  all o: demandMutators | committed[o] implies dPre[o].sStatus = DS_OPEN
}

// ── C3 · the saga commit gates (R3/R8) — CONVERGENT/OPERATION, call-first ───────────────────────
/** A committed attach saw its member ACCEPTED (cycle at REQUESTED — the prior cycle-side Accept
    is the saga's first leg; refusal flows back on ITS response). */
pred attachRequiresAccepted {
  all o: CreateWithCycleOcc + AddCycleOcc | committed[o] implies
    statusAt[resolve[o.member] & CardCycle, o.tick] = REQUESTED
}
/** A committed remove saw its member SHELVED back to the queue (cycle at REQUESTING). */
pred removeRequiresShelved {
  all o: RemoveCycleOcc | committed[o] implies
    statusAt[resolve[o.member] & CardCycle, o.tick] = REQUESTING
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
    (all m: o.fills | statusAt[resolve[m] & CardCycle, o.tick] = READY)
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

// ── C5 · closure guards (R8) — single-log law ───────────────────────────────────────────────────
/** Complete requires everything produced to be gone from the holding pool — distributed to
    members or placed at a locator ("never had any" satisfies vacuously). */
pred completeRequiresDistributed {
  all o: CompleteOcc | committed[o] implies
    no heldAt[resolve[dPre[o].sHolding] & InventoryPool, o.tick]
}

// ── C6 · the withdrawal reaction (R7) — CONVERGENT/NOTIFICATION ─────────────────────────────────
/** The reaction kind reconciles: a committed DetachWithdrawn removes the member and decrements
    the intent by the member's genesis-fixed quantity. The quiescence reading ("no withdrawn
    member in an OPEN demand at quiescence") is the runtime law probe's job — in-flight
    intermediates are LEGAL (suite boundary witness), the emitter cannot fix a miss, the
    listener (this kind) restores. */
pred withdrawnDetachReconciles {
  all o: DetachWithdrawnOcc | committed[o] implies {
    dPost[o].sMembership = dPre[o].sMembership - o.member
    qtyMap[dPost[o].sDemandQty] =
      add[qtyMap[dPre[o].sDemandQty], negate[effectiveQtyMap[resolve[o.member] & CardCycle]]]
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
    breach stays representable, and a weakened guard stays refusable (the R1 distinction). */
pred demandPoolGenesis {
  all disj a, b: StartProcessingOcc | (committed[a] and committed[b]) implies no (a.pool & b.pool)
  all disj a, b: StartProductionOcc | (committed[a] and committed[b]) implies no (a.holding & b.holding)
  all a: StartProcessingOcc, b: StartProductionOcc |
    (committed[a] and committed[b]) implies no (a.pool & b.holding)
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
    pairwise row is check-only in the system tier). Guard-and-genesis-derived THEOREM —
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
  and completeRequiresDistributed
  and withdrawnDetachReconciles
  and terminalClosure
  and createDeliveryGated       // §8.1.4 (vacuous in PD-free consumer universes)
  and deliveryTerminalRevoke    // §8.1.1 (likewise vacuous without PDs)
  and holdingProvenance         // cut 5 (the kanban poolProvenance twin; L9 publication)
  and holdingExclusiveWhileLive // §8.5.3 lattice row (premise-conditional; unit-tier discharge since cut 5)
  // createRecordsAtomically / revokeExtractsAtomically: deliberately NOT here — see C8.
}
