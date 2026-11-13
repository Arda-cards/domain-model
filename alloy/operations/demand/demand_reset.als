module operations/demand/demand_reset

/*
 * DEMAND — the CONFINED ResetQty Σ (R3b: THE arity-4 entrant). Opened ONLY by its dedicated
 * root (tests/unit/demand_reset.als). Reflects dafny-domain src/operations/demand/demand.dfy: under QA704 Q3 (a)
 * (MP, 2026-11-05) the guard computes the sum, the effect stores the fold and `ResetSnapsToSum` is the reference
 * model's theorem; this module is that effect at the witness sizes, a class-2 extension (alloy/EXTENSIONS.md) —
 * kept confined for the solver budget below, not retired (DT-015's plan said retired; the budget decided). FINDING (2026-07-06, solver-limits): even confined, the
 * demand cone CANNOT carry the keyed_sum fold — the transitive vocabulary (kanban + II + item)
 * fixes ~250+ atoms into every universe, past Kodkod's ~215-atom arity-4 ceiling. So the Σ is
 * stated CASE-WISE for the witness sizes (0/1/2 live members — exact) and left UNCONSTRAINED
 * beyond; the general fold returns with the spine's F2 fold-ergonomics work (or a vocabulary
 * diet at the kanban four-file cut). The runtime computes the real Σ without ceilings — this is
 * a solver-budget artifact, not a domain rule (R3b note).
 */

open operations/demand/demand_implementation

/** THE Σ EFFECT (case-wise): the committed ResetQty snaps the intent to the live members' Σ of
    genesis-fixed effective quantities; empty membership → the keyed zero (the emptied DemandItem
    PERSISTS — R3b). */
fact ResetQtySum {
  all o: ResetQtyOcc | committed[o] implies {
    let ms = preMemberCycles[o] | {
      (no ms)   implies no qtyMap[dPost[o].sDemandQty]
      (one ms)  implies qtyMap[dPost[o].sDemandQty] = effectiveQtyMap[ms]
      (#ms = 2) implies (some disj c1, c2: ms |
        qtyMap[dPost[o].sDemandQty] = add[effectiveQtyMap[c1], effectiveQtyMap[c2]])
      // #ms > 2: unconstrained HERE (see the header finding) — dedicated-root scopes stay ≤ 2.
    }
  }
}
