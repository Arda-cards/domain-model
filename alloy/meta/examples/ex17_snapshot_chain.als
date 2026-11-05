module meta/examples/ex17_snapshot_chain

/*
 * PATTERN:  Snapshot-carrying occurrences (meta/action/stateful, the as-of-read pattern — DT-006
 *           build prep): each committed action records the state it read (`pre`) and produced
 *           (`post`); state-at-t is LOCF OF RECORDS (one reducer, no fold zoo);  guards read the
 *           materialized `pre` (field access, not prefix folds); domain CHAINING ties one
 *           action's `post` to the next one's `pre`; transition semantics are VALUE-
 *           PARAMETERIZED CORES witnessed per kind; and the domain invariant (balance ≥ 0) is a
 *           THEOREM derived from the guards — not a fact (the invariant role-change: enforcement
 *           belongs to guards once refusals are recorded). Punchline: a mini agreement theorem —
 *           the LOCF-of-snapshots read equals the delta-cumulative view.
 * UML:      event store with per-event state snapshots; memento.
 * FP:       scan-carrying-state: each event stores the accumulator it produced; read = last.
 * USE WHEN:  translating a rich mutable entity to the log world (the InventoryItemState recipe):
 *           many fields / mixed reducers / derived guards — snapshots collapse all of it to LOCF.
 * AVOID:     delta-primary logs for state with resets/couplings (the reducer zoo — see the DT-006
 *           build-prep analysis), and stating domain invariants as FACTS on the log (that bans the
 *           refused attempts the audit trail exists to record — derive them from guards instead).
 * SEE ALSO:  meta/action/stateful; ex15 (guards/witnessing); ex16 (two time models);
 *           workbook design-topics/dt-006 §Build preparation; modeling/two-time-models.md.
 *
 * Neutral cast: a guest FOLIO (running bill). Charge adds, Payment subtracts; a payment may not
 * exceed the balance. Opening balance is 0.
 */

open meta/action/stateful   // StatefulAction (pre/post), Snapshot; re-exports action (committed, committedUpTo, …)

/** Folio — a guest's running bill (the subject; in the live model: an Entity). */
sig Folio {}

/** FolioState — the domain's snapshot record: the folio's mutable payload at one moment.
    NOTE: deliberately NO "balance ≥ 0" fact here — non-negativity is PROVEN from the guards below. */
sig FolioState extends Snapshot { balance: Int }

// ── the action kinds: typed binding field + snapshot typing ─────────────────────────────────────
abstract sig FolioAction extends StatefulAction { folio: one Folio } { bindings = folio }
fact FolioSnapshotsAreFolioStates { all a: FolioAction | a.pre in FolioState and a.post in FolioState }

// Amounts are bounded (1..3) so the ≤4 actions' sums stay inside the 5-bit Int range: UNBOUNDED
// amounts let `plus` WRAP (15+15 < 0) and the non-negativity theorem falsifies through a charge —
// the scalar_int overflow lesson (order breaks under wraparound; the live model uses the abstract
// `Scalar` ring + premises, never native Int — see modeling/scalar-arithmetic.md).
/** Charge — adds `amount` to the balance. */
sig Charge  extends FolioAction { amount: Int } { amount > 0 and amount <= 3 }
/** Payment — subtracts `amount`; admissible only up to the current balance. */
sig Payment extends FolioAction { amount: Int } { amount > 0 and amount <= 3 }

// ── domain CHAINING: my `pre` is the `post` of the latest earlier committed action on my folio ──
fun prior[a: FolioAction]: lone FolioAction {
  { b: FolioAction | committed[b] and b.folio = a.folio and precedes[b.tick, a.tick]
      and (no c: FolioAction | committed[c] and c.folio = a.folio
             and precedes[b.tick, c.tick] and precedes[c.tick, a.tick]) }
}
// UNCONDITIONAL: a REFUSED action still READ the real prior state — if `pre` were free on refused
// actions, the solver could invent a state that "justifies" any refusal and the guard would be gamed.
fact FolioChaining { all a: FolioAction | a.pre = prior[a].post }

/** balBefore — what the admission guard reads: the pre-snapshot's balance, or the opening 0. */
fun balBefore[a: FolioAction]: Int { some a.pre => a.pre.balance else 0 }

// ── transition CORES: value-parameterized (the shared-spec style — usable by ANY carrier) ───────
pred chargeT[balBefore, balAfter, amt: Int] { balAfter = balBefore.plus[amt] }
pred payT[balBefore, balAfter, amt: Int]    { amt <= balBefore and balAfter = balBefore.minus[amt] }

// ── WITNESSING: verdicts tied to evaluable guards; Effects tied to the cores ─────────────────────
fact ChargeAdmission  { all a: Charge  | a.admission = Accepted }                          // always admissible
fact PaymentAdmission { all a: Payment | a.admission = Accepted iff a.amount <= balBefore[a] }
fact ChargeEffect     { all a: Charge  | committed[a] implies chargeT[balBefore[a], a.post.balance, a.amount] }
fact PaymentEffect    { all a: Payment | committed[a] implies payT[balBefore[a], a.post.balance, a.amount] }

// ── the state read: LOCF of records (the ONLY reducer) ───────────────────────────────────────────
fun balanceAt[f: Folio, t: Tick]: Int {
  let last = { a: FolioAction | a in committedUpTo[t] and a.folio = f
                 and (no b: FolioAction | b in committedUpTo[t] and b.folio = f
                        and precedes[a.tick, b.tick]) } |
  some last => last.post.balance else 0
}

// ── it works (expect SAT) ────────────────────────────────────────────────────────────────────────
// A chain charge(3) · charge(3) · pay(2) on one folio, all committed, reads 4 at the end.
run unit_ex17_chainThenRead {
  some f: Folio, disj c1, c2: Charge, p: Payment |
    c1.folio = f and c2.folio = f and p.folio = f
    and precedes[c1.tick, c2.tick] and precedes[c2.tick, p.tick]
    and c1.amount = 3 and c2.amount = 3 and p.amount = 2
    and committed[c1] and committed[c2] and committed[p]
    and balanceAt[f, p.tick] = 4
} for 4 but 5 Int expect 1

// An over-payment is REFUSED and recorded with reasons (not unrepresentable — the audit trail).
run unit_ex17_overpayRefused {
  some p: Payment | refusedAtAdmission[p] and some refusalReasons[p]
} for 4 but 5 Int expect 1

// ── invariant as THEOREM (check; UNSAT = holds): non-negativity FOLLOWS from the guards ──────────
assert unit_ex17_balanceNeverNegative {
  all f: Folio, t: Tick | balanceAt[f, t] >= 0
}
check unit_ex17_balanceNeverNegative for 4 but 5 Int expect 0

// ── mini AGREEMENT theorem: LOCF-of-snapshots ≡ the delta-cumulative view (the ex14/ex16 echo) ───
assert unit_ex17_locfMatchesDeltas {
  all f: Folio, t: Tick |
    balanceAt[f, t] =
      (sum c: { x: Charge  | x in committedUpTo[t] and x.folio = f } | c.amount).minus[
       sum p: { x: Payment | x in committedUpTo[t] and x.folio = f } | p.amount]
}
check unit_ex17_locfMatchesDeltas for 4 but 5 Int expect 0
