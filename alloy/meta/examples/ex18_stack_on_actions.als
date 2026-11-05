module meta/examples/ex18_stack_on_actions

/*
 * PATTERN:  ex16's tray stack REBUILT on the completed Action machinery — the end of the ladder:
 *           ex16 Model 2 had bare ops and made illegal logs UNREPRESENTABLE (discipline as fact);
 *           here every op is a full StatefulAction: pop-on-empty is REPRESENTABLE BUT REFUSED
 *           (recorded, with reasons), guards are witnessed, snapshots chain, and the state read is
 *           LOCF of records. Note the structural free ride RETURNS: the snapshot record carries
 *           Model 1's held `seq` as a VALUE, so LIFO is free again — snapshots give the log model
 *           Model 1's structures without Model 1's clocks.
 * UML:      command + guard + event store with mementos.
 * FP:       scan-carrying-state over a validated event stream; refusals are Left values that
 *           still appear in the output list.
 * USE WHEN:  the definitive self-contained template for a domain occurrence log (the InventoryItem
 *           build's shape): kinds + typed bindings, unconditional chaining, value-parameterized
 *           cores, witnessed guards/Effects, LOCF read, invariant-as-theorem, delta agreement.
 * AVOID:     conditional chaining (`committed[a] implies a.pre = …` — a refused action still READ
 *           the real state; a free `pre` lets the solver justify any refusal), and discipline-as-
 *           fact when you need the audit trail (that was ex16's deliberate simplification).
 * SEE ALSO:  ex16 (the same stack, both bare time models); ex17 (snapshot chains); meta/action/
 *           stateful; workbook design-topics/dt-006 §Build preparation.
 *
 * Neutral cast: the room-service TRAY STACK again (learn it once — ex16's cast).
 */

open meta/action/stateful   // StatefulAction (pre/post), Snapshot; re-exports action + Tick order

/** Tray — a physical tray (the stacked element). */
sig Tray {}

/** StackState — the snapshot record: the whole stack AS A VALUE (top = first). LIFO comes free
    from the seq — the record smuggles Model 1's structure into the log world. */
sig StackState extends Snapshot { trays: seq Tray }

// ── the action kinds (one implicit subject: THE stack) ──────────────────────────────────────────
abstract sig StackAction extends StatefulAction {}
fact StackSnapshotsAreStackStates { all a: StackAction | a.pre in StackState and a.post in StackState }

/** PushA — stack a tray (an input binding: the tray). */
sig PushA extends StackAction { tray: one Tray } { bindings = tray }
/** PopA — take the top tray (no parameters; the state decides what comes off). */
sig PopA extends StackAction {} { no bindings }

// ── UNCONDITIONAL chaining: every action (committed OR refused) read the real prior state ────────
fun prior[a: StackAction]: lone StackAction {
  { b: StackAction | committed[b] and precedes[b.tick, a.tick]
      and (no c: StackAction | committed[c] and precedes[b.tick, c.tick] and precedes[c.tick, a.tick]) }
}
fact StackChaining { all a: StackAction | a.pre = prior[a].post }

/** traysBefore — what the admission guard reads: the prior snapshot's seq, or the empty opening. */
fun traysBefore[a: StackAction]: seq Tray { some a.pre => a.pre.trays else (none -> none) }

// ── transition CORES: value-parameterized (any carrier could instantiate these) ─────────────────
pred pushT[sBefore, sAfter: seq Tray, t: Tray] { sAfter = insert[sBefore, 0, t] }
pred popT[sBefore, sAfter: seq Tray]           { some sBefore and sAfter = sBefore.rest }

// ── WITNESSING: verdicts ⟺ evaluable guards; committed Effects ⟺ the cores ──────────────────────
fact PushAdmission { all a: PushA | a.admission = Accepted }                       // always admissible
fact PopAdmission  { all a: PopA  | a.admission = Accepted iff some traysBefore[a] }
fact PushEffect    { all a: PushA | committed[a] implies pushT[traysBefore[a], a.post.trays, a.tray] }
fact PopEffect     { all a: PopA  | committed[a] implies popT[traysBefore[a], a.post.trays] }

// ── the state read: LOCF of records ─────────────────────────────────────────────────────────────
fun traysAt[t: Tick]: seq Tray {
  let last = { a: StackAction | a in committedUpTo[t]
                 and (no b: StackAction | b in committedUpTo[t] and precedes[a.tick, b.tick]) } |
  some last => last.post.trays else (none -> none)
}

// ── it works (expect SAT) ────────────────────────────────────────────────────────────────────────
// The ex16 chain — push x · push y · pop — all committed; the read afterwards holds exactly ⟨x⟩.
run unit_ex18_chainThenRead {
  some disj x, y: Tray, disj q1, q2: PushA, p: PopA |
    q1.tray = x and q2.tray = y
    and precedes[q1.tick, q2.tick] and precedes[q2.tick, p.tick]
    and committed[q1] and committed[q2] and committed[p]
    and traysAt[p.tick].elems = x and #traysAt[p.tick] = 1
} for 4 but 5 Int expect 1

// Pop-on-empty is REFUSED AND RECORDED — ex16 made this unrepresentable; the audit trail keeps it.
run unit_ex18_popEmptyRefused {
  some p: PopA | refusedAtAdmission[p] and some refusalReasons[p] and no traysBefore[p]
} for 4 but 5 Int expect 1

// ── LIFO as THEOREM: a committed pop removed exactly the most recent surviving push ──────────────
assert unit_ex18_popTakesTop {
  all p: PopA | committed[p] implies p.post.trays = p.pre.trays.rest and some p.pre.trays
}
check unit_ex18_popTakesTop for 4 but 5 Int expect 0

// ── the delta agreement (the ex14/ex16/ex17 echo): LOCF size ≡ pushes − pops, at every tick ──────
assert unit_ex18_sizeMatchesDeltas {
  all t: Tick |
    #traysAt[t] = (#{ a: PushA | a in committedUpTo[t] }).minus[#{ a: PopA | a in committedUpTo[t] }]
}
check unit_ex18_sizeMatchesDeltas for 4 but 5 Int expect 0
