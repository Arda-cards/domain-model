module meta/activation/tests/activation

open meta/activation/activation

/*
 * Suite for the activation module (DT-015 D1 to D3). Reflects dafny-domain src/meta/tests/activation-tests.dfy: two
 * services (a desk that originates, a bar it calls), one entity row family per service, each log activated by its
 * service. The witnesses mint the `Call` their rows cite; the theorems re-check what the kernel already gives the tree
 * (effects follow their act, callers precede, no proper cycle) so a change to either module is caught here.
 */

sig Thing {}
one sig Desk, Bar extends Service {}

/** DeskEffect / BarEffect — one entity row family per service (an Action on a Thing). */
sig DeskEffect extends Action { subject: one Thing } { bindings = subject }
sig BarEffect  extends Action { subject: one Thing } { bindings = subject }

fact DeskActivated { activated[Desk, DeskEffect] }
fact BarActivated  { activated[Bar, BarEffect] }

// ── witnesses ───────────────────────────────────────────────────────────────────────────────────
// An origin: an activation citing itself, committed, writing one row.
run unit_act_originWritesRow {
  some a: Call, e: DeskEffect | origin[a] and committed[a] and committed[e] and e.arche = a
} for 4 expect 1

// THE SIBLING WITNESS (MP, Journal 192741; D3): one activation writes TWO committed rows on ONE subject.
run unit_act_siblingEffectsOneSubject {
  some a: Call, t: Thing, disj e, f: DeskEffect |
    committed[a] and committed[e] and committed[f] and e.arche = a and f.arche = a and e.subject = t and f.subject = t
} for 4 expect 1

// A nested call: the desk's origin calls the bar; the bar's activation cites the desk's and writes the bar's row.
run unit_act_nestedCall {
  some disj a, b: Call, e: BarEffect |
    origin[a] and a.service = Desk and b.arche = a and b.service = Bar and committed[a] and committed[b]
    and e.arche = b and committed[e]
} for 5 expect 1

// A refused activation's effect is refused with it — and is still a row.
run unit_act_refusedAgrees {
  some a: Call, e: DeskEffect | refusedAtAdmission[a] and e.arche = a and refusedAtAdmission[e]
} for 4 expect 1

// A pass-through activation: admitted, with no effect.
run unit_act_passThrough {
  some a: Call | committed[a] and no effectsOf[a, Action]
} for 4 expect 1

// ── negative controls (UNSAT = the law bites) ───────────────────────────────────────────────────
// An effect whose verdict differs from its activation's is unrepresentable (Dafny: `!EffectsAgree(lying, …)`).
run unit_act_lyingVerdict {
  some e: DeskEffect | committed[e] and not committed[e.arche]
} for 5 expect 0

// An effect refused for ANOTHER reason than its activation is unrepresentable: the agreement is the whole verdict (Dafny
// `EffectsAgree` with `Same`, the dafny-domain PR 31 review; R4). RED on the tree before bd05604: only the commit bit agreed.
run unit_act_otherReason {
  some e: DeskEffect | refusedAtAdmission[e] and refusalReasons[e] != refusalReasons[e.arche]
} for 5 expect 0

// An entity row is never cited: it is a leaf of the tree (D1).
run unit_act_effectCited {
  some o: Occurrence, e: DeskEffect + BarEffect | o.arche = e
} for 5 expect 0

// An entity row never self-cites (D1).
run unit_act_effectSelfCites {
  some e: DeskEffect + BarEffect | e.arche = e
} for 5 expect 0

// A desk row citing a bar activation is unrepresentable: the act is the service's own.
run unit_act_crossServiceCitation {
  some e: DeskEffect | e.arche.service = Bar
} for 5 expect 0

// ── theorems (check; UNSAT = holds) ─────────────────────────────────────────────────────────────
// Effects follow their act (Dafny `EffectsFollow`; the kernel's `ArcheOriginPrecedes` through D1).
assert unit_act_effectsFollow { all e: DeskEffect + BarEffect | precedes[e.arche.tick, e.tick] }
check unit_act_effectsFollow for 5 expect 0

// Callers precede (Dafny `CallersPrecede`): a non-origin activation follows the activation it cites.
assert unit_act_callersPrecede { all a: Activation | not origin[a] implies precedes[a.arche.tick, a.tick] }
check unit_act_callersPrecede for 5 expect 0

// No proper cycle (Dafny `NoProperCycle`): the only loop in the tree is an origin's self-citation.
assert unit_act_noProperCycle { all o: Occurrence | o in o.^arche implies origin[o] }
check unit_act_noProperCycle for 5 expect 0

// Every walk ends at an origin: the tree is rooted.
assert unit_act_walkEndsAtOrigin { all o: Occurrence | some origins & o.*arche }
check unit_act_walkEndsAtOrigin for 5 expect 0

// The origins are exactly the kernel's self-initiated occurrences.
assert unit_act_originsAreSelfInitiated { origins = selfInitiated }
check unit_act_originsAreSelfInitiated for 5 expect 0
