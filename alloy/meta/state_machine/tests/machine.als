module meta/state_machine/tests/machine
// Reflects dafny-domain src/meta/tests/state-machine-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/state_machine/machine

/*
 * Generic-framework unit suite, exercised on a synthetic 2-state machine:
 *   S0 --Go--> S1 --Go--> S0 ;  Stay = self-loop from either state.
 * Confirms the framework is consistent and that the generic properties hold for a
 * well-formed machine.
 */

one sig S0, S1 extends State {}
one sig Go, Stay extends Signal {}

abstract sig TT extends Transition {}
one sig T_go   extends TT {} { from = S0      and on = Go   and to = S1 and no guard }
one sig T_back extends TT {} { from = S1      and on = Go   and to = S0 and no guard }
one sig T_stay extends TT {} { from = S0 + S1 and on = Stay and no to  and no guard }

one sig M extends StateMachine {}
fact MDef {
  M.states = State and M.signals = Signal and M.start = S0 and M.transitions = TT
}

// SAT: the framework + synthetic machine admit an instance.
run unit_sm_loads {} for 4 but exactly 2 State, exactly 2 Signal, exactly 3 Transition, exactly 1 StateMachine, 0 Guard expect 1

// Holds: every state reachable from the start; every signal labels a transition.
check unit_sm_allReachable { allStatesReachable[M] }
  for 4 but exactly 2 State, exactly 2 Signal, exactly 3 Transition, exactly 1 StateMachine, 0 Guard expect 0
check unit_sm_liveSignals  { liveSignals[M] }
  for 4 but exactly 2 State, exactly 2 Signal, exactly 3 Transition, exactly 1 StateMachine, 0 Guard expect 0

// firedInto agrees with the edges: Go can land at either S1 (T_go) or S0 (T_back);
// Stay (self-loop) holds either state.
check unit_sm_firedInto {
  firedInto[M, S1, Go]
  firedInto[M, S0, Go]
  firedInto[M, S0, Stay]
  firedInto[M, S1, Stay]
} for 4 but exactly 2 State, exactly 2 Signal, exactly 3 Transition, exactly 1 StateMachine, 0 Guard expect 0
