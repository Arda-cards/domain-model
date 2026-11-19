module shared/x731_state/tests/state
// Reflects dafny-domain src/shared/x731-state/tests/state-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/state_machine/machine
open shared/x731_state/state

/*
 * X.731 suite. The interlock holds (relocated check; name kept), a valid resource
 * exists, and each region machine is well-formed (all states reachable, signals
 * live). Scope pins the reified families: 8 State, 10 Signal, 10 Transition,
 * 3 StateMachine, 0 Guard; Resource left at the global scope.
 */

check X731Consistency
  for 4 but 8 State, 10 Signal, 10 Transition, 3 StateMachine, 0 Guard expect 0

run someResource { some Resource }
  for 4 but 8 State, 10 Signal, 10 Transition, 3 StateMachine, 0 Guard expect 1

check x731_op_reachable    { allStatesReachable[OperationalMachine] }
  for 4 but 8 State, 10 Signal, 10 Transition, 3 StateMachine, 0 Guard expect 0
check x731_usage_reachable { allStatesReachable[UsageMachine] }
  for 4 but 8 State, 10 Signal, 10 Transition, 3 StateMachine, 0 Guard expect 0
check x731_admin_reachable { allStatesReachable[AdministrativeMachine] }
  for 4 but 8 State, 10 Signal, 10 Transition, 3 StateMachine, 0 Guard expect 0
check x731_liveSignals {
  liveSignals[OperationalMachine]
  liveSignals[UsageMachine]
  liveSignals[AdministrativeMachine]
} for 4 but 8 State, 10 Signal, 10 Transition, 3 StateMachine, 0 Guard expect 0
