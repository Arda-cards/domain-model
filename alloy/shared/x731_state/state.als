module shared/x731_state/state

open meta/state_machine/machine

/*
 * ITU-T X.731 resource state model, expressed with the generic state-machine
 * framework (DT-003): three orthogonal REGIONS, each a reified StateMachine, plus
 * the X.731 interlocks as cross-region invariants on the Resource host. This mirrors
 * how the email config runs parallel StateEngine machines (Operational ∥
 * Administrative) on one host. Multi-region = a host with several state fields, each
 * bound (by type) to a region machine; no separate Region sig (DT-003).
 */

// --- Operational region: physical health / capability -----------------------
/** OperationalState — X.731 operational region: physical health / capability (ENABLED, DISABLED). */
abstract sig OperationalState extends State {}
one sig ENABLED, DISABLED extends OperationalState {}
/** OperationalSignal — events driving the operational region (ENABLE, DISABLE). */
abstract sig OperationalSignal extends Signal {}
one sig DISABLE, ENABLE extends OperationalSignal {}

one sig OperationalMachine extends StateMachine {}
abstract sig OpTransition extends Transition {}
one sig XOp_disable extends OpTransition {} { from = ENABLED  and on = DISABLE and to = DISABLED }
one sig XOp_enable  extends OpTransition {} { from = DISABLED and on = ENABLE  and to = ENABLED }
fact OperationalMachineDef {
  OperationalMachine.states      = OperationalState
  OperationalMachine.signals     = OperationalSignal
  OperationalMachine.start       = ENABLED
  OperationalMachine.transitions = OpTransition
  all t: OpTransition | no t.guard
}

// --- Usage region: process loading ------------------------------------------
/** UsageState — X.731 usage region: process loading (IDLE, ACTIVE, BUSY). */
abstract sig UsageState extends State {}
one sig IDLE, ACTIVE, BUSY extends UsageState {}
/** UsageSignal — events driving the usage region. */
abstract sig UsageSignal extends Signal {}
one sig ACQUIRE, SATURATE, RELIEVE, QUIESCE extends UsageSignal {}

one sig UsageMachine extends StateMachine {}
abstract sig UsageTransition extends Transition {}
one sig XUse_acquire  extends UsageTransition {} { from = IDLE   and on = ACQUIRE  and to = ACTIVE }
one sig XUse_saturate extends UsageTransition {} { from = ACTIVE and on = SATURATE and to = BUSY }
one sig XUse_relieve  extends UsageTransition {} { from = BUSY   and on = RELIEVE  and to = ACTIVE }
one sig XUse_quiesce  extends UsageTransition {} { from = ACTIVE and on = QUIESCE  and to = IDLE }
fact UsageMachineDef {
  UsageMachine.states      = UsageState
  UsageMachine.signals     = UsageSignal
  UsageMachine.start       = IDLE
  UsageMachine.transitions = UsageTransition
  all t: UsageTransition | no t.guard
}

// --- Administrative region: policy control ----------------------------------
/** AdministrativeState — X.731 administrative region: policy control (UNLOCKED, LOCKED, SHUTTING_DOWN). */
abstract sig AdministrativeState extends State {}
one sig UNLOCKED, LOCKED, SHUTTING_DOWN extends AdministrativeState {}
/** AdministrativeSignal — events driving the administrative region. */
abstract sig AdministrativeSignal extends Signal {}
one sig LOCK, UNLOCK, SHUTDOWN, DRAINED extends AdministrativeSignal {}

one sig AdministrativeMachine extends StateMachine {}
abstract sig AdminTransition extends Transition {}
one sig XAdm_lock     extends AdminTransition {} { from = UNLOCKED               and on = LOCK     and to = LOCKED }
one sig XAdm_shutdown extends AdminTransition {} { from = UNLOCKED               and on = SHUTDOWN and to = SHUTTING_DOWN }
one sig XAdm_drained  extends AdminTransition {} { from = SHUTTING_DOWN          and on = DRAINED  and to = LOCKED }
one sig XAdm_unlock   extends AdminTransition {} { from = LOCKED + SHUTTING_DOWN and on = UNLOCK   and to = UNLOCKED }
fact AdministrativeMachineDef {
  AdministrativeMachine.states      = AdministrativeState
  AdministrativeMachine.signals     = AdministrativeSignal
  AdministrativeMachine.start       = UNLOCKED
  AdministrativeMachine.transitions = AdminTransition
  all t: AdminTransition | no t.guard
}

// --- Resource: a three-region host ------------------------------------------
// Concrete resources (Equipment, Personnel, …) will refine this. Each field is
// bound by type to one region machine's state set.
/** Resource — an asset bearing an X.731 three-region state (operational ∥ usage ∥
    administrative), with cross-region interlocks. */
sig Resource {
  opState:    one OperationalState,
  usageState: one UsageState,
  adminState: one AdministrativeState
}

// X.731 interlocks — entry/exit conditions modeled as cross-region state invariants
// (DT-003 decision 2): a disabled or locked resource cannot be carrying load.
fact ResourceInterlocks {
  all r: Resource | r.opState    = DISABLED => r.usageState = IDLE
  all r: Resource | r.adminState = LOCKED   => r.usageState = IDLE
}

// Checkable form of the operational interlock (relocated assert; name kept).
assert X731Consistency {
  all r: Resource | r.opState = DISABLED => r.usageState = IDLE
}
