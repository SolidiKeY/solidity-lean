import SolidityBridge.ExternalEvm.Assembly.Linked

/-! Definitional exposure of the pinned X driver's exceptional-halting gate.
This is an adapter for the existing target gas/stack/static/destination checks,
not a source gas semantics. The continuation theorem below checks the adapter
against actual X, so drift in any check cannot silently weaken a premise.
-/
namespace Solidity.Evm.External.Assembly

open EvmYul EvmYul.EVM

def driverGate (validJumps : Array UInt256) (evmState : EVM.State) (w : Operation .EVM) :
    Except EVM.ExecutionException (EVM.State × Nat) :=
  let W (w : Operation .EVM) (s : Stack UInt256) : Bool :=
    w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
    (w = .CALL ∧ s[2]? ≠ some ⟨0⟩)
  -- Exceptional halting (158)
  let Z (evmState : EVM.State) : Except EVM.ExecutionException (EVM.State × ℕ) := do
    let cost₁ := memoryExpansionCost evmState w
    if evmState.gasAvailable.toNat < cost₁ then
      .error .OutOfGass
    let gasAvailable := evmState.gasAvailable - .ofNat cost₁
    let evmState := { evmState with gasAvailable := gasAvailable}
    let cost₂ := C' evmState w

    if evmState.gasAvailable.toNat < cost₂ then
      .error .OutOfGass

    if δ w = none then
      .error .InvalidInstruction

    if evmState.stack.length < (δ w).getD 0 then
      .error .StackUnderflow

    let invalidJump := X.notIn evmState.stack[0]? validJumps

    if w = .JUMP ∧ invalidJump then
      .error .BadJumpDestination

    if w = .JUMPI ∧ (evmState.stack[1]? ≠ some ⟨0⟩) ∧ invalidJump then
      .error .BadJumpDestination

    if w = .RETURNDATACOPY ∧ (evmState.stack.getD 1 ⟨0⟩).toNat + (evmState.stack.getD 2 ⟨0⟩).toNat > evmState.returnData.size then
      .error .InvalidMemoryAccess

    if evmState.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024 then
      .error .StackOverflow

    if (¬ evmState.executionEnv.perm) ∧ W w evmState.stack then
      .error .StaticModeViolation

    if (w = .SSTORE) ∧ evmState.gasAvailable.toNat ≤ GasConstants.Gcallstipend then
      .error .OutOfGass

    if
      w.isCreate ∧ evmState.stack.getD 2 ⟨0⟩ > ⟨49152⟩
    then
      .error .OutOfGass

    pure (evmState, cost₂)
  Z evmState

def NonhaltingOpcode (w : Operation .EVM) : Prop :=
  w ≠ .RETURN ∧ w ≠ .REVERT ∧ w ≠ .STOP ∧ w ≠ .SELFDESTRUCT

def driverHalt (s : EVM.State) (w : Operation .EVM) : Option ByteArray :=
  if w ∈ ([Operation.RETURN, Operation.REVERT] : List (Operation .EVM)) then some s.H_return
  else if w ∈ ([Operation.STOP, Operation.SELFDESTRUCT] : List (Operation .EVM)) then some .empty else none

/-- Definitionally the actual pinned driver's one-step unfolding. -/
theorem X_unfold (fuel : Nat) (valid : Array UInt256) (s : EVM.State) :
    EVM.X (fuel + 1) valid s = (
      let packet := (EVM.decode s.executionEnv.code s.pc).getD (.STOP, none)
      match driverGate valid s packet.1 with
      | .error e => .error e
      | .ok (charged, cost) => do
        let next ← EVM.step fuel cost (some packet) charged
        match driverHalt next packet.1 with
        | none => EVM.X fuel valid next
        | some output => if packet.1 == (Operation.REVERT : Operation .EVM)
          then .ok (.revert next.gasAvailable output) else .ok (.success next output)) := by
  rfl

/-- One actual target step with positive dispatcher fuel and all original
upstream resource/destination checks retained. -/
theorem X_continue (fuel : Nat) (valid : Array UInt256) (s charged next : EVM.State)
    (packet : Packet) (cost : Nat)
    (decoded : EVM.decode s.executionEnv.code s.pc = some packet)
    (gate : driverGate valid s packet.1 = .ok (charged, cost))
    (step : EVM.step (fuel + 1) cost (some packet) charged = .ok next)
    (continues : NonhaltingOpcode packet.1) :
    EVM.X (fuel + 2) valid s = EVM.X (fuel + 1) valid next := by
  rw [X_unfold, decoded]
  dsimp only [Option.getD]
  rw [gate]
  change (do
    let next ← EVM.step (fuel + 1) cost (some packet) charged
    match driverHalt next packet.1 with
    | none => EVM.X (fuel + 1) valid next
    | some output => if packet.1 == (Operation.REVERT : Operation .EVM)
      then .ok (.revert next.gasAvailable output) else .ok (.success next output)) = _
  rw [step]
  obtain ⟨hret, hrev, hstop, hself⟩ := continues
  simp only [bind, Except.bind, driverHalt, List.mem_cons, List.not_mem_nil, or_false,
    hret, hrev, hstop, hself, if_false]

/-- Exact retained target observations; only gas and execLength are absent. -/
structure StateView where
  world : EvmYul.State .EVM
  activeWords : UInt256
  memory : ByteArray
  returnData : ByteArray
  H_return : ByteArray
  pc : UInt256
  stack : List UInt256

def observeState (s : EVM.State) : StateView :=
  ⟨s.toState, s.activeWords, s.memory, s.returnData, s.H_return, s.pc, s.stack⟩

inductive PurePacket : Packet → Prop where
  | dest : PurePacket (.JUMPDEST, none)
  | push (w : UInt256) : PurePacket (.Push .PUSH32, some (w, 32))
  | pop : PurePacket (.POP, none)
  | zero : PurePacket (.ISZERO, none)
  | jump : PurePacket (.JUMP, none)
  | jumpi : PurePacket (.JUMPI, none)

theorem PurePacket.nonhalting {packet : Packet} (pure : PurePacket packet) : NonhaltingOpcode packet.1 := by
  cases pure <;> dsimp only [NonhaltingOpcode] <;> decide

private theorem observe_dest (fuel cost : Nat) (s : EVM.State) :
    (EVM.step (fuel + 1) cost (some (.JUMPDEST, none)) s).map observeState =
      (EVM.step 1 0 (some (.JUMPDEST, none)) s).map observeState := rfl

private theorem observe_push (fuel cost : Nat) (s : EVM.State) (w : UInt256) :
    (EVM.step (fuel + 1) cost (some (.Push .PUSH32, some (w, 32))) s).map observeState =
      (EVM.step 1 0 (some (.Push .PUSH32, some (w, 32))) s).map observeState := rfl

private theorem observe_pop (fuel cost : Nat) (s : EVM.State) :
    (EVM.step (fuel + 1) cost (some (.POP, none)) s).map observeState =
      (EVM.step 1 0 (some (.POP, none)) s).map observeState := by
  cases s with
  | mk shared pc stack length => cases stack <;> rfl

private theorem observe_zero (fuel cost : Nat) (s : EVM.State) :
    (EVM.step (fuel + 1) cost (some (.ISZERO, none)) s).map observeState =
      (EVM.step 1 0 (some (.ISZERO, none)) s).map observeState := by
  cases s with
  | mk shared pc stack length => cases stack <;> rfl

private theorem observe_jump (fuel cost : Nat) (s : EVM.State) :
    (EVM.step (fuel + 1) cost (some (.JUMP, none)) s).map observeState =
      (EVM.step 1 0 (some (.JUMP, none)) s).map observeState := by
  cases s with
  | mk shared pc stack length => cases stack <;> rfl

private theorem observe_jumpi (fuel cost : Nat) (s : EVM.State) :
    (EVM.step (fuel + 1) cost (some (.JUMPI, none)) s).map observeState =
      (EVM.step 1 0 (some (.JUMPI, none)) s).map observeState := by
  cases s with
  | mk shared pc stack length =>
    cases stack with
    | nil => rfl
    | cons a tail => cases tail <;> rfl

/-- Charged upstream execution and the zero-charge control semantics agree
on every retained field. The charge and positive fuel are arbitrary. -/
theorem pure_step_observe (fuel cost : Nat) (s : EVM.State) (packet : Packet)
    (pure : PurePacket packet) :
    (EVM.step (fuel + 1) cost (some packet) s).map observeState =
      (EVM.step 1 0 (some packet) s).map observeState := by
  cases pure with
  | dest => exact observe_dest fuel cost s
  | push w => exact observe_push fuel cost s w
  | pop => exact observe_pop fuel cost s
  | zero => exact observe_zero fuel cost s
  | jump => exact observe_jump fuel cost s
  | jumpi => exact observe_jumpi fuel cost s

private theorem checked_else {α ε : Type} {p : Prop} [Decidable p]
    {e : ε} {rest : Except ε α} {a : α}
    (h : (if p then Except.error e else rest) = .ok a) : rest = .ok a := by
  by_cases hp : p
  · rw [if_pos hp] at h
    cases h
  · simpa only [if_neg hp] using h

/-- Resource checks alter gas only; this fact is proved from the exact
adapter for upstream X, not assumed as a frame condition. -/
theorem driverGate_observe (valid : Array UInt256) (s charged : EVM.State)
    (op : Operation .EVM) (cost : Nat)
    (gate : driverGate valid s op = .ok (charged, cost)) :
    observeState charged = observeState s := by
  unfold driverGate at gate
  dsimp only at gate
  simp only [bind, Except.bind, pure, Except.pure] at gate
  repeat' have gate := checked_else gate
  have he := congrArg Prod.fst (Except.ok.inj gate)
  dsimp only [Prod.fst] at he
  rw [← he]
  rfl

/-- Retained-field equality is enough for pure opcode execution, even when
gas and execLength differ. -/
theorem pure_step_congr (fuel cost : Nat) (s t : EVM.State) (packet : Packet)
    (pure : PurePacket packet) (same : observeState s = observeState t) :
    (EVM.step (fuel + 1) cost (some packet) s).map observeState =
      (EVM.step 1 0 (some packet) t).map observeState := by
  rw [pure_step_observe fuel cost s packet pure]
  cases s with
  | mk shared pc stack length =>
    cases t with
    | mk shared' pc' stack' length' =>
      cases shared with
      | mk world machine =>
        cases shared' with
        | mk world' machine' =>
          cases machine with
          | mk gas active memory ret hret =>
            cases machine' with
            | mk gas' active' memory' ret' hret' =>
              dsimp only [observeState] at same
              cases same
              cases pure with
              | dest => rfl
              | push w => rfl
              | pop => cases stack <;> rfl
              | zero => cases stack <;> rfl
              | jump => cases stack <;> rfl
              | jumpi => cases stack with
                | nil => rfl
                | cons a tail => cases tail <;> rfl

/-- Executable driver-side readiness. This checks the original exceptional
halting gate and opcode fragment, not the zero-charge trace's result. A step
error is deliberately accepted here: simulation must rule it out. -/
def DriverReady : Nat → Nat → Array UInt256 → EVM.State → Prop
  | 0, _, _, _ => True
  | _ + 1, 0, _, _ => False
  | _ + 1, 1, _, _ => False
  | n + 1, fuel + 2, valid, s =>
    match EVM.decode s.executionEnv.code s.pc with
    | none => False
    | some packet => PurePacket packet ∧
      match driverGate valid s packet.1 with
      | .error _ => False
      | .ok (charged, cost) =>
        match EVM.step (fuel + 1) cost (some packet) charged with
        | .error _ => True
        | .ok next => DriverReady n (fuel + 1) valid next

private theorem observe_decode {s t : EVM.State}
    (same : observeState s = observeState t) :
    EVM.decode s.executionEnv.code s.pc = EVM.decode t.executionEnv.code t.pc := by
  have hw := congrArg StateView.world same
  have hp := congrArg StateView.pc same
  change s.toState = t.toState at hw
  change s.pc = t.pc at hp
  rw [hp]
  have hc := congrArg (fun w : EvmYul.State .EVM => w.executionEnv.code) hw
  change EVM.decode s.toState.executionEnv.code t.pc = _
  dsimp only at hc
  rw [hc]

private theorem fetch_of_decode {s : EVM.State} {packet : Packet}
    (decoded : EVM.decode s.executionEnv.code s.pc = some packet) : Fetches s packet := by
  unfold Fetches EVM.fetchInstr
  rw [decoded]
  rfl

/-- Any certified fetched prefix lifts to the actual charged, finite-fuel X
continuation under its explicit original driver checks. No result of X is
assumed, and gas/execLength are the only fields omitted from the relation. -/
theorem fetchedSteps_driver (n fuel : Nat) (valid : Array UInt256)
    (s t actual : EVM.State)
    (trace : fetchedSteps n s = .ok t)
    (same : observeState actual = observeState s)
    (ready : DriverReady n fuel valid actual) :
    ∃ final, observeState final = observeState t ∧
      EVM.X fuel valid actual = EVM.X (fuel - n) valid final := by
  induction n generalizing fuel s actual with
  | zero =>
    have ht : s = t := Except.ok.inj trace
    subst t
    exact ⟨actual, same, by rw [Nat.sub_zero]⟩
  | succ n ih =>
    cases fuel with
    | zero => exact False.elim ready
    | succ fuel =>
      cases fuel with
      | zero => exact False.elim ready
      | succ fuel =>
        simp only [DriverReady] at ready
        cases hd : EVM.decode actual.executionEnv.code actual.pc with
        | none => simp only [hd] at ready
        | some packet =>
          rw [hd] at ready
          obtain ⟨pure, ready⟩ := ready
          cases hg : driverGate valid actual packet.1 with
          | error e => simp only [hg] at ready
          | ok pair =>
            obtain ⟨charged, cost⟩ := pair
            rw [hg] at ready
            dsimp only at ready
            have hsdecode : EVM.decode s.executionEnv.code s.pc = some packet :=
              (observe_decode same).symm.trans hd
            have hf := fetched_step 0 s packet (fetch_of_decode hsdecode)
            simp only [fetchedSteps] at trace
            rw [hf] at trace
            cases hz : EVM.step 1 0 (some packet) s with
            | error e => simp only [hz, bind, Except.bind] at trace; cases trace
            | ok next =>
              simp only [hz, bind, Except.bind] at trace
              have congr := pure_step_congr fuel cost charged s packet pure
                ((driverGate_observe valid actual charged packet.1 cost hg).trans same)
              rw [hz] at congr
              cases ha : EVM.step (fuel + 1) cost (some packet) charged with
              | error e => rw [ha] at congr; cases congr
              | ok actualNext =>
                rw [ha] at congr
                have nextSame : observeState actualNext = observeState next := Except.ok.inj congr
                rw [ha] at ready
                obtain ⟨final, finalSame, rest⟩ := ih (fuel + 1) next actualNext trace nextSame ready
                refine ⟨final, finalSame, ?_⟩
                rw [X_continue fuel valid actual charged actualNext packet cost hd hg ha pure.nonhalting, rest]
                congr 1
                omega


/-- Relating an actual charged endpoint back to the source boundary uses
only fields preserved by the driver theorem. -/
theorem Boundary.of_observe {code : List Instr} {base index : Nat}
    {image : Image code base} {frame s t : EVM.State} {m : Machine}
    (boundary : Boundary image frame index m s)
    (same : observeState t = observeState s) : Boundary image frame index m t := by
  have hp := congrArg StateView.pc same
  have hs := congrArg StateView.stack same
  have hw := congrArg StateView.world same
  have hm := congrArg StateView.memory same
  exact ⟨boundary.inBounds, by simpa only [show t.pc = s.pc from hp] using boundary.pc,
    by simpa only [show t.stack = s.stack from hs] using boundary.stack,
    hw.trans boundary.state, hm.trans boundary.memory⟩

/-- General compiler/driver prefix refinement. The certificate is generated
by the linker, while finite target resource readiness remains explicit. -/
theorem LinkedProgram.driver_simulation {code : List Instr} (program : LinkedProgram code)
    (m m' : Machine) (s : EVM.State)
    (entry : Boundary program.checked.image program.frame 0 m s)
    (source : run code m = .ok m' 0) :
    ∃ n, ∀ fuel actual, observeState actual = observeState s →
      DriverReady n fuel program.validJumps actual →
      ∃ final, Boundary program.checked.image program.frame code.length m' final ∧
        EVM.X fuel program.validJumps actual = EVM.X (fuel - n) program.validJumps final := by
  obtain ⟨n, t, trace, boundary, _⟩ := program.simulation m m' s entry source
  refine ⟨n, ?_⟩
  intro fuel actual same ready
  obtain ⟨final, finalSame, hx⟩ := fetchedSteps_driver n fuel program.validJumps s t actual trace same ready
  exact ⟨final, boundary.of_observe finalSame, hx⟩

def chargedPrepare (s : EVM.State) (cost : Nat) : EVM.State :=
  {s with execLength := s.execLength + 1, gasAvailable := s.gasAvailable - .ofNat cost}

def stopAfter (s : EVM.State) (cost : Nat) : EVM.State :=
  {chargedPrepare s cost with returnData := .empty}

/-- STOP retains the pinned upstream policy, including clearing returnData
and leaving the PC at STOP. Positive dispatcher fuel is indispensable. -/
theorem X_stop (fuel : Nat) (valid : Array UInt256) (s charged : EVM.State) (cost : Nat)
    (decoded : (EVM.decode s.executionEnv.code s.pc).getD (.STOP, none) = (.STOP, none))
    (gate : driverGate valid s .STOP = .ok (charged, cost)) :
    EVM.X (fuel + 2) valid s = .ok (.success (stopAfter charged cost) .empty) := by
  rw [X_unfold, decoded]
  dsimp only
  rw [gate]
  rfl

/-- The assembled final JUMPDEST followed by STOP really terminates in X.
The two exact driver gates retain gas/stack/static checks unchanged. -/
theorem X_destination_stop (fuel : Nat) (valid : Array UInt256)
    (s charged chargedStop : EVM.State) (cost costStop : Nat)
    (decoded : EVM.decode s.executionEnv.code s.pc = some (.JUMPDEST, none))
    (gate : driverGate valid s .JUMPDEST = .ok (charged, cost))
    (stopDecoded : (EVM.decode (chargedPrepare charged cost).executionEnv.code
      ((chargedPrepare charged cost).incrPC).pc).getD (.STOP, none) = (.STOP, none))
    (stopGate : driverGate valid ((chargedPrepare charged cost).incrPC) .STOP =
      .ok (chargedStop, costStop)) :
    EVM.X (fuel + 3) valid s = .ok (.success (stopAfter chargedStop costStop) .empty) := by
  rw [X_continue (fuel + 1) valid s charged ((chargedPrepare charged cost).incrPC)
    (.JUMPDEST, none) cost decoded gate rfl PurePacket.dest.nonhalting]
  exact X_stop fuel valid _ chargedStop costStop stopDecoded stopGate

/-- Executable proof-producing classifier for the emitted opcode fragment. -/
def checkPure (packet : Packet) : Option (PLift (PurePacket packet)) :=
  match packet with
  | (.JUMPDEST, none) => some ⟨.dest⟩
  | (.Push .PUSH32, some (w, 32)) => some ⟨.push w⟩
  | (.POP, none) => some ⟨.pop⟩
  | (.ISZERO, none) => some ⟨.zero⟩
  | (.JUMP, none) => some ⟨.jump⟩
  | (.JUMPI, none) => some ⟨.jumpi⟩
  | _ => none

/-- Finite readiness checking follows actual charged states and retains all
original X gates. Its recursion bound is the requested prefix length. -/
def checkReady : (n fuel : Nat) → (valid : Array UInt256) → (s : EVM.State) →
    Option (PLift (DriverReady n fuel valid s))
  | 0, _, _, _ => some ⟨trivial⟩
  | _ + 1, 0, _, _ => none
  | _ + 1, 1, _, _ => none
  | n + 1, fuel + 2, valid, s =>
    match hd : EVM.decode s.executionEnv.code s.pc with
    | none => none
    | some packet => do
      let pure ← checkPure packet
      match hg : driverGate valid s packet.1 with
      | .error _ => none
      | .ok (charged, cost) =>
        match hs : EVM.step (fuel + 1) cost (some packet) charged with
        | .error _ => some ⟨by simp only [DriverReady, hd, hg, hs]; exact ⟨pure.down, trivial⟩⟩
        | .ok next => do
          let tail ← checkReady n (fuel + 1) valid next
          return ⟨by simp only [DriverReady, hd, hg, hs]; exact ⟨pure.down, tail.down⟩⟩

end Solidity.Evm.External.Assembly

/-- info: 'Solidity.Evm.External.Assembly.fetchedSteps_driver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.fetchedSteps_driver
