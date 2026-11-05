import SolidityBridge.RoadmapV15.P10.Interface
import SolidityBridge.ExternalEvm.Assembly.Driver

/-! P10 execution over the actual pinned dispatcher and its unchanged charged
gate. CALL invokes the real account operation and retains its whole State/word
result; copy invokes the actual byte-memory operation, with no padding axiom. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem Site.recover {op : Backend.Op} (site : Site op)
    (pc : site.seed.pc = .ofNat (Backend.encode site.before).length)
    (code : site.seed.executionEnv.code = ⟨(Backend.encode (site.before ++ .op op :: site.after)).toArray⟩) :
    site.state = site.seed := by
  unfold Site.state
  rw [←pc,←code]

private theorem checked_dispatch (s : EVM.State)
    (packet : Operation .EVM × Option (UInt256 × Nat))
    (decoded : EVM.decode s.executionEnv.code s.pc = some packet)
    (valid : Array UInt256) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) valid s =
      match Assembly.driverGate valid s packet.1 with
      | .error error => .error error
      | .ok (charged,cost) => EVM.step (fuel+1) cost (some packet) charged := by
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind]
  cases gate : Assembly.driverGate valid s packet.1 with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨charged,cost⟩
    dsimp only
    cases step : EVM.step (fuel+1) cost (some packet) charged <;> rfl

theorem dispatch_call (s : EVM.State) (fuel cost : Nat) :
    EVM.step (fuel+1) cost (some (.CALL,none)) s =
      match s.stack.pop7 with
      | none => .error .StackUnderflow
      | some (tail,gas,recipient,value,inOffset,inSize,outOffset,outSize) =>
        (EVM.call fuel cost s.executionEnv.blobVersionedHashes gas
          (.ofNat s.executionEnv.codeOwner) recipient recipient value value inOffset inSize outOffset outSize
          s.executionEnv.perm {s with execLength := s.execLength+1}).map
          (fun result => result.2.replaceStackAndIncrPC (result.1 :: tail)) := by
  cases s with
  | mk shared pc stack count =>
    cases stack with
    | nil => rfl
    | cons gas rest1 =>
      cases rest1 with
      | nil => rfl
      | cons recipient rest2 =>
        cases rest2 with
        | nil => rfl
        | cons value rest3 =>
          cases rest3 with
          | nil => rfl
          | cons inOffset rest4 =>
            cases rest4 with
            | nil => rfl
            | cons inSize rest5 =>
              cases rest5 with
              | nil => rfl
              | cons outOffset rest6 =>
                cases rest6 <;> rfl

theorem dispatch_return_size (s : EVM.State) (fuel cost : Nat) :
    EVM.step (fuel+1) cost (some (.RETURNDATASIZE,none)) s =
      Except.ok ((Assembly.chargedPrepare s cost).replaceStackAndIncrPC
      (UInt256.ofNat s.returnData.size :: s.stack)) := by
  rfl

theorem dispatch_return_copy (s : EVM.State) (fuel cost : Nat) :
    EVM.step (fuel+1) cost (some (.RETURNDATACOPY,none)) s =
      match s.stack.pop3 with
      | none => .error .StackUnderflow
      | some (tail,destination,source,length) =>
        .ok (({Assembly.chargedPrepare s cost with
          toMachineState := (Assembly.chargedPrepare s cost).toMachineState.returndatacopy destination source length}).replaceStackAndIncrPC tail) := by
  cases s with
  | mk shared pc stack length =>
    cases stack with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => rfl
      | cons b rest => cases rest <;> rfl

theorem dispatch_jump (s : EVM.State) (fuel cost : Nat) :
    EVM.step (fuel+1) cost (some (.JUMP,none)) s =
      match s.stack.pop with
      | none => .error .StackUnderflow
      | some (tail,destination) =>
        .ok {Assembly.chargedPrepare s cost with pc := destination,stack := tail} := by
  cases s with
  | mk shared pc stack length => cases stack <;> rfl

theorem dispatch_jump_if (s : EVM.State) (fuel cost : Nat) :
    EVM.step (fuel+1) cost (some (.JUMPI,none)) s =
      match s.stack.pop2 with
      | none => .error .StackUnderflow
      | some (tail,destination,condition) =>
        .ok {Assembly.chargedPrepare s cost with
          pc := if condition != (⟨0⟩ : UInt256) then destination else s.pc + ⟨1⟩
          stack := tail} := by
  cases s with
  | mk shared pc stack length =>
    cases stack with
    | nil => rfl
    | cons a rest => cases rest <;> rfl

theorem dispatch_jump_dest (s : EVM.State) (fuel cost : Nat) :
    EVM.step (fuel+1) cost (some (.JUMPDEST,none)) s =
      Except.ok ((Assembly.chargedPrepare s cost).replaceStackAndIncrPC s.stack) := by
  rfl

/-- Actual backend-encoded fetched transition, including every original gate
failure; no desired result, supplied-step or gate-success hypothesis. -/
theorem checked_call (site : Site .CALL) (valid : Array UInt256) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) valid site.state =
      match Assembly.driverGate valid site.state .CALL with
      | .error error => .error error
      | .ok (charged,cost) =>
        match charged.stack.pop7 with
              | none => .error .StackUnderflow
              | some (tail,gas,recipient,value,inOffset,inSize,outOffset,outSize) =>
                (EVM.call fuel cost charged.executionEnv.blobVersionedHashes gas
                  (.ofNat charged.executionEnv.codeOwner) recipient recipient value value inOffset inSize outOffset outSize
                  charged.executionEnv.perm {charged with execLength := charged.execLength+1}).map
                  (fun result => result.2.replaceStackAndIncrPC (result.1 :: tail)) := by
  rw [checked_dispatch site.state (.CALL,none) (decode_call site) valid fuel]
  cases gate : Assembly.driverGate valid site.state .CALL with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨charged,cost⟩
    exact dispatch_call charged fuel cost

/-- Actual backend-encoded fetched transition, including every original gate
failure; no desired result, supplied-step or gate-success hypothesis. -/
theorem checked_return_size (site : Site .RETURNDATASIZE) (valid : Array UInt256) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) valid site.state =
      match Assembly.driverGate valid site.state .RETURNDATASIZE with
      | .error error => .error error
      | .ok (charged,cost) =>
        Except.ok ((Assembly.chargedPrepare charged cost).replaceStackAndIncrPC
              (UInt256.ofNat charged.returnData.size :: charged.stack)) := by
  rw [checked_dispatch site.state (.RETURNDATASIZE,none) (decode_return_size site) valid fuel]
  cases gate : Assembly.driverGate valid site.state .RETURNDATASIZE with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨charged,cost⟩
    exact dispatch_return_size charged fuel cost

/-- Actual backend-encoded fetched transition, including every original gate
failure; no desired result, supplied-step or gate-success hypothesis. -/
theorem checked_return_copy (site : Site .RETURNDATACOPY) (valid : Array UInt256) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) valid site.state =
      match Assembly.driverGate valid site.state .RETURNDATACOPY with
      | .error error => .error error
      | .ok (charged,cost) =>
        match charged.stack.pop3 with
              | none => .error .StackUnderflow
              | some (tail,destination,source,length) =>
                .ok (({Assembly.chargedPrepare charged cost with
                  toMachineState := (Assembly.chargedPrepare charged cost).toMachineState.returndatacopy destination source length}).replaceStackAndIncrPC tail) := by
  rw [checked_dispatch site.state (.RETURNDATACOPY,none) (decode_return_copy site) valid fuel]
  cases gate : Assembly.driverGate valid site.state .RETURNDATACOPY with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨charged,cost⟩
    exact dispatch_return_copy charged fuel cost

/-- Actual backend-encoded fetched transition, including every original gate
failure; no desired result, supplied-step or gate-success hypothesis. -/
theorem checked_jump (site : Site .JUMP) (valid : Array UInt256) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) valid site.state =
      match Assembly.driverGate valid site.state .JUMP with
      | .error error => .error error
      | .ok (charged,cost) =>
        match charged.stack.pop with
              | none => .error .StackUnderflow
              | some (tail,destination) =>
                .ok {Assembly.chargedPrepare charged cost with pc := destination,stack := tail} := by
  rw [checked_dispatch site.state (.JUMP,none) (decode_jump site) valid fuel]
  cases gate : Assembly.driverGate valid site.state .JUMP with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨charged,cost⟩
    exact dispatch_jump charged fuel cost

/-- Actual backend-encoded fetched transition, including every original gate
failure; no desired result, supplied-step or gate-success hypothesis. -/
theorem checked_jump_if (site : Site .JUMPI) (valid : Array UInt256) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) valid site.state =
      match Assembly.driverGate valid site.state .JUMPI with
      | .error error => .error error
      | .ok (charged,cost) =>
        match charged.stack.pop2 with
              | none => .error .StackUnderflow
              | some (tail,destination,condition) =>
                .ok {Assembly.chargedPrepare charged cost with
                  pc := if condition != (⟨0⟩ : UInt256) then destination else charged.pc + ⟨1⟩
                  stack := tail} := by
  rw [checked_dispatch site.state (.JUMPI,none) (decode_jump_if site) valid fuel]
  cases gate : Assembly.driverGate valid site.state .JUMPI with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨charged,cost⟩
    exact dispatch_jump_if charged fuel cost

/-- Actual backend-encoded fetched transition, including every original gate
failure; no desired result, supplied-step or gate-success hypothesis. -/
theorem checked_jump_dest (site : Site .JUMPDEST) (valid : Array UInt256) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) valid site.state =
      match Assembly.driverGate valid site.state .JUMPDEST with
      | .error error => .error error
      | .ok (charged,cost) =>
        Except.ok ((Assembly.chargedPrepare charged cost).replaceStackAndIncrPC charged.stack) := by
  rw [checked_dispatch site.state (.JUMPDEST,none) (decode_jump_dest site) valid fuel]
  cases gate : Assembly.driverGate valid site.state .JUMPDEST with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨charged,cost⟩
    exact dispatch_jump_dest charged fuel cost


private theorem checked_X (s : EVM.State) (packet : Operation .EVM × Option (UInt256 × Nat))
    (decoded : EVM.decode s.executionEnv.code s.pc = some packet)
    (nonhalting : Assembly.NonhaltingOpcode packet.1) (valid : Array UInt256) (fuel : Nat) :
    EVM.X (fuel+2) valid s =
      match Assembly.driverSteps 1 (fuel+2) valid s with
      | .error error => .error error
      | .ok next => EVM.X (fuel+1) valid next := by
  rw [checked_dispatch s packet decoded valid fuel]
  cases gate : Assembly.driverGate valid s packet.1 with
  | error error =>
    rw [Assembly.X_unfold (fuel+1) valid s,decoded]
    simp only [Option.getD,gate]
  | ok pair =>
    rcases pair with ⟨charged,cost⟩
    dsimp only
    cases step : EVM.step (fuel+1) cost (some packet) charged with
    | error error =>
      rw [Assembly.X_unfold (fuel+1) valid s,decoded]
      simp only [Option.getD,gate,step,bind,Except.bind]
    | ok next =>
      exact Assembly.X_continue fuel valid s charged next packet cost decoded gate step nonhalting

/-- One actual checked backend instruction composes with the pinned X
continuation; errors propagate, and no successful step is an input premise. -/
theorem x_call (site : Site .CALL) (valid : Array UInt256) (fuel : Nat) :
    EVM.X (fuel+2) valid site.state =
      match Assembly.driverSteps 1 (fuel+2) valid site.state with
      | .error error => .error error
      | .ok next => EVM.X (fuel+1) valid next :=
  checked_X site.state (.CALL,none) (decode_call site)
    (by unfold Assembly.NonhaltingOpcode; decide) valid fuel

/-- One actual checked backend instruction composes with the pinned X
continuation; errors propagate, and no successful step is an input premise. -/
theorem x_return_size (site : Site .RETURNDATASIZE) (valid : Array UInt256) (fuel : Nat) :
    EVM.X (fuel+2) valid site.state =
      match Assembly.driverSteps 1 (fuel+2) valid site.state with
      | .error error => .error error
      | .ok next => EVM.X (fuel+1) valid next :=
  checked_X site.state (.RETURNDATASIZE,none) (decode_return_size site)
    (by unfold Assembly.NonhaltingOpcode; decide) valid fuel

/-- One actual checked backend instruction composes with the pinned X
continuation; errors propagate, and no successful step is an input premise. -/
theorem x_return_copy (site : Site .RETURNDATACOPY) (valid : Array UInt256) (fuel : Nat) :
    EVM.X (fuel+2) valid site.state =
      match Assembly.driverSteps 1 (fuel+2) valid site.state with
      | .error error => .error error
      | .ok next => EVM.X (fuel+1) valid next :=
  checked_X site.state (.RETURNDATACOPY,none) (decode_return_copy site)
    (by unfold Assembly.NonhaltingOpcode; decide) valid fuel

/-- One actual checked backend instruction composes with the pinned X
continuation; errors propagate, and no successful step is an input premise. -/
theorem x_jump (site : Site .JUMP) (valid : Array UInt256) (fuel : Nat) :
    EVM.X (fuel+2) valid site.state =
      match Assembly.driverSteps 1 (fuel+2) valid site.state with
      | .error error => .error error
      | .ok next => EVM.X (fuel+1) valid next :=
  checked_X site.state (.JUMP,none) (decode_jump site)
    (by unfold Assembly.NonhaltingOpcode; decide) valid fuel

/-- One actual checked backend instruction composes with the pinned X
continuation; errors propagate, and no successful step is an input premise. -/
theorem x_jump_if (site : Site .JUMPI) (valid : Array UInt256) (fuel : Nat) :
    EVM.X (fuel+2) valid site.state =
      match Assembly.driverSteps 1 (fuel+2) valid site.state with
      | .error error => .error error
      | .ok next => EVM.X (fuel+1) valid next :=
  checked_X site.state (.JUMPI,none) (decode_jump_if site)
    (by unfold Assembly.NonhaltingOpcode; decide) valid fuel

/-- One actual checked backend instruction composes with the pinned X
continuation; errors propagate, and no successful step is an input premise. -/
theorem x_jump_dest (site : Site .JUMPDEST) (valid : Array UInt256) (fuel : Nat) :
    EVM.X (fuel+2) valid site.state =
      match Assembly.driverSteps 1 (fuel+2) valid site.state with
      | .error error => .error error
      | .ok next => EVM.X (fuel+1) valid next :=
  checked_X site.state (.JUMPDEST,none) (decode_jump_dest site)
    (by unfold Assembly.NonhaltingOpcode; decide) valid fuel

end SolidityBridge.RoadmapV15.P10
