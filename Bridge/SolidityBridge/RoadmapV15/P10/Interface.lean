import Solidity.Backend.Opcode
import EvmYul.EVM.Semantics

/-! P10's typed backend instruction site. The exact ordered Backend.encode
image and nonwrapping PC construct an actual pinned reference state. There is
no source-lowering/frame-origin, call-result or decoder hypothesis. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul

structure Site (op : Backend.Op) where
  seed : EVM.State
  before : Backend.Program
  after : Backend.Program
  pcFits : (Backend.encode before).length < UInt256.size

def Site.state {op : Backend.Op} (site : Site op) : EVM.State :=
  {site.seed with
    pc := .ofNat (Backend.encode site.before).length
    executionEnv := {site.seed.executionEnv with
      code := ⟨(Backend.encode (site.before ++ .op op :: site.after)).toArray⟩}}

theorem Site.code_bytes {op : Backend.Op} (site : Site op) :
    site.state.executionEnv.code.data.toList = Backend.encode (site.before ++ .op op :: site.after) := by
  exact List.toList_toArray

theorem Site.pc_nat {op : Backend.Op} (site : Site op) :
    site.state.pc.toNat = (Backend.encode site.before).length := by
  change (Backend.encode site.before).length % UInt256.size = _
  exact Nat.mod_eq_of_lt site.pcFits

private theorem opcode_at {op : Backend.Op} (site : Site op) :
    site.state.executionEnv.code.get? (Backend.encode site.before).length = some op.code := by
  change (Backend.encode (site.before ++ .op op :: site.after)).toArray[(Backend.encode site.before).length]? = _
  rw [List.getElem?_toArray]
  simp only [Backend.encode_append,Backend.encode_cons,Instr.encode,List.singleton_append]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self,List.getElem?_cons_zero]

private theorem fetched_dispatch (s : EVM.State) (packet : Operation .EVM × Option (UInt256 × Nat))
    (decoded : EVM.decode s.executionEnv.code s.pc = some packet) (fuel cost : Nat) :
    EVM.step (fuel+1) cost none s = EVM.step (fuel+1) cost (some packet) s := by
  cases packet with
  | mk op arg =>
    simp only [EVM.step,EVM.fetchInstr,decoded,Option.option,bind,Except.bind]
    rfl

theorem decode_call (site : Site .CALL) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.CALL,none) := by
  have byte := opcode_at site
  simp only [EVM.decode,Site.pc_nat,byte]
  rfl

/-- Actual on-demand fetched step, including its original fuel/call semantics. -/
theorem fetch_call (site : Site .CALL) (fuel cost : Nat) :
    EVM.step (fuel+1) cost none site.state =
      EVM.step (fuel+1) cost (some (.CALL,none)) site.state :=
  fetched_dispatch site.state (.CALL,none) (decode_call site) fuel cost

theorem decode_return_size (site : Site .RETURNDATASIZE) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.RETURNDATASIZE,none) := by
  have byte := opcode_at site
  simp only [EVM.decode,Site.pc_nat,byte]
  rfl

/-- Actual on-demand fetched step, including its original fuel/call semantics. -/
theorem fetch_return_size (site : Site .RETURNDATASIZE) (fuel cost : Nat) :
    EVM.step (fuel+1) cost none site.state =
      EVM.step (fuel+1) cost (some (.RETURNDATASIZE,none)) site.state :=
  fetched_dispatch site.state (.RETURNDATASIZE,none) (decode_return_size site) fuel cost

theorem decode_return_copy (site : Site .RETURNDATACOPY) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.RETURNDATACOPY,none) := by
  have byte := opcode_at site
  simp only [EVM.decode,Site.pc_nat,byte]
  rfl

/-- Actual on-demand fetched step, including its original fuel/call semantics. -/
theorem fetch_return_copy (site : Site .RETURNDATACOPY) (fuel cost : Nat) :
    EVM.step (fuel+1) cost none site.state =
      EVM.step (fuel+1) cost (some (.RETURNDATACOPY,none)) site.state :=
  fetched_dispatch site.state (.RETURNDATACOPY,none) (decode_return_copy site) fuel cost

theorem decode_jump (site : Site .JUMP) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.JUMP,none) := by
  have byte := opcode_at site
  simp only [EVM.decode,Site.pc_nat,byte]
  rfl

/-- Actual on-demand fetched step, including its original fuel/call semantics. -/
theorem fetch_jump (site : Site .JUMP) (fuel cost : Nat) :
    EVM.step (fuel+1) cost none site.state =
      EVM.step (fuel+1) cost (some (.JUMP,none)) site.state :=
  fetched_dispatch site.state (.JUMP,none) (decode_jump site) fuel cost

theorem decode_jump_if (site : Site .JUMPI) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.JUMPI,none) := by
  have byte := opcode_at site
  simp only [EVM.decode,Site.pc_nat,byte]
  rfl

/-- Actual on-demand fetched step, including its original fuel/call semantics. -/
theorem fetch_jump_if (site : Site .JUMPI) (fuel cost : Nat) :
    EVM.step (fuel+1) cost none site.state =
      EVM.step (fuel+1) cost (some (.JUMPI,none)) site.state :=
  fetched_dispatch site.state (.JUMPI,none) (decode_jump_if site) fuel cost

theorem decode_jump_dest (site : Site .JUMPDEST) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.JUMPDEST,none) := by
  have byte := opcode_at site
  simp only [EVM.decode,Site.pc_nat,byte]
  rfl

/-- Actual on-demand fetched step, including its original fuel/call semantics. -/
theorem fetch_jump_dest (site : Site .JUMPDEST) (fuel cost : Nat) :
    EVM.step (fuel+1) cost none site.state =
      EVM.step (fuel+1) cost (some (.JUMPDEST,none)) site.state :=
  fetched_dispatch site.state (.JUMPDEST,none) (decode_jump_dest site) fuel cost

end SolidityBridge.RoadmapV15.P10
