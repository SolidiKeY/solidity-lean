import SolidityBridge.RoadmapV15.P10.Interface

namespace SolidityBridge.RoadmapV15.P10.Controls
open Solidity Solidity.Backend EvmYul
private def seed : EVM.State :=
  {(default : EVM.State) with
    execLength := 41,gasAvailable := .ofNat 10000
    memory := ⟨#[0xaa,0xbb]⟩,returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    stack := [.ofNat 2300,.ofNat 9,.ofNat 7,.ofNat 0,.ofNat 0,.ofNat 0,.ofNat 0,.ofNat 258,.ofNat 513]
    executionEnv := {(default : EVM.State).executionEnv with codeOwner := .ofNat 7,source := .ofNat 11,perm := true}}
private def site (op : Backend.Op) : Site op :=
  ⟨seed,[.push ⟨1,by decide⟩ #v[0xf1],.op .POP],[.op .RETURNDATASIZE,.op .JUMPDEST],by decide⟩

theorem populated_code : (site .CALL).state.executionEnv.code.data.toList =
    [0x60,0xf1,0x50,0xf1,0x3d,0x5b] := by decide +kernel

theorem populated_decode : EVM.decode (site .CALL).state.executionEnv.code (site .CALL).state.pc =
    some (.CALL,none) := decode_call _

example : (site .CALL).state.pc.toNat = 3 := Site.pc_nat _
example : EVM.decode (site .RETURNDATASIZE).state.executionEnv.code (site .RETURNDATASIZE).state.pc =
    some (.RETURNDATASIZE,none) := decode_return_size _
example : EVM.decode (site .RETURNDATACOPY).state.executionEnv.code (site .RETURNDATACOPY).state.pc =
    some (.RETURNDATACOPY,none) := decode_return_copy _
example : EVM.decode (site .JUMP).state.executionEnv.code (site .JUMP).state.pc =
    some (.JUMP,none) := decode_jump _
example : EVM.decode (site .JUMPI).state.executionEnv.code (site .JUMPI).state.pc =
    some (.JUMPI,none) := decode_jump_if _
example : EVM.decode (site .JUMPDEST).state.executionEnv.code (site .JUMPDEST).state.pc =
    some (.JUMPDEST,none) := decode_jump_dest _
-- An embedded CALL byte in PUSH data is not the CALL instruction site.
example : EVM.decode (site .CALL).state.executionEnv.code (.ofNat 0) ≠ some (.CALL,none) := by
  intro h
  have projected := congrArg (Option.map Prod.fst) h
  change some (.Push .PUSH1 : Operation .EVM) = some .CALL at projected
  cases projected
example : EVM.decode (site .JUMP).state.executionEnv.code (site .JUMP).state.pc ≠ some (.CALL,none) := by
  rw [decode_jump]
  intro h
  cases h
example : EVM.step 0 2 none (site .CALL).state = .error .OutOfFuel := rfl
-- Positive outer dispatcher fuel still gives the nested CALL its actual zero fuel.
example : EVM.step 1 2 none (site .CALL).state = .error .OutOfFuel := by
  rw [fetch_call (site .CALL) 0 2]
  rfl
#print axioms Site.code_bytes
#print axioms Site.pc_nat
#print axioms decode_call
#print axioms decode_return_size
#print axioms decode_return_copy
#print axioms decode_jump
#print axioms decode_jump_if
#print axioms decode_jump_dest
#print axioms fetch_call
#print axioms fetch_return_size
#print axioms fetch_return_copy
#print axioms fetch_jump
#print axioms fetch_jump_if
#print axioms fetch_jump_dest
end SolidityBridge.RoadmapV15.P10.Controls
