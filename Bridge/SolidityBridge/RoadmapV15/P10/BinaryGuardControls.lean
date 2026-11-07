import SolidityBridge.RoadmapV15.P10.BinaryGuards
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Twenty populated native result/cost rows, not general source arithmetic
correspondence. Legal input capacity and raw over-limit total-definition cases
are distinguished; errors carry no rollback State. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
namespace BinaryGuardControls
open WordPushFixtures (seed u accounts spill before after)
def rows : List (Backend.Op × Nat × Nat) := [(.ADD,13,3),(.MUL,22,5),(.SUB,9,3),(.DIV,5,5),(.SDIV,5,5),(.MOD,1,5),(.SMOD,1,5),(.SIGNEXTEND,2,5),(.LT,0,3),(.GT,1,3),(.SLT,0,3),(.SGT,1,3),(.EQ,0,3),(.AND,2,3),(.OR,11,3),(.XOR,9,3),(.BYTE,0,3),(.SHL,4096,3),(.SHR,0,3),(.SAR,0,3)]
def site (op : Backend.Op) (gas : Nat) (perm : Bool) (words : Scalar.Stack) : Site op :=
  ⟨{seed gas perm with stack := words.map (fun w => UInt256.mk w.toFin)},before,after,by decide⟩
def expected (op : Backend.Op) (value cost : Nat) (perm : Bool) : EVM.State :=
  {(site op 9 perm (11::2::spill)).state with pc := u 4,gasAvailable := u (9-cost),execLength := 42,stack := u value::spill.map (fun w => UInt256.mk w.toFin)}
theorem coverage : rows.map Prod.fst = binaryPureOps := by rfl
theorem cost_control (op : Backend.Op) (value cost : Nat) (row : (op,value,cost) ∈ rows) (s : EVM.State) :
    EVM.C' s (DecoderAgreement.referenceOp op) = cost ∧ 1 < cost ∧ cost ≤ 9 := by
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at row
  rcases row with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> exact ⟨rfl,by decide,by decide⟩
theorem row_client (op : Backend.Op) (value cost : Nat) (row : (op,value,cost) ∈ rows) (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (site op 9 perm (11::2::spill)).state = .ok (expected op value cost perm) := by
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at row
  rcases row with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> cases perm <;> rfl
theorem refusal_client (op : Backend.Op) (value cost : Nat) (row : (op,value,cost) ∈ rows) (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (site op 1 perm [11]).state = .error .OutOfGass ∧
    EVM.X 2 #[] (site op 1 perm [11]).state = .error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (site op 9 perm [11]).state = .error .StackUnderflow ∧
    EVM.X 2 #[] (site op 9 perm [11]).state = .error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (site op 1 perm [11]).state = .error .OutOfFuel ∧
    EVM.X 1 #[] (site op 1 perm [11]).state = .error .OutOfGass := by
  have member : op ∈ binaryPureOps := by
    rw [←coverage]
    exact List.mem_map.mpr ⟨(op,value,cost),row,rfl⟩
  have low : (site op 1 perm [11]).state.gasAvailable.toNat < EVM.C' (site op 1 perm [11]).state (DecoderAgreement.referenceOp op) := by
    rw [(cost_control op value cost row _).1]
    change 1 < cost
    exact (cost_control op value cost row (site op 9 perm [11]).state).2.1
  have enough : EVM.C' (site op 9 perm [11]).state (DecoderAgreement.referenceOp op) ≤ (site op 9 perm [11]).state.gasAvailable.toNat := by
    rw [(cost_control op value cost row _).1]
    change cost ≤ 9
    exact (cost_control op value cost row (site op 9 perm [11]).state).2.2
  have under : (site op 9 perm [11]).state.stack.length < 2 := by change 1 < 2; decide
  have a := (binary_checked_refusals op member (site op 1 perm [11]) 0 #[]).1 low
  have b := (binary_checked_refusals op member (site op 9 perm [11]) 0 #[]).2.1 enough under
  have short := (binary_short_fuel op member (site op 1 perm [11]) #[]).2
  simp only [if_pos low] at short
  exact ⟨a.1,a.2,b.1,b.2,rfl,short⟩
theorem capacity_client (op : Backend.Op) (value cost : Nat) (row : (op,value,cost) ∈ rows) (perm : Bool) :
    let image := site op 9 perm (11::2::spill++List.replicate 1020 777)
    Assembly.driverGate #[] image.state (DecoderAgreement.referenceOp op) = .ok (image.state,cost) := by
  have member : op ∈ binaryPureOps := by
    rw [←coverage]
    exact List.mem_map.mpr ⟨(op,value,cost),row,rfl⟩
  let image := site op 9 perm (11::2::spill++List.replicate 1020 777)
  have gas : EVM.C' image.state (DecoderAgreement.referenceOp op) ≤ image.state.gasAvailable.toNat := by
    rw [(cost_control op value cost row _).1]
    change cost ≤ 9
    exact (cost_control op value cost row (site op 9 perm [11]).state).2.2
  have enough : 2 ≤ image.state.stack.length := by
    change 2 ≤ ((11::2::spill++List.replicate 1020 777).map (fun (w : Scalar.Word) => UInt256.mk w.toFin)).length
    simp only [List.length_map,List.length_cons,List.length_append,List.length_replicate]; decide
  have legal : image.state.stack.length ≤ 1024 := by
    change ((11::2::spill++List.replicate 1020 777).map (fun (w : Scalar.Word) => UInt256.mk w.toFin)).length ≤ 1024
    simp only [List.length_map,List.length_cons,List.length_append,List.length_replicate]; decide
  have h := binary_gate_wellformed op member image.state #[] gas enough legal
  rw [(cost_control op value cost row _).1] at h
  exact h
theorem complete_ordered_observation (op : Backend.Op) (value cost : Nat) (perm : Bool) :
    (expected op value cost perm).stack = [u value,u 258,u 513] ∧
    (expected op value cost perm).stack ≠ [u value,u 513,u 258] ∧
    (expected op value cost perm).executionEnv.code.data.toList = [0x60,0x7f,0x50,op.code,0x00] ∧
    (expected op value cost perm).memory.data.toList = [0xaa,0xbb]++List.replicate 30 0 ∧
    (expected op value cost perm).returnData.data.toList = [0xcc,0xdd] ∧
    (expected op value cost perm).H_return.data.toList = [0xee,0xff] ∧
    (expected op value cost perm).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (expected op value cost perm).accountMap = accounts ∧ (expected op value cost perm).σ₀ = accounts ∧
    (expected op value cost perm).pc = u 4 ∧ (expected op value cost perm).execLength = 42 := by
  refine ⟨rfl,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  intro bad
  have different := congrArg (fun xs : List UInt256 => xs[1]?) bad
  change some (u 258) = some (u 513) at different
  exact (by decide : some (u 258) ≠ some (u 513)) different
theorem short_fuel_boundaries (op : Backend.Op) (value cost : Nat) (row : (op,value,cost) ∈ rows) (perm : Bool) :
    Assembly.driverSteps 1 1 #[] (site op 9 perm [11]).state = .error .OutOfFuel ∧
    EVM.X 1 #[] (site op 9 perm [11]).state = .error .StackUnderflow ∧
    EVM.X 1 #[] (site op 9 perm (11::2::spill)).state = .error .OutOfFuel := by
  have member : op ∈ binaryPureOps := by
    rw [←coverage]
    exact List.mem_map.mpr ⟨(op,value,cost),row,rfl⟩
  have gas1 : ¬(site op 9 perm [11]).state.gasAvailable.toNat < EVM.C' (site op 9 perm [11]).state (DecoderAgreement.referenceOp op) := by
    rw [(cost_control op value cost row _).1]
    change ¬9 < cost
    exact Nat.not_lt_of_ge (cost_control op value cost row (site op 9 perm [11]).state).2.2
  have gas4 : ¬(site op 9 perm (11::2::spill)).state.gasAvailable.toNat < EVM.C' (site op 9 perm (11::2::spill)).state (DecoderAgreement.referenceOp op) := by
    rw [(cost_control op value cost row _).1]
    change ¬9 < cost
    exact Nat.not_lt_of_ge (cost_control op value cost row (site op 9 perm [11]).state).2.2
  have a := (binary_short_fuel op member (site op 9 perm [11]) #[]).2
  have b := (binary_short_fuel op member (site op 9 perm (11::2::spill)) #[]).2
  have under : (site op 9 perm [11]).state.stack.length < 2 := by change 1 < 2; decide
  have enough : ¬(site op 9 perm (11::2::spill)).state.stack.length < 2 := by change ¬4 < 2; decide
  have room : ¬1024 < (site op 9 perm (11::2::spill)).state.stack.length-2+1 := by change ¬1024 < 3; decide
  simp only [if_neg gas1,if_pos under] at a
  simp only [if_neg gas4,if_neg enough,if_neg room] at b
  exact ⟨rfl,a,b⟩
/-- Total-definition control only: 1026 input words are outside the admitted ≤1024 profile. -/
theorem raw_overflow_control (op : Backend.Op) (value cost : Nat) (row : (op,value,cost) ∈ rows) (perm : Bool) :
    let image := site op 9 perm (11::2::spill++List.replicate 1022 777)
    Assembly.driverSteps 1 2 #[] image.state = .error .StackOverflow ∧
    EVM.X 2 #[] image.state = .error .StackOverflow ∧
    Assembly.driverSteps 1 1 #[] image.state = .error .OutOfFuel ∧
    EVM.X 1 #[] image.state = .error .StackOverflow := by
  have member : op ∈ binaryPureOps := by
    rw [←coverage]
    exact List.mem_map.mpr ⟨(op,value,cost),row,rfl⟩
  let image := site op 9 perm (11::2::spill++List.replicate 1022 777)
  have gas : EVM.C' image.state (DecoderAgreement.referenceOp op) ≤ image.state.gasAvailable.toNat := by
    rw [(cost_control op value cost row _).1]
    change cost ≤ 9
    exact (cost_control op value cost row image.state).2.2
  have length : image.state.stack.length = 1026 := by
    change ((11::2::spill++List.replicate 1022 777).map (fun (w : Scalar.Word) => UInt256.mk w.toFin)).length = 1026
    simp only [List.length_map,List.length_cons,List.length_append,List.length_replicate]; rfl
  have enough : 2 ≤ image.state.stack.length := by rw [length]; decide
  have over : 1024 < image.state.stack.length-2+1 := by rw [length]; decide
  have h := (binary_checked_refusals op member image 0 #[]).2.2 gas enough over
  have short := (binary_short_fuel op member image #[]).2
  simp only [if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge enough),if_pos over] at short
  exact ⟨h.1,h.2,rfl,short⟩
#print axioms coverage
#print axioms cost_control
#print axioms row_client
#print axioms refusal_client
#print axioms capacity_client
#print axioms complete_ordered_observation
#print axioms short_fuel_boundaries
#print axioms raw_overflow_control
end BinaryGuardControls
end SolidityBridge.RoadmapV15.P10
