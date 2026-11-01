import SolidityBridge.RoadmapV15.NumericReference

/-! A real resource-ready emitted ADD client for the parallel interface.
The exact backend opcode byte is fetched; all original driver checks remain.
No compiler source reachability, whole-transaction or Osaka relation is assumed.
Memory, active words, account/context, static permission and buffers are framed.
-/
namespace SolidityBridge.RoadmapV15
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def readyAddInput (s : EVM.State) (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  {s with
    pc := .ofNat 0
    gasAvailable := .ofNat 3
    stack := (a :: b :: tail).map scalarReference
    executionEnv := {s.executionEnv with code := (Instr.op .ADD).encode.toByteArray} }

def readyAddNext (s : EVM.State) (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  let input := readyAddInput s a b tail
  ({input with
    execLength := input.execLength + 1
    gasAvailable := UInt256.ofNat 3 - UInt256.ofNat 3}).replaceStackAndIncrPC
      (((a + b) :: tail).map scalarReference)

theorem ready_add_decode (s : EVM.State) (a b : Scalar.Word) (tail : Scalar.Stack) :
    EVM.decode (readyAddInput s a b tail).executionEnv.code
      (readyAddInput s a b tail).pc = some (.ADD, none) := rfl

theorem ready_add_gate (s : EVM.State) (a b : Scalar.Word) (tail : Scalar.Stack)
    (height : tail.length + 2 ≤ 1024) :
    Assembly.driverGate #[] (readyAddInput s a b tail) .ADD =
      .ok (readyAddInput s a b tail, 3) := by
  let input := readyAddInput s a b tail
  have expansion : EVM.memoryExpansionCost input .ADD = 0 := by
    simp only [EVM.memoryExpansionCost, EVM.memoryExpansionCost.μᵢ', Nat.sub_self]
  have base : ∀ t : EVM.State, EVM.C' t .ADD = 3 := fun _ => rfl
  have gas : input.gasAvailable = UInt256.ofNat 3 := rfl
  have charge : input.gasAvailable - UInt256.ofNat 0 = input.gasAvailable := by
    rw [gas]
    decide +kernel
  have under : ¬input.stack.length < 2 := by
    change ¬((a :: b :: tail).map scalarReference).length < 2
    simp only [List.length_map, List.length_cons]
    omega
  have over : ¬input.stack.length - 2 + 1 > 1024 := by
    change ¬((a :: b :: tail).map scalarReference).length - 2 + 1 > 1024
    simp only [List.length_map, List.length_cons]
    omega
  change Assembly.driverGate #[] input .ADD = .ok (input, 3)
  simp only [Assembly.driverGate]
  rw [expansion, charge]
  simp only [base, gas, EVM.δ, EVM.α, Option.getD_some, if_neg under, if_neg over]
  cases permission : input.executionEnv.perm <;> rfl

/-- The gate witness contains only actual decoder and resource facts. -/
def readyAdd (s : EVM.State) (a b : Scalar.Word) (tail : Scalar.Stack)
    (height : tail.length + 2 ≤ 1024) :
    OpcodeReady #[] (readyAddInput s a b tail) (.ADD, none) where
  charged := readyAddInput s a b tail
  cost := 3
  decoded := ready_add_decode s a b tail
  gate := ready_add_gate s a b tail height

theorem ready_add_step (s : EVM.State) (a b : Scalar.Word) (tail : Scalar.Stack) (fuel : Nat) :
    EVM.step (fuel + 1) 3 (some (.ADD, none)) (readyAddInput s a b tail) =
      .ok (readyAddNext s a b tail) :=
  scalar_add_reference (readyAddInput s a b tail) a b tail fuel 3

/-- A new emitted numeric opcode advances the actual driver under its proved
resource gate; this is not an assumed simulation or a final-success claim. -/
theorem ready_add_driver (s : EVM.State) (a b : Scalar.Word) (tail : Scalar.Stack)
    (height : tail.length + 2 ≤ 1024) (fuel : Nat) :
    EVM.X (fuel + 2) #[] (readyAddInput s a b tail) =
      EVM.X (fuel + 1) #[] (readyAddNext s a b tail) := by
  exact (readyAdd s a b tail height).continue fuel (readyAddNext s a b tail)
    (ready_add_step s a b tail fuel) (by unfold Assembly.NonhaltingOpcode; decide)
/-- Concrete intrinsic client of the handoff: consume the real wrapping-add
certificate, not an assumed compiler simulation, then discharge decoder and gas
readiness for the actual emitted ADD and transport its whole typed result state. -/
theorem ready_add_intrinsic (s : EVM.State) (a b : PrimTy.uint.Denote)
    (tail : Scalar.Stack) (height : tail.length + 2 ≤ 1024) (fuel : Nat) :
    ∃ r : PrimTy.uint.Denote, BinOp.evalT (op := .addW) rfl a b = some r ∧
      let input := readyAddInput s (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail
      let next := ({input with
        execLength := input.execLength + 1
        gasAvailable := UInt256.ofNat 3 - UInt256.ofNat 3}).replaceStackAndIncrPC
          ((Scalar.encodeValue .uint r :: tail).map scalarReference)
      EVM.X (fuel + 2) #[] input = EVM.X (fuel + 1) #[] next := by
  let input := readyAddInput s (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail
  obtain ⟨r, value, step⟩ := wrapping_add_reference input a b tail fuel 3
  refine ⟨r, value, ?_⟩
  exact (readyAdd s (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail height).continue
    fuel _ step (by unfold Assembly.NonhaltingOpcode; decide)
end SolidityBridge.RoadmapV15
