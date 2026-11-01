import SolidityBridge.RoadmapV15.ReadyNumeric
import SolidityBridge.RoadmapV15.ReferenceEncoding

/-! Inhabited actual state/resource clients, complete numeric observations,
input-height and refusal boundaries. These are not full Osaka/transaction proofs. -/
namespace SolidityBridge.RoadmapV15.ParallelControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private def seed : EVM.State :=
  { (default : EVM.State) with
    gasAvailable := .ofNat 29
    activeWords := .ofNat 1
    memory := ⟨Array.replicate 32 0xaa⟩
    returnData := ⟨#[0xcc, 0xdd]⟩
    H_return := ⟨#[0xee, 0xff]⟩
    stack := [.ofNat 99]
    pc := .ofNat 17
    execLength := 41
    executionEnv := { (default : ExecutionEnv .EVM) with
      codeOwner := .ofNat 7, source := .ofNat 11, weiValue := .ofNat 13, perm := false }
    accountMap := (∅ : AccountMap .EVM).insert (.ofNat 7)
      { (default : Account .EVM) with nonce := .ofNat 3, balance := .ofNat 29 } }
private def u (n : Nat) (h : n < 2 ^ 256 := by decide) : PrimTy.uint.Denote := lenU n h
private def hi : Scalar.Word := BitVec.ofNat 256 (2 ^ 256 - 1)
private def tail : Scalar.Stack := [258, 513]

example : ReferenceRelated seed {seed with gasAvailable := .ofNat 0, execLength := 0} := rfl
example : seed ≠ {seed with gasAvailable := .ofNat 0, execLength := 0} := by
  intro h
  have hn : seed.execLength ≠ 0 := by decide
  exact hn (congrArg EVM.State.execLength h)
example : ¬ReferenceRelated seed {seed with returnData := ⟨#[0xcc]⟩} := by
  intro h
  have he := congrArg Assembly.StateView.returnData h
  have hn : seed.returnData ≠ (⟨#[0xcc]⟩ : ByteArray) := by decide +kernel
  exact hn he
example : ApprovedResource :=
  ⟨⟨⟨fun _ => 17⟩, 5⟩, Solidity.Roadmap.Evm.GasRes.admissible_pinned _⟩

example : OpcodeReady #[] (readyAddInput seed hi 2 tail) (.ADD, none) :=
  readyAdd seed hi 2 tail (by decide)
example : OpcodeReady #[] (readyAddInput seed 7 11 (List.replicate 1022 13)) (.ADD, none) :=
  readyAdd seed 7 11 (List.replicate 1022 13) (by simp only [List.length_replicate]; decide)
example : ¬((List.replicate 1023 (13 : Scalar.Word)).length + 2 ≤ 1024) := by
  simp only [List.length_replicate]; decide
example : (readyAddInput seed hi 2 tail).memory = seed.memory := rfl
example : (readyAddInput seed hi 2 tail).activeWords = seed.activeWords := rfl
example : (readyAddInput seed hi 2 tail).executionEnv.perm = false := rfl
example : (readyAddInput seed hi 2 tail).accountMap = seed.accountMap := rfl
example : (readyAddNext seed hi 2 tail).returnData = seed.returnData := rfl
example : (readyAddNext seed hi 2 tail).H_return = seed.H_return := rfl

/-- Full ordered stack plus independently retained memory/return buffers. -/
example (fuel : Nat) :
    (EVM.step (fuel + 1) 3 (some (.ADD, none)) (readyAddInput seed hi 2 tail)).map
      (fun t => (t.pc.toNat, t.gasAvailable.toNat, t.execLength, t.stack.map UInt256.toNat,
        t.memory.toList, t.returnData.toList, t.H_return.toList)) =
      .ok (1, 0, 42, [1, 258, 513], List.replicate 32 0xaa, [0xcc, 0xdd], [0xee, 0xff]) := by
  rw [ready_add_step]
  apply congrArg Except.ok
  change ((UInt256.ofNat 0 + UInt256.ofNat 1).toNat,
    (UInt256.ofNat 3 - UInt256.ofNat 3).toNat, 42,
    [(scalarReference (hi + 2)).toNat, 258, 513], seed.memory.toList,
    seed.returnData.toList, seed.H_return.toList) = _
  simp only [seed, Solidity.Evm.External.Memory.bytes_list]
  repeat' apply Prod.ext
  all_goals decide +kernel
example (fuel : Nat) : EVM.X (fuel + 2) #[] (readyAddInput seed hi 2 tail) =
    EVM.X (fuel + 1) #[] (readyAddNext seed hi 2 tail) :=
  ready_add_driver seed hi 2 tail (by decide) fuel
example (fuel : Nat) : ∃ r : PrimTy.uint.Denote,
    BinOp.evalT (op := .addW) rfl (u (2 ^ 256 - 1)) (u 2) = some r ∧
      let input := readyAddInput seed (Scalar.encodeValue .uint (u (2 ^ 256 - 1)))
        (Scalar.encodeValue .uint (u 2)) tail
      let next := ({input with
        execLength := input.execLength + 1
        gasAvailable := UInt256.ofNat 3 - UInt256.ofNat 3}).replaceStackAndIncrPC
          ((Scalar.encodeValue .uint r :: tail).map scalarReference)
      EVM.X (fuel + 2) #[] input = EVM.X (fuel + 1) #[] next :=
  ready_add_intrinsic seed (u (2 ^ 256 - 1)) (u 2) tail (by decide) fuel
example : BinOp.evalT (op := .addW) rfl (u (2 ^ 256 - 1)) (u 2) = some (u 1) := by decide +kernel
example : (Scalar.run Scalar.wrappingSub.code [1, 2, 258, 513]).map
    (List.map (fun w : Scalar.Word => w.toNat)) = some [2 ^ 256 - 1, 258, 513] := by decide +kernel
example : (Scalar.run Scalar.wrappingSub.code [1, 2, 258, 513]).map
    (List.map (fun w : Scalar.Word => w.toNat)) ≠ some [1, 258, 513] := by decide +kernel
example : scalarReference (hi * 2) = UInt256.ofNat (2 ^ 256 - 2) := by decide +kernel
example : scalarReference (hi * 2) ≠ UInt256.ofNat 2 := by decide +kernel
example : scalarReference (BitVec.ofInt 256 (-1)) = scalarReference hi := by decide +kernel
example : Scalar.unsignedClean ⟨0, by decide⟩ ((255 : Scalar.Word) + 1) = 0 := by decide +kernel
example : ((255 : Scalar.Word) + 1) ≠ Scalar.unsignedClean ⟨0, by decide⟩ (255 + 1) := by decide +kernel
example : (Assembly.driverGate #[] {readyAddInput seed 7 11 tail with gasAvailable := .ofNat 2} .ADD).isOk = false := by
  decide +kernel
example : (Assembly.driverGate #[] (readyAddInput seed 7 11 (List.replicate 1024 13)) .ADD).isOk = false := by
  let input := readyAddInput seed 7 11 (List.replicate 1024 13)
  have expansion : EVM.memoryExpansionCost input .ADD = 0 := by
    simp only [EVM.memoryExpansionCost, EVM.memoryExpansionCost.μᵢ', Nat.sub_self]
  have charge : input.gasAvailable - UInt256.ofNat 0 = input.gasAvailable := by
    change UInt256.ofNat 3 - UInt256.ofNat 0 = UInt256.ofNat 3
    decide +kernel
  have length : input.stack.length = 1026 := by
    change ((7 :: 11 :: List.replicate 1024 13 : Scalar.Stack).map scalarReference).length = 1026
    simp only [List.length_map, List.length_cons, List.length_replicate]
  have base : ∀ t : EVM.State, EVM.C' t .ADD = 3 := fun _ => rfl
  change (Assembly.driverGate #[] input .ADD).isOk = false
  simp only [Assembly.driverGate]
  rw [expansion, charge]
  simp only [base, EVM.δ, EVM.α, Option.getD_some, length]
  rfl
example (s : EVM.State) : EVM.step 1 0 (some (.SUB, none)) {s with stack := []} = .error .StackUnderflow := rfl
example (s : EVM.State) : EVM.step 1 0 (some (.MUL, none)) {s with stack := [.ofNat 7]} = .error .StackUnderflow := rfl
example (s : EVM.State) : EVM.step 0 3 (some (.ADD, none)) s = .error .OutOfFuel := rfl

#print axioms reference_related_exact
#print axioms OpcodeReady.continue
#print axioms scalar_reference_add
#print axioms scalar_reference_sub
#print axioms scalar_reference_mul
#print axioms scalar_add_reference
#print axioms scalar_sub_reference
#print axioms scalar_mul_reference
#print axioms wrapping_add_reference
#print axioms wrapping_sub_reference
#print axioms wrapping_mul_reference
#print axioms ready_add_decode
#print axioms ready_add_gate
#print axioms ready_add_step
#print axioms ready_add_driver
#print axioms ready_add_intrinsic
end SolidityBridge.RoadmapV15.ParallelControls
