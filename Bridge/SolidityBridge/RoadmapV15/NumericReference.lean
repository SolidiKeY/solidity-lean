import SolidityBridge.RoadmapV15.ParallelInterface
import Solidity.Backend.Scalar.Wrapping
import SolidityBridge.ExternalEvm

/-! New consumers of the published intrinsic wrapping certificates and actual
reference arithmetic. The existing BitVec backend and Fin/UInt reference
representations are reused, not reimplemented. Charged supplied dispatch is
proved with complete state/tail; gate adequacy is a separate real obligation.
Shared arithmetic equations are not full Osaka fork agreement. -/
namespace SolidityBridge.RoadmapV15
open Solidity Solidity.Backend EvmYul

def scalarReference (w : Scalar.Word) : UInt256 := Solidity.Evm.External.encode w.toFin

theorem scalar_reference_add (a b : Scalar.Word) :
    scalarReference (a + b) = UInt256.add (scalarReference a) (scalarReference b) := by
  rfl

theorem scalar_reference_sub (a b : Scalar.Word) :
    scalarReference (a - b) = UInt256.sub (scalarReference a) (scalarReference b) := by
  rfl

theorem scalar_reference_mul (a b : Scalar.Word) :
    scalarReference (a * b) = UInt256.mul (scalarReference a) (scalarReference b) := by
  rfl

theorem scalar_add_reference (s : EVM.State) (a b : Scalar.Word) (tail : Scalar.Stack)
    (fuel cost : Nat) :
    EVM.step (fuel + 1) cost (some (.ADD, none))
      {s with stack := (a :: b :: tail).map scalarReference} =
      .ok (({s with
        stack := (a :: b :: tail).map scalarReference
        execLength := s.execLength + 1
        gasAvailable := s.gasAvailable - UInt256.ofNat cost}).replaceStackAndIncrPC
          (((a + b) :: tail).map scalarReference)) := by
  simp only [List.map_cons]
  rw [scalar_reference_add]
  rfl

theorem scalar_sub_reference (s : EVM.State) (a b : Scalar.Word) (tail : Scalar.Stack)
    (fuel cost : Nat) :
    EVM.step (fuel + 1) cost (some (.SUB, none))
      {s with stack := (a :: b :: tail).map scalarReference} =
      .ok (({s with
        stack := (a :: b :: tail).map scalarReference
        execLength := s.execLength + 1
        gasAvailable := s.gasAvailable - UInt256.ofNat cost}).replaceStackAndIncrPC
          (((a - b) :: tail).map scalarReference)) := by
  simp only [List.map_cons]
  rw [scalar_reference_sub]
  rfl

theorem scalar_mul_reference (s : EVM.State) (a b : Scalar.Word) (tail : Scalar.Stack)
    (fuel cost : Nat) :
    EVM.step (fuel + 1) cost (some (.MUL, none))
      {s with stack := (a :: b :: tail).map scalarReference} =
      .ok (({s with
        stack := (a :: b :: tail).map scalarReference
        execLength := s.execLength + 1
        gasAvailable := s.gasAvailable - UInt256.ofNat cost}).replaceStackAndIncrPC
          (((a * b) :: tail).map scalarReference)) := by
  simp only [List.map_cons]
  rw [scalar_reference_mul]
  rfl

/-- Consume the published intrinsic addW certificate, discharging source
value selection rather than assuming a source/target correspondence. -/
theorem wrapping_add_reference (s : EVM.State) (a b : PrimTy.uint.Denote)
    (tail : Scalar.Stack) (fuel cost : Nat) :
    ∃ r : PrimTy.uint.Denote, BinOp.evalT (op := .addW) rfl a b = some r ∧
      EVM.step (fuel + 1) cost (some (.ADD, none))
        {s with stack := (Scalar.encodeValue .uint a :: Scalar.encodeValue .uint b :: tail).map scalarReference} =
        .ok (({s with
          stack := (Scalar.encodeValue .uint a :: Scalar.encodeValue .uint b :: tail).map scalarReference
          execLength := s.execLength + 1
          gasAvailable := s.gasAvailable - UInt256.ofNat cost}).replaceStackAndIncrPC
            ((Scalar.encodeValue .uint r :: tail).map scalarReference)) := by
  have hc := Scalar.wrappingAdd.correct a b tail
  change some ((Scalar.encodeValue .uint a + Scalar.encodeValue .uint b) :: tail) =
    (BinOp.evalT (op := .addW) rfl a b).map (fun r => Scalar.encodeValue .uint r :: tail) at hc
  cases hv : BinOp.evalT (op := .addW) rfl a b with
  | none =>
    simp only [hv, Option.map_none] at hc
    cases hc
  | some r =>
    refine ⟨r, rfl, ?_⟩
    have he : Scalar.encodeValue .uint a + Scalar.encodeValue .uint b = Scalar.encodeValue .uint r := by
      have hl : ((Scalar.encodeValue .uint a + Scalar.encodeValue .uint b) :: tail) =
          Scalar.encodeValue .uint r :: tail := by
        simpa only [hv, Option.map_some, Option.some.injEq] using hc
      exact (List.cons.inj hl).1
    have step := scalar_add_reference s (Scalar.encodeValue .uint a)
      (Scalar.encodeValue .uint b) tail fuel cost
    rw [he] at step
    exact step

/-- Consume the published intrinsic subW certificate, discharging source
value selection rather than assuming a source/target correspondence. -/
theorem wrapping_sub_reference (s : EVM.State) (a b : PrimTy.uint.Denote)
    (tail : Scalar.Stack) (fuel cost : Nat) :
    ∃ r : PrimTy.uint.Denote, BinOp.evalT (op := .subW) rfl a b = some r ∧
      EVM.step (fuel + 1) cost (some (.SUB, none))
        {s with stack := (Scalar.encodeValue .uint a :: Scalar.encodeValue .uint b :: tail).map scalarReference} =
        .ok (({s with
          stack := (Scalar.encodeValue .uint a :: Scalar.encodeValue .uint b :: tail).map scalarReference
          execLength := s.execLength + 1
          gasAvailable := s.gasAvailable - UInt256.ofNat cost}).replaceStackAndIncrPC
            ((Scalar.encodeValue .uint r :: tail).map scalarReference)) := by
  have hc := Scalar.wrappingSub.correct a b tail
  change some ((Scalar.encodeValue .uint a - Scalar.encodeValue .uint b) :: tail) =
    (BinOp.evalT (op := .subW) rfl a b).map (fun r => Scalar.encodeValue .uint r :: tail) at hc
  cases hv : BinOp.evalT (op := .subW) rfl a b with
  | none =>
    simp only [hv, Option.map_none] at hc
    cases hc
  | some r =>
    refine ⟨r, rfl, ?_⟩
    have he : Scalar.encodeValue .uint a - Scalar.encodeValue .uint b = Scalar.encodeValue .uint r := by
      have hl : ((Scalar.encodeValue .uint a - Scalar.encodeValue .uint b) :: tail) =
          Scalar.encodeValue .uint r :: tail := by
        simpa only [hv, Option.map_some, Option.some.injEq] using hc
      exact (List.cons.inj hl).1
    have step := scalar_sub_reference s (Scalar.encodeValue .uint a)
      (Scalar.encodeValue .uint b) tail fuel cost
    rw [he] at step
    exact step

/-- Consume the published intrinsic mulW certificate, discharging source
value selection rather than assuming a source/target correspondence. -/
theorem wrapping_mul_reference (s : EVM.State) (a b : PrimTy.uint.Denote)
    (tail : Scalar.Stack) (fuel cost : Nat) :
    ∃ r : PrimTy.uint.Denote, BinOp.evalT (op := .mulW) rfl a b = some r ∧
      EVM.step (fuel + 1) cost (some (.MUL, none))
        {s with stack := (Scalar.encodeValue .uint a :: Scalar.encodeValue .uint b :: tail).map scalarReference} =
        .ok (({s with
          stack := (Scalar.encodeValue .uint a :: Scalar.encodeValue .uint b :: tail).map scalarReference
          execLength := s.execLength + 1
          gasAvailable := s.gasAvailable - UInt256.ofNat cost}).replaceStackAndIncrPC
            ((Scalar.encodeValue .uint r :: tail).map scalarReference)) := by
  have hc := Scalar.wrappingMul.correct a b tail
  change some ((Scalar.encodeValue .uint a * Scalar.encodeValue .uint b) :: tail) =
    (BinOp.evalT (op := .mulW) rfl a b).map (fun r => Scalar.encodeValue .uint r :: tail) at hc
  cases hv : BinOp.evalT (op := .mulW) rfl a b with
  | none =>
    simp only [hv, Option.map_none] at hc
    cases hc
  | some r =>
    refine ⟨r, rfl, ?_⟩
    have he : Scalar.encodeValue .uint a * Scalar.encodeValue .uint b = Scalar.encodeValue .uint r := by
      have hl : ((Scalar.encodeValue .uint a * Scalar.encodeValue .uint b) :: tail) =
          Scalar.encodeValue .uint r :: tail := by
        simpa only [hv, Option.map_some, Option.some.injEq] using hc
      exact (List.cons.inj hl).1
    have step := scalar_mul_reference s (Scalar.encodeValue .uint a)
      (Scalar.encodeValue .uint b) tail fuel cost
    rw [he] at step
    exact step

end SolidityBridge.RoadmapV15
