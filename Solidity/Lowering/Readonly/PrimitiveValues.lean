import Solidity.Source.State
import Solidity.Semantics.Value

/-! Faithful primitive source/intrinsic value transport for call lowering.
This is a bijection on uint256/int256/bool values, not an ABI decoder or a
whole-contract layout certificate. Other source types are outside this map. -/
namespace Solidity.Lowering.Readonly.PrimitiveValues
open Solidity.Source

def sourceTy : PrimTy → STy
  | .uint => .int IntTy.u256
  | .int => .int ⟨true, 256, by decide⟩
  | .bool => .bool

def toSource (D : Layout) (p : PrimTy) (v : p.Denote) : Solidity.Source.Val D (sourceTy p) := by
  cases p with
  | uint =>
    refine .int v.val ?_
    have bounds := of_decide_eq_true v.property
    change 0 ≤ v.val ∧ v.val ≤ ((2 ^ 256 : Nat) : Int) - 1
    change 0 ≤ v.val ∧ v.val < ((2 ^ 256 : Nat) : Int) at bounds
    exact ⟨bounds.1, Int.le_sub_one_of_lt bounds.2⟩
  | int =>
    refine .int v.val ?_
    have bounds := of_decide_eq_true v.property
    change -((2 ^ 255 : Nat) : Int) ≤ v.val ∧ v.val ≤ ((2 ^ 255 : Nat) : Int) - 1
    change -((2 ^ 255 : Nat) : Int) ≤ v.val ∧ v.val < ((2 ^ 255 : Nat) : Int) at bounds
    exact ⟨bounds.1, Int.le_sub_one_of_lt bounds.2⟩
  | bool => exact .bool v

def fromSource (D : Layout) (p : PrimTy) : Solidity.Source.Val D (sourceTy p) → p.Denote := by
  cases p with
  | uint =>
    intro v
    cases v with
    | int n bounds =>
      refine ⟨n, ?_⟩
      apply decide_eq_true
      change 0 ≤ n ∧ n < ((2 ^ 256 : Nat) : Int)
      change 0 ≤ n ∧ n ≤ ((2 ^ 256 : Nat) : Int) - 1 at bounds
      exact ⟨bounds.1, Int.lt_of_le_sub_one bounds.2⟩
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ => cases h
  | int =>
    intro v
    cases v with
    | int n bounds =>
      refine ⟨n, ?_⟩
      apply decide_eq_true
      change -((2 ^ 255 : Nat) : Int) ≤ n ∧ n < ((2 ^ 255 : Nat) : Int)
      change -((2 ^ 255 : Nat) : Int) ≤ n ∧ n ≤ ((2 ^ 255 : Nat) : Int) - 1 at bounds
      exact ⟨bounds.1, Int.lt_of_le_sub_one bounds.2⟩
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ => cases h
  | bool =>
    intro v
    cases v with
    | bool b => exact b
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ => cases h

theorem from_to (D : Layout) (p : PrimTy) (v : p.Denote) :
    fromSource D p (toSource D p v) = v := by
  cases p with
  | uint => apply Subtype.ext; rfl
  | int => apply Subtype.ext; rfl
  | bool => rfl

theorem to_from (D : Layout) (p : PrimTy) (v : Solidity.Source.Val D (sourceTy p)) :
    toSource D p (fromSource D p v) = v := by
  cases p <;> cases v <;> first | rfl | contradiction

theorem faithful (D : Layout) (p : PrimTy) : Function.Injective (toSource D p) := by
  intro left right same
  have values := congrArg (fromSource D p) same
  simpa only [from_to] using values

/-- The source's own primitive default is transported exactly. -/
theorem default_value (D : Layout) (p : PrimTy) :
    Solidity.Source.Val.default D (sourceTy p) = some (toSource D p (PrimTy.dflt p)) := by
  cases p <;> rfl

end Solidity.Lowering.Readonly.PrimitiveValues
