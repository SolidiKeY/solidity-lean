import Solidity.Frontend.ConstantDepth.Complete

/-! # Constant-depth controls

Kernel-checked (`decide`) controls for the declaration-derived bound: a
chain whose rank equals the declaration count (one level below the rank
refuses), a shared diamond, contract scopes with inheritance and
shadowing, duplicate declarations, used and unused cycles, and overflow
refusal. Each acyclic, clash-free unit instantiates `evalConst_iff` /
`evalConst_none_iff`, so the decided values are the `TEval` values.
-/
namespace Solidity.Frontend.ConstantDepth.Controls
open Solidity.Source Solidity.Frontend.Static Solidity.Frontend.ConstantDepth

def u256T : Syn .typeName := .elem (.int false 256 (by decide))
def u8T : Syn .typeName := .elem (.int false 8 (by decide))
def num (n : Nat) : Syn .expr := .lit (.num (.dec n 0 0))
def plus (a b : Syn .expr) : Syn .expr := .addSub .add a b
def times (a b : Syn .expr) : Syn .expr := .mulDivMod .mul a b
/-- A file-level `uint256 constant x = e;`. -/
def fileConst (x : String) (e : Syn .expr) : Syn .top := .topPart (.constant u256T x e)
/-- A contract member `uint256 constant x = e;`. -/
def memberConst (x : String) (e : Syn .expr) : Syn (.part false) :=
  .stateVar u256T none (some .constant) none false x (.some e)

/-- The top-level value of a name, as an integer. -/
def valueOf (E : Env) (s : Option String) (x : String) : Option Int :=
  (evalConst E s (.ident x)).map (·.2.toInt)

/-- The clash-free projection of the existing well-formedness contract, decided. -/
def noClashB (E : Env) : Bool := decide (E.decls.Pairwise fun a b => a.clash E b = false)

theorem noClashB_sound {E : Env} (h : noClashB E = true) :
    E.decls.Pairwise fun a b => a.clash E b = false := of_decide_eq_true h

/-! ## A chain at the declaration count -/

/-- Constant names `C0, C1, …`. -/
def cname (i : Nat) : String := "C" ++ toString i

/-- `C0 = 1; C(i+1) = C(i) + 1`, in declaration order. -/
def chainParts : Nat → List (Syn .top)
  | 0 => []
  | k + 1 => chainParts k ++ [fileConst (cname k) (if k = 0 then num 1 else plus (.ident (cname (k - 1))) (num 1))]

def listTop : List (Syn .top) → Syn (.list .top)
  | [] => .nil
  | x :: xs => .cons x (listTop xs)

def chainUnit (k : Nat) : Syn .unit := .unit (listTop (chainParts k))
def chainE : Env := (chainUnit 6).env

theorem chain_decls : chainE.decls.length = 6 := by decide
theorem chain_contract : (chainE.decls.Pairwise fun a b => a.clash chainE b = false) ∧
    ConstsAcyclic chainE :=
  ⟨noClashB_sound (by decide), acyclic_iff.mp (by decide)⟩
/-- The deepest constant's rank is the declaration count. -/
theorem chain_rank : rank chainE (none, cname 5) = chainE.decls.length := by decide
theorem chain_value : valueOf chainE none (cname 5) = some 6 := by decide
/-- Exactly the rank suffices; one level fewer refuses. -/
theorem chain_rank_tight : (nconstP chainE 6 none (cname 5)).isSome = true ∧
    (nconstP chainE 5 none (cname 5)).isNone = true := by decide
theorem chain_levels : levels chainE = chainE.decls.length + 1 := rfl
/-- The decided value is the independently specified typed value. -/
theorem chain_teval : TEval chainE none (.ident (cname 5)) (some .u256, Q.ofInt 6) :=
  (evalConst_iff chain_contract.1 chain_contract.2).mp (by decide)

/-! ## A shared diamond -/

/-- `A = 1; B = A + 1; C = A * 2; D = B + C;` -/
def diamondE : Env := (Syn.unit (listTop [fileConst "A" (num 1), fileConst "B" (plus (.ident "A") (num 1)),
  fileConst "C" (times (.ident "A") (num 2)), fileConst "D" (plus (.ident "B") (.ident "C"))])).env

theorem diamond_contract : (diamondE.decls.Pairwise fun a b => a.clash diamondE b = false) ∧
    ConstsAcyclic diamondE :=
  ⟨noClashB_sound (by decide), acyclic_iff.mp (by decide)⟩
/-- The shared node is counted once. -/
theorem diamond_rank : rank diamondE (none, "D") = 4 ∧ rank diamondE (none, "A") = 1 := by decide
theorem diamond_value : valueOf diamondE none "D" = some 4 := by decide
theorem diamond_teval : TEval diamondE none (.ident "D") (some .u256, Q.ofInt 4) :=
  (evalConst_iff diamond_contract.1 diamond_contract.2).mp (by decide)

/-! ## Scopes, inheritance and shadowing -/

/-- ```
uint256 constant X = 100;
contract K { uint256 constant X = 5; uint256 constant Y = X + 1; }
contract L is K { uint256 constant Z = Y * 2; }
uint256 constant W = X + 1;
``` -/
def scopedE : Env := (Syn.unit (listTop [fileConst "X" (num 100),
  .contract false "K" .none .nil (.cons (memberConst "X" (num 5))
    (.cons (memberConst "Y" (plus (.ident "X") (num 1))) .nil)),
  .contract false "L" .none (.cons (.inherit ⟨"K", []⟩ .none) .nil)
    (.cons (memberConst "Z" (times (.ident "Y") (num 2))) .nil),
  fileConst "W" (plus (.ident "X") (num 1))])).env

theorem scoped_contract : (scopedE.decls.Pairwise fun a b => a.clash scopedE b = false) ∧
    ConstsAcyclic scopedE :=
  ⟨noClashB_sound (by decide), acyclic_iff.mp (by decide)⟩
/-- `K.X` shadows the file-level `X` inside `K` and in the derived `L`. -/
theorem scoped_values : valueOf scopedE (some "K") "Y" = some 6 ∧
    valueOf scopedE (some "L") "Z" = some 12 ∧ valueOf scopedE (some "L") "X" = some 5 ∧
    valueOf scopedE none "X" = some 100 ∧ valueOf scopedE none "W" = some 101 := by decide
/-- File level does not see contract members. -/
theorem scoped_member_hidden : valueOf scopedE none "Y" = none := by decide
theorem scoped_no_teval : ¬ ∃ v, TEval scopedE none (.ident "Y") v :=
  (evalConst_none_iff scoped_contract.1 scoped_contract.2).mp (by decide)
theorem scoped_teval : TEval scopedE (some "L") (.ident "Z") (some .u256, Q.ofInt 12) :=
  (evalConst_iff scoped_contract.1 scoped_contract.2).mp (by decide)

/-! ## Duplicates -/

/-- `X = 1; X = 2;` — the existing clash refusal, and no value. -/
def duplicateE : Env := (Syn.unit (listTop [fileConst "X" (num 1), fileConst "X" (num 2)])).env

theorem duplicate_clashes : noClashB duplicateE = false := by decide
theorem duplicate_refused : valueOf duplicateE none "X" = none := by decide

/-! ## Cycles -/

/-- `A = B + 1; B = A + 1; S = S + 1; N = 3; M = N + 1;` -/
def cyclicE : Env := (Syn.unit (listTop [fileConst "A" (plus (.ident "B") (num 1)),
  fileConst "B" (plus (.ident "A") (num 1)), fileConst "S" (plus (.ident "S") (num 1)),
  fileConst "N" (num 3), fileConst "M" (plus (.ident "N") (num 1))])).env

theorem cyclic_refused : ¬ ConstsAcyclic cyclicE := fun h => by
  have e := acyclic_iff.mpr h
  revert e
  decide
/-- Cycle members and the self-loop have no value at the public bound. -/
theorem cyclic_values : valueOf cyclicE none "A" = none ∧ valueOf cyclicE none "B" = none ∧
    valueOf cyclicE none "S" = none := by decide
/-- An unused cycle does not block an unrelated constant. -/
theorem unused_cycle_value : valueOf cyclicE none "M" = some 4 := by decide

/-! ## Overflow and exact conversion -/

/-- `uint8 constant C = 255; uint8 constant D = C + 1; uint8 constant F = 300 - 100;` -/
def overflowE : Env := (Syn.unit (listTop [.topPart (.constant u8T "C" (num 255)),
  .topPart (.constant u8T "D" (plus (.ident "C") (num 1))),
  .topPart (.constant u8T "F" (.addSub .sub (num 300) (num 100)))])).env

theorem overflow_contract : (overflowE.decls.Pairwise fun a b => a.clash overflowE b = false) ∧
    ConstsAcyclic overflowE :=
  ⟨noClashB_sound (by decide), acyclic_iff.mp (by decide)⟩
/-- Typed `uint8` overflow is a refusal; rational folding of literals is exact. -/
theorem overflow_values : valueOf overflowE none "C" = some 255 ∧ valueOf overflowE none "D" = none ∧
    valueOf overflowE none "F" = some 200 := by decide
theorem overflow_no_teval : ¬ ∃ v, TEval overflowE none (.ident "D") v :=
  (evalConst_none_iff overflow_contract.1 overflow_contract.2).mp (by decide)
/-- `uint8[D]` is no array length; `uint8[F]` has length 200. -/
theorem overflow_lengths : arrayLenB overflowE none (.some (.ident "D")) = none ∧
    arrayLenB overflowE none (.some (.ident "F")) = some (some 200) := by decide
theorem overflow_length_refused : ¬ ∃ n, ArrayLenOK overflowE none (.some (.ident "D")) n :=
  (arrayLenB_none_iff overflow_contract.1 overflow_contract.2).mp (by decide)

end Solidity.Frontend.ConstantDepth.Controls
