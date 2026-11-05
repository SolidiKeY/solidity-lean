import Solidity.Frontend.ConstantDepth.Correspondence

/-! # Constant-depth controls

Kernel-checked (`decide`) controls for the declaration-derived bound, on the
real `evalConst`/`nconstP`/`rank`/`acyclicB`:
- a chain whose rank equals the declaration count, and one whose rank is one
  below it (in both, one level fewer than the rank refuses);
- a shared diamond; contract scopes with inheritance and shadowing;
- duplicate declarations; used and unused cycles; a qualified member
  reference; overflow refusal.

Each acyclic, clash-free unit instantiates `evalConst_iff`/`evalConst_none_iff`,
so its decided values and refusals are exactly the `TEval` facts. For the cyclic
unit the contract fails, so only soundness (`evalConst_sound`) applies and its
members are shown refused by `evalConst`, not shown to lack a `TEval` value
(the existing `InferExamples.cyc_nc` proves that for a separate `A ↔ B` unit).
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
/-- The decided value is the independently specified typed value. -/
theorem chain_teval : TEval chainE none (.ident (cname 5)) (some .u256, Q.ofInt 6) :=
  (evalConst_iff chain_contract.1 chain_contract.2).mp (by decide)

/-- Near the declaration count: the chain `C0 … C4` plus one unrelated constant.
The deepest rank is `decls.length - 1`; exactly that many levels suffice. -/
def nearE : Env := (Syn.unit (listTop (chainParts 5 ++ [fileConst "U" (num 9)]))).env

theorem near_contract : (nearE.decls.Pairwise fun a b => a.clash nearE b = false) ∧
    ConstsAcyclic nearE :=
  ⟨noClashB_sound (by decide), acyclic_iff.mp (by decide)⟩
theorem near_rank : nearE.decls.length = 6 ∧ rank nearE (none, cname 4) = 5 ∧
    rank nearE (none, "U") = 1 := by decide
theorem near_rank_tight : (nconstP nearE 5 none (cname 4)).isSome = true ∧
    (nconstP nearE 4 none (cname 4)).isNone = true := by decide
theorem near_teval : TEval nearE none (.ident (cname 4)) (some .u256, Q.ofInt 5) :=
  (evalConst_iff near_contract.1 near_contract.2).mp (by decide)

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
/-- Soundness needs no contract, so the unused-cycle value is a `TEval` value. -/
theorem unused_cycle_teval : TEval cyclicE none (.ident "M") (some .u256, Q.ofInt 4) :=
  evalConst_sound (by decide)

/-! ## Qualified references

`uint256 constant V = K.X;` with `contract K { uint256 constant X = 5; }`: the
member access contributes only the path `K` (`Syn.paths`), so the existing
graph has no edge to `K.X` and the existing typed evaluation (`TEval` has no
member rule) gives no value. Recorded as existing behaviour, not changed here. -/
def qualifiedE : Env := (Syn.unit (listTop [
  .contract false "K" .none .nil (.cons (memberConst "X" (num 5)) .nil),
  fileConst "V" (.member (.ident "K") "X")])).env

theorem qualified_contract : (qualifiedE.decls.Pairwise fun a b => a.clash qualifiedE b = false) ∧
    ConstsAcyclic qualifiedE :=
  ⟨noClashB_sound (by decide), acyclic_iff.mp (by decide)⟩
/-- `K.X` itself evaluates in `K`; only the qualified reference has no edge. -/
theorem qualified_no_edge : valueOf qualifiedE (some "K") "X" = some 5 ∧
    qualifiedE.constDeps (none, "V") = [] ∧ rank qualifiedE (none, "V") = 1 := by
  decide
theorem qualified_refused : ¬ ∃ v, TEval qualifiedE none (.ident "V") v :=
  (evalConst_none_iff qualified_contract.1 qualified_contract.2).mp (by decide)

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

/-! Exact axiom pins (mirrored in `tests/sol-constant-depth/Axioms.lean`). -/

/-- info: 'Solidity.Frontend.ConstantDepth.mem_constDeps_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.mem_constDeps_iff
/-- info: 'Solidity.Frontend.ConstantDepth.mem_constNodes_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.mem_constNodes_iff
/-- info: 'Solidity.Frontend.ConstantDepth.constNodes_length_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.constNodes_length_le
/-- info: 'Solidity.Frontend.ConstantDepth.reaches_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.reaches_iff
/-- info: 'Solidity.Frontend.ConstantDepth.rank_le_decls' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.rank_le_decls
/-- info: 'Solidity.Frontend.ConstantDepth.filter_length_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.filter_length_mono
/-- info: 'Solidity.Frontend.ConstantDepth.filter_length_strict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.filter_length_strict
/-- info: 'Solidity.Frontend.ConstantDepth.no_self_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.no_self_path
/-- info: 'Solidity.Frontend.ConstantDepth.rank_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.rank_lt
/-- info: 'Solidity.Frontend.ConstantDepth.rank_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.rank_mono
/-- info: 'Solidity.Frontend.ConstantDepth.rank_lt_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.rank_lt_path
/-- info: 'Solidity.Frontend.ConstantDepth.rank_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.rank_pos
/-- info: 'Solidity.Frontend.ConstantDepth.walk_rank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.walk_rank
/-- info: 'Solidity.Frontend.ConstantDepth.walk_length_lt_decls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.walk_length_lt_decls
/-- info: 'Solidity.Frontend.ConstantDepth.declared_identity' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.declared_identity
/-- info: 'Solidity.Frontend.ConstantDepth.lookup_identity' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.lookup_identity
/-- info: 'Solidity.Frontend.ConstantDepth.constant_not_overload' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.constant_not_overload
/-- info: 'Solidity.Frontend.ConstantDepth.constant_clash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.constant_clash
/-- info: 'Solidity.Frontend.ConstantDepth.singleton_of_pairwise' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.singleton_of_pairwise
/-- info: 'Solidity.Frontend.ConstantDepth.declared_constant_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.declared_constant_singleton
/-- info: 'Solidity.Frontend.ConstantDepth.linearize_starts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.linearize_starts
/-- info: 'Solidity.Frontend.ConstantDepth.lookup_own_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.lookup_own_singleton
/-- info: 'Solidity.Frontend.ConstantDepth.lookup_constant_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.lookup_constant_canonical
/-- info: 'Solidity.Frontend.ConstantDepth.initializer_dependency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.initializer_dependency
/-- info: 'Solidity.Frontend.ConstantDepth.rank_resolved_dependency_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.rank_resolved_dependency_lt
/-- info: 'Solidity.Frontend.ConstantDepth.constBin_paths' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.constBin_paths
/-- info: 'Solidity.Frontend.ConstantDepth.teval_with_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.teval_with_oracle
/-- info: 'Solidity.Frontend.ConstantDepth.nconst_rank_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.nconst_rank_complete
/-- info: 'Solidity.Frontend.ConstantDepth.nconst_levels_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.nconst_levels_complete
/-- info: 'Solidity.Frontend.ConstantDepth.evalConst_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.evalConst_complete
/-- info: 'Solidity.Frontend.ConstantDepth.evalConst_resolved_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.evalConst_resolved_complete
/-- info: 'Solidity.Frontend.ConstantDepth.nconst_resolved_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.nconst_resolved_complete
/-- info: 'Solidity.Frontend.ConstantDepth.evalConst_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.evalConst_iff
/-- info: 'Solidity.Frontend.ConstantDepth.evalConst_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.evalConst_none_iff
/-- info: 'Solidity.Frontend.ConstantDepth.arrayLenB_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.arrayLenB_complete
/-- info: 'Solidity.Frontend.ConstantDepth.arrayLenB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.arrayLenB_iff
/-- info: 'Solidity.Frontend.ConstantDepth.arrayLenB_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.arrayLenB_none_iff
/-- info: 'Solidity.Frontend.ConstantDepth.arrayLenB_resolved_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.arrayLenB_resolved_complete
/-- info: 'Solidity.Frontend.ConstantDepth.teval_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.teval_det
/-- info: 'Solidity.Frontend.ConstantDepth.nconst_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.nconst_det
/-- info: 'Solidity.Frontend.ConstantDepth.arrayLen_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.arrayLen_det
/-- info: 'Solidity.Frontend.ConstantDepth.lookup_declared_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.lookup_declared_constant
/-- info: 'Solidity.Frontend.ConstantDepth.constDeps_declared_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.constDeps_declared_iff
/-- info: 'Solidity.Frontend.ConstantDepth.rank_declared_dependency_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.rank_declared_dependency_lt
/-- info: 'Solidity.Frontend.ConstantDepth.depPath_rank_no_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.depPath_rank_no_return
/-- info: 'Solidity.Frontend.ConstantDepth.teval_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.teval_unique
/-- info: 'Solidity.Frontend.ConstantDepth.nconst_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.nconst_unique
/-- info: 'Solidity.Frontend.ConstantDepth.arrayLen_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.arrayLen_unique
/-- info: 'Solidity.Frontend.ConstantDepth.arrayLen_static_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.arrayLen_static_value
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.noClashB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.noClashB_sound
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.chain_decls' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.chain_decls
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.chain_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.chain_contract
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.chain_rank' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.chain_rank
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.chain_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.chain_value
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.chain_rank_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.chain_rank_tight
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.chain_teval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.chain_teval
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.near_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.near_contract
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.near_rank' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.near_rank
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.near_rank_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.near_rank_tight
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.near_teval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.near_teval
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.diamond_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.diamond_contract
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.diamond_rank' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.diamond_rank
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.diamond_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.diamond_value
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.diamond_teval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.diamond_teval
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.scoped_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.scoped_contract
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.scoped_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.scoped_values
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.scoped_member_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.scoped_member_hidden
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.scoped_no_teval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.scoped_no_teval
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.scoped_teval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.scoped_teval
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.duplicate_clashes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.duplicate_clashes
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.duplicate_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.duplicate_refused
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.cyclic_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.cyclic_refused
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.cyclic_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.cyclic_values
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.unused_cycle_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.unused_cycle_value
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.unused_cycle_teval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.unused_cycle_teval
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.qualified_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.qualified_contract
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.qualified_no_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.qualified_no_edge
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.qualified_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.qualified_refused
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.overflow_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.overflow_contract
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.overflow_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.overflow_values
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.overflow_no_teval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.overflow_no_teval
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.overflow_lengths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.overflow_lengths
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.overflow_length_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.overflow_length_refused
