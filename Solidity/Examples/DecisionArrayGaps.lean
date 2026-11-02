import Solidity.Calculus.Decision
import Solidity.Calculus.Surface
import Solidity.Syntax.Contract
/-!
# Actual assigned array-gap census

Fixed bounded blocks now have kernel coverage and certified verdicts through
exact finite preparation. The five formerly unknown valid-instance fixtures now have computed source-chain
coverage and certified positive verdicts. This is not exhaustive array completeness
or an implementation of the global Residue theorem. Arrays below
keys/fields and arrays of structures/arrays are separately named.
-/
namespace Solidity.Examples.DecisionArrayGaps
open Solidity.Decide
set_option Elab.async false

def Probe : Contract := contract!{
  struct Box { uint[] xs; uint[3] fs; }
  struct Cell { uint v; }
  uint[3] fixedArr;
  mapping(uint => uint[]) rows;
  mapping(uint => uint[3]) fixedRows;
  Box box;
  uint[][] grid;
  Cell[] cells;
}
local instance arrayCensusContract : InContract := ⟨Probe⟩

def fixedBlock : Fml Probe [] := dl[Probe]{
  (∀ uint i; i < 3 → fixedArr[i] = 0) → fixedArr[1] = 0 }
def fixedBad : Fml Probe [] := dl[Probe]{
  (∀ uint i; i < 2 → fixedArr[i] = 0) → fixedArr[2] = 0 }
def belowKey : Fml Probe [] := dl[Probe]{ ∀ uint k;
  (∀ uint i; i < 3 → rows[k][i] = 0) → rows[k][1] = 0 }
def fixedBelowKey : Fml Probe [] := dl[Probe]{ ∀ uint k;
  (∀ uint i; i < 3 → fixedRows[k][i] = 0) → fixedRows[k][1] = 0 }
def belowField : Fml Probe [] := dl[Probe]{
  (∀ uint i; i < 3 → box.xs[i] = 0) → box.xs[1] = 0 }
def arrayStruct : Fml Probe [] := dl[Probe]{
  (∀ uint i; i < 3 → cells[i].v = 0) → cells[1].v = 0 }
def arrayArray : Fml Probe [] := dl[Probe]{ ∀ uint k;
  (∀ uint i; i < 3 → grid[k][i] = 0) → grid[k][1] = 0 }

@[noinline] def classify (φ : Fml Probe []) : Bool × Bool × String :=
  let c := φ.Covered
  (φ.inTarget {}, c, if c then "covered: verdict search not profiled" else
    match decideGoal φ with
    | .proved => "proved"
    | .refuted _ => "refuted"
    | .unknown => "unknown")
#eval [("fixed", fixedBlock), ("fixedBad", fixedBad), ("key", belowKey),
  ("fixedKey", fixedBelowKey), ("field", belowField), ("struct", arrayStruct), ("array", arrayArray)].map
  (fun (name, φ) => (name, classify φ))

/-- The original source shape `fixedBlock` is admitted by the requested fragment. -/
theorem fixedBlock_target : fixedBlock.inTarget {} = true := by decide +kernel

/-- Exact bounded preparation covers the original positive fixed block. -/
theorem fixedBlock_covered : fixedBlock.Covered = true := by decide +kernel

/-- The original source shape `fixedBad` is admitted by the requested fragment. -/
theorem fixedBad_target : fixedBad.inTarget {} = true := by decide +kernel

/-- The same coverage route includes the false fixed-array control. -/
theorem fixedBad_covered : fixedBad.Covered = true := by decide +kernel

/-- The original source shape `belowKey` is admitted by the requested fragment. -/
theorem belowKey_target : belowKey.inTarget {} = true := by decide +kernel

/-- Computed source-chain recognition covers the original `belowKey` fixture. -/
theorem belowKey_covered : belowKey.Covered = true :=
  sourceUIntLiteral_covered (by decide +kernel) (by decide +kernel)

/-- The actual original source now has a kernel-certified positive verdict. -/
theorem belowKey_proved : decideGoal belowKey = .proved :=
  sourceUIntLiteral_proved (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The original source shape `fixedBelowKey` is admitted by the requested fragment. -/
theorem fixedBelowKey_target : fixedBelowKey.inTarget {} = true := by decide +kernel

/-- Computed source-chain recognition covers the original `fixedBelowKey` fixture. -/
theorem fixedBelowKey_covered : fixedBelowKey.Covered = true :=
  sourceUIntLiteral_covered (by decide +kernel) (by decide +kernel)

/-- The actual original source now has a kernel-certified positive verdict. -/
theorem fixedBelowKey_proved : decideGoal fixedBelowKey = .proved :=
  sourceUIntLiteral_proved (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The original source shape `belowField` is admitted by the requested fragment. -/
theorem belowField_target : belowField.inTarget {} = true := by decide +kernel

/-- Computed source-chain recognition covers the original `belowField` fixture. -/
theorem belowField_covered : belowField.Covered = true :=
  sourceUIntLiteral_covered (by decide +kernel) (by decide +kernel)

/-- The actual original source now has a kernel-certified positive verdict. -/
theorem belowField_proved : decideGoal belowField = .proved :=
  sourceUIntLiteral_proved (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The original source shape `arrayStruct` is admitted by the requested fragment. -/
theorem arrayStruct_target : arrayStruct.inTarget {} = true := by decide +kernel

/-- Computed source-chain recognition covers the original `arrayStruct` fixture. -/
theorem arrayStruct_covered : arrayStruct.Covered = true :=
  sourceUIntLiteral_covered (by decide +kernel) (by decide +kernel)

/-- The actual original source now has a kernel-certified positive verdict. -/
theorem arrayStruct_proved : decideGoal arrayStruct = .proved :=
  sourceUIntLiteral_proved (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The original source shape `arrayArray` is admitted by the requested fragment. -/
theorem arrayArray_target : arrayArray.inTarget {} = true := by decide +kernel

/-- Computed source-chain recognition covers the original `arrayArray` fixture. -/
theorem arrayArray_covered : arrayArray.Covered = true :=
  sourceUIntLiteral_covered (by decide +kernel) (by decide +kernel)

/-- The actual original source now has a kernel-certified positive verdict. -/
theorem arrayArray_proved : decideGoal arrayArray = .proved :=
  sourceUIntLiteral_proved (by decide +kernel) (by decide +kernel) (by decide +kernel)


/-- The positive `fixedBlock` block is valid by its inhabited index-one instance. -/
theorem fixedBlock_valid : Fml.Valid fixedBlock := by
  intro σ h
  exact h (uintOfNat 1) rfl

/-- The positive `belowKey` block is valid by its inhabited index-one instance. -/
theorem belowKey_valid : Fml.Valid belowKey := by
  intro σ k h
  exact h (uintOfNat 1) rfl

/-- The positive `fixedBelowKey` block is valid by its inhabited index-one instance. -/
theorem fixedBelowKey_valid : Fml.Valid fixedBelowKey := by
  intro σ k h
  exact h (uintOfNat 1) rfl

/-- The positive `belowField` block is valid by its inhabited index-one instance. -/
theorem belowField_valid : Fml.Valid belowField := by
  intro σ h
  exact h (uintOfNat 1) rfl

/-- The positive `arrayStruct` block is valid by its inhabited index-one instance. -/
theorem arrayStruct_valid : Fml.Valid arrayStruct := by
  intro σ h
  exact h (uintOfNat 1) rfl

/-- The positive `arrayArray` block is valid by its inhabited index-one instance. -/
theorem arrayArray_valid : Fml.Valid arrayArray := by
  intro σ k h
  exact h (uintOfNat 1) rfl

/-- Replace only a named fixed uint-array root by a typed vector with a nonzero third slot. -/
def fixedBadValue (a : Name) (T : Ty) (v : SVal T) : SVal T :=
  match T with
  | .ref (.fixed (.prim .uint) n) =>
    if a == "fixedArr" then
      .fixed (vecOf (fun i => .prim (uintOfNat (if i == 2 then 1 else 0))) n)
    else v
  | _ => v

/-- An actual intrinsic state, retaining every other default root. -/
def fixedBadState : State Probe [] :=
  (State.init Probe).withStorage ((State.init Probe).storage.mapF fixedBadValue)

/-- The negative control's three array entries are constructed, not postulated. -/
theorem fixedBadState_shape :
    fixedBadState.storage.get
      (by decide : Probe.rootType "fixedArr" = some (.ref (.fixed (.prim .uint) 3))) =
      .fixed (.cons (.prim (uintOfNat 0))
        (.cons (.prim (uintOfNat 0)) (.cons (.prim (uintOfNat 1)) .nil))) := by
  rfl

/-- The realized [0,0,1] root satisfies the bounded hypothesis but falsifies slot two. -/
theorem fixedBad_countermodel : ¬ holds fixedBadState fixedBad := by
  intro h
  have hc : (holds fixedBadState (dl[Probe]{ fixedArr[2] = 0 }) ↔
      uintOfNat 1 = uintOfNat 0) :=
    holds_eq_of_eval (by decide +kernel) (by decide +kernel)
  apply (by decide +kernel : uintOfNat 1 ≠ uintOfNat 0)
  apply hc.mp
  apply h
  intro i hi
  change (some (decide (i.1 < 2)) : Option Bool) = some true at hi
  have hi2 : i.1 < 2 := of_decide_eq_true (Option.some.inj hi)
  have hn : 0 ≤ i.1 := PrimTy.uint_nonneg i
  have he : i.1 = 0 ∨ i.1 = 1 := by omega
  rcases he with he | he
  · have ei : i = uintOfNat 0 := Subtype.ext he
    subst i
    apply (holds_eq_of_eval (x := uintOfNat 0) (y := uintOfNat 0)
      (by decide +kernel) (by decide +kernel)).mpr
    rfl
  · have ei : i = uintOfNat 1 := Subtype.ext he
    subst i
    apply (holds_eq_of_eval (x := uintOfNat 0) (y := uintOfNat 0)
      (by decide +kernel) (by decide +kernel)).mpr
    rfl

/-- The negative fixed-array control is genuinely false. -/
theorem fixedBad_notValid : ¬ Fml.Valid fixedBad := by
  intro h
  exact fixedBad_countermodel (h fixedBadState)

theorem fixedBlock_hashFree : fixedBlock.hasHash = false := by decide +kernel

theorem fixedBad_hashFree : fixedBad.hasHash = false := by decide +kernel

/-- Coverage and the existing semantic proof force the actual certified verdict. -/
theorem fixedBlock_proved : decideGoal fixedBlock = .proved := by
  have hd : decideGoal fixedBlock ≠ .unknown :=
    decideGoal_complete fixedBlock_covered fixedBlock_hashFree
  have hv : Fml.ValidH fixedBlock := (Fml.validH_iff fixedBlock_hashFree).mpr fixedBlock_valid
  cases he : decideGoal fixedBlock with
  | proved => rfl
  | refuted σ => exact False.elim (decideGoal_refutes he (hv σ))
  | unknown => exact False.elim (hd he)

/-- The returned state is kernel-certified; no expected verdict substitutes for it. -/
theorem fixedBad_refuted : ∃ σ : State Probe [], decideGoal fixedBad = .refuted σ ∧
    ¬ Fml.holdsH σ fixedBad := by
  have hd : decideGoal fixedBad ≠ .unknown :=
    decideGoal_complete fixedBad_covered fixedBad_hashFree
  cases he : decideGoal fixedBad with
  | proved =>
    have hv : Fml.Valid fixedBad := (Fml.validH_iff fixedBad_hashFree).mp (decideGoal_sound he)
    exact False.elim (fixedBad_notValid hv)
  | refuted σ => exact ⟨σ, rfl, decideGoal_refutes he⟩
  | unknown => exact False.elim (hd he)

end Solidity.Examples.DecisionArrayGaps
