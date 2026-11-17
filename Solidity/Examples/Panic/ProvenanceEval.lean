import Solidity.Correctness.Panic.Provenance.Eval

/-!
# Checks: evaluator leaves of panic code provenance

Concrete failing evaluations whose solc code is read off the retained failed
site through the leaves of `Correctness/Panic/Provenance/Eval.lean`.
-/

namespace Solidity.Examples.Panic.ProvenanceEval
open Solidity.Panic Solidity.Semantics.Panic Solidity.Correctness.Panic

/-- The emitted solc code of an intrinsic failure. -/
def code? {α : Type} : EvalResult α → Option Nat
  | .error (.intrinsic code _) => some code.code
  | _ => none

/-- The failed site retained by an intrinsic failure. -/
def site? {α : Type} : EvalResult α → Option Site
  | .error (.intrinsic _ origin) => some origin.site
  | _ => none

/-- On a coded result the emitted code is determined by the retained site. -/
theorem code_of_site {α : Type} {r : EvalResult α} (hr : ErrCoded r) :
    code? r = (site? r).map Site.code := by
  match r, hr with
  | .ok _, _ => rfl
  | .error (.intrinsic code origin), hr =>
    simp only [code?, site?, Option.map_some, hr.intrinsic rfl, siteCode_code]
  | .error .revert, _ | .error .exhausted, _ | .error .diverge, _
  | .error (.externalRevert _), _ | .error (.revertWith _), _ => rfl

def zero : PrimTy.uint.Denote := ⟨0, by decide⟩
def one : PrimTy.uint.Denote := ⟨1, by decide⟩

def maxU : PrimTy.uint.Denote := ⟨2^256 - 1, by decide +kernel⟩

/-- `type(uint256).max + 1` under checked arithmetic retains the arithmetic
site, hence code 0x11. -/
example : code? (binary .add rfl maxU one) = some 0x11 := by
  rw [code_of_site (binary_coded .add rfl maxU one)]
  have : site? (binary .add rfl maxU one) = some .arithmetic := by decide +kernel
  rw [this]
  rfl

/-- `1 / 0` as an expression retains the zero-divisor site, hence code 0x12. -/
def divZero {C : Contract} {Γ : Ctx} : Val C Γ .uint :=
  .binop .div rfl rfl (.simple (.lit 1 (by decide))) (.simple (.lit 0 (by decide)))

example {C : Contract} {Γ : Ctx} (σ : State C Γ) : code? (value σ divZero) = some 0x12 := by
  rw [code_of_site (value_coded σ divZero)]
  have : site? (value σ divZero) = some .zeroDivisor := rfl
  rw [this]
  rfl

/-- An out-of-range memory index retains the bounds site, hence code 0x32. -/
example {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H) (ref : HRef H R)
    (array : ArrTy R E) (i : PrimTy.uint.Denote) (failed : hp.index ref array i = none) :
    code? (memoryRead hp (.index ref array i)) = some 0x32 := by
  rw [code_of_site (memoryRead_coded hp _)]
  have : site? (memoryRead hp (.index ref array i)) = some .bounds := by
    rw [memoryRead, evalProducer_origin _ _ (index_origin hp ref array i failed)]
    exact congrArg some (Raised.ofOrigin_site _ _ _)
  rw [this]
  rfl

end Solidity.Examples.Panic.ProvenanceEval
