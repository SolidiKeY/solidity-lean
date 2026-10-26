import Solidity.Calculus.Arms
import Solidity.Calculus.LexVariant

/-!
# A typed lexicographic diamond premise

Every old metric is captured before the condition; every new metric is
captured after the body. The postcondition demands decrease after every
successful body, including the last turn. This conservative rule is separate
from callback modalities and from strict successful-termination certificates.
-/
namespace Solidity.LoopLex

variable {C : Contract} {Γ Γ₁ : Ctx}

def diamondPost (k : Nat) (I : Val C Γ .bool) {n : Nat}
    (metrics : LoopMetrics C Γ n) : Fml C (SavedCtx n Γ) :=
  let h := Thin.ofExt (savedExt Γ n)
  .and (.isBool (I.wk h).lower true)
    (.upd .diamond (snapshot (k + n + 1) (metrics.wk h)) (snapshotsDecrease n))

def diamondPremise (k : Nat) (I c : Val C Γ .bool) {n : Nat}
    (metrics : LoopMetrics C Γ n) (body : Prog C Γ Γ₁)
    (xs : List ((t : LTy) × Idx Γ t)) (hv : Option (List Name)) : Premise C Γ Γ :=
  .inv (.isBool I.lower true) none xs hv
    ((snapshot k metrics).decl (fse (k + n)) (.val c.lower))
    (.isBool (.pvV .here) true) (.isBool (.pvV .here) false)
    (savedExt Γ n) (.push .refl) (body.wk (.ofExt (savedExt Γ n))).2.2
    (diamondPost k I metrics)

/-- A conservative prospective dispatch. Break-flag and quantified invariant
annotations remain explicit obligations; this ordinary rule is not a callback
rule. The source annotation itself is retained by the eventual loop rule. -/
def diamondStep (k : Nat) (I c : Val C Γ .bool) {n : Nat}
    (metrics : LoopMetrics C Γ n) (brk : Bool) (qs : List (LoopQ C Γ))
    (body : Prog C Γ Γ₁)
    (frame : Option (List ((t : LTy) × Idx Γ t) × Option (List Name))) : Premise C Γ Γ :=
  match brk, qs, frame with
  | false, [], some (xs, hv) => diamondPremise k I c metrics body xs hv
  | _, _, _ => .done false

end Solidity.LoopLex
