import Solidity.Calculus.CallbackSound
import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.Quote

/-!
# Guarded native push premises

Division/remainder test the simple divisor outside both updates. The premise
keeps an explicit intermediate context, and its quotation is kernel-checked
even when the first update declares a local and the second drops it.
-/

namespace Solidity.Examples.Tactics.PushSuffixGuards

open scoped Solidity.Schema

/-- The guard of `sp.push() /= se` encloses both successive updates. -/
example {C : Contract} {Γ Δ : Ctx} (c : Fml C Γ) (U : Upd C Γ Δ) (V : Upd C Δ Γ) :
    (dl{ if c then (‹U› ‹V› ⟨[ ]⟩) else (⟨[ revert(); ]⟩) } : Premise C Γ Γ) =
      .guardedUpdates c U V := rfl

/-- The zero in `sp.push() /= se` has the source's numeric Solidity type. -/
example {C : Contract} {Γ Δ : Ctx} (p : PrimTy) (hp : p.isNumeric = true)
    (se : Simple C Γ p) (U : Upd C Γ Δ) (V : Upd C Δ Γ) :
    (dl{ if se != 0 then (‹U› ‹V› ⟨[ ]⟩) else (⟨[ revert(); ]⟩) } : Premise C Γ Γ) =
      .guardedUpdates (PushSuffix.nonzero hp se) U V := rfl

/-- Renaming the type/proof binders in `sp.push() /= se` preserves notation. -/
example {C : Contract} {Γ Δ : Ctx} (q : PrimTy) (hq : q.isNumeric = true)
    (se : Simple C Γ q) (U : Upd C Γ Δ) (V : Upd C Δ Γ) :
    (dl{ if se != 0 then (‹U› ‹V› ⟨[ ]⟩) else (⟨[ revert(); ]⟩) } : Premise C Γ Γ) =
      .guardedUpdates (PushSuffix.nonzero hq se) U V := rfl

def GuardedExample : Contract := contract!{ uint[] values; int[] signedValues; }

/-- The concrete printed guard parses with no ambient numeric binders. -/
example :
    (dl{ if 2 != 0 then ({ storage := storage } { storage := storage } ⟨[ ]⟩)
      else (⟨[ revert(); ]⟩) } : Premise GuardedExample [] []) =
      .guardedUpdates (PushSuffix.nonzero (p := .uint) rfl (.lit 2 rfl))
        (Upd.nil.snoc (.storage (.app0 .storage)))
        (Upd.nil.snoc (.storage (.app0 .storage))) := rfl

private def path : SPath GuardedExample [] (.array (.prim .uint)) :=
  .loc (.root "values" rfl)
private def signedPath : SPath GuardedExample [] (.array (.prim .int)) :=
  .loc (.root "signedValues" rfl)

/-- `values.push() /= 2` leaves the nonzero guard before append and save. -/
example : (Stmt.pushOpAssign .div rfl rfl path (.simple (.lit 2 rfl))).step 0 .diamond =
    .guardedUpdates (PushSuffix.nonzero (p := .uint) rfl (.lit 2 rfl))
      (Upd.nil.snoc (UpdElem.pushSlot path))
      (PushSuffix.saveOp .div rfl rfl path (.lit 2 rfl)) := rfl

/-- Signed `signedValues.push() %= 2` uses a signed zero in its outer guard. -/
example : (Stmt.pushOpAssign .mod rfl rfl signedPath (.simple (.lit 2 rfl))).step 0 .box =
    .guardedUpdates (PushSuffix.nonzero (p := .int) rfl (.lit 2 rfl))
      (Upd.nil.snoc (UpdElem.pushSlot signedPath))
      (PushSuffix.saveOp .mod rfl rfl signedPath (.lit 2 rfl)) := rfl

/- Quoting a guarded pair preserves its declaring intermediate context. -/
run_meta do
  let U : Upd GuardedExample [] [.val .uint] :=
    Upd.nil.decl (.user "x") (.val (.app0 (.lit (p := .uint) ⟨3, rfl⟩)))
  let V : Upd GuardedExample [.val .uint] [] := Upd.nil.pop (.push .refl)
  let e := Premise.quote (Lean.mkConst ``GuardedExample) (.guardedUpdates .tt U V)
  Lean.Meta.check e

/-- info: dl{ if 2 != 0 then ({ storage := storage } { storage := storage } ⟨[ ]⟩) else (⟨[ revert(); ]⟩) } -/
#guard_msgs in
run_meta do
  let U : Upd GuardedExample [] [] := Upd.nil.snoc (.storage (.app0 .storage))
  let se : Simple GuardedExample [] .uint := .lit 2 rfl
  let e := Premise.quote (Lean.mkConst ``GuardedExample)
    (.guardedUpdates (PushSuffix.nonzero rfl se) U U)
  Lean.Meta.check e
  Lean.logInfo m!"{e}"

end Solidity.Examples.Tactics.PushSuffixGuards
