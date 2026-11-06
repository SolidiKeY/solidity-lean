import Solidity.Lowering.P9.ElaborationAdmission

/-! Reusable exact cuts through the real elaborator. These generalize the
single-body proof technique of `ElaboratedCalls` without introducing desired executions.
-/
namespace Solidity.Lowering.P9.InferenceCuts
open Source

theorem body_some (E : Env) (d : Decl) (f : Frame)
    (hf : d.frame? E = some f)
    (hi : (ItemsD.infer (f.ctx E d.scope) f.locals f.body).isSome = true)
    (hm : d.modInvs.invList = []) : (Source.elabBody E d).isSome = true := by
  have hmSome : (Source.elabMods E d f d.modInvs.invList).isSome = true := by
    rw [hm, Source.elabMods]
    rfl
  unfold Source.elabBody
  split
  next he => rw [he] at hf; cases hf
  next f' he =>
    have hff : f' = f := Option.some.inj (he.symm.trans hf)
    subst f'
    split
    next he => rw [he] at hi; cases hi
    next L' D he =>
      split
      next he => rw [he] at hmSome; cases hmSome
      next ms hms he => rfl


theorem base_some (E : Env) (c : String)
    (hi : (E.inheritOf c).inheritList = []) (hc : E.ctorDecl c = none) :
    (Source.elabBaseArgs E c).isSome = true := by
  have hh : (Source.elabInherit E c (E.inheritOf c).inheritList).isSome = true := by
    rw [hi, Source.elabInherit]
    rfl
  unfold Source.elabBaseArgs
  cases he : Source.elabInherit E c (E.inheritOf c).inheritList with
  | none => rw [he] at hh; cases hh
  | some value =>
    rcases value with ⟨xs, hxs⟩
    dsimp only [Bind.bind, Option.bind]
    split
    next he => rfl
    next d he => rw [he] at hc; cases hc

end Solidity.Lowering.P9.InferenceCuts
