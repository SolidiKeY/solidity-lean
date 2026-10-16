import Solidity.Calculus.NotationResolve

/-!
# Initialized reference inputs

Hidden reference binders include unset locals. Source function inputs and
actual call arguments are initialized: the diamond identity update below
accepts precisely references whose identities can be read, without copying
or allocating them. This is an input-domain guard, not a program taclet.
-/

namespace Solidity

variable {C : Contract}

private def refInputUpdate {Γ : Ctx} : (Δ : Ctx) →
    (∀ {t : LTy}, Idx Δ t → Idx Γ t) → Upd C Γ Γ
  | [], _ => .nil
  | t :: Δ, f =>
    let U := refInputUpdate Δ (fun i => f (.there i))
    match t with
    | .alias _ => U.snoc (.local (f .here) (.path (.pvP (f .here))))
    | .mem _ => U.snoc (.local (f .here) (.mref (.pvI (f .here))))
    | _ => U

def Fml.refInputs (C : Contract) (Γ : Ctx) : Fml C Γ :=
  .upd .diamond (refInputUpdate Γ (fun i => i)) .tt

/-- The same guard read by name after a specification's snapshots. -/
def NRead.refInputs (params : NCtx) : NRead C := fun Γ => do
  let mut U : Upd C Γ.ctx Γ.ctx := .nil
  for (x, t) in params.reverse do
    match t with
    | .alias R =>
      let i ← Γ.idx x (.alias R)
      U := U.snoc (.local i (.path (.pvP i)))
    | .mem R =>
      let i ← Γ.idx x (.mem R)
      U := U.snoc (.local i (.mref (.pvI i)))
    | _ => pure ()
  pure (.upd .diamond U .tt)

end Solidity
