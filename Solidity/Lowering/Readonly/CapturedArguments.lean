import Solidity.Lowering.Readonly.PrimitiveLocals
import Solidity.Semantics.Run

/-! Lower ALREADY captured primitive values to the actual intrinsic Args API.
The supplied binders keep their exact names/types/order; no source expression is
reevaluated. Connecting those binders to a selected compiled function remains
P1's obligation. ABI byte transport remains P3's obligation. -/
namespace Solidity.Lowering.Readonly.CapturedArguments
variable {C : Contract} {Ξ ρ : Ctx} {H : HTy}

def literal (p : PrimTy) (value : p.Denote) : Solidity.Val C Ξ p := by
  cases p with
  | uint => exact .simple (.lit value.val value.property)
  | int => exact .simple (.lit value.val value.property)
  | bool => exact .simple (.bool value)

theorem literal_eval (state : State C Ξ) (p : PrimTy) (value : p.Denote) :
    (literal p value).evalT state = .ok value := by cases p <;> rfl

def arguments : {ρ : Ctx} → (binders : Binders ρ) → TEnv C H ρ → Args C Ξ ρ
  | _, binders =>
    Binders.casesOn (motive := fun ρ _ => TEnv C H ρ → Args C Ξ ρ) binders
      (fun _ => .nil)
      (fun rest p name values => .snoc (arguments rest values.2) p name (literal p values.1))
termination_by structural _ρ binders => binders

/-- Only primitive scalar environments are transported; no heap object or
reference is copied or equated. -/
def reheap {H' : HTy} : {ρ : Ctx} → (binders : Binders ρ) → TEnv C H ρ → TEnv C H' ρ
  | _, binders =>
    Binders.casesOn (motive := fun ρ _ => TEnv C H ρ → TEnv C H' ρ) binders
      (fun _ => ())
      (fun rest _ _ values => (values.1, reheap rest values.2))
termination_by structural _ρ binders => binders

theorem reheap_id (binders : Binders ρ) (values : TEnv C H ρ) :
    reheap (H' := H) binders values = values := by
  induction binders with
  | nil => cases values; rfl
  | snoc rest p name ih =>
    rcases values with ⟨value, values⟩
    change (value, reheap rest values) = (value, values)
    rw [ih]

theorem eval_any_heap (state : State C Ξ) (binders : Binders ρ) (values : TEnv C H ρ) :
    (arguments binders values).evalT state = .ok (reheap (H' := state.H) binders values) := by
  induction binders with
  | nil => cases values; rfl
  | snoc rest p name ih =>
    rcases values with ⟨value, values⟩
    change (do let tail ← (arguments rest values).evalT state
               let head ← (literal p value).evalT state
               pure (head, tail)) = .ok (value, reheap rest values)
    rw [ih, literal_eval]
    rfl

theorem eval (state : State C Ξ) (binders : Binders ρ) (values : TEnv C state.H ρ) :
    (arguments binders values).evalT state = .ok values := by
  rw [eval_any_heap, reheap_id]

theorem names (binders : Binders ρ) (values : TEnv C H ρ) :
    (arguments (Ξ := Ξ) binders values).names = binders.names := by
  induction binders with
  | nil => rfl
  | snoc rest p name ih =>
    change name :: (arguments rest values.2).names = name :: rest.names
    rw [ih]

/-- Evaluation of captured primitive arguments is independent of subsequent
caller-state mutations; it is not a frozen expression oracle. -/
theorem stable (first second : State C Ξ) (binders : Binders ρ) (values : TEnv C H ρ) :
    (arguments binders values).evalT first = .ok (reheap (H' := first.H) binders values) ∧
    (arguments binders values).evalT second = .ok (reheap (H' := second.H) binders values) :=
  ⟨eval_any_heap first binders values, eval_any_heap second binders values⟩

end Solidity.Lowering.Readonly.CapturedArguments
