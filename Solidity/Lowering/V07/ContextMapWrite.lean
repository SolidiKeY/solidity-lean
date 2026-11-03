import Solidity.Lowering.V07.ContextMap

namespace Solidity.Lowering.V07

theorem source_idx_type_eq : {Γ : Source.RCtx} → {τ σ : Source.STy} →
    (i : Source.Idx Γ τ) → (j : Source.Idx Γ σ) → i.toNat = j.toNat → τ = σ
  | _,_,_,.here,.here,_ => rfl
  | _,_,_,.here,.there _,h => by change 0 = _+1 at h; omega
  | _,_,_,.there _,.here,h => by change _+1 = 0 at h; omega
  | _,_,_,.there i,.there j,h => source_idx_type_eq i j (Nat.succ.inj h)

namespace ContextMap
variable {D : Source.Layout} {srcΓ : Source.RCtx} {C : Contract} {H : HTy} {Γ : Ctx}
  (m : ContextMap srcΓ Γ)
  (R : (τ : Source.STy) → (u : LTy) → Source.Val D τ → u.TDenote C H → Prop)
  (source : Source.Locals D srcΓ) (target : TEnv C H Γ)

theorem value_at (aligned : m.Related R source target) {τ : Source.STy} {u : LTy}
    (i : Source.Idx srcΓ τ) (j : Idx Γ u) (mapped : m.slot i = ⟨u,j⟩) :
    R τ u (source.get i) (TEnv.get j target) := by
  have value := aligned i
  change R τ (m.slot i).1 (source.get i) (TEnv.get (m.slot i).2 target) at value
  exact Eq.mp (congrArg (fun slot : (u : LTy) × Idx Γ u =>
    R τ slot.1 (source.get i) (TEnv.get slot.2 target)) mapped) value

/-- A typed local write preserves ALL mapped bindings, including different
Source widths and mixed local kinds. Frame disjointness comes from the one
heterogeneous position certificate, never from content agreement. R is only
a relation on initial/new values; no compiler/run result is assumed. -/
theorem related_write (aligned : m.Related R source target) {τ : Source.STy} {u : LTy}
    (i : Source.Idx srcΓ τ) (j : Idx Γ u) (mapped : m.slot i = ⟨u,j⟩)
    (sv : Source.Val D τ) (tv : u.TDenote C H) (new : R τ u sv tv) :
    m.Related R (source.set i sv) (TEnv.set j tv target) := by
  intro σ k
  by_cases same : i.toNat = k.toNat
  · have typeEq := source_idx_type_eq i k same
    cases typeEq
    have indexEq := source_idx_injective i k same
    cases indexEq
    change R τ (m.slot i).1 ((source.set i sv).get i)
      (TEnv.get (m.slot i).2 (TEnv.set j tv target))
    rw [source_locals_get_set,mapped,TEnv.get_set]
    exact new
  · have targetDifferent : j.toNat ≠ (m.slot k).2.toNat := by
      intro eq
      apply same
      apply (m.positions i k).mpr
      rw [mapped]
      exact eq
    change R σ (m.slot k).1 ((source.set i sv).get k)
      (TEnv.get (m.slot k).2 (TEnv.set j tv target))
    rw [source_locals_get_set_ne source i k sv same,
      TEnv.get_set_ne j (m.slot k).2 tv target targetDifferent]
    exact aligned k

theorem related_assign (aligned : m.Related R source target) {τ : Source.STy} {u : LTy}
    (i a : Source.Idx srcΓ τ) (j b : Idx Γ u)
    (writeMap : m.slot i = ⟨u,j⟩) (readMap : m.slot a = ⟨u,b⟩) :
    m.Related R (source.set i (source.get a)) (TEnv.set j (TEnv.get b target) target) :=
  related_write m R source target aligned i j writeMap _ _
    (value_at m R source target aligned a b readMap)

end ContextMap
end Solidity.Lowering.V07
