import Solidity.Lowering.V07.AssignmentSubtraction

/-! Selected integer-local family over EXISTING locals/environments. Content
agreement does not imply identity: alias reflection is separate evidence. -/
namespace Solidity.Lowering.V07

theorem source_idx_injective {Γ : Source.RCtx} {τ : Source.STy} :
    (i j : Source.Idx Γ τ) → i.toNat = j.toNat → i = j
  | .here,.here,_ => rfl
  | .there i,.there j,h => congrArg Source.Idx.there (source_idx_injective i j (Nat.succ.inj h))

theorem source_locals_get_set_ne {D : Source.Layout} :
    {Γ : Source.RCtx} → {τ σ : Source.STy} →
    (locals : Source.Locals D Γ) → (i : Source.Idx Γ τ) → (j : Source.Idx Γ σ) →
    (v : Source.Val D τ) → i.toNat ≠ j.toNat → (locals.set i v).get j = locals.get j
  | _,_,_,.cons _ _,.here,.here,_,h => absurd rfl h
  | _,_,_,.cons _ _,.here,.there _,_,_ => rfl
  | _,_,_,.cons _ _,.there _,.here,_,_ => rfl
  | _,_,_,.cons _ rest,.there i,.there j,v,h =>
    source_locals_get_set_ne rest i j v (fun e => h (congrArg (·+1) e))

structure IntegerLocalFamily {D : Source.Layout} {srcΓ : Source.RCtx}
    {C : Contract} {H : HTy} {Γ : Ctx} {ι : Type}
    (t : Source.IntTy) (si : ι → Source.Idx srcΓ (.int t))
    (ti : ι → Idx Γ (.val (integerPrim t)))
    (source : Source.Locals D srcΓ) (target : TEnv C H Γ) : Prop where
  values : ∀ k, IntValueRel t (source.get (si k)) (TEnv.get (ti k) target)
  aliases : ∀ k l, (si k).toNat = (si l).toNat ↔ (ti k).toNat = (ti l).toNat

namespace IntegerLocalFamily
variable {D : Source.Layout} {srcΓ : Source.RCtx} {C : Contract} {H : HTy} {Γ : Ctx}
  {ι : Type} {t : Source.IntTy} {si : ι → Source.Idx srcΓ (.int t)}
  {ti : ι → Idx Γ (.val (integerPrim t))} {source : Source.Locals D srcΓ} {target : TEnv C H Γ}

theorem write (h : IntegerLocalFamily t si ti source target) (written rhs : ι) :
    IntegerLocalFamily t si ti (source.set (si written) (source.get (si rhs)))
      (TEnv.set (ti written) (TEnv.get (ti rhs) target) target) := by
  refine ⟨?_,h.aliases⟩
  intro k
  by_cases same : (si written).toNat = (si k).toNat
  · have hs := source_idx_injective _ _ same
    have ht := Idx.toNat_inj _ _ ((h.aliases written k).mp same)
    rw [←hs,←ht,source_locals_get_set,TEnv.get_set]
    exact h.values rhs
  · have ht : (ti written).toNat ≠ (ti k).toNat := fun e => same ((h.aliases written k).mpr e)
    rw [source_locals_get_set_ne source _ _ _ same,TEnv.get_set_ne _ _ _ target ht]
    exact h.values k

theorem reindex (h : IntegerLocalFamily t si ti source target) {κ : Type} (f : κ → ι) :
    IntegerLocalFamily t (fun k => si (f k)) (fun k => ti (f k)) source target :=
  ⟨fun k => h.values (f k),fun k l => h.aliases (f k) (f l)⟩

theorem under_binders (h : IntegerLocalFamily t si ti source target)
    {σ : Source.STy} {u : LTy} (sv : Source.Val D σ) (tv : u.TDenote C H) :
    IntegerLocalFamily t (fun k => .there (si k)) (fun k => .there (ti k))
      (.cons sv source) (tv,target) := by
  refine ⟨h.values,?_⟩
  intro k l
  change (si k).toNat+1 = (si l).toNat+1 ↔ (ti k).toNat+1 = (ti l).toNat+1
  exact ⟨fun e => congrArg (·+1) ((h.aliases k l).mp (Nat.succ.inj e)),
    fun e => congrArg (·+1) ((h.aliases k l).mpr (Nat.succ.inj e))⟩

end IntegerLocalFamily
/-- The family postrelation is DERIVED from initial correspondence; selected
Source/target disjointness is not supplied as an unrelated global hypothesis. -/
theorem assignment_family_transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} {ι : Type} (t : Source.IntTy)
    (si : ι → Source.Idx srcΓ (.int t)) (ti : ι → Idx Γ (.val (integerPrim t)))
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (family : IntegerLocalFamily t si ti source.1 target.env) (written rhs : ι) :
    (Source.evalE G F (fuel+2) (.assign (.local (si written)) (.local (si rhs)))).run source =
      (.ok (.val (source.1.get (si rhs))),
        (source.1.set (si written) (source.1.get (si rhs)),source.2)) ∧
    (assignLocalOperand (ti written) (ti rhs)).run target =
      .ok (⟨target.setLocal (ti written) (TEnv.get (ti rhs) target.env),List.prefix_refl _⟩,
        .prim (TEnv.get (ti rhs) target.env)) ∧
    IntegerLocalFamily t si ti (source.1.set (si written) (source.1.get (si rhs)))
      (target.setLocal (ti written) (TEnv.get (ti rhs) target.env)).env :=
  ⟨source_assign_local_run G F fuel source _ _ _ rfl,
    assign_local_operand_run target _ _ _ rfl,family.write written rhs⟩

end Solidity.Lowering.V07
