import Solidity.Calculus.Fml

/-!
# First-order formulas, and names by the recursor

`Fml.FO`, the first-order formulas a callback's invariant is
(`Calculus/CallbackSound.lean`), and the names of a scope's positions by the
recursor (`Idx.nameR`, `Thin.namesR`, Gate G0, condition 2), with the
originals as their compiled twins.
-/

namespace Solidity

variable {C : Contract}

/-- A first-order formula: no update, modality or binder but `∀`: a
callback's invariant (`Calculus/CallbackSound.lean`), read alike in every
typed state of one erasure. -/
def Fml.FO : {Γ : Ctx} → Fml C Γ → Bool
  | _, φ => Fml.casesOn (motive := fun _ _ => Bool) φ
    (tt := true) (eq := fun _ _ => true) (defined := fun _ => true) (not := fun φ => Fml.FO φ)
    (and := fun φ ψ => Fml.FO φ && Fml.FO ψ) (imp := fun φ ψ => Fml.FO φ && Fml.FO ψ)
    (upd := fun _ _ _ => false) (modal := fun _ _ _ _ => false) (havoc := fun _ => false)
    (all := fun _ _ φ => Fml.FO φ) (bind := fun _ _ _ _ => false) (anon := fun _ _ => false)
  termination_by structural _ φ => φ

/-- `Idx.name`, by the recursor: the head of the names after as many tails as
the position. -/
@[implemented_by Idx.name]
def Idx.nameR {Γ : Ctx} {t : LTy} (ns : List Var) (i : Idx Γ t) : Var :=
  Idx.rec (motive := fun _ _ _ => List Var → Var) (fun ns => ns.headD (.user "_"))
    (fun _ ih ns => ih ns.tail) i ns

theorem Idx.nameR_eq {Γ : Ctx} {t : LTy} (ns : List Var) (i : Idx Γ t) :
    i.nameR ns = i.name ns := by
  induction i generalizing ns with
  | here => cases ns <;> rfl
  | there i ih =>
    cases ns with
    | nil => exact (ih []).trans (by simp only [Idx.name, List.getD_nil])
    | cons n ns => exact (ih ns).trans (by simp only [Idx.name, Idx.toNat, List.getD_cons_succ])

/-- `Thin.names`, by the recursor. -/
@[implemented_by Thin.names]
def Thin.namesR {Γ Δ : Ctx} (h : Thin Γ Δ) : List Var → List Var :=
  Thin.rec (motive := fun _ _ _ => List Var → List Var) (fun ns => ns)
    (fun _ ih ns => List.casesOn (motive := fun _ => List Var) ns (ih []) (fun n ns => n :: ih ns))
    (fun _ ih ns => ih ns.tail) h

theorem Thin.namesR_eq {Γ Δ : Ctx} (h : Thin Γ Δ) (ns : List Var) :
    h.namesR ns = h.names ns := by
  induction h generalizing ns with
  | refl => rfl
  | keep h ih =>
    cases ns with
    | nil => exact (ih []).trans (by simp only [Thin.names])
    | cons n ns => exact (congrArg (n :: ·) (ih ns)).trans (by simp only [Thin.names])
  | drop h ih => exact (ih ns.tail).trans (by simp only [Thin.names])

end Solidity
