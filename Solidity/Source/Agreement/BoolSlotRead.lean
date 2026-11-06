import Solidity.Source.Agreement.BoolSlotAssign

/-! Actual primitive local-read initialization through the existing paired indices.
This adds no Source interpretation or full-state correspondence judgment. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Actual existing local reads retain primitive value correspondence. -/
theorem bool_slot_get_related (D : Layout) (C : Contract) (H : HTy)
    (pre tail : List PrimTy)
    (ls : Locals D (sourceContext (pre ++ .bool::tail)))
    (ws : TEnv C H (modelContext (pre ++ .bool::tail)))
    (related : LocalsRel D C H (pre ++ .bool::tail) ls ws) :
    PrimitiveRel D .bool (ls.get (sourceBoolSlot tail pre))
      (TEnv.get (modelBoolSlot tail pre) ws) := by
  induction pre with
  | nil =>
    obtain ⟨rest, he, hr⟩ := bool_locals_shape D C H tail ls ws.1 ws.2 related
    subst ls
    exact PrimitiveRel.bool ws.1
  | cons p ps ih =>
    cases related with
    | cons head rest => exact ih _ _ rest

/-- Source initialization copies the actual selected value, retaining its old locals. -/
theorem bool_read_init_source (pre tail : List PrimTy) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E) :
    (execS G F (n+2) nps ph
      (.declInit (.local (sourceBoolSlot tail pre)) rfl : RStmt E R M k
        (sourceContext (pre ++ .bool::tail))
        (sourceContext (.bool::pre ++ .bool::tail))) ls).run (.nil, st) =
      (.ok (.normal (.cons (ls.get (sourceBoolSlot tail pre)) ls)), (.nil, st)) := by
  rfl

/-- Model initialization reads the actual old environment before pushing its copy. -/
theorem bool_read_init_model (pre tail : List PrimTy) (name : Var)
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) :
    Solidity.Stmt.runC (.declLocal .bool name
      (some (.simple (.local (modelBoolSlot tail pre))))) model =
      .ok ⟨model.push (TEnv.get (modelBoolSlot tail pre) model.env), List.prefix_refl _⟩ := by
  rfl

/-- Concrete local-read producer; the read's value is derived rather than supplied. -/
theorem bool_read_init_step (pre tail : List PrimTy) (name : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalStmtObligation (C := C) (R := R) (M := M) (k := k)
      (pre ++ .bool::tail) (.bool::pre ++ .bool::tail) G F nps ph
      (.declInit (.local (sourceBoolSlot tail pre)) rfl)
      (.declLocal .bool name (some (.simple (.local (modelBoolSlot tail pre))))) := by
  intro ls st model related fuel ls' journal ran
  cases fuel with
  | zero => cases ran
  | succ n =>
    cases n with
    | zero => cases ran
    | succ n =>
      rw [bool_read_init_source] at ran
      have he : (.cons (ls.get (sourceBoolSlot tail pre)) ls) = ls' :=
        Source.Out.normal.inj (Except.ok.inj (Prod.mk.inj ran).1)
      subst ls'
      exact ⟨⟨model.push (TEnv.get (modelBoolSlot tail pre) model.env), List.prefix_refl _⟩,
        bool_read_init_model pre tail name model,
        LocalsRel.cons (bool_slot_get_related E.layout C model.H pre tail ls model.env related) related⟩

/-- The actual copied initializer is composed with a later write to its original
slot, shifted under the new local; no desired read value or step premise is used. -/
theorem bool_read_then_assign_agree (pre tail : List PrimTy) (b : Bool) (name : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalLocalsObligation (C := C) (R := R) (M := M) (k := k)
      (pre ++ .bool::tail) (.bool::pre ++ .bool::tail) G F nps ph
      (.stmt (.declInit (.local (sourceBoolSlot tail pre)) rfl)
        (.stmt (.expr (.assign (.local (sourceBoolSlot tail (.bool::pre))) (.bool b))) .nil))
      (.cons (.declLocal .bool name (some (.simple (.local (modelBoolSlot tail pre)))))
        (.cons (.assignLocal (modelBoolSlot tail (.bool::pre)) (.simple (.bool b))) .nil)) := by
  exact normal_two G F nps ph _ _ _ _
    (bool_read_init_step pre tail name G F nps ph)
    (bool_slot_assign_step (.bool::pre) tail b G F nps ph)

end Solidity.Source.Agreement
