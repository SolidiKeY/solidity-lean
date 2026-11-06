import Solidity.Source.Agreement.BoolSlot

/-! Arbitrary-position boolean assignment uses actual existing local operations;
only explicit resolved Source/model pairs are related. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- The actual Source write does not depend on the selected local's depth. -/
theorem bool_slot_assign_source (pre tail : List PrimTy) (b : Bool)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E) :
    (execS G F (n+3) nps ph
      (.expr (.assign (.local (sourceBoolSlot tail pre)) (.bool b)) :
        RStmt E R M k (sourceContext (pre ++ .bool::tail))
          (sourceContext (pre ++ .bool::tail))) ls).run (.nil, st) =
      (.ok (.normal (ls.set (sourceBoolSlot tail pre) (.bool b))), (.nil, st)) := by
  rfl

/-- Actual model evaluation changes precisely the selected existing local. -/
theorem bool_slot_assign_model (pre tail : List PrimTy) (b : Bool)
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) :
    Solidity.Stmt.runC (.assignLocal (modelBoolSlot tail pre) (.simple (.bool b))) model =
      .ok ⟨model.setLocal (modelBoolSlot tail pre) b, List.prefix_refl _⟩ := by
  rfl

/-- Concrete producer with no successful-run or desired-result premise. The
normal-only target still retains its actual Source execution antecedent. -/
theorem bool_slot_assign_step (pre tail : List PrimTy) (b : Bool)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalStmtObligation (C := C) (R := R) (M := M) (k := k)
      (pre ++ .bool::tail) (pre ++ .bool::tail) G F nps ph
      (.expr (.assign (.local (sourceBoolSlot tail pre)) (.bool b)))
      (.assignLocal (modelBoolSlot tail pre) (.simple (.bool b))) := by
  intro ls st model related fuel ls' journal ran
  cases fuel with
  | zero => cases ran
  | succ n =>
    cases n with
    | zero => cases ran
    | succ n =>
      cases n with
      | zero => cases ran
      | succ n =>
        rw [bool_slot_assign_source] at ran
        have he : (ls.set (sourceBoolSlot tail pre) (.bool b)) = ls' :=
          Source.Out.normal.inj (Except.ok.inj (Prod.mk.inj ran).1)
        subst ls'
        exact ⟨⟨model.setLocal (modelBoolSlot tail pre) b, List.prefix_refl _⟩,
          bool_slot_assign_model pre tail b model,
          bool_slot_set_related E.layout C model.H pre tail ls model.env b related⟩

/-- Total initial locals and the actual positive Source run instantiate the
producer internally; no reached local state or relation is required. -/
theorem bool_slot_assign_client (R : List STy) (M : Bool) (k : SCtx)
    (pre tail : List PrimTy) (b : Bool) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) (st : St E) :
    StateLocalsRel E C (pre ++ .bool::tail)
      ((localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env).set
        (sourceBoolSlot tail pre) (.bool b))
      (model.setLocal (modelBoolSlot tail pre) b) := by
  obtain ⟨out, ran, related⟩ :=
    (bool_slot_assign_step (R := R) (M := M) (k := k) pre tail b G F nps ph)
      _ st model (stateLocals_total E C _ model) 3 _ (.nil, st)
      (bool_slot_assign_source (R := R) (M := M) (k := k) pre tail b G F 0 nps ph _ st)
  have he : out = ⟨model.setLocal (modelBoolSlot tail pre) b, List.prefix_refl _⟩ :=
    (Except.ok.inj ((bool_slot_assign_model pre tail b model).symm.trans ran)).symm
  subst out
  exact related

/-- Even an arbitrary deep local still requires location evaluation fuel. -/
theorem bool_slot_assign_two_timeout (pre tail : List PrimTy) (b : Bool)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E) :
    (execS G F 2 nps ph
      (.expr (.assign (.local (sourceBoolSlot tail pre)) (.bool b)) :
        RStmt E R M k (sourceContext (pre ++ .bool::tail))
          (sourceContext (pre ++ .bool::tail))) ls).run (.nil, st) =
      (.error .timeout, (.nil, st)) := by
  rfl

end Solidity.Source.Agreement
