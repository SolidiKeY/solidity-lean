import Solidity.Source.Agreement.PrimitiveSlot

/-! Actual primitive assignment from the head local to a deeper same-typed
slot. Both reads use the original environment before the write. This is a
fixed resolved pair, not general Source or heap simulation. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Source evaluates the real old head before updating the deeper slot. -/
theorem primitive_head_assign_source (p : PrimTy) (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (p::pre ++ p::tail))) (st : St E) :
    (execS G F (n+3) nps ph
      (.expr (.assign (.local (sourcePrimitiveSlot p tail (p::pre))) (.local .here)) :
        RStmt E R M k (sourceContext (p::pre ++ p::tail))
          (sourceContext (p::pre ++ p::tail))) ls).run (.nil, st) =
      (.ok (.normal (ls.set (sourcePrimitiveSlot p tail (p::pre)) (ls.get .here))),
        (.nil, st)) := by
  cases p <;> rfl

/-- Model assignment reads the old head and changes exactly the deeper slot. -/
theorem primitive_head_assign_model (p : PrimTy) (pre tail : List PrimTy)
    (model : Solidity.State C (modelContext (p::pre ++ p::tail))) :
    Solidity.Stmt.runC (.assignLocal (modelPrimitiveSlot p tail (p::pre))
      (.simple (.local .here))) model =
      .ok ⟨model.setLocal (modelPrimitiveSlot p tail (p::pre)) model.env.1,
        List.prefix_refl _⟩ := by
  rfl

/-- The fixed assignment pair has a concrete normal-result producer. Its
operand relation follows from the actual old head, not a desired value. -/
theorem primitive_head_assign_step (p : PrimTy) (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalStmtObligation (C := C) (R := R) (M := M) (k := k)
      (p::pre ++ p::tail) (p::pre ++ p::tail) G F nps ph
      (.expr (.assign (.local (sourcePrimitiveSlot p tail (p::pre))) (.local .here)))
      (.assignLocal (modelPrimitiveSlot p tail (p::pre)) (.simple (.local .here))) := by
  intro ls st model related fuel ls' journal ran
  cases fuel with
  | zero => cases ran
  | succ n => cases n with
    | zero => cases ran
    | succ n => cases n with
      | zero => cases ran
      | succ n =>
        rw [primitive_head_assign_source] at ran
        have he : ls.set (sourcePrimitiveSlot p tail (p::pre)) (ls.get .here) = ls' :=
          Source.Out.normal.inj (Except.ok.inj (Prod.mk.inj ran).1)
        subst ls'
        have head : PrimitiveRel E.layout p (ls.get .here) model.env.1 :=
          primitive_slot_get_related E.layout C model.H p [] (pre ++ p::tail) ls model.env related
        exact ⟨⟨model.setLocal (modelPrimitiveSlot p tail (p::pre)) model.env.1,
          List.prefix_refl _⟩, primitive_head_assign_model p pre tail model,
          primitive_slot_set_related E.layout C model.H p (p::pre) tail ls model.env
            (ls.get .here) model.env.1 head related⟩

/-- The initial relation and actual Source run are constructed internally. -/
theorem primitive_head_assign_client (R : List STy) (M : Bool) (k : SCtx)
    (p : PrimTy) (pre tail : List PrimTy) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext (p::pre ++ p::tail))) (st : St E) :
    StateLocalsRel E C (p::pre ++ p::tail)
      ((localsOfModel E.layout C model.H (p::pre ++ p::tail) model.env).set
        (sourcePrimitiveSlot p tail (p::pre))
        ((localsOfModel E.layout C model.H (p::pre ++ p::tail) model.env).get .here))
      (model.setLocal (modelPrimitiveSlot p tail (p::pre)) model.env.1) := by
  obtain ⟨out, ran, related⟩ :=
    (primitive_head_assign_step (R := R) (M := M) (k := k) p pre tail G F nps ph)
      _ st model (stateLocals_total E C _ model) 3 _ (.nil, st)
      (primitive_head_assign_source (R := R) (M := M) (k := k) p pre tail G F 0 nps ph _ st)
  have he : out = ⟨model.setLocal (modelPrimitiveSlot p tail (p::pre)) model.env.1,
      List.prefix_refl _⟩ :=
    (Except.ok.inj ((primitive_head_assign_model p pre tail model).symm.trans ran)).symm
  subst out
  exact related

/-- Location evaluation still consumes its real Source horizon. -/
theorem primitive_head_assign_two_timeout (p : PrimTy) (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (p::pre ++ p::tail))) (st : St E) :
    (execS G F 2 nps ph
      (.expr (.assign (.local (sourcePrimitiveSlot p tail (p::pre))) (.local .here)) :
        RStmt E R M k (sourceContext (p::pre ++ p::tail))
          (sourceContext (p::pre ++ p::tail))) ls).run (.nil, st) =
      (.error .timeout, (.nil, st)) := by
  rfl

end Solidity.Source.Agreement
