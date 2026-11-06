import Solidity.Source.Agreement.PrimitiveSlot

/-! Actual copy from a deeper primitive slot into the head. The RHS read is
from the old locals; the source slot and all neighbors survive the write.
Only a fixed resolved primitive-local pair is associated here. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Actual Source assignment reads the deeper old slot before writing the head. -/
theorem primitive_reverse_source (p : PrimTy) (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (p::pre ++ p::tail))) (st : St E) :
    (execS G F (n+3) nps ph
      (.expr (.assign (.local .here) (.local (sourcePrimitiveSlot p tail (p::pre)))) :
        RStmt E R M k (sourceContext (p::pre ++ p::tail))
          (sourceContext (p::pre ++ p::tail))) ls).run (.nil, st) =
      (.ok (.normal (ls.set .here (ls.get (sourcePrimitiveSlot p tail (p::pre))))),
        (.nil, st)) := by
  cases p <;> rfl

/-- Actual model assignment reads the same physical source before writing. -/
theorem primitive_reverse_model (p : PrimTy) (pre tail : List PrimTy)
    (model : Solidity.State C (modelContext (p::pre ++ p::tail))) :
    Solidity.Stmt.runC (.assignLocal .here
      (.simple (.local (modelPrimitiveSlot p tail (p::pre))))) model =
      .ok ⟨model.setLocal .here (TEnv.get (modelPrimitiveSlot p tail (p::pre)) model.env),
        List.prefix_refl _⟩ := by
  rfl

/-- The operand relation is derived from the actual deeper getter. -/
theorem primitive_reverse_step (p : PrimTy) (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalStmtObligation (C := C) (R := R) (M := M) (k := k)
      (p::pre ++ p::tail) (p::pre ++ p::tail) G F nps ph
      (.expr (.assign (.local .here) (.local (sourcePrimitiveSlot p tail (p::pre)))))
      (.assignLocal .here (.simple (.local (modelPrimitiveSlot p tail (p::pre))))) := by
  intro ls st model related fuel ls' journal ran
  cases fuel with
  | zero => cases ran
  | succ n => cases n with
    | zero => cases ran
    | succ n => cases n with
      | zero => cases ran
      | succ n =>
        rw [primitive_reverse_source] at ran
        have he : ls.set .here (ls.get (sourcePrimitiveSlot p tail (p::pre))) = ls' :=
          Source.Out.normal.inj (Except.ok.inj (Prod.mk.inj ran).1)
        subst ls'
        have operand : PrimitiveRel E.layout p
            (ls.get (sourcePrimitiveSlot p tail (p::pre)))
            (TEnv.get (modelPrimitiveSlot p tail (p::pre)) model.env) :=
          primitive_slot_get_related E.layout C model.H p (p::pre) tail ls model.env related
        exact ⟨⟨model.setLocal .here (TEnv.get (modelPrimitiveSlot p tail (p::pre)) model.env),
          List.prefix_refl _⟩, primitive_reverse_model p pre tail model,
          primitive_slot_set_related E.layout C model.H p [] (pre ++ p::tail) ls model.env
            _ _ operand related⟩

/-- Initial locals and actual Source execution are produced internally. -/
theorem primitive_reverse_client (R : List STy) (M : Bool) (k : SCtx)
    (p : PrimTy) (pre tail : List PrimTy) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext (p::pre ++ p::tail))) (st : St E) :
    StateLocalsRel E C (p::pre ++ p::tail)
      ((localsOfModel E.layout C model.H (p::pre ++ p::tail) model.env).set .here
        ((localsOfModel E.layout C model.H (p::pre ++ p::tail) model.env).get
          (sourcePrimitiveSlot p tail (p::pre))))
      (model.setLocal .here (TEnv.get (modelPrimitiveSlot p tail (p::pre)) model.env)) := by
  obtain ⟨out, ran, related⟩ :=
    (primitive_reverse_step (R := R) (M := M) (k := k) p pre tail G F nps ph)
      _ st model (stateLocals_total E C _ model) 3 _ (.nil, st)
      (primitive_reverse_source (R := R) (M := M) (k := k) p pre tail G F 0 nps ph _ st)
  have he : out = ⟨model.setLocal .here
      (TEnv.get (modelPrimitiveSlot p tail (p::pre)) model.env), List.prefix_refl _⟩ :=
    (Except.ok.inj ((primitive_reverse_model p pre tail model).symm.trans ran)).symm
  subst out
  exact related

/-- Location evaluation retains its actual insufficient-horizon error. -/
theorem primitive_reverse_two_timeout (p : PrimTy) (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (p::pre ++ p::tail))) (st : St E) :
    (execS G F 2 nps ph
      (.expr (.assign (.local .here) (.local (sourcePrimitiveSlot p tail (p::pre)))) :
        RStmt E R M k (sourceContext (p::pre ++ p::tail))
          (sourceContext (p::pre ++ p::tail))) ls).run (.nil, st) =
      (.error .timeout, (.nil, st)) := by
  rfl

end Solidity.Source.Agreement
