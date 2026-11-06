import Solidity.Source.Agreement.PrimitiveSlotAssign
import Solidity.Source.Agreement.PrimitiveSlotReverse
import Solidity.Source.Agreement.NormalComposition

/-! Ordered bidirectional primitive copies. The second read is from the actual
first poststate, so the sequence does not restore the overwritten old target.
This is concrete normal-local composition, not heap aliasing or a swap. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Actual Source sequence reads the second operand after the first write. -/
theorem primitive_copy_sequence_source (p : PrimTy) (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (p::pre ++ p::tail))) (st : St E) :
    let mid := ls.set (sourcePrimitiveSlot p tail (p::pre)) (ls.get .here)
    (execItems G F (n+5) nps ph
      (.stmt (.expr (.assign (.local (sourcePrimitiveSlot p tail (p::pre))) (.local .here)))
        (.stmt (.expr (.assign (.local .here) (.local (sourcePrimitiveSlot p tail (p::pre)))))
          .nil) : RItems E R M k (sourceContext (p::pre ++ p::tail))
            (sourceContext (p::pre ++ p::tail))) ls).run (.nil, st) =
      (.ok (.normal (mid.set .here (mid.get (sourcePrimitiveSlot p tail (p::pre))))),
        (.nil, st)) := by
  cases p <;> rfl

/-- Model execution likewise obtains its second operand from the actual midstate. -/
theorem primitive_copy_sequence_model (p : PrimTy) (pre tail : List PrimTy)
    (model : Solidity.State C (modelContext (p::pre ++ p::tail))) :
    let mid := model.setLocal (modelPrimitiveSlot p tail (p::pre)) model.env.1
    Prog.runC (.cons (.assignLocal (modelPrimitiveSlot p tail (p::pre)) (.simple (.local .here)))
      (.cons (.assignLocal .here (.simple (.local (modelPrimitiveSlot p tail (p::pre))))) .nil))
        model = .ok ⟨mid.setLocal .here (TEnv.get (modelPrimitiveSlot p tail (p::pre)) mid.env),
          List.prefix_refl _⟩ := by
  rfl

/-- Both concrete per-statement producers are instantiated; no intermediate
state, successful step or producer field is required from the caller. -/
theorem primitive_copy_sequence_agree (p : PrimTy) (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalLocalsObligation (C := C) (R := R) (M := M) (k := k)
      (p::pre ++ p::tail) (p::pre ++ p::tail) G F nps ph
      (.stmt (.expr (.assign (.local (sourcePrimitiveSlot p tail (p::pre))) (.local .here)))
        (.stmt (.expr (.assign (.local .here) (.local (sourcePrimitiveSlot p tail (p::pre))))) .nil))
      (.cons (.assignLocal (modelPrimitiveSlot p tail (p::pre)) (.simple (.local .here)))
        (.cons (.assignLocal .here (.simple (.local (modelPrimitiveSlot p tail (p::pre))))) .nil)) := by
  exact normal_two G F nps ph _ _ _ _
    (primitive_head_assign_step p pre tail G F nps ph)
    (primitive_reverse_step p pre tail G F nps ph)

/-- The initial relation and both actual sequence computations are consumed
internally. The computed midstate supplies the second read on each side. -/
theorem primitive_copy_sequence_client (R : List STy) (M : Bool) (k : SCtx)
    (p : PrimTy) (pre tail : List PrimTy) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext (p::pre ++ p::tail))) (st : St E) :
    let ls := localsOfModel E.layout C model.H (p::pre ++ p::tail) model.env
    let sourceMid := ls.set (sourcePrimitiveSlot p tail (p::pre)) (ls.get .here)
    let modelMid := model.setLocal (modelPrimitiveSlot p tail (p::pre)) model.env.1
    StateLocalsRel E C (p::pre ++ p::tail)
      (sourceMid.set .here (sourceMid.get (sourcePrimitiveSlot p tail (p::pre))))
      (modelMid.setLocal .here (TEnv.get (modelPrimitiveSlot p tail (p::pre)) modelMid.env)) := by
  obtain ⟨out, ran, related⟩ :=
    (primitive_copy_sequence_agree (R := R) (M := M) (k := k) p pre tail G F nps ph)
      _ st model (stateLocals_total E C _ model) 5 _ (.nil, st)
      (primitive_copy_sequence_source (R := R) (M := M) (k := k) p pre tail G F 0 nps ph _ st)
  have he : out = ⟨(model.setLocal (modelPrimitiveSlot p tail (p::pre)) model.env.1).setLocal
      .here (TEnv.get (modelPrimitiveSlot p tail (p::pre))
        (model.setLocal (modelPrimitiveSlot p tail (p::pre)) model.env.1).env), List.prefix_refl _⟩ :=
    (Except.ok.inj ((primitive_copy_sequence_model p pre tail model).symm.trans ran)).symm
  subst out
  exact related

/-- The second location evaluation retains its real horizon-four timeout. -/
theorem primitive_copy_sequence_four_timeout (p : PrimTy) (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (p::pre ++ p::tail))) (st : St E) :
    (execItems G F 4 nps ph
      (.stmt (.expr (.assign (.local (sourcePrimitiveSlot p tail (p::pre))) (.local .here)))
        (.stmt (.expr (.assign (.local .here) (.local (sourcePrimitiveSlot p tail (p::pre)))))
          .nil) : RItems E R M k (sourceContext (p::pre ++ p::tail))
            (sourceContext (p::pre ++ p::tail))) ls).run (.nil, st) =
      (.error .timeout, (.nil, st)) := by
  rfl

/-- Actual inward-first Source sequence reads the new head for the second copy. -/
theorem primitive_copy_inward_source (p : PrimTy) (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (p::pre ++ p::tail))) (st : St E) :
    let mid := ls.set .here (ls.get (sourcePrimitiveSlot p tail (p::pre)))
    (execItems G F (n+5) nps ph
      (.stmt (.expr (.assign (.local .here) (.local (sourcePrimitiveSlot p tail (p::pre)))))
        (.stmt (.expr (.assign (.local (sourcePrimitiveSlot p tail (p::pre))) (.local .here)))
          .nil) : RItems E R M k (sourceContext (p::pre ++ p::tail))
            (sourceContext (p::pre ++ p::tail))) ls).run (.nil, st) =
      (.ok (.normal (mid.set (sourcePrimitiveSlot p tail (p::pre)) (mid.get .here))),
        (.nil, st)) := by
  cases p <;> rfl

/-- Actual model inward-first evaluation retains its computed midstate. -/
theorem primitive_copy_inward_model (p : PrimTy) (pre tail : List PrimTy)
    (model : Solidity.State C (modelContext (p::pre ++ p::tail))) :
    let mid := model.setLocal .here (TEnv.get (modelPrimitiveSlot p tail (p::pre)) model.env)
    Prog.runC (.cons (.assignLocal .here (.simple (.local (modelPrimitiveSlot p tail (p::pre)))))
      (.cons (.assignLocal (modelPrimitiveSlot p tail (p::pre)) (.simple (.local .here))) .nil))
        model = .ok ⟨mid.setLocal (modelPrimitiveSlot p tail (p::pre)) mid.env.1,
          List.prefix_refl _⟩ := by
  rfl

/-- Reversing the concrete producer order proves the other resolved pair. -/
theorem primitive_copy_inward_agree (p : PrimTy) (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalLocalsObligation (C := C) (R := R) (M := M) (k := k)
      (p::pre ++ p::tail) (p::pre ++ p::tail) G F nps ph
      (.stmt (.expr (.assign (.local .here) (.local (sourcePrimitiveSlot p tail (p::pre)))))
        (.stmt (.expr (.assign (.local (sourcePrimitiveSlot p tail (p::pre))) (.local .here))) .nil))
      (.cons (.assignLocal .here (.simple (.local (modelPrimitiveSlot p tail (p::pre)))))
        (.cons (.assignLocal (modelPrimitiveSlot p tail (p::pre)) (.simple (.local .here))) .nil)) := by
  exact normal_two G F nps ph _ _ _ _
    (primitive_reverse_step p pre tail G F nps ph)
    (primitive_head_assign_step p pre tail G F nps ph)

/-- The inward-first client derives both runs and the initial relation internally. -/
theorem primitive_copy_inward_client (R : List STy) (M : Bool) (k : SCtx)
    (p : PrimTy) (pre tail : List PrimTy) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext (p::pre ++ p::tail))) (st : St E) :
    let ls := localsOfModel E.layout C model.H (p::pre ++ p::tail) model.env
    let sourceMid := ls.set .here (ls.get (sourcePrimitiveSlot p tail (p::pre)))
    let modelMid := model.setLocal .here (TEnv.get (modelPrimitiveSlot p tail (p::pre)) model.env)
    StateLocalsRel E C (p::pre ++ p::tail)
      (sourceMid.set (sourcePrimitiveSlot p tail (p::pre)) (sourceMid.get .here))
      (modelMid.setLocal (modelPrimitiveSlot p tail (p::pre)) modelMid.env.1) := by
  obtain ⟨out, ran, related⟩ :=
    (primitive_copy_inward_agree (R := R) (M := M) (k := k) p pre tail G F nps ph)
      _ st model (stateLocals_total E C _ model) 5 _ (.nil, st)
      (primitive_copy_inward_source (R := R) (M := M) (k := k) p pre tail G F 0 nps ph _ st)
  have he : out = ⟨(model.setLocal .here
      (TEnv.get (modelPrimitiveSlot p tail (p::pre)) model.env)).setLocal
      (modelPrimitiveSlot p tail (p::pre))
      (model.setLocal .here (TEnv.get (modelPrimitiveSlot p tail (p::pre)) model.env)).env.1,
      List.prefix_refl _⟩ :=
    (Except.ok.inj ((primitive_copy_inward_model p pre tail model).symm.trans ran)).symm
  subst out
  exact related

/-- Inward-first also retains its actual horizon-four Source error. -/
theorem primitive_copy_inward_four_timeout (p : PrimTy) (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (p::pre ++ p::tail))) (st : St E) :
    (execItems G F 4 nps ph
      (.stmt (.expr (.assign (.local .here) (.local (sourcePrimitiveSlot p tail (p::pre)))))
        (.stmt (.expr (.assign (.local (sourcePrimitiveSlot p tail (p::pre))) (.local .here)))
          .nil) : RItems E R M k (sourceContext (p::pre ++ p::tail))
            (sourceContext (p::pre ++ p::tail))) ls).run (.nil, st) =
      (.error .timeout, (.nil, st)) := by
  rfl

end Solidity.Source.Agreement
