import Solidity.Source.Agreement.PrimitiveSlotAssign
import Solidity.Source.Agreement.NormalComposition

/-! Saving the actual head and assigning it to a deeper local through the two
existing concrete primitive producers. Context growth shifts both old slots;
no value, intermediate locals or successful whole run are supplied. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Actual Source declaration followed by assignment from the new saved head. -/
theorem primitive_saved_assign_source (p : PrimTy) (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (p::pre ++ p::tail))) (st : St E) :
    (execItems G F (n+5) nps ph
      (.stmt (.declInit (.local .here) (primitive_source_implicit E p))
        (.stmt (.expr (.assign (.local (sourcePrimitiveSlot p tail (p::p::pre)))
          (.local .here))) .nil) : RItems E R M k
            (sourceContext (p::pre ++ p::tail)) (sourceContext (p::p::pre ++ p::tail)))
      ls).run (.nil, st) =
      (.ok (.normal ((Locals.cons (ls.get .here) ls).set
        (sourcePrimitiveSlot p tail (p::p::pre)) (ls.get .here))), (.nil, st)) := by
  cases p <;> rfl

/-- Actual model declaration and shifted assignment retain the old head value. -/
theorem primitive_saved_assign_model (p : PrimTy) (pre tail : List PrimTy) (name : Var)
    (model : Solidity.State C (modelContext (p::pre ++ p::tail))) :
    Prog.runC (.cons (.declLocal p name (some (.simple (.local .here))))
      (.cons (.assignLocal (modelPrimitiveSlot p tail (p::p::pre))
        (.simple (.local .here))) .nil)) model =
      .ok ⟨(model.push model.env.1).setLocal (modelPrimitiveSlot p tail (p::p::pre))
        model.env.1, List.prefix_refl _⟩ := by
  rfl

/-- Two concrete producer proofs discharge the normal whole-sequence contract.
No generic producer premise is exposed to the user of this resolved pair. -/
theorem primitive_saved_assign_agree (p : PrimTy) (pre tail : List PrimTy) (name : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalLocalsObligation (C := C) (R := R) (M := M) (k := k)
      (p::pre ++ p::tail) (p::p::pre ++ p::tail) G F nps ph
      (.stmt (.declInit (.local .here) (primitive_source_implicit E p))
        (.stmt (.expr (.assign (.local (sourcePrimitiveSlot p tail (p::p::pre)))
          (.local .here))) .nil))
      (.cons (.declLocal p name (some (.simple (.local .here))))
        (.cons (.assignLocal (modelPrimitiveSlot p tail (p::p::pre))
          (.simple (.local .here))) .nil)) := by
  exact normal_two G F nps ph _ _ _ _
    (primitive_read_init_step p [] (pre ++ p::tail) name G F nps ph)
    (primitive_head_assign_step p (p::pre) tail G F nps ph)

/-- Both actual runs and the initial relation are instantiated internally. -/
theorem primitive_saved_assign_client (R : List STy) (M : Bool) (k : SCtx)
    (p : PrimTy) (pre tail : List PrimTy) (name : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext (p::pre ++ p::tail))) (st : St E) :
    StateLocalsRel E C (p::p::pre ++ p::tail)
      ((Locals.cons ((localsOfModel E.layout C model.H (p::pre ++ p::tail) model.env).get .here)
        (localsOfModel E.layout C model.H (p::pre ++ p::tail) model.env)).set
          (sourcePrimitiveSlot p tail (p::p::pre))
          ((localsOfModel E.layout C model.H (p::pre ++ p::tail) model.env).get .here))
      ((model.push model.env.1).setLocal (modelPrimitiveSlot p tail (p::p::pre)) model.env.1) := by
  obtain ⟨out, ran, related⟩ :=
    (primitive_saved_assign_agree (R := R) (M := M) (k := k) p pre tail name G F nps ph)
      _ st model (stateLocals_total E C _ model) 5 _ (.nil, st)
      (primitive_saved_assign_source (R := R) (M := M) (k := k) p pre tail G F 0 nps ph _ st)
  have he : out = ⟨(model.push model.env.1).setLocal
      (modelPrimitiveSlot p tail (p::p::pre)) model.env.1, List.prefix_refl _⟩ :=
    (Except.ok.inj ((primitive_saved_assign_model p pre tail name model).symm.trans ran)).symm
  subst out
  exact related

/-- Insufficient sequence horizon retains the actual Source timeout. -/
theorem primitive_saved_assign_four_timeout (p : PrimTy) (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (p::pre ++ p::tail))) (st : St E) :
    (execItems G F 4 nps ph
      (.stmt (.declInit (.local .here) (primitive_source_implicit E p))
        (.stmt (.expr (.assign (.local (sourcePrimitiveSlot p tail (p::p::pre)))
          (.local .here))) .nil) : RItems E R M k
            (sourceContext (p::pre ++ p::tail)) (sourceContext (p::p::pre ++ p::tail)))
      ls).run (.nil, st) = (.error .timeout, (.nil, st)) := by
  cases p <;> rfl

end Solidity.Source.Agreement
