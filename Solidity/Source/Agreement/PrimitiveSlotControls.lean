import Solidity.Source.Agreement.PrimitiveSlot

/-! Actual primitive copy clients and horizon/value controls. These controls
are independent interpreter examples, not installed-source/native fixtures. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- The initial relation and actual Source run are produced internally from any
model state. No desired read value, execution or terminal state is assumed. -/
theorem primitive_read_init_client (R : List STy) (M : Bool) (k : SCtx)
    (p : PrimTy) (pre tail : List PrimTy) (name : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext (pre ++ p::tail))) (st : St E) :
    StateLocalsRel E C (p::pre ++ p::tail)
      (.cons ((localsOfModel E.layout C model.H (pre ++ p::tail) model.env).get
        (sourcePrimitiveSlot p tail pre))
        (localsOfModel E.layout C model.H (pre ++ p::tail) model.env))
      (model.push (TEnv.get (modelPrimitiveSlot p tail pre) model.env)) := by
  obtain ⟨out, ran, related⟩ :=
    (primitive_read_init_step (R := R) (M := M) (k := k) p pre tail name G F nps ph)
      _ st model (stateLocals_total E C _ model) 2 _ (.nil, st)
      (primitive_read_init_source (R := R) (M := M) (k := k) p pre tail G F 0 nps ph _ st)
  have he : out = ⟨model.push (TEnv.get (modelPrimitiveSlot p tail pre) model.env),
      List.prefix_refl _⟩ :=
    (Except.ok.inj ((primitive_read_init_model p pre tail name model).symm.trans ran)).symm
  subst out
  exact related

/-- A local read still requires its own Source horizon. -/
theorem primitive_read_init_one_timeout (p : PrimTy) (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ p::tail))) (st : St E) :
    (execS G F 1 nps ph
      (.declInit (.local (sourcePrimitiveSlot p tail pre)) (primitive_source_implicit E p) :
        RStmt E R M k (sourceContext (pre ++ p::tail))
          (sourceContext (p::pre ++ p::tail))) ls).run (.nil, st) =
      (.error .timeout, (.nil, st)) := by
  rfl

/-- Every intrinsically ranged unsigned integer is copied by actual Source execution. -/
theorem primitive_uint_copy_source (v : PrimTy.uint.Denote) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+2) nps ph
      (.declInit (.local (sourcePrimitiveSlot .uint [] [])) (primitive_source_implicit E .uint) :
        RStmt E R M k (sourceContext [.uint]) (sourceContext [.uint,.uint]))
      (.cons (ofModel E.layout .uint v) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (ofModel E.layout .uint v)
        (.cons (ofModel E.layout .uint v) .nil))), (.nil, st)) := by
  rfl

/-- Signed copying retains the signed range evidence, including negative values. -/
theorem primitive_int_copy_source (v : PrimTy.int.Denote) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+2) nps ph
      (.declInit (.local (sourcePrimitiveSlot .int [] [])) (primitive_source_implicit E .int) :
        RStmt E R M k (sourceContext [.int]) (sourceContext [.int,.int]))
      (.cons (ofModel E.layout .int v) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (ofModel E.layout .int v)
        (.cons (ofModel E.layout .int v) .nil))), (.nil, st)) := by
  rfl

/-- A different unsigned number cannot stand for the copied Source integer. -/
theorem primitive_uint_wrong_value (D : Layout) (v w : PrimTy.uint.Denote)
    (different : v ≠ w) : ¬ PrimitiveRel D .uint (ofModel D .uint v) w := by
  intro related
  have same : ofModel D .uint v = ofModel D .uint w :=
    primitive_related_ofModel D .uint _ w related
  apply different
  apply Subtype.ext
  injection same

end Solidity.Source.Agreement
