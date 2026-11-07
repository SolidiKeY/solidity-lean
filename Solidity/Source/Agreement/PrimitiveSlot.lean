import Solidity.Source.Agreement.NormalStep

/-! Primitive-local read and write transport through the existing Source and
model indices. Integer values retain their intrinsic range proofs. These are
local-state facts and an actual initialization consumer, not a heap simulation. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Source position of a primitive below an arbitrary primitive prefix. -/
def sourcePrimitiveSlot (p : PrimTy) (tail : List PrimTy) : (pre : List PrimTy) →
    Source.Idx (sourceContext (pre ++ p::tail)) (sourceTy p)
  | [] => .here
  | _::ps => .there (sourcePrimitiveSlot p tail ps)

/-- Model position at the same physical local slot. -/
def modelPrimitiveSlot (p : PrimTy) (tail : List PrimTy) : (pre : List PrimTy) →
    Solidity.Idx (modelContext (pre ++ p::tail)) (.val p)
  | [] => .here
  | _::ps => .there (modelPrimitiveSlot p tail ps)

/-- The selected actual reads preserve the primitive relation. -/
theorem primitive_slot_get_related (D : Layout) (C : Contract) (H : HTy)
    (p : PrimTy) (pre tail : List PrimTy)
    (ls : Locals D (sourceContext (pre ++ p::tail)))
    (ws : TEnv C H (modelContext (pre ++ p::tail)))
    (related : LocalsRel D C H (pre ++ p::tail) ls ws) :
    PrimitiveRel D p (ls.get (sourcePrimitiveSlot p tail pre))
      (TEnv.get (modelPrimitiveSlot p tail pre) ws) := by
  induction pre with
  | nil => cases related with | cons head rest => exact head
  | cons q ps ih => cases related with | cons head rest => exact ih _ _ rest

/-- Replacing one slot by related values retains every other local. -/
theorem primitive_slot_set_related (D : Layout) (C : Contract) (H : HTy)
    (p : PrimTy) (pre tail : List PrimTy)
    (ls : Locals D (sourceContext (pre ++ p::tail)))
    (ws : TEnv C H (modelContext (pre ++ p::tail)))
    (v : Source.Val D (sourceTy p)) (w : p.Denote)
    (value : PrimitiveRel D p v w)
    (related : LocalsRel D C H (pre ++ p::tail) ls ws) :
    LocalsRel D C H (pre ++ p::tail)
      (ls.set (sourcePrimitiveSlot p tail pre) v)
      (TEnv.set (modelPrimitiveSlot p tail pre) w ws) := by
  induction pre with
  | nil => cases related with | cons head rest => exact .cons value rest
  | cons q ps ih => cases related with | cons head rest => exact .cons head (ih _ _ rest)

/-- Self-conversion for precisely the supported primitive Source types. -/
theorem primitive_source_implicit (E : Env) (p : PrimTy) :
    STy.implicit E.isBase E.mapFree (sourceTy p) (sourceTy p) = true := by
  cases p <;> rfl

/-- The primitive relation retains the same value and its intrinsic evidence. -/
theorem primitive_related_ofModel (D : Layout) (p : PrimTy)
    (s : Source.Val D (sourceTy p)) (v : p.Denote)
    (related : PrimitiveRel D p s v) : s = ofModel D p v := by
  cases related <;> rfl

/-- Actual Source initialization copies the selected primitive, without writing
heap or storage and without a desired value premise. -/
theorem primitive_read_init_source (p : PrimTy) (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ p::tail))) (st : St E) :
    (execS G F (n+2) nps ph
      (.declInit (.local (sourcePrimitiveSlot p tail pre)) (primitive_source_implicit E p) : RStmt E R M k
        (sourceContext (pre ++ p::tail)) (sourceContext (p::pre ++ p::tail))) ls).run
      (.nil, st) = (.ok (.normal (.cons (ls.get (sourcePrimitiveSlot p tail pre)) ls)),
        (.nil, st)) := by
  cases p <;> rfl

/-- Actual model initialization copies its existing environment value. -/
theorem primitive_read_init_model (p : PrimTy) (pre tail : List PrimTy) (name : Var)
    (model : Solidity.State C (modelContext (pre ++ p::tail))) :
    Solidity.Stmt.runC (.declLocal p name
      (some (.simple (.local (modelPrimitiveSlot p tail pre))))) model =
      .ok ⟨model.push (TEnv.get (modelPrimitiveSlot p tail pre) model.env),
        List.prefix_refl _⟩ := by
  rfl

/-- Concrete initialization agreement for every supported primitive. Both
interpreter computations and the actual read relation are supplied internally. -/
theorem primitive_read_init_step (p : PrimTy) (pre tail : List PrimTy) (name : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalStmtObligation (C := C) (R := R) (M := M) (k := k)
      (pre ++ p::tail) (p::pre ++ p::tail) G F nps ph
      (.declInit (.local (sourcePrimitiveSlot p tail pre)) (primitive_source_implicit E p))
      (.declLocal p name (some (.simple (.local (modelPrimitiveSlot p tail pre))))) := by
  intro ls st model related fuel ls' journal ran
  cases fuel with
  | zero => cases ran
  | succ n => cases n with
    | zero => cases ran
    | succ n =>
      rw [primitive_read_init_source] at ran
      have he : (.cons (ls.get (sourcePrimitiveSlot p tail pre)) ls) = ls' :=
        Source.Out.normal.inj (Except.ok.inj (Prod.mk.inj ran).1)
      subst ls'
      exact ⟨⟨model.push (TEnv.get (modelPrimitiveSlot p tail pre) model.env), List.prefix_refl _⟩,
        primitive_read_init_model p pre tail name model,
        LocalsRel.cons (primitive_slot_get_related E.layout C model.H p pre tail ls model.env related) related⟩

end Solidity.Source.Agreement
