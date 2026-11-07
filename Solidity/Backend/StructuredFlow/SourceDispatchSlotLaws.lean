import Solidity.Backend.StructuredFlow.SourceDispatchLower

/-!
# Completeness of checked dispatcher operands

Guards a reject-all operand checker from refusing mappings that satisfy the
original compiler theorem's exact slot equations. These are metadata laws;
value alignment remains the separate, unchanged ContextMap.Related premise.
-/
namespace Solidity.Backend.StructuredFlow.SourceDispatch

private theorem transported_index {Γ : Ctx} {u : LTy}
    (slot : (t : LTy) × Idx Γ t) (index : Idx Γ u) (eq : slot = ⟨u,index⟩) :
    Eq.mp (congrArg (fun t => Idx Γ t) (congrArg (fun x => x.1) eq)) slot.2 = index := by
  cases eq
  rfl

private theorem checkedSlot_ext {srcΓ : Source.RCtx} {Γ : Ctx} {slots : Slots srcΓ Γ}
    {τ : Source.STy} {i : Source.Idx srcΓ τ} {u : LTy}
    (a b : CheckedSlot slots i u) (eq : a.index = b.index) : a = b := by
  cases a
  cases b
  cases eq
  rfl

@[simp] theorem checkedSlot_exact {srcΓ : Source.RCtx} {Γ : Ctx} {slots : Slots srcΓ Γ}
    {τ : Source.STy} {i : Source.Idx srcΓ τ} {u : LTy} (checked : CheckedSlot slots i u) :
    checkedSlot? slots i u = some checked := by
  unfold checkedSlot?
  rw [dif_pos checked.type_eq]
  apply congrArg some
  apply checkedSlot_ext
  exact transported_index (slots i) checked.index checked.exact

@[simp] theorem primitiveSlot_exact {srcΓ : Source.RCtx} {Γ : Ctx} {slots : Slots srcΓ Γ}
    {τ : Source.STy} {i : Source.Idx srcΓ τ} {p : PrimTy}
    (checked : CheckedSlot slots i (.val p)) :
    primitiveSlot? slots i = some ⟨p,checked⟩ := by
  unfold primitiveSlot?
  rw [checked.type_eq]
  simp [primitive?,checkedSlot_exact checked]

@[simp] theorem boolPair_exact {srcΓ : Source.RCtx} {Γ : Ctx} {slots : Slots srcΓ Γ}
    {i a : Source.Idx srcΓ .bool} (pair : BoolPair slots i a) : boolPair? slots i a = some pair := by
  simp [boolPair?,checkedSlot_exact pair.dest,checkedSlot_exact pair.donor]

@[simp] theorem copySlots_exact {srcΓ : Source.RCtx} {Γ : Ctx} {slots : Slots srcΓ Γ}
    {τ : Source.STy} {i a : Source.Idx srcΓ τ} (copy : CopySlots slots i a) :
    copySlots? slots i a = some copy := by
  simp [copySlots?,primitiveSlot_exact copy.dest,checkedSlot_exact copy.donor]

@[simp] theorem branchSlots_exact {srcΓ : Source.RCtx} {Γ : Ctx} {slots : Slots srcΓ Γ}
    {τ : Source.STy} {ci ca : Source.Idx srcΓ .bool} {i a j b : Source.Idx srcΓ τ}
    (branch : BranchSlots slots ci ca i a j b) : branchSlots? slots ci ca i a j b = some branch := by
  simp [branchSlots?,boolPair_exact branch.condition,copySlots_exact branch.left,
    checkedSlot_exact branch.rightDest,checkedSlot_exact branch.rightDonor]

/-- The universal Boolean-slot check preserves precisely the old block premise. -/
theorem booleanSlots_complete {Γ : Ctx} (srcΓ : Source.RCtx) (slots : Slots srcΓ Γ)
    (valid : BooleanSlots slots) : (booleanSlots? srcΓ slots).isSome = true := by
  induction srcΓ with
  | nil => rfl
  | cons head tail ih =>
    let tailSlots : Slots tail Γ := fun i => slots (.there i)
    let tailValid : BooleanSlots tailSlots := {
      index := fun i => valid.index (.there i)
      exact := fun i => valid.exact (.there i) }
    have tailAccepted := ih tailSlots tailValid
    cases h : booleanSlots? tail tailSlots with
    | none => simp [h] at tailAccepted
    | some rest =>
      change ((booleanSlots? tail tailSlots).bind _).isSome = true
      rw [h]
      simp only [Option.bind_some]
      split
      next same =>
        cases same
        have first : CheckedSlot slots .here (.val .bool) := ⟨valid.index .here,valid.exact .here⟩
        simp [checkedSlot_exact first]
      next different => rfl

/-- Exact slot equations determine the Boolean index function uniquely. -/
theorem booleanSlots_unique {srcΓ : Source.RCtx} {Γ : Ctx} {slots : Slots srcΓ Γ}
    (a b : BooleanSlots slots) : a = b := by
  cases a with
  | mk ai am =>
    cases b with
    | mk bi bm =>
      have same : ai = bi := by
        funext i
        have eq : (⟨ai i,am i⟩ : CheckedSlot slots i (.val .bool)) = ⟨bi i,bm i⟩ :=
          Option.some.inj ((checkedSlot_exact ⟨ai i,am i⟩).symm.trans
            (checkedSlot_exact ⟨bi i,bm i⟩))
        exact congrArg CheckedSlot.index eq
      cases same
      rfl

@[simp] theorem booleanSlots_exact {Γ : Ctx} (srcΓ : Source.RCtx) (slots : Slots srcΓ Γ)
    (valid : BooleanSlots slots) : booleanSlots? srcΓ slots = some valid := by
  have accepts := booleanSlots_complete srcΓ slots valid
  cases h : booleanSlots? srcΓ slots with
  | none => simp [h] at accepts
  | some other =>
    have same := booleanSlots_unique other valid
    simpa only [same] using h

/-- Every mapping admitted by the selected old theorem survives checking. -/
theorem mapping_exact {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} {s : Source.RStmt E R M k srcΓ srcΔ}
    {Γ : Ctx} (m : Solidity.Lowering.V07.ContextMap srcΓ Γ) (plan : Plan E M s)
    (valid : Mapping m plan) : mapping? m plan = some valid := by
  cases plan <;> dsimp [Mapping] at valid
  case blocks steps => exact booleanSlots_exact _ m.slot valid
  case conditional ci ca i a j b => simp [mapping?,branchSlots_exact valid]
  case sequence ci ca i a j b dest donor =>
    simp [mapping?,branchSlots_exact valid.1,copySlots_exact valid.2]
  case returning ci ca i a j b => simp [mapping?,branchSlots_exact valid]
  case continuation ci ca i a j b tail => simp [mapping?,branchSlots_exact valid]
  case returnTail ci ca dest donor => simp [mapping?,boolPair_exact valid.1,copySlots_exact valid.2]
  case returnPair ci ca i a dest donor =>
    simp [mapping?,boolPair_exact valid.1,copySlots_exact valid.2.1,copySlots_exact valid.2.2]
  case whileBreak i a => simp [mapping?,boolPair_exact valid]
  case whileContinue i a tail => simp [mapping?,boolPair_exact valid]
  case whileReturn i a => simp [mapping?,boolPair_exact valid]
  case forBreak i a post => simp [mapping?,boolPair_exact valid]
  case forContinue i a tail => simp [mapping?,boolPair_exact valid]
  case forReturn i a post => simp [mapping?,boolPair_exact valid]
  case doBreak i a condition => simp [mapping?,boolPair_exact valid]
  case doContinue i a tail => simp [mapping?,boolPair_exact valid]
  case doReturn i a condition => simp [mapping?,boolPair_exact valid]

/-- Every mapping admitted by the selected old theorem survives checking. -/
theorem mapping_complete {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} {s : Source.RStmt E R M k srcΓ srcΔ}
    {Γ : Ctx} (m : Solidity.Lowering.V07.ContextMap srcΓ Γ) (plan : Plan E M s)
    (valid : Mapping m plan) : (mapping? m plan).isSome = true := by
  rw [mapping_exact m plan valid]
  rfl

end Solidity.Backend.StructuredFlow.SourceDispatch
