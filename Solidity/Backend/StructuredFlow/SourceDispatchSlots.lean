import Solidity.Lowering.V07.ContextMap
import Solidity.Source.Value

/-!
# Checked slot extraction for the structured Source dispatcher

Guards lowering a local through a target slot of the wrong intrinsic type.
Every extracted target index carries the original context-map equation. The
Boolean-block check retains the existing theorem's universal Boolean-slot
premise; other templates can check only their own finitely many slots.
-/
namespace Solidity.Backend.StructuredFlow.SourceDispatch

abbrev Slots (srcΓ : Source.RCtx) (Γ : Ctx) :=
  {τ : Source.STy} → Source.Idx srcΓ τ → (u : LTy) × Idx Γ u

structure CheckedSlot {srcΓ : Source.RCtx} {Γ : Ctx} (slots : Slots srcΓ Γ)
    {τ : Source.STy} (i : Source.Idx srcΓ τ) (u : LTy) where
  index : Idx Γ u
  exact : slots i = ⟨u,index⟩

private theorem slot_cast {Γ : Ctx} (slot : (u : LTy) × Idx Γ u) {wanted : LTy}
    (same : slot.1 = wanted) :
    slot = ⟨wanted,Eq.mp (congrArg (fun u => Idx Γ u) same) slot.2⟩ := by
  cases slot with
  | mk actual index =>
    cases same
    rfl

def checkedSlot? {srcΓ : Source.RCtx} {Γ : Ctx} (slots : Slots srcΓ Γ)
    {τ : Source.STy} (i : Source.Idx srcΓ τ) (wanted : LTy) :
    Option (CheckedSlot slots i wanted) :=
  if same : (slots i).1 = wanted then
    some ⟨Eq.mp (congrArg (fun u => Idx Γ u) same) (slots i).2,slot_cast (slots i) same⟩
  else none

def primitive? (u : LTy) : Option PrimTy := by
  cases u
  case val p => exact some p
  all_goals exact none

def primitiveSlot? {srcΓ : Source.RCtx} {Γ : Ctx} (slots : Slots srcΓ Γ)
    {τ : Source.STy} (i : Source.Idx srcΓ τ) :
    Option ((p : PrimTy) × CheckedSlot slots i (.val p)) := do
  let p ← primitive? (slots i).1
  let checked ← checkedSlot? slots i (.val p)
  return ⟨p,checked⟩

structure BooleanSlots {srcΓ : Source.RCtx} {Γ : Ctx} (slots : Slots srcΓ Γ) where
  index : Source.Idx srcΓ .bool → Idx Γ (.val .bool)
  exact : ∀ i, slots i = ⟨.val .bool,index i⟩

def booleanSlots? {Γ : Ctx} (srcΓ : Source.RCtx) (slots : Slots srcΓ Γ) :
    Option (BooleanSlots slots) := by
  cases srcΓ with
  | nil =>
    exact some {
      index := fun i => by cases i
      exact := fun i => by cases i }
  | cons head tail =>
    let tailSlots : Slots tail Γ := fun i => slots (.there i)
    refine (booleanSlots? tail tailSlots).bind ?_
    intro rest
    if same : head = .bool then
      cases same
      refine (checkedSlot? slots .here (.val .bool)).map ?_
      intro first
      exact {
        index := fun i => by
          cases i
          case here => exact first.index
          case there i => exact rest.index i
        exact := fun i => by
          cases i
          case here => exact first.exact
          case there i => exact rest.exact i }
    else
      exact some {
        index := fun i => by
          cases i
          case here => exact False.elim (same rfl)
          case there i => exact rest.index i
        exact := fun i => by
          cases i
          case here => exact False.elim (same rfl)
          case there i => exact rest.exact i }
termination_by structural srcΓ

structure BoolPair {srcΓ : Source.RCtx} {Γ : Ctx} (slots : Slots srcΓ Γ)
    (i a : Source.Idx srcΓ .bool) where
  dest : CheckedSlot slots i (.val .bool)
  donor : CheckedSlot slots a (.val .bool)

def boolPair? {srcΓ : Source.RCtx} {Γ : Ctx} (slots : Slots srcΓ Γ)
    (i a : Source.Idx srcΓ .bool) : Option (BoolPair slots i a) := do
  let dest ← checkedSlot? slots i (.val .bool)
  let donor ← checkedSlot? slots a (.val .bool)
  return ⟨dest,donor⟩

structure CopySlots {srcΓ : Source.RCtx} {Γ : Ctx} (slots : Slots srcΓ Γ)
    {τ : Source.STy} (i a : Source.Idx srcΓ τ) where
  primitive : PrimTy
  dest : CheckedSlot slots i (.val primitive)
  donor : CheckedSlot slots a (.val primitive)

def copySlots? {srcΓ : Source.RCtx} {Γ : Ctx} (slots : Slots srcΓ Γ)
    {τ : Source.STy} (i a : Source.Idx srcΓ τ) : Option (CopySlots slots i a) := do
  let ⟨p,dest⟩ ← primitiveSlot? slots i
  let donor ← checkedSlot? slots a (.val p)
  return ⟨p,dest,donor⟩

structure BranchSlots {srcΓ : Source.RCtx} {Γ : Ctx} (slots : Slots srcΓ Γ)
    (ci ca : Source.Idx srcΓ .bool) {τ : Source.STy} (i a j b : Source.Idx srcΓ τ) where
  condition : BoolPair slots ci ca
  left : CopySlots slots i a
  rightDest : CheckedSlot slots j (.val left.primitive)
  rightDonor : CheckedSlot slots b (.val left.primitive)

def branchSlots? {srcΓ : Source.RCtx} {Γ : Ctx} (slots : Slots srcΓ Γ)
    (ci ca : Source.Idx srcΓ .bool) {τ : Source.STy} (i a j b : Source.Idx srcΓ τ) :
    Option (BranchSlots slots ci ca i a j b) := do
  let condition ← boolPair? slots ci ca
  let left ← copySlots? slots i a
  let rightDest ← checkedSlot? slots j (.val left.primitive)
  let rightDonor ← checkedSlot? slots b (.val left.primitive)
  return ⟨condition,left,rightDest,rightDonor⟩

theorem CheckedSlot.type_eq {srcΓ : Source.RCtx} {Γ : Ctx} {slots : Slots srcΓ Γ}
    {τ : Source.STy} {i : Source.Idx srcΓ τ} {u : LTy} (checked : CheckedSlot slots i u) :
    (slots i).1 = u := congrArg (fun slot => slot.1) checked.exact

end Solidity.Backend.StructuredFlow.SourceDispatch
