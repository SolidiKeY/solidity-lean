import Solidity.Lowering.V07.P12LocalCaptures
import Solidity.Lowering.V07.P12StorageCaptureControls
import Solidity.Lowering.V07.P12MemoryCaptureControls

/-!
# Non-vacuity of the generic P12 local captures

The existing mixed caller fixture's relations satisfy the four premises of
`P12LocalCaptures`, so the generic producers instantiate there and emit the
same native code as the fixture producers (CP72/CP73). A collapsing relation
that relates two distinct storage paths to one reference violates
`StorageFaithful`: the premise is not trivially true.
-/
namespace Solidity.Lowering.V07.P12LocalCaptureControls
open Source.SemanticsExamples P12NextInterface P12LocalCaptures
open P12Controls (C E SrcCtx TgtCtx source target mapping BindingRel memoryRef)
open P12AssignedConditionControls (values worlds initial initial_pair srcPair tgtPair)
open MixedAssignmentControls (globals path storageRef)

theorem storage_binding {σ : Source.STy} {loc : σ.loc? = some .storage} {p : Source.SPath}
    {v : (LTy.alias bytesR).TDenote C target.H}
    (h : BindingRel σ (.alias bytesR) (.storRef loc p) v) : p = path ∧ v = some storageRef := by
  cases σ with
  | bytes l =>
    cases l with
    | storage =>
      obtain ⟨hp, hv⟩ := h
      cases hp
      exact ⟨rfl, hv⟩
    | _ => exact h.elim
  | _ => exact h.elim

theorem memory_binding {σ : Source.STy} {R : RefTy} {loc : σ.loc? = some .memory} {a : Nat}
    {v : (LTy.mem R).TDenote C target.H}
    (h : BindingRel σ (.mem R) (.memRef loc a) v) : R = bytesR ∧ a = 0 ∧ HEq v (some memoryRef) := by
  cases σ with
  | bytes l =>
    cases l with
    | memory =>
      unfold BindingRel at h
      split at h
      case h_1 => rename_i hσ _ _ _; cases hσ
      case h_2 => rename_i hσ _ _ _; cases hσ
      case h_3 =>
        rename_i _ hR hv
        obtain ⟨ha, hr⟩ := h
        cases hR
        cases ha
        subst hr
        exact ⟨rfl, rfl, hv⟩
      case h_4 => rename_i hσ _ _ _; cases hσ
      case h_5 => exact h.elim
    | _ => exact h.elim
  | _ => exact h.elim

theorem storage_nonnull : StorageNonnull values worlds bytesR := by
  intro s g _ σ loc p v h
  obtain ⟨original, same, rel⟩ := h
  have hv : v = original := eq_of_heq same
  exact ⟨storageRef, hv.trans (storage_binding rel).2⟩

theorem storage_faithful : StorageFaithful values worlds bytesR := by
  intro s g _ σ σ' loc loc' p p' r r' h h'
  obtain ⟨o, same, rel⟩ := h
  obtain ⟨o', same', rel'⟩ := h'
  obtain ⟨hp, ho⟩ := storage_binding rel
  obtain ⟨hp', ho'⟩ := storage_binding rel'
  have hr : some r = some storageRef := (eq_of_heq same).trans ho
  have hr' : some r' = some storageRef := (eq_of_heq same').trans ho'
  rw [hp, hp', Option.some.inj hr, Option.some.inj hr']
  exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem memory_nonnull : MemoryNonnull values worlds bytesR := by
  intro s g w σ loc a v h
  obtain ⟨_, hg⟩ := w
  subst hg
  obtain ⟨original, same, rel⟩ := h
  have hv : v = original := eq_of_heq same
  subst hv
  exact ⟨memoryRef, eq_of_heq (memory_binding rel).2.2⟩

theorem memory_faithful : MemoryFaithful values worlds bytesR := by
  intro s g w σ σ' R' loc loc' a a' r r' h h'
  obtain ⟨_, hg⟩ := w
  subst hg
  obtain ⟨o, same, rel⟩ := h
  obtain ⟨o', same', rel'⟩ := h'
  have hv : some r = o := eq_of_heq same
  have hv' : some r' = o' := eq_of_heq same'
  subst hv hv'
  obtain ⟨_, ha, hr⟩ := memory_binding rel
  obtain ⟨hR, ha', hr'⟩ := memory_binding rel'
  subst hR ha ha'
  have e : r = memoryRef := Option.some.inj (eq_of_heq hr)
  have e' : r' = memoryRef := Option.some.inj (eq_of_heq hr')
  subst e e'
  exact ⟨fun _ => rfl, fun _ => rfl⟩

def storageProducer (G : Source.Glob E) (F : Source.Fr) :=
  storageLocal G F mapping values worlds (.bytes .storage) rfl bytesR
    P12StorageCaptureControls.sourceSlot P12StorageCaptureControls.targetSlot rfl
    ⟨source, target, initial⟩ storage_nonnull storage_faithful

def memoryProducer (G : Source.Glob E) (F : Source.Fr) :=
  memoryLocal G F mapping values worlds (.bytes .memory) rfl bytesR rfl
    P12MemoryCaptureControls.sourceSlot P12MemoryCaptureControls.targetSlot rfl
    ⟨source, target, initial⟩ memory_nonnull memory_faithful

/-- The generic producers emit exactly the fixture producers' native code. -/
theorem same_code (G : Source.Glob E) (F : Source.Fr) :
    (storageProducer G F).code = (P12StorageCaptureControls.producer G F).code ∧
    (memoryProducer G F).code = (P12MemoryCaptureControls.producer G F).code :=
  ⟨rfl, rfl⟩

/-- The generic producers' success fields at the fixture callers, both
pipelines and checked flags, through actual Source local execution. -/
def storage_success_client (p : Roadmap.Pipeline) (checked old rhs : Bool) (n : Nat) :=
  (storageProducer (globals p) {F0 with checked := checked}).success (n+1) (srcPair old rhs)
    (srcPair old rhs) (tgtPair old rhs) path (initial_pair old rhs)
    (source_local_value_run (globals p) {F0 with checked := checked} n (srcPair old rhs)
      P12StorageCaptureControls.sourceSlot (.storRef rfl path) (by rfl))

def memory_success_client (p : Roadmap.Pipeline) (checked old rhs : Bool) (n : Nat) :=
  (memoryProducer (globals p) {F0 with checked := checked}).success (n+1) (srcPair old rhs)
    (srcPair old rhs) (tgtPair old rhs) 0 (initial_pair old rhs)
    (source_local_value_run (globals p) {F0 with checked := checked} n (srcPair old rhs)
      P12MemoryCaptureControls.sourceSlot (.memRef rfl 0) (by rfl))

/-- A collapsing relation: every storage binding relates to every reference. -/
def collapse : ValueRelation E C := fun _ _ _ _ _ _ => True

def otherPath : Source.SPath := ⟨⟨some "C", "other"⟩, []⟩

theorem collapse_not_faithful :
    ¬ StorageFaithful collapse (fun _ _ => True) bytesR := by
  intro h
  have := (h source.2 target.glob trivial (.bytes .storage) (.bytes .storage) rfl rfl path otherPath
    storageRef storageRef trivial trivial).mpr rfl
  exact absurd this (by decide)

/-- info: 'Solidity.Lowering.V07.P12LocalCaptureControls.storage_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storage_binding
/-- info: 'Solidity.Lowering.V07.P12LocalCaptureControls.memory_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms memory_binding
/-- info: 'Solidity.Lowering.V07.P12LocalCaptureControls.storage_nonnull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storage_nonnull
/-- info: 'Solidity.Lowering.V07.P12LocalCaptureControls.storage_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storage_faithful
/-- info: 'Solidity.Lowering.V07.P12LocalCaptureControls.memory_nonnull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms memory_nonnull
/-- info: 'Solidity.Lowering.V07.P12LocalCaptureControls.memory_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms memory_faithful
/-- info: 'Solidity.Lowering.V07.P12LocalCaptureControls.storageProducer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storageProducer
/-- info: 'Solidity.Lowering.V07.P12LocalCaptureControls.memoryProducer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms memoryProducer
/-- info: 'Solidity.Lowering.V07.P12LocalCaptureControls.same_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms same_code
/-- info: 'Solidity.Lowering.V07.P12LocalCaptureControls.storage_success_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storage_success_client
/-- info: 'Solidity.Lowering.V07.P12LocalCaptureControls.memory_success_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms memory_success_client
/-- info: 'Solidity.Lowering.V07.P12LocalCaptureControls.collapse_not_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms collapse_not_faithful

end Solidity.Lowering.V07.P12LocalCaptureControls
