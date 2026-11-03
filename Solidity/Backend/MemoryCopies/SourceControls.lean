import Solidity.Backend.MemoryCopies.SourceInterface
import Solidity.Backend.MemoryCopies.SourceSize
import Solidity.Backend.Aggregates.G18ArrayAccessControls

/-! Inhabited Source certificate controls. The published populated array fixture
has two live uint8 elements. Actual source reads of the copied object retain
those values; nonheap state and the older Boolean object remain explicit.
These are Source controls, not a Source-to-backend representation theorem. -/
namespace Solidity.Backend.MemoryCopies.SourceControls

private abbrev E := Solidity.Backend.Aggregates.SourceArray.Controls.E
private abbrev frame := Solidity.Backend.Aggregates.SourceArray.Controls.frame
private abbrev path := Solidity.Backend.Aggregates.SourceArray.Controls.arrayPath
private abbrev T : Source.STy := .array .memory (.int .u8) none
private def before : Source.EMState E [.bool] :=
  (Solidity.Backend.Aggregates.SourceArray.Controls.locals,
    Solidity.Backend.Aggregates.SourceArray.Controls.state
      Solidity.Backend.Aggregates.SourceArray.Controls.live)
private def data : Source.Data E.layout T :=
  .array 2 (fun _ h => nomatch h)
    (Source.finCons (.val (.int 7 (by decide)))
      (Source.finCons (.val (.int 11 (by decide))) Fin.elim0))
private def after : Source.EMState E [.bool] :=
  (before.1, {before.2 with heap := (before.2.heap.alloc ⟨T, data⟩).1})

private def bytesAfter {E : Source.Env} {Γ : Source.RCtx} (input : Source.EMState E Γ) :
    Source.EMState E Γ :=
  (input.1, {input.2 with heap :=
    (input.2.heap.alloc ⟨.bytes .memory, Source.Data.bytes []⟩).1})

/-- Actual fresh bytes default, uniform in a populated input state and fuel slack. -/
def bytes_default {E : Source.Env} {Γ : Source.RCtx}
    (input : Source.EMState E Γ) (fuel : Nat) :
    SourceDefaultCertificate (fuel + 2) (.bytes .memory) rfl input (bytesAfter input)
      input.2.heap.next (Source.Data.bytes []) := by
  refine ⟨rfl, rfl, ?_, Nat.le_refl _, Source.Heap.alloc_get _ _, ?_⟩
  · change input.2.heap.next ≤ input.2.heap.next + 1
    omega
  · intro address older
    exact Source.Heap.alloc_other _ _ (Nat.ne_of_lt older)

private def load : SourceStorageLoadCertificate frame 4 T path before before data :=
  ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl⟩

private def copy : SourceStorageCopyCertificate frame 4 T rfl path before before after
    before.2.heap.next data where
  load := load
  allocation := rfl
  execution := rfl
  fresh := Nat.le_refl _
  object := Source.Heap.alloc_get _ _
  nonheap := rfl
  old := by
    intro address older
    exact Source.Heap.alloc_other _ _ (Nat.ne_of_lt older)

theorem default_inhabited :
    Nonempty (SourceDefaultCertificate 2 (.bytes .memory) rfl before (bytesAfter before)
      before.2.heap.next (Source.Data.bytes [])) := ⟨bytes_default before 0⟩

theorem default_outcome_inhabited :
    Nonempty (SourceDefaultOutcomeCertificate 2 (.bytes .memory) before (bytesAfter before)
      (.ok (.memRef rfl before.2.heap.next))) :=
  ⟨⟨(bytes_default before 0).execution, (bytes_default before 0).frame,
    (bytes_default before 0).growth, (bytes_default before 0).old⟩⟩

theorem load_inhabited :
    Nonempty (SourceStorageLoadCertificate frame 4 T path before before data) := ⟨load⟩

theorem load_outcome_inhabited :
    Nonempty (SourceStorageLoadOutcomeCertificate frame 4 T path before before (.ok data)) :=
  ⟨⟨load.execution, load.nonheap, load.growth, load.old⟩⟩

theorem copy_inhabited :
    Nonempty (SourceStorageCopyCertificate frame 4 T rfl path before before after
      before.2.heap.next data) := ⟨copy⟩

/-- Exact timeout constructors retain the actual input state at horizon zero. -/
theorem default_timeout (type : Source.STy) :
    Nonempty (SourceDefaultOutcomeCertificate 0 type before before (.error .timeout)) :=
  ⟨⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl⟩⟩

theorem load_timeout :
    Nonempty (SourceStorageLoadOutcomeCertificate frame 0 T path before before (.error .timeout)) :=
  ⟨⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl⟩⟩

/-- The copy's parent was absent before and is present afterward at the fresh
identity; the old populated Boolean object remains the original object. -/
theorem fresh_parent_and_old_object :
    before.2.heap.get before.2.heap.next = none ∧
    after.2.heap.get before.2.heap.next = some ⟨T, data⟩ ∧
    after.2.heap.get 0 = before.2.heap.get 0 :=
  ⟨Source.Heap.alloc_fresh before.2.heap ⟨T, data⟩, copy.object, copy.old 0 (by decide)⟩

/-- Observe both actual copied elements and the distinct bounds-panic branch. -/
theorem copied_element_observations :
    (Source.memElem (E := E) (Γ := [.bool]) before.2.heap.next 0 (.int .u8)).run after =
      (.ok (.int 7 (by decide)), after) ∧
    (Source.memElem (E := E) (Γ := [.bool]) before.2.heap.next 1 (.int .u8)).run after =
      (.ok (.int 11 (by decide)), after) ∧
    (Source.memElem (E := E) (Γ := [.bool]) before.2.heap.next 2 (.int .u8)).run after =
      (Source.panic .index, after) := ⟨rfl, rfl, rfl⟩

private def large : Source.Val E.layout (.int .u256) := .int (2 ^ 64) (by decide)
private def lengthInput : Source.EMState E [.int .u256] := (.cons large .nil, before.2)
private def zeroInput : Source.EMState E [.int .u256] := (.cons (.int 0 (by decide)) .nil, before.2)
private def lengthExpr : Source.RExpr E [.int .u256] (.int .u256) := .local .here

/-- All premises of the current length-panic law are actual evaluations. -/
def oversized_length (global : Source.Glob E) :
    NewArrayLengthPanicPremise global frame 1 (τ := .bytes .memory) rfl lengthExpr rfl
      (.val large) (2 ^ 64) lengthInput lengthInput := ⟨rfl, rfl, Nat.le_refl _⟩

theorem oversized_length_panics (global : Source.Glob E) :
    (Source.evalE global frame 2
      (Source.RExpr.newArray (τ := .bytes .memory) rfl lengthExpr rfl)).run lengthInput =
        (Source.panic .alloc, lengthInput) := (oversized_length global).failure

/-- A permitted empty allocation succeeds; it is not a size-panic refusal. -/
theorem zero_length_succeeds (global : Source.Glob E) :
    (Source.evalE global frame 2
      (Source.RExpr.newArray (τ := .bytes .memory) rfl lengthExpr rfl)).run zeroInput =
        (.ok (.val (.memRef rfl before.2.heap.next)), bytesAfter zeroInput) := by
  rfl

/-- Horizon exhaustion remains distinct from the allocation panic. -/
theorem length_horizon_timeout (global : Source.Glob E) :
    (Source.evalE global frame 0
      (Source.RExpr.newArray (τ := .bytes .memory) rfl lengthExpr rfl)).run lengthInput =
        (.error .timeout, lengthInput) := rfl

#print axioms default_inhabited
#print axioms default_outcome_inhabited
#print axioms load_inhabited
#print axioms load_outcome_inhabited
#print axioms copy_inhabited
#print axioms default_timeout
#print axioms load_timeout
#print axioms fresh_parent_and_old_object
#print axioms copied_element_observations
#print axioms oversized_length_panics
#print axioms zero_length_succeeds
#print axioms length_horizon_timeout
end Solidity.Backend.MemoryCopies.SourceControls
