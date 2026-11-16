/-! Shared conversion backfill. The source index stays fixed in both
conversion directions; payload equality is required, not just a shared
observation. No Yul producer or completion theorem is changed here. -/
namespace Solidity.Yul.Compilation.ArtifactBackfill
universe u v w x

structure LosslessAdapter {I : Sort u} (A : I → Sort v) (B : I → Sort w) where
  toModel : {i : I} → A i → B i
  toSource : {i : I} → B i → A i
  source_roundtrip : ∀ {i : I} (a : A i), toSource (toModel a) = a
  model_roundtrip : ∀ {i : I} (b : B i), toModel (toSource b) = b

namespace LosslessAdapter
variable {I : Sort u} {A : I → Sort v} {B : I → Sort w} {C : I → Sort x}

def refl (A : I → Sort v) : LosslessAdapter A A :=
  ⟨fun a => a, fun a => a, fun _ => rfl, fun _ => rfl⟩

def symm (e : LosslessAdapter A B) : LosslessAdapter B A :=
  ⟨e.toSource, e.toModel, e.model_roundtrip, e.source_roundtrip⟩

def trans (e : LosslessAdapter A B) (f : LosslessAdapter B C) : LosslessAdapter A C where
  toModel := fun a => f.toModel (e.toModel a)
  toSource := fun c => e.toSource (f.toSource c)
  source_roundtrip := fun a => by rw [f.source_roundtrip, e.source_roundtrip]
  model_roundtrip := fun c => by rw [e.model_roundtrip, f.model_roundtrip]

theorem toModel_injective (e : LosslessAdapter A B) {i : I} (a b : A i)
    (same : e.toModel a = e.toModel b) : a = b := by
  have recovered : e.toSource (e.toModel a) = e.toSource (e.toModel b) := congrArg e.toSource same
  rw [e.source_roundtrip, e.source_roundtrip] at recovered
  exact recovered

theorem toSource_injective (e : LosslessAdapter A B) {i : I} (a b : B i)
    (same : e.toSource a = e.toSource b) : a = b :=
  e.symm.toModel_injective a b same

/-- Any original predicate is preserved exactly by a round trip. -/
theorem preserves (e : LosslessAdapter A B) {i : I} (P : A i → Prop) (a : A i) :
    P (e.toSource (e.toModel a)) ↔ P a := by rw [e.source_roundtrip]
end LosslessAdapter

/-- A projection that drops constructor data cannot satisfy the source law. -/
theorem constant_adapter_refused
    (e : LosslessAdapter (fun _ : Unit => Bool) (fun _ : Unit => Unit)) : False := by
  have same : e.toModel (i := ()) true = e.toModel (i := ()) false := Subsingleton.elim _ _
  have bad : true = false := e.toModel_injective true false same
  cases bad

/-- Bidirectional observations alone do not recover discarded evidence. -/
theorem observed_equality_does_not_imply_lossless :
    (fun _ : Bool => ()) true = (fun _ : Bool => ()) false ∧ true ≠ false := by
  exact ⟨rfl, Bool.noConfusion⟩
end Solidity.Yul.Compilation.ArtifactBackfill
