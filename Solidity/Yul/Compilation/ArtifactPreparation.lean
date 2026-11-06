import Solidity.Yul.Compilation.Artifact

/-! Exact provenance for a producer stage before successful code selection.
The optional payload is the existing common Artifact, not another execution
state or semantics. None remains preparation failure, never a runtime verdict.

Guarded regression: both selected and refused preparations must recover their
complete original producer; successful payloads retain the existing semantic
certificate. The generic roundtrips prevent losing either preparation phase. -/
namespace Solidity.Yul.Compilation.Artifact
variable {c : Control} {n depth : Nat} {stmt : Stmt [] [] c n}

/-- Certify a selected payload while retaining preparation refusal exactly.
The certificate is supplied by existing producer proofs, never by the table. -/
def select {E A : Type} (selection : E → Option A)
    (certify : ∀ original payload, selection original = some payload → Artifact depth stmt)
    (original : E) : Option (Artifact depth stmt) :=
  match selected : selection original with
  | none => none
  | some payload => some (certify original payload selected)

theorem select_none {E A : Type} (selection : E → Option A)
    (certify : ∀ original payload, selection original = some payload → Artifact depth stmt)
    (original : E) (refused : selection original = none) :
    select selection certify original = none := by
  unfold select
  split
  next observed => rfl
  next payload observed => cases observed.symm.trans refused

theorem select_some {E A : Type} (selection : E → Option A)
    (certify : ∀ original payload, selection original = some payload → Artifact depth stmt)
    (original : E) (payload : A) (selected : selection original = some payload) :
    select selection certify original = some (certify original payload selected) := by
  unfold select
  split
  next observed => cases observed.symm.trans selected
  next actual observed =>
    have same : actual = payload := Option.some.inj (observed.symm.trans selected)
    subst actual
    rfl

structure PreparationImage {E : Type} (encode : E → Option (Artifact depth stmt)) where
  original : E
  artifact : Option (Artifact depth stmt)
  agrees : artifact = encode original

def toPreparationImage {E : Type} (encode : E → Option (Artifact depth stmt)) (a : E) :
    PreparationImage encode := ⟨a, encode a, rfl⟩

def recoverPreparation {E : Type} {encode : E → Option (Artifact depth stmt)}
    (a : PreparationImage encode) : E := a.original

theorem preparation_source_roundtrip {E : Type} (encode : E → Option (Artifact depth stmt)) (a : E) :
    recoverPreparation (toPreparationImage encode a) = a := rfl

theorem preparation_image_roundtrip {E : Type} {encode : E → Option (Artifact depth stmt)}
    (a : PreparationImage encode) : toPreparationImage encode (recoverPreparation a) = a := by
  rcases a with ⟨original, artifact, agrees⟩
  cases agrees
  rfl
end Solidity.Yul.Compilation.Artifact
