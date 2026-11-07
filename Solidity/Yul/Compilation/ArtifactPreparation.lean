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

/-- A total accepted producer can yield a semantic certificate directly.
Selection totality is an actual proof obligation; this asserts no visitor or
admission totality. The chosen payload is constrained by exact selection. -/
noncomputable def ofTotalSelection {E A : Type} (selection : E → Option A)
    (certify : ∀ original payload, selection original = some payload → Artifact depth stmt)
    (total : ∀ original, ∃ payload, selection original = some payload)
    (original : E) : Artifact depth stmt :=
  certify original (Classical.choose (total original)) (Classical.choose_spec (total original))

theorem select_total {E A : Type} (selection : E → Option A)
    (certify : ∀ original payload, selection original = some payload → Artifact depth stmt)
    (total : ∀ original, ∃ payload, selection original = some payload)
    (original : E) :
    select selection certify original = some (ofTotalSelection selection certify total original) :=
  select_some selection certify original _ (Classical.choose_spec (total original))

/-- Compose an actual emission with actual payload selection. Both phase
proofs remain available to the existing semantic certificate constructor. -/
def afterSelection {E A B : Type} (first : E → Option A) (second : A → Option B)
    (certify : ∀ original payload, first original = some payload →
      ∀ output, second payload = some output → Artifact depth stmt)
    (original : E) : Option (Artifact depth stmt) :=
  match emitted : first original with
  | none => none
  | some payload =>
    select (fun _ : Unit => second payload)
      (fun _ output selected => certify original payload emitted output selected) ()

theorem afterSelection_first_none {E A B : Type} (first : E → Option A) (second : A → Option B)
    (certify : ∀ original payload, first original = some payload →
      ∀ output, second payload = some output → Artifact depth stmt)
    (original : E) (refused : first original = none) :
    afterSelection first second certify original = none := by
  unfold afterSelection
  split
  next observed => rfl
  next payload observed => cases observed.symm.trans refused

theorem afterSelection_second_none {E A B : Type} (first : E → Option A) (second : A → Option B)
    (certify : ∀ original payload, first original = some payload →
      ∀ output, second payload = some output → Artifact depth stmt)
    (original : E) (payload : A) (emitted : first original = some payload)
    (refused : second payload = none) : afterSelection first second certify original = none := by
  unfold afterSelection
  split
  next observed => cases observed.symm.trans emitted
  next actual observed =>
    have same : actual = payload := Option.some.inj (observed.symm.trans emitted)
    subst actual
    exact select_none _ _ () refused

theorem afterSelection_some {E A B : Type} (first : E → Option A) (second : A → Option B)
    (certify : ∀ original payload, first original = some payload →
      ∀ output, second payload = some output → Artifact depth stmt)
    (original : E) (payload : A) (output : B) (emitted : first original = some payload)
    (selected : second payload = some output) :
    afterSelection first second certify original = some (certify original payload emitted output selected) := by
  unfold afterSelection
  split
  next observed => cases observed.symm.trans emitted
  next actual observed =>
    have same : actual = payload := Option.some.inj (observed.symm.trans emitted)
    subst actual
    exact select_some _ _ () output selected

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
