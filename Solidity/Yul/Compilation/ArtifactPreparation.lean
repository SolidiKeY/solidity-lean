import Solidity.Yul.Compilation.WordMachine
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
/-- Result-polymorphic two-stage preparation. The dependent payload retains
its original source/profile indices; neither emission nor selection is erased. -/
def prepareResult {E A B : Type} {P : E → Type} (first : E → Option A)
    (second : A → Option B)
    (certify : ∀ original payload, first original = some payload →
      ∀ output, second payload = some output → P original) (original : E) : Option (P original) :=
  match emitted : first original with
  | none => none
  | some payload =>
    match selected : second payload with
    | none => none
    | some output => some (certify original payload emitted output selected)

theorem prepareResult_none {E A B : Type} {P : E → Type} (first : E → Option A)
    (second : A → Option B)
    (certify : ∀ original payload, first original = some payload →
      ∀ output, second payload = some output → P original)
    (original : E) (refused : first original = none) :
    prepareResult first second certify original = none := by
  unfold prepareResult
  split
  next observed => rfl
  next payload observed => cases observed.symm.trans refused

theorem prepareResult_some {E A B : Type} {P : E → Type} (first : E → Option A)
    (second : A → Option B)
    (certify : ∀ original payload, first original = some payload →
      ∀ output, second payload = some output → P original)
    (original : E) (payload : A) (output : B) (emitted : first original = some payload)
    (selected : second payload = some output) :
    prepareResult first second certify original = some (certify original payload emitted output selected) := by
  unfold prepareResult
  split
  next observed => cases observed.symm.trans emitted
  next actual observed =>
    have same : actual = payload := Option.some.inj (observed.symm.trans emitted)
    subst actual
    split
    next observed => cases observed.symm.trans selected
    next actual observed =>
      have same : actual = output := Option.some.inj (observed.symm.trans selected)
      subst actual
      rfl

/-- Exact image for dependent typed result preparations, including None. -/
structure ResultImage {E : Type} {P : E → Type} (encode : ∀ original, Option (P original)) where
  original : E
  payload : Option (P original)
  agrees : payload = encode original

def toResultImage {E : Type} {P : E → Type} (encode : ∀ original, Option (P original))
    (original : E) : ResultImage encode := ⟨original, encode original, rfl⟩

def recoverResult {E : Type} {P : E → Type} {encode : ∀ original, Option (P original)}
    (image : ResultImage encode) : E := image.original

theorem result_source_roundtrip {E : Type} {P : E → Type}
    (encode : ∀ original, Option (P original)) (original : E) :
    recoverResult (toResultImage encode original) = original := rfl

theorem result_image_roundtrip {E : Type} {P : E → Type}
    {encode : ∀ original, Option (P original)} (image : ResultImage encode) :
    toResultImage encode (recoverResult image) = image := by
  rcases image with ⟨original, payload, agrees⟩
  cases agrees
  rfl
/-- Actual instruction selection preserves concatenation of selected programs.
This is target preparation, with no execution, gas or capacity assertion. -/
theorem selectCode_append {first second : Backend.Program} {a b : List Evm.Instr}
    (left : WordMachine.selectCode first = some a) (right : WordMachine.selectCode second = some b) :
    WordMachine.selectCode (first ++ second) = some (a ++ b) := by
  induction first generalizing a with
  | nil =>
    have same : a = [] := (Option.some.inj left).symm
    subst a
    exact right
  | cons i first ih =>
    change (WordMachine.selectInstr i).bind (fun j =>
      (WordMachine.selectCode first).map (fun rest => j :: rest)) = some a at left
    obtain ⟨j, selected, rest⟩ := Option.bind_eq_some_iff.mp left
    obtain ⟨tail, selectedTail, same⟩ := Option.map_eq_some_iff.mp rest
    subst a
    change (WordMachine.selectInstr i).bind (fun j =>
      (WordMachine.selectCode (first ++ second)).map (fun rest => j :: rest)) = _
    rw [selected, ih selectedTail]
    rfl

/-- Every existing typed prefix push selects actual code. Word order is the
original pushPrefix order; no bounded-depth or native-capacity claim follows. -/
theorem pushPrefix_selection_total (words : List Backend.Scalar.Word) :
    ∃ code, WordMachine.selectCode (pushPrefix words) = some code := by
  induction words with
  | nil => exact ⟨[], rfl⟩
  | cons word words ih =>
    obtain ⟨code, selected⟩ := ih
    have singleton : WordMachine.selectCode [Backend.Scalar.pushWord word] =
        some [Evm.Instr.push (MachineAdapter.coreWord word)] := by
      rw [WordMachine.selectCode, WordMachine.select_pushWord]
      rfl
    exact ⟨code ++ [Evm.Instr.push (MachineAdapter.coreWord word)], selectCode_append selected singleton⟩

/-- Prefix retirement selection is total independently of execution operands. -/
theorem popPrefix_selected (fresh : Nat) :
    WordMachine.selectCode (popPrefix fresh) = some (List.replicate fresh Evm.Instr.pop) := by
  induction fresh with
  | zero => rfl
  | succ fresh ih =>
    change (WordMachine.selectCode (popPrefix fresh)).map (fun code => Evm.Instr.pop :: code) = _
    rw [ih]
    rfl
end Solidity.Yul.Compilation.Artifact
