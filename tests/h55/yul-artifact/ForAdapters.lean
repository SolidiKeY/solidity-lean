import Solidity.Yul.Compilation.ArtifactPreparation
import Solidity.Yul.Compilation.ForCompilation

/-! Exact selected and preselection for-producer adapters. A successful phase
retains both old execution laws; a refused preparation retains the original
producer and exact None without inventing runtime failure or a run premise. -/
namespace Solidity.Yul.Compilation.H55For
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel depth : Nat} {stmt : Stmt [] [] c n}

def encode (a : ForCompilation.Artifact fuel stmt depth) : Artifact depth stmt where
  profile := a.compiled.profile
  code := a.code
  source_to_model := by
    intro horizon locals result ran newer m caller
    rcases a with ⟨compiled, block, code, emitted, selected⟩
    cases compiled with
    | loop initial condition post body =>
      exact SourceLoopInitializer.source_to_model initial condition post body depth block code
        emitted selected horizon locals result ran newer m caller
  model_to_source := a.reflected

abbrev Image (fuel depth : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.Image (encode (fuel := fuel) (depth := depth) (stmt := stmt))
def toImage (a : ForCompilation.Artifact fuel stmt depth) : Image fuel depth stmt :=
  Artifact.toImage encode a
def fromImage (a : Image fuel depth stmt) : ForCompilation.Artifact fuel stmt depth :=
  Artifact.fromImage a

theorem source_roundtrip (a : ForCompilation.Artifact fuel stmt depth) : fromImage (toImage a) = a := rfl
theorem image_roundtrip (a : Image fuel depth stmt) : toImage (fromImage a) = a := Artifact.image_roundtrip a
theorem code_preserved (a : ForCompilation.Artifact fuel stmt depth) :
    (toImage a).artifact.code = a.code := rfl

def prepare (a : ForCompilation.Compiled fuel stmt) (depth : Nat) : Option (Artifact depth stmt) :=
  match emitted : a.emit depth with
  | none => none
  | some block =>
    match selected : WordControl.blockCode block with
    | none => none
    | some code => some (encode ⟨a, block, code, emitted, selected⟩)

abbrev Preparation (fuel depth : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.PreparationImage (fun a : ForCompilation.Compiled fuel stmt => prepare a depth)
def toPreparation (depth : Nat) (a : ForCompilation.Compiled fuel stmt) : Preparation fuel depth stmt :=
  Artifact.toPreparationImage (fun a => prepare a depth) a
def fromPreparation (a : Preparation fuel depth stmt) : ForCompilation.Compiled fuel stmt :=
  Artifact.recoverPreparation a

theorem preparation_source_roundtrip (depth : Nat) (a : ForCompilation.Compiled fuel stmt) :
    fromPreparation (toPreparation depth a) = a := rfl
theorem preparation_image_roundtrip (a : Preparation fuel depth stmt) :
    toPreparation depth (fromPreparation a) = a := Artifact.preparation_image_roundtrip a

theorem prepare_emission_none (depth : Nat) (a : ForCompilation.Compiled fuel stmt)
    (refused : a.emit depth = none) : prepare a depth = none := by
  unfold prepare
  split
  next observed => rfl
  next block observed => cases observed.symm.trans refused

theorem prepare_selection_none (depth : Nat) (a : ForCompilation.Compiled fuel stmt) (block : Backend.Block)
    (emitted : a.emit depth = some block) (refused : WordControl.blockCode block = none) :
    prepare a depth = none := by
  unfold prepare
  split
  next observed => cases observed.symm.trans emitted
  next actualBlock observed =>
    have same : actualBlock = block := Option.some.inj (observed.symm.trans emitted)
    subst actualBlock
    split
    next selected => rfl
    next code selected => cases selected.symm.trans refused

theorem prepare_selected (depth : Nat) (a : ForCompilation.Compiled fuel stmt)
    (block : Backend.Block) (code : List Evm.Instr)
    (emitted : a.emit depth = some block) (selected : WordControl.blockCode block = some code) :
    prepare a depth = some (encode ⟨a, block, code, emitted, selected⟩) := by
  unfold prepare
  split
  next observed => cases observed.symm.trans emitted
  next actualBlock observed =>
    have same : actualBlock = block := Option.some.inj (observed.symm.trans emitted)
    subst actualBlock
    split
    next actual => cases actual.symm.trans selected
    next actualCode actual =>
      have sameCode : actualCode = code := Option.some.inj (actual.symm.trans selected)
      subst actualCode
      rfl

namespace Controls
def inaccessibleSource : Stmt [] [] ⟨false, false⟩ 17 :=
  .for_ .skip (.local 16) .skip .skip
def rawProducer : ForCompilation.Compiled 1 inaccessibleSource :=
  (ForCompilation.compile 1 inaccessibleSource).get (by rfl)

theorem inaccessible_source_completes : evalStmt 3 .nil True.intro inaccessibleSource rawProducer.profile
    (sourceLocals (Vector.replicate 17 0)) =
    some ⟨sourceLocals (Vector.replicate 17 0), .normal⟩ := rfl

theorem inaccessible_emission : rawProducer.emit 0 = none := rfl
theorem inaccessible_preparation : (toPreparation 0 rawProducer).artifact = none := rfl
theorem refused_original_recovered : fromPreparation (toPreparation 0 rawProducer) = rawProducer := rfl

def stoppedSource : Stmt [] [] ⟨false, false⟩ 1 := .for_ .skip (.literal 0) .skip .skip
def selectedProducer : ForCompilation.Artifact 1 stoppedSource 2 :=
  (ForCompilation.lower 1 stoppedSource 2).get (by rfl)

theorem selected_image_inhabited : Nonempty (Image 1 2 stoppedSource) := ⟨toImage selectedProducer⟩
#guard (ForCompilation.compile 0 stoppedSource).isNone

theorem stopped_source (locals : Vector Scalar.Word 1) : evalStmt 3 .nil True.intro stoppedSource
    selectedProducer.compiled.profile (sourceLocals locals) = some ⟨sourceLocals locals, .normal⟩ := rfl

theorem stopped_model (locals : Vector Scalar.Word 1) (newer : Vector Scalar.Word 2)
    (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode selectedProducer).code
      {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
      .ok {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} 0 :=
  (encode selectedProducer).normal_to_model 3 locals locals (stopped_source locals) newer m caller

theorem selected_preparation : (toPreparation 2 selectedProducer.compiled).artifact =
    some (encode selectedProducer) :=
  prepare_selected 2 selectedProducer.compiled selectedProducer.block selectedProducer.code
    selectedProducer.emitted selectedProducer.selected

#print axioms stopped_source
#print axioms stopped_model
#print axioms selected_preparation
#print axioms inaccessible_source_completes
#print axioms inaccessible_emission
#print axioms inaccessible_preparation
#print axioms refused_original_recovered
#print axioms selected_image_inhabited
end Controls

#print axioms Artifact.preparation_source_roundtrip
#print axioms Artifact.preparation_image_roundtrip
#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_preserved
#print axioms preparation_source_roundtrip
#print axioms preparation_image_roundtrip
#print axioms prepare_emission_none
#print axioms prepare_selection_none
#print axioms prepare_selected
end Solidity.Yul.Compilation.H55For
