import Solidity.Yul.Compilation.ArtifactPreparation
import Solidity.Yul.Compilation.ScopedForCompletion
import Solidity.Yul.Compilation.ScopedForCompilationControls
import Solidity.Yul.Compilation.ForCompilation
import Solidity.Yul.Compilation.GuardedForCompilationControls

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

/-! The guarded-for producers instantiate the common semantic Artifact and
PreparationImage. No additional per-shape Artifact or execution semantics. -/
namespace Solidity.Yul.Compilation.H55For.Guarded
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel depth : Nat} {stmt : Stmt [] [] c n}

def encode (a : GuardedForCompilation.Artifact fuel depth stmt) : Artifact depth stmt where
  profile := a.compiled.profile
  code := a.code
  source_to_model := by
    intro horizon locals result ran newer m caller
    rcases a with ⟨compiled, code, lowered⟩
    cases compiled with
    | branch condition loop =>
      exact GuardedFor.source_to_model condition loop code lowered horizon locals result ran newer m caller
  model_to_source := a.reflected

abbrev Image (fuel depth : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.Image (encode (fuel := fuel) (depth := depth) (stmt := stmt))

theorem selected_roundtrip (a : GuardedForCompilation.Artifact fuel depth stmt) :
    Artifact.fromImage (Artifact.toImage encode a) = a := Artifact.source_roundtrip encode a

def prepare (a : GuardedForCompilation.Compiled fuel depth stmt) : Option (Artifact depth stmt) :=
  Artifact.select GuardedForCompilation.Compiled.code
    (fun compiled code selected => encode ⟨compiled, code, selected⟩) a

abbrev Preparation (fuel depth : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.PreparationImage (prepare (fuel := fuel) (depth := depth) (stmt := stmt))

theorem raw_roundtrip (a : GuardedForCompilation.Compiled fuel depth stmt) :
    Artifact.recoverPreparation (Artifact.toPreparationImage prepare a) = a :=
  Artifact.preparation_source_roundtrip prepare a

theorem prepare_none (a : GuardedForCompilation.Compiled fuel depth stmt)
    (refused : a.code = none) : prepare a = none :=
  Artifact.select_none _ _ a refused

theorem prepare_some (a : GuardedForCompilation.Compiled fuel depth stmt) (code : List Evm.Instr)
    (selected : a.code = some code) : prepare a = some (encode ⟨a, code, selected⟩) :=
  Artifact.select_some _ _ a code selected

namespace Controls
def source (guard : Solidity.Yul.Word) : Stmt [] [] ⟨false, false⟩ 1 :=
  .if_ (.literal guard) H55For.Controls.stoppedSource

def producer (guard : Solidity.Yul.Word) : GuardedForCompilation.Artifact 1 2 (source guard) :=
  (GuardedForCompilation.lower 1 2 (source guard)).get (by rfl)

theorem skipped_source (locals : Vector Scalar.Word 1) :
    evalStmt 2 .nil True.intro (source 0) (producer 0).compiled.profile (sourceLocals locals) =
      some ⟨sourceLocals locals, .normal⟩ := rfl

theorem taken_source (locals : Vector Scalar.Word 1) :
    evalStmt 4 .nil True.intro (source 1) (producer 1).compiled.profile (sourceLocals locals) =
      some ⟨sourceLocals locals, .normal⟩ := rfl

theorem selected_preparation (guard : Solidity.Yul.Word) :
    prepare (producer guard).compiled = some (encode (producer guard)) :=
  prepare_some _ _ (producer guard).lowered

theorem skipped_model (locals : Vector Scalar.Word 1) (newer : Vector Scalar.Word 2)
    (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode (producer 0)).code
      {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
      .ok {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} 0 :=
  (encode (producer 0)).normal_to_model 2 locals locals (skipped_source locals) newer m caller

theorem taken_model (locals : Vector Scalar.Word 1) (newer : Vector Scalar.Word 2)
    (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode (producer 1)).code
      {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
      .ok {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} 0 :=
  (encode (producer 1)).normal_to_model 4 locals locals (taken_source locals) newer m caller

/-- Reuse the existing effectful visitor fixture: the taken branch resets
an arbitrary old counter. This distinguishes taking the loop from skipping it. -/
theorem effectful_taken (a b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode GuardedForCompilation.Controls.takenArtifact).code
      {m with stack := [coreWord a, coreWord b] ++ caller} =
      .ok {m with stack := [coreWord 0, coreWord (~~~(~~~b+3)+3)] ++ caller} 0 :=
  GuardedForCompilation.Controls.taken_success a b m caller

#guard (GuardedForCompilation.lower 0 2 (source 1)).isNone
/-- The real guard needs DUP17 below the newer prefix. The loop itself
remains selectable; a source-feasible raw producer survives code refusal. -/
def refusedSource : Stmt [] [] ⟨false, false⟩ 1 :=
  .if_ (.local 0) H55For.Controls.stoppedSource
def refusedRaw : GuardedForCompilation.Compiled 1 16 refusedSource :=
  (GuardedForCompilation.compile 1 16 refusedSource).get (by rfl)
theorem refused_code : refusedRaw.code = none := rfl
theorem refused_preparation :
    (Artifact.toPreparationImage prepare refusedRaw).artifact = none := prepare_none _ refused_code
theorem refused_source_completes :
    evalStmt 2 .nil True.intro refusedSource refusedRaw.profile
      (sourceLocals (Vector.replicate 1 0)) =
      some ⟨sourceLocals (Vector.replicate 1 0), .normal⟩ := rfl
theorem refused_original_recovered :
    Artifact.recoverPreparation (Artifact.toPreparationImage prepare refusedRaw) = refusedRaw :=
  raw_roundtrip refusedRaw
#guard (GuardedForCompilation.lower 1 16 refusedSource).isNone
#guard (GuardedForCompilation.lower 1 2 H55For.Controls.stoppedSource).isNone
end Controls

#print axioms encode
#print axioms selected_roundtrip
#print axioms raw_roundtrip
#print axioms Artifact.select_none
#print axioms Artifact.select_some
#print axioms Artifact.preparation_image_roundtrip
#print axioms Artifact.image_roundtrip
#print axioms prepare_none
#print axioms prepare_some
#print axioms Controls.skipped_model
#print axioms Controls.taken_model
#print axioms Controls.effectful_taken
#print axioms Controls.selected_preparation
#print axioms Controls.refused_code
#print axioms Controls.refused_preparation
#print axioms Controls.refused_source_completes
#print axioms Controls.refused_original_recovered
end Solidity.Yul.Compilation.H55For.Guarded

/-! Scoped FOR retains the actual component artifacts, full source horizons
and zero-newer-prefix convention. Both stages instantiate shared interfaces. -/
namespace Solidity.Yul.Compilation.H55For.Scoped
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}

def encode (a : ScopedForCompilation.Artifact fuel stmt) : Artifact 0 stmt :=
  Artifact.ofZero a.compiled.profile a.code a.source_to_model (ScopedForCompletion.model_to_source a)

abbrev Image (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.Image (encode (fuel := fuel) (stmt := stmt))

def toImage (a : ScopedForCompilation.Artifact fuel stmt) : Image fuel stmt := Artifact.toImage encode a

def fromImage (a : Image fuel stmt) : ScopedForCompilation.Artifact fuel stmt := Artifact.fromImage a

theorem source_roundtrip (a : ScopedForCompilation.Artifact fuel stmt) : fromImage (toImage a) = a := rfl

theorem image_roundtrip (a : Image fuel stmt) : toImage (fromImage a) = a := Artifact.image_roundtrip a

theorem code_preserved (a : ScopedForCompilation.Artifact fuel stmt) : (encode a).code = a.code := rfl

def prepare (a : ScopedForCompilation.Compiled fuel stmt) : Option (Artifact 0 stmt) :=
  Artifact.afterSelection ScopedForCompilation.Compiled.emit WordControl.blockCode
    (fun compiled block emitted code selected => encode ⟨compiled, block, code, emitted, selected⟩) a

abbrev Preparation (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.PreparationImage (prepare (fuel := fuel) (stmt := stmt))

theorem prepared (a : ScopedForCompilation.Artifact fuel stmt) :
    prepare a.compiled = some (encode a) :=
  Artifact.afterSelection_some _ _ _ a.compiled a.block a.code a.emitted a.selected

namespace Controls
theorem selected : prepare ScopedForCompilation.Controls.artifact.compiled =
    some (encode ScopedForCompilation.Controls.artifact) := prepared _

theorem effectful (b c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode ScopedForCompilation.Controls.artifact).code
      {m with stack := coreWord b :: coreWord c :: caller} =
      .ok {m with stack := coreWord 0 :: coreWord (ScopedForCompilation.Controls.finish b c) :: caller} 0 :=
  ScopedForCompilation.Controls.target_done b c m caller

theorem zero_exit (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode ScopedForCompilation.Controls.artifact).code
      {m with stack := coreWord 0 :: coreWord c :: caller} =
      .ok {m with stack := coreWord 0 :: coreWord (c+3) :: caller} 0 :=
  ScopedForCompilation.Controls.zero_target c m caller

theorem taken_exit (b c : Scalar.Word) (nonzero : b ≠ 0)
    (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode ScopedForCompilation.Controls.artifact).code
      {m with stack := coreWord b :: coreWord c :: caller} =
      .ok {m with stack := coreWord 0 :: coreWord ((c+3)+7) :: caller} 0 :=
  ScopedForCompilation.Controls.nonzero_target b c nonzero m caller

def refusedSource : Stmt [] [] ⟨false, false⟩ 17 := .for_ .skip (.local 16) .skip .skip
def refused : ScopedForCompilation.Compiled 1 refusedSource :=
  (ScopedForCompilation.compile 1 refusedSource).get (by rfl)
theorem refused_emission : refused.emit = none := rfl
theorem refused_preparation : (Artifact.toPreparationImage prepare refused).artifact = none :=
  Artifact.afterSelection_first_none ScopedForCompilation.Compiled.emit WordControl.blockCode
    (fun compiled block emitted code selected => encode ⟨compiled, block, code, emitted, selected⟩)
    refused refused_emission

theorem refused_original : Artifact.recoverPreparation
    (Artifact.toPreparationImage prepare refused) = refused :=
  Artifact.preparation_source_roundtrip prepare refused

theorem source_completes : evalStmt 3 .nil True.intro refusedSource refused.profile
    (sourceLocals (Vector.replicate 17 0)) =
      some ⟨sourceLocals (Vector.replicate 17 0), .normal⟩ := rfl
#guard (ScopedForCompilation.compile 0 refusedSource).isNone
end Controls

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_preserved
#print axioms prepare
#print axioms prepared
#print axioms Controls.selected
#print axioms Controls.effectful
#print axioms Controls.zero_exit
#print axioms Controls.taken_exit
#print axioms Controls.refused_emission
#print axioms Controls.refused_preparation
#print axioms Controls.refused_original
#print axioms Controls.source_completes
end Solidity.Yul.Compilation.H55For.Scoped
