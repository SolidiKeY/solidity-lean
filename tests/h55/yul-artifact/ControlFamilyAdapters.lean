import Solidity.Yul.Compilation.ArtifactPreparation
import Solidity.Yul.Compilation.LetBranchCompletionControls
import Solidity.Yul.Compilation.LetControlCompilationControls
import Solidity.Yul.Compilation.InitializedSequenceCompilationControls
import Solidity.Yul.Compilation.LetControlCompletion
import Solidity.Yul.Compilation.LetScopeCompletion
import Solidity.Yul.Compilation.LoopControlCompletion

/-! Three explicit producer-to-common-artifact transports. Existing execution
laws supply both directions; exact images retain all original producer data.
These are additive adapters, not compiler migrations or totality claims. -/
namespace Solidity.Yul.Compilation.H55ControlFamilies
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel depth : Nat} {stmt : Stmt [] [] c n}

namespace LetControl
def encode (a : LetControlCompilation.Artifact fuel stmt) : Artifact 0 stmt where
  profile := a.compiled.profile
  code := a.code
  source_to_model := by
    intro horizon locals result ran newer m caller
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    simpa only [empty, List.nil_append] using a.source_to_model horizon locals result ran m caller
  model_to_source := by
    intro locals newer m final caller skip ran
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    simp only [empty, List.nil_append] at ran
    simpa only [empty, List.nil_append] using
      LetControlCompletion.artifact_reflected a locals m final caller skip ran

abbrev Image (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.Image (encode (fuel := fuel) (stmt := stmt))
def toImage (a : LetControlCompilation.Artifact fuel stmt) : Image fuel stmt := Artifact.toImage encode a
def fromImage (a : Image fuel stmt) : LetControlCompilation.Artifact fuel stmt := Artifact.fromImage a

theorem source_roundtrip (a : LetControlCompilation.Artifact fuel stmt) :
    fromImage (toImage a) = a := rfl
theorem image_roundtrip (a : Image fuel stmt) : toImage (fromImage a) = a :=
  Artifact.image_roundtrip a
theorem code_preserved (a : LetControlCompilation.Artifact fuel stmt) :
    (toImage a).artifact.code = a.code := rfl

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_preserved
end LetControl

namespace LetScope
def encode (a : LetScopeCompilation.Artifact fuel stmt) : Artifact 0 stmt where
  profile := a.compiled.profile
  code := a.code
  source_to_model := by
    intro horizon locals result ran newer m caller
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    simpa only [empty, List.nil_append] using a.source_to_model horizon locals result ran m caller
  model_to_source := by
    intro locals newer m final caller skip ran
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    simp only [empty, List.nil_append] at ran
    simpa only [empty, List.nil_append] using
      LetScopeCompletion.model_to_source a locals m final caller skip ran

abbrev Image (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.Image (encode (fuel := fuel) (stmt := stmt))
def toImage (a : LetScopeCompilation.Artifact fuel stmt) : Image fuel stmt := Artifact.toImage encode a
def fromImage (a : Image fuel stmt) : LetScopeCompilation.Artifact fuel stmt := Artifact.fromImage a

theorem source_roundtrip (a : LetScopeCompilation.Artifact fuel stmt) :
    fromImage (toImage a) = a := rfl
theorem image_roundtrip (a : Image fuel stmt) : toImage (fromImage a) = a :=
  Artifact.image_roundtrip a
theorem code_preserved (a : LetScopeCompilation.Artifact fuel stmt) :
    (toImage a).artifact.code = a.code := rfl

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_preserved
end LetScope

namespace LoopControl
/-- The original arbitrary newer prefix is retained, rather than restricted to zero. -/
def encode (a : LoopControlCompilation.Artifact fuel stmt depth) : Artifact depth stmt where
  profile := a.compiled.profile
  code := a.code
  source_to_model := a.source_to_model
  model_to_source := LoopControlCompletion.artifact_reflected a

abbrev Image (fuel depth : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.Image (encode (fuel := fuel) (depth := depth) (stmt := stmt))
def toImage (a : LoopControlCompilation.Artifact fuel stmt depth) : Image fuel depth stmt :=
  Artifact.toImage encode a
def fromImage (a : Image fuel depth stmt) : LoopControlCompilation.Artifact fuel stmt depth :=
  Artifact.fromImage a

theorem source_roundtrip (a : LoopControlCompilation.Artifact fuel stmt depth) :
    fromImage (toImage a) = a := rfl
theorem image_roundtrip (a : Image fuel depth stmt) : toImage (fromImage a) = a :=
  Artifact.image_roundtrip a
theorem code_preserved (a : LoopControlCompilation.Artifact fuel stmt depth) :
    (toImage a).artifact.code = a.code := rfl

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_preserved
end LoopControl

namespace Controls
def skipSource : Stmt [] [] ⟨false, false⟩ 0 := .skip
def letSource : Stmt [] [] ⟨false, false⟩ 0 := .let_ 1 (.literal 0) .skip

def letControlProducer : LetControlCompilation.Artifact 3 letSource :=
  (LetControlCompilation.lower 3 letSource).get (by rfl)
def letScopeProducer : LetScopeCompilation.Artifact 3 letSource :=
  (LetScopeCompilation.lower 3 letSource).get (by rfl)
def loopControlProducer : LoopControlCompilation.Artifact 1 skipSource 2 :=
  (LoopControlCompilation.lower 1 skipSource 2).get (by rfl)

theorem inhabited_images : Nonempty (LetControl.Image 3 letSource) ∧
    Nonempty (LetScope.Image 3 letSource) ∧ Nonempty (LoopControl.Image 1 2 skipSource) :=
  ⟨⟨LetControl.toImage letControlProducer⟩, ⟨LetScope.toImage letScopeProducer⟩,
    ⟨LoopControl.toImage loopControlProducer⟩⟩

-- Original fuel refusals remain explicit, outside the lossless image laws.
#guard (LetControlCompilation.lower 0 letSource).isNone
#guard (LetControlCompilation.lower 1 skipSource).isNone
#guard (LoopControlCompilation.lower 0 skipSource 2).isNone
#print axioms inhabited_images
end Controls
end Solidity.Yul.Compilation.H55ControlFamilies

/-! Another producer instantiation of the same common Artifact and exact
image. The empty-newer-prefix calling convention is preserved, not extended. -/
namespace Solidity.Yul.Compilation.H55ControlFamilies.InitializedSequence
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n f g : Nat} {rhs : Expr [] [] n 1} {body : Stmt [] [] c (1+n)}

def encode (a : InitializedSequenceCompilation.Artifact f g rhs body) :
    Artifact 0 (.let_ 1 rhs body) :=
  Artifact.ofZero a.profile a.code a.source_to_model a.model_to_source

abbrev Image (f g : Nat) (rhs : Expr [] [] n 1) (body : Stmt [] [] c (1+n)) :=
  Artifact.Image (encode (f := f) (g := g) (rhs := rhs) (body := body))

theorem source_roundtrip (a : InitializedSequenceCompilation.Artifact f g rhs body) :
    Artifact.fromImage (Artifact.toImage encode a) = a := Artifact.source_roundtrip encode a

theorem image_roundtrip (a : Image f g rhs body) :
    Artifact.toImage encode (Artifact.fromImage a) = a := Artifact.image_roundtrip a

theorem code_preserved (a : InitializedSequenceCompilation.Artifact f g rhs body) :
    (encode a).code = a.code := rfl

namespace Controls
/-- The actual initializer and sequence visitor copy all dirty high bits to
an outer local, then retire the fresh slot. Reuse its original effectful law. -/
theorem dirty_copy (old : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode InitializedSequenceCompilation.Controls.copied).code
      {m with stack := coreWord old :: caller} =
      .ok {m with stack := coreWord SourceLoop.Controls.dirty :: caller} 0 :=
  InitializedSequenceCompilation.Controls.copied_target old m caller

theorem compiler_image_inhabited :
    Nonempty (Image (n := 1) (c := SourceLoop.Controls.root) 2 6 (.literal SourceLoop.Controls.dirty.toFin)
      InitializedSequenceCompilation.Controls.copiedBody) :=
  ⟨Artifact.toImage encode InitializedSequenceCompilation.Controls.copied⟩

#guard (InitializedSequenceCompilation.lower (n := 1) 0 6
  (.literal SourceLoop.Controls.dirty.toFin) InitializedSequenceCompilation.Controls.copiedBody).isNone
#guard (InitializedSequenceCompilation.lower (n := 1) 2 0
  (.literal SourceLoop.Controls.dirty.toFin) InitializedSequenceCompilation.Controls.copiedBody).isNone
end Controls

#print axioms Artifact.ofZero
#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_preserved
#print axioms Controls.dirty_copy
#print axioms Controls.compiler_image_inhabited
end Solidity.Yul.Compilation.H55ControlFamilies.InitializedSequence

namespace Solidity.Yul.Compilation.H55ControlFamilies.LetBranch
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}

def encode (a : LetBranchCompilation.Artifact fuel stmt) : Artifact 0 stmt :=
  Artifact.ofZero a.compiled.profile a.code a.source_to_model
    (LetBranchCompletion.model_to_source a)

abbrev Image (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.Image (encode (fuel := fuel) (stmt := stmt))

theorem source_roundtrip (a : LetBranchCompilation.Artifact fuel stmt) :
    Artifact.fromImage (Artifact.toImage encode a) = a := Artifact.source_roundtrip encode a

theorem image_roundtrip (a : Image fuel stmt) :
    Artifact.toImage encode (Artifact.fromImage a) = a := Artifact.image_roundtrip a

def prepare (a : LetBranchCompilation.Compiled fuel stmt) : Option (Artifact 0 stmt) :=
  Artifact.select LetBranchCompilation.Compiled.code
    (fun compiled code selected => encode ⟨compiled, code, selected⟩) a

abbrev Preparation (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.PreparationImage (prepare (fuel := fuel) (stmt := stmt))

theorem raw_roundtrip (a : LetBranchCompilation.Compiled fuel stmt) :
    Artifact.recoverPreparation (Artifact.toPreparationImage prepare a) = a :=
  Artifact.preparation_source_roundtrip prepare a

theorem prepare_some (a : LetBranchCompilation.Compiled fuel stmt) (code : List Evm.Instr)
    (selected : a.code = some code) : prepare a = some (encode ⟨a, code, selected⟩) :=
  Artifact.select_some _ _ a code selected

theorem prepare_none (a : LetBranchCompilation.Compiled fuel stmt) (refused : a.code = none) :
    prepare a = none := Artifact.select_none _ _ a refused

namespace Controls
/-- Reuse the existing visitor's raw-word conditional effect and exact frame. -/
theorem branch_model (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode LetBranchCompilation.Controls.artifact).code
      {m with stack := coreWord b :: caller} =
      .ok {m with stack := coreWord (LetBranchCompilation.Controls.update b) :: caller} 0 :=
  LetBranchCompilation.Controls.target_done b m caller

theorem selected_preparation : prepare LetBranchCompilation.Controls.artifact.compiled =
    some (encode LetBranchCompilation.Controls.artifact) :=
  prepare_some _ _ LetBranchCompilation.Controls.artifact.lowered

/-- A valid source local16 has no DUP17 selection. The actual raw visitor
still succeeds and its source-feasible refusal remains exact provenance. -/
def refusedRaw : LetBranchCompilation.Compiled 2 LetBranchCompilation.Controls.beyondSource :=
  (LetBranchCompilation.compile 2 LetBranchCompilation.Controls.beyondSource).get (by rfl)
theorem refused_code : refusedRaw.code = none := rfl
theorem refused_preparation : (Artifact.toPreparationImage prepare refusedRaw).artifact = none :=
  prepare_none _ refused_code
theorem refused_original :
    Artifact.recoverPreparation (Artifact.toPreparationImage prepare refusedRaw) = refusedRaw :=
  raw_roundtrip refusedRaw
theorem refused_source_completes :
    evalStmt 2 .nil True.intro LetBranchCompilation.Controls.beyondSource refusedRaw.profile
      (sourceLocals (Vector.replicate 17 0)) =
      some ⟨sourceLocals (Vector.replicate 17 0), .normal⟩ := rfl

#guard LetBranchCompilation.Controls.update LetBranchCompilation.Controls.highOnly ≠
  LetBranchCompilation.Controls.highOnly
#guard (LetBranchCompilation.lower 0 LetBranchCompilation.Controls.source).isNone
#guard (LetBranchCompilation.lower 2 LetBranchCompilation.Controls.lastSource).isSome
#guard (LetBranchCompilation.lower 2 LetBranchCompilation.Controls.beyondSource).isNone
end Controls

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms raw_roundtrip
#print axioms prepare_some
#print axioms prepare_none
#print axioms Artifact.preparation_image_roundtrip
#print axioms Controls.branch_model
#print axioms Controls.selected_preparation
#print axioms Controls.refused_code
#print axioms Controls.refused_preparation
#print axioms Controls.refused_original
#print axioms Controls.refused_source_completes
end Solidity.Yul.Compilation.H55ControlFamilies.LetBranch

/-! Raw stages reuse their already-existing selected adapters and generic
selection/provenance laws. No additional semantic certificate type is needed. -/
namespace Solidity.Yul.Compilation.H55ControlFamilies.LetControl
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}

def prepare (a : LetControlCompilation.Compiled fuel stmt) : Option (Artifact 0 stmt) :=
  Artifact.select LetControlCompilation.Compiled.code
    (fun compiled code selected => encode ⟨compiled, code, selected⟩) a

abbrev Preparation (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.PreparationImage (prepare (fuel := fuel) (stmt := stmt))

namespace RawControls
theorem selected : prepare LetControlCompilation.Controls.artifact.compiled =
    some (encode LetControlCompilation.Controls.artifact) :=
  Artifact.select_some _ _ _ _ LetControlCompilation.Controls.artifact.lowered

theorem effectful (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode LetControlCompilation.Controls.artifact).code
      {m with stack := coreWord b :: caller} =
      .ok {m with stack := coreWord (LetControlCompilation.Controls.update b) :: caller} 0 :=
  LetControlCompilation.Controls.target_done b m caller

def refused : LetControlCompilation.Compiled 3 LetBranchCompilation.Controls.beyondSource :=
  (LetControlCompilation.compile 3 LetBranchCompilation.Controls.beyondSource).get (by rfl)
theorem refused_code : refused.code = none := rfl
theorem refused_preparation : (Artifact.toPreparationImage prepare refused).artifact = none :=
  Artifact.select_none LetControlCompilation.Compiled.code
    (fun compiled code selected => encode ⟨compiled, code, selected⟩) refused refused_code
theorem original_recovered :
    Artifact.recoverPreparation (Artifact.toPreparationImage prepare refused) = refused :=
  Artifact.preparation_source_roundtrip prepare refused
theorem source_completes :
    evalStmt 2 .nil True.intro LetBranchCompilation.Controls.beyondSource refused.profile
      (sourceLocals (Vector.replicate 17 0)) =
      some ⟨sourceLocals (Vector.replicate 17 0), .normal⟩ := rfl
#guard (LetControlCompilation.compile 0 LetControlCompilation.Controls.source).isNone
end RawControls

#print axioms prepare
#print axioms RawControls.selected
#print axioms RawControls.effectful
#print axioms RawControls.refused_code
#print axioms RawControls.refused_preparation
#print axioms RawControls.original_recovered
#print axioms RawControls.source_completes
end Solidity.Yul.Compilation.H55ControlFamilies.LetControl

namespace Solidity.Yul.Compilation.H55ControlFamilies.LetScope
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}

def prepare (a : LetScopeCompilation.Compiled fuel stmt) : Option (Artifact 0 stmt) :=
  Artifact.select LetScopeCompilation.Compiled.code
    (fun compiled code selected => encode ⟨compiled, code, selected⟩) a

abbrev Preparation (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.PreparationImage (prepare (fuel := fuel) (stmt := stmt))

namespace RawControls
theorem selected : prepare LetScopeCompilation.Controls.artifact.compiled =
    some (encode LetScopeCompilation.Controls.artifact) :=
  Artifact.select_some _ _ _ _ LetScopeCompilation.Controls.artifact.lowered

theorem effectful (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode LetScopeCompilation.Controls.artifact).code
      {m with stack := coreWord b :: caller} =
      .ok {m with stack := coreWord ((~~~(~~~(b+SourceLoop.Controls.dirty)+3)+3)+3) :: caller} 0 :=
  LetScopeCompilation.Controls.target_done b m caller

def refused : LetScopeCompilation.Compiled 2 LetScopeCompilation.Controls.beyondSource :=
  (LetScopeCompilation.compile 2 LetScopeCompilation.Controls.beyondSource).get (by rfl)
theorem refused_code : refused.code = none := rfl
theorem refused_preparation : (Artifact.toPreparationImage prepare refused).artifact = none :=
  Artifact.select_none LetScopeCompilation.Compiled.code
    (fun compiled code selected => encode ⟨compiled, code, selected⟩) refused refused_code
theorem original_recovered :
    Artifact.recoverPreparation (Artifact.toPreparationImage prepare refused) = refused :=
  Artifact.preparation_source_roundtrip prepare refused
theorem source_completes : ∃ result,
    evalStmt 3 .nil True.intro LetScopeCompilation.Controls.beyondSource refused.profile
      (sourceLocals (Vector.replicate 17 0)) = some result := ⟨_, rfl⟩
#guard (LetScopeCompilation.compile 0 LetScopeCompilation.Controls.source).isNone
end RawControls

#print axioms prepare
#print axioms RawControls.selected
#print axioms RawControls.effectful
#print axioms RawControls.refused_code
#print axioms RawControls.refused_preparation
#print axioms RawControls.original_recovered
#print axioms RawControls.source_completes
end Solidity.Yul.Compilation.H55ControlFamilies.LetScope
