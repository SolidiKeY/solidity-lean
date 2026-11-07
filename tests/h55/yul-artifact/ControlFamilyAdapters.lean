import Solidity.Yul.Compilation.ZeroSequenceCompilationControls
import Solidity.Yul.Compilation.ZeroScopeCompilationControls
import Solidity.Yul.Compilation.ZeroControlCompletion
import Solidity.Yul.Compilation.ZeroControlCompilationControls
import Solidity.Yul.Compilation.SwitchSequenceCompletion
import Solidity.Yul.Compilation.SwitchCompletion
import Solidity.Yul.Compilation.SwitchCompilationControls
import Solidity.Yul.Compilation.StructuredSequenceCompletion
import Solidity.Yul.Compilation.StructuredSequenceCompilationControls
import Solidity.Yul.Compilation.SequenceCompletion
import Solidity.Yul.Compilation.SequenceCompilationControls
import Solidity.Yul.Compilation.ArtifactPreparation
import Solidity.Yul.Compilation.LetBranchCompletionControls
import Solidity.Yul.Compilation.LetControlCompilationControls
import Solidity.Yul.Compilation.LetSequenceCompletion
import Solidity.Yul.Compilation.MultiSwitchCompletion
import Solidity.Yul.Compilation.OpenStatements
import Solidity.Yul.Compilation.OpenExpressionControls
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

namespace Solidity.Yul.Compilation.H55ControlFamilies.LetSequence
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}

def encode (a : LetSequenceCompilation.Artifact fuel stmt) : Artifact 0 stmt :=
  Artifact.ofZero a.compiled.profile a.code a.source_to_model
    (LetSequenceCompletion.artifact_reflected a)

abbrev Image (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.Image (encode (fuel := fuel) (stmt := stmt))

theorem source_roundtrip (a : LetSequenceCompilation.Artifact fuel stmt) :
    Artifact.fromImage (Artifact.toImage encode a) = a := Artifact.source_roundtrip encode a

theorem image_roundtrip (a : Image fuel stmt) :
    Artifact.toImage encode (Artifact.fromImage a) = a := Artifact.image_roundtrip a

/-- Accepted sequence evidence consists only of selected scopes and their
concatenations. Unlike a raw guard, it cannot have code-selection refusal. -/
theorem code_total (a : LetSequenceCompilation.Compiled fuel stmt) :
    ∃ code, a.code = some code := by
  induction a with
  | scope artifact => exact ⟨artifact.code, rfl⟩
  | seq left right ihLeft ihRight =>
    obtain ⟨leftCode, leftSelected⟩ := ihLeft
    obtain ⟨rightCode, rightSelected⟩ := ihRight
    refine ⟨leftCode ++ rightCode, ?_⟩
    change (do
      let first ← left.code
      let second ← right.code
      pure (first ++ second)) = some (leftCode ++ rightCode)
    rw [leftSelected, rightSelected]
    rfl

noncomputable def encodeRaw (a : LetSequenceCompilation.Compiled fuel stmt) : Artifact 0 stmt :=
  Artifact.ofTotalSelection LetSequenceCompilation.Compiled.code
    (fun compiled code selected => encode ⟨compiled, code, selected⟩) code_total a

abbrev RawImage (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.Image (encodeRaw (fuel := fuel) (stmt := stmt))

theorem raw_source_roundtrip (a : LetSequenceCompilation.Compiled fuel stmt) :
    Artifact.fromImage (Artifact.toImage encodeRaw a) = a := Artifact.source_roundtrip encodeRaw a

theorem raw_image_roundtrip (a : RawImage fuel stmt) :
    Artifact.toImage encodeRaw (Artifact.fromImage a) = a := Artifact.image_roundtrip a

theorem raw_code_selected (a : LetSequenceCompilation.Compiled fuel stmt) :
    a.code = some (encodeRaw a).code := Classical.choose_spec (code_total a)

theorem code_ne_none (a : LetSequenceCompilation.Compiled fuel stmt) : a.code ≠ none := by
  obtain ⟨code, selected⟩ := code_total a
  rw [selected]
  intro impossible
  cases impossible

namespace Controls
theorem selected_model (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode LetSequenceCompilation.Controls.artifact).code
      {m with stack := coreWord b :: caller} =
      .ok {m with stack := coreWord (LetSequenceCompilation.Controls.update
        (LetSequenceCompilation.Controls.update b)) :: caller} 0 :=
  LetSequenceCompilation.Controls.target_done b m caller

theorem raw_model (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encodeRaw LetSequenceCompilation.Controls.artifact.compiled).code
      {m with stack := coreWord b :: caller} =
      .ok {m with stack := coreWord (LetSequenceCompilation.Controls.update
        (LetSequenceCompilation.Controls.update b)) :: caller} 0 := by
  have same : (encodeRaw LetSequenceCompilation.Controls.artifact.compiled).code =
      LetSequenceCompilation.Controls.artifact.code :=
    Option.some.inj ((raw_code_selected _).symm.trans LetSequenceCompilation.Controls.artifact.lowered)
  rw [same]
  exact LetSequenceCompilation.Controls.target_done b m caller

#guard (LetSequenceCompilation.compile 0 LetSequenceCompilation.Controls.source).isNone
#guard (LetSequenceCompilation.lower 2 LetScopeCompilation.Controls.beyondSource).isNone
end Controls

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_total
#print axioms encodeRaw
#print axioms raw_source_roundtrip
#print axioms raw_image_roundtrip
#print axioms raw_code_selected
#print axioms code_ne_none
#print axioms Controls.selected_model
#print axioms Controls.raw_model
#print axioms Artifact.select_total
end Solidity.Yul.Compilation.H55ControlFamilies.LetSequence

namespace Solidity.Yul.Compilation.H55ControlFamilies.LoopControl
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel depth : Nat} {stmt : Stmt [] [] c n}

def prepare (depth : Nat) (a : LoopControlCompilation.Compiled fuel stmt) :
    Option (Artifact depth stmt) :=
  Artifact.afterSelection (fun a : LoopControlCompilation.Compiled fuel stmt => a.emit depth) WordControl.blockCode
    (fun compiled block emitted code selected => encode ⟨compiled, block, code, emitted, selected⟩) a

abbrev Preparation (fuel depth : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.PreparationImage (prepare (fuel := fuel) (stmt := stmt) depth)

theorem selected (a : LoopControlCompilation.Artifact fuel stmt depth) :
    prepare depth a.compiled = some (encode a) :=
  Artifact.afterSelection_some _ _ _ a.compiled a.block a.code a.emitted a.selected

theorem emission_none (a : LoopControlCompilation.Compiled fuel stmt)
    (refused : a.emit depth = none) : prepare depth a = none :=
  Artifact.afterSelection_first_none (fun a : LoopControlCompilation.Compiled fuel stmt => a.emit depth) WordControl.blockCode
    (fun compiled block emitted code selected => encode ⟨compiled, block, code, emitted, selected⟩) a refused

theorem selection_none (a : LoopControlCompilation.Compiled fuel stmt) (block : Backend.Block)
    (emitted : a.emit depth = some block) (refused : WordControl.blockCode block = none) :
    prepare depth a = none :=
  Artifact.afterSelection_second_none (fun a : LoopControlCompilation.Compiled fuel stmt => a.emit depth) WordControl.blockCode
    (fun compiled block emitted code selected => encode ⟨compiled, block, code, emitted, selected⟩)
    a block emitted refused

namespace RawControls
theorem prepared : prepare 0 LoopControlCompilation.Controls.artifact.compiled =
    some (encode LoopControlCompilation.Controls.artifact) := selected _

theorem effectful (a b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode LoopControlCompilation.Controls.artifact).code
      {m with stack := [coreWord a, coreWord b] ++ caller} =
      .ok {m with stack := [coreWord 0, coreWord (~~~(~~~b+3)+3)] ++ caller} 0 :=
  LoopControlCompilation.Controls.target_done a b m caller

theorem refused_emission : LoopControlCompilation.Controls.artifact.compiled.emit 15 = none := rfl
theorem refused_preparation :
    (Artifact.toPreparationImage (prepare 15) LoopControlCompilation.Controls.artifact.compiled).artifact = none :=
  emission_none _ refused_emission

theorem refused_original : Artifact.recoverPreparation
    (Artifact.toPreparationImage (prepare 15) LoopControlCompilation.Controls.artifact.compiled) =
    LoopControlCompilation.Controls.artifact.compiled :=
  Artifact.preparation_source_roundtrip (prepare 15) _

theorem refused_source_completes (a b : Scalar.Word) :
    evalStmt 12 .nil True.intro LoopControlCompilation.Controls.source
      LoopControlCompilation.Controls.artifact.compiled.profile (sourceLocals #v[a,b]) =
      some ⟨sourceLocals #v[0,~~~(~~~b+3)+3], .normal⟩ :=
  LoopControlCompilation.Controls.source_done a b
end RawControls

#print axioms prepare
#print axioms selected
#print axioms emission_none
#print axioms selection_none
#print axioms RawControls.prepared
#print axioms RawControls.effectful
#print axioms RawControls.refused_emission
#print axioms RawControls.refused_preparation
#print axioms RawControls.refused_original
#print axioms RawControls.refused_source_completes
end Solidity.Yul.Compilation.H55ControlFamilies.LoopControl

namespace Solidity.Yul.Compilation.H55ControlFamilies.MultiSwitch
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}

def encode (a : MultiSwitchCompilation.Artifact fuel stmt) : Artifact 0 stmt :=
  Artifact.ofZero a.compiled.profile a.code a.source_to_model
    (MultiSwitchCompletion.model_to_source a)

abbrev Image (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.Image (encode (fuel := fuel) (stmt := stmt))

theorem source_roundtrip (a : MultiSwitchCompilation.Artifact fuel stmt) :
    Artifact.fromImage (Artifact.toImage encode a) = a := Artifact.source_roundtrip encode a

theorem image_roundtrip (a : Image fuel stmt) :
    Artifact.toImage encode (Artifact.fromImage a) = a := Artifact.image_roundtrip a

def prepare (a : MultiSwitchCompilation.Compiled fuel stmt) : Option (Artifact 0 stmt) :=
  Artifact.afterSelection (fun a : MultiSwitchCompilation.Compiled fuel stmt => a.emit) WordControl.blockCode
    (fun compiled block emitted code selected => encode ⟨compiled, block, code, emitted, selected⟩) a

abbrev Preparation (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.PreparationImage (prepare (fuel := fuel) (stmt := stmt))

theorem selected (a : MultiSwitchCompilation.Artifact fuel stmt) : prepare a.compiled = some (encode a) :=
  Artifact.afterSelection_some _ _ _ a.compiled a.block a.code a.emitted a.selected

theorem emission_none (a : MultiSwitchCompilation.Compiled fuel stmt) (refused : a.emit = none) :
    prepare a = none :=
  Artifact.afterSelection_first_none (fun a : MultiSwitchCompilation.Compiled fuel stmt => a.emit)
    WordControl.blockCode
    (fun compiled block emitted code selected => encode ⟨compiled, block, code, emitted, selected⟩) a refused

theorem selection_none (a : MultiSwitchCompilation.Compiled fuel stmt) (block : Backend.Block)
    (emitted : a.emit = some block) (refused : WordControl.blockCode block = none) : prepare a = none :=
  Artifact.afterSelection_second_none (fun a : MultiSwitchCompilation.Compiled fuel stmt => a.emit)
    WordControl.blockCode
    (fun compiled block emitted code selected => encode ⟨compiled, block, code, emitted, selected⟩)
    a block emitted refused

namespace Controls
theorem first_model (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode MultiSwitchCompilation.Controls.artifact).code
      {m with stack := coreWord 0 :: coreWord b :: caller} =
      .ok {m with stack := coreWord 0 :: coreWord (b+3) :: caller} 0 :=
  MultiSwitchCompilation.Controls.first_target b m caller

theorem later_model (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode MultiSwitchCompilation.Controls.artifact).code
      {m with stack := coreWord SourceLoop.Controls.dirty :: coreWord b :: caller} =
      .ok {m with stack := coreWord (ScopedControlCompilation.Controls.update SourceLoop.Controls.dirty) :: coreWord b :: caller} 0 :=
  MultiSwitchCompilation.Controls.later_target b m caller

theorem alias_default_model (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode MultiSwitchCompilation.Controls.artifact).code
      {m with stack := coreWord SwitchCompilation.Controls.lowOnly :: coreWord b :: caller} =
      .ok {m with stack := coreWord SwitchCompilation.Controls.lowOnly :: coreWord b :: caller} 0 :=
  MultiSwitchCompilation.Controls.alias_target b m caller

theorem prepared : prepare MultiSwitchCompilation.Controls.artifact.compiled =
    some (encode MultiSwitchCompilation.Controls.artifact) := selected _

def refusedSource : Stmt [] [] SourceLoop.Controls.root 17 := .switch (.local 16) .nil .skip
def refusedRaw : MultiSwitchCompilation.Compiled 2 refusedSource :=
  (MultiSwitchCompilation.compile 2 refusedSource).get (by rfl)
theorem refused_emission : refusedRaw.emit = none := rfl
theorem refused_preparation : (Artifact.toPreparationImage prepare refusedRaw).artifact = none :=
  emission_none _ refused_emission
theorem refused_original : Artifact.recoverPreparation (Artifact.toPreparationImage prepare refusedRaw) =
    refusedRaw := Artifact.preparation_source_roundtrip prepare refusedRaw
theorem source_completes :
    evalStmt 2 .nil True.intro refusedSource refusedRaw.profile (sourceLocals (Vector.replicate 17 0)) =
      some ⟨sourceLocals (Vector.replicate 17 0), .normal⟩ := rfl
#guard (MultiSwitchCompilation.compile 0 MultiSwitchCompilation.Controls.source).isNone
end Controls

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms prepare
#print axioms selected
#print axioms emission_none
#print axioms selection_none
#print axioms Artifact.preparation_image_roundtrip
#print axioms Controls.first_model
#print axioms Controls.later_model
#print axioms Controls.alias_default_model
#print axioms Controls.prepared
#print axioms Controls.refused_emission
#print axioms Controls.refused_preparation
#print axioms Controls.refused_original
#print axioms Controls.source_completes
end Solidity.Yul.Compilation.H55ControlFamilies.MultiSwitch

namespace Solidity.Yul.Compilation.H55ControlFamilies.Statements
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel depth : Nat} {stmt : Stmt [] [] c n}

def certify (a : ProducerStatements.Compiled fuel stmt) (depth : Nat) (program : Backend.Program)
    (code : List Evm.Instr) (emitted : a.lowered.code depth = some program)
    (selected : WordMachine.selectCode program = some code) : Artifact depth stmt :=
  Artifact.ofTotalRun a.profile code fuel a.update a.source
    (WordExecution.loweredStmt_machine a.lowered depth program code emitted selected)

def prepare (depth : Nat) (a : ProducerStatements.Compiled fuel stmt) : Option (Artifact depth stmt) :=
  Artifact.afterSelection (fun a : ProducerStatements.Compiled fuel stmt => a.lowered.code depth)
    WordMachine.selectCode
    (fun compiled program emitted code selected => certify compiled depth program code emitted selected) a

abbrev Preparation (fuel depth : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.PreparationImage (prepare (fuel := fuel) (stmt := stmt) depth)

theorem prepared (a : ProducerStatements.Compiled fuel stmt) (program : Backend.Program)
    (code : List Evm.Instr) (emitted : a.lowered.code depth = some program)
    (selected : WordMachine.selectCode program = some code) :
    prepare depth a = some (certify a depth program code emitted selected) :=
  Artifact.afterSelection_some _ _ _ a program code emitted selected

theorem emission_none (a : ProducerStatements.Compiled fuel stmt)
    (refused : a.lowered.code depth = none) : prepare depth a = none :=
  Artifact.afterSelection_first_none
    (fun a : ProducerStatements.Compiled fuel stmt => a.lowered.code depth) WordMachine.selectCode
    (fun compiled program emitted code selected => certify compiled depth program code emitted selected) a refused

namespace Controls
def source : Stmt [] [] SourceLoop.Controls.root 1 :=
  .assign (fun _ : Fin 1 => .local 0)
    (.builtin (.pure .add) (Fin.cases (.local 0) (fun _ => .literal 3)))
def producer : ProducerStatements.Compiled 3 source := (ProducerStatements.compile 3 source).get (by rfl)
def program := (producer.lowered.code 2).get (by rfl)
def code := (WordMachine.selectCode program).get (by rfl)
def artifact : Artifact 2 source := certify producer 2 program code rfl rfl

theorem selected : prepare 2 producer = some artifact := prepared _ _ _ rfl rfl

theorem effectful (locals : Vector Scalar.Word 1) (newer : Vector Scalar.Word 2)
    (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run artifact.code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
      .ok {m with stack := (newer.toList ++ (producer.update locals).toList).map coreWord ++ caller} 0 :=
  artifact.normal_to_model 3 locals (producer.update locals) (producer.source locals) newer m caller

#guard producer.update #v[7] = #v[10]
theorem refused_emission : producer.lowered.code 16 = none := rfl
theorem refused_preparation : (Artifact.toPreparationImage (prepare 16) producer).artifact = none :=
  emission_none _ refused_emission
theorem refused_original : Artifact.recoverPreparation
    (Artifact.toPreparationImage (prepare 16) producer) = producer :=
  Artifact.preparation_source_roundtrip (prepare 16) producer
theorem source_completes (locals : Vector Scalar.Word 1) :
    evalStmt 3 .nil True.intro source producer.profile (sourceLocals locals) =
      some ⟨sourceLocals (producer.update locals), .normal⟩ := producer.source locals
#guard (ProducerStatements.compile 0 source).isNone
end Controls

#print axioms Artifact.ofTotalRun
#print axioms certify
#print axioms prepare
#print axioms prepared
#print axioms emission_none
#print axioms Controls.selected
#print axioms Controls.effectful
#print axioms Controls.refused_emission
#print axioms Controls.refused_preparation
#print axioms Controls.refused_original
#print axioms Controls.source_completes
end Solidity.Yul.Compilation.H55ControlFamilies.Statements

/-! Open producers retain their actual existing WordAdapter program as the
common closed-source payload. Original open evaluation and projected state
are related explicitly below; no new packing or post-state encoding law. -/
namespace Solidity.Yul.Compilation.H55ControlFamilies.OpenStatement
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {X : List ExternalType} {c : Control} {n fuel depth : Nat}
    {stmt : Stmt [] X c n} {policy : Policy.StmtP .A stmt}

def prepare (depth : Nat) (a : OpenStatements.Compiled fuel stmt policy) :
    Option (Artifact depth (WordAdapter.program stmt policy).code) :=
  Statements.prepare depth a.packed

abbrev Preparation (fuel depth : Nat) (stmt : Stmt [] X c n) (policy : Policy.StmtP .A stmt) :=
  Artifact.PreparationImage (prepare (fuel := fuel) (stmt := stmt) (policy := policy) depth)

theorem prepared (a : OpenStatements.Compiled fuel stmt policy) (program : Backend.Program)
    (code : List Evm.Instr) (emitted : a.packed.lowered.code depth = some program)
    (selected : WordMachine.selectCode program = some code) :
    prepare depth a = some (Statements.certify a.packed depth program code emitted selected) :=
  Statements.prepared a.packed program code emitted selected

/-- The original source result is projected with the original unpacker.
The target observation is the exact packed update, not an unproved equality
between repacking that projection and every raw target word. -/
theorem actual_source_model (a : OpenStatements.Compiled fuel stmt policy)
    (program : Backend.Program) (code : List Evm.Instr)
    (emitted : a.packed.lowered.code depth = some program)
    (selected : WordMachine.selectCode program = some code)
    (state : WordState X n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word) :
    DirectBindings.eval fuel a.support policy state = some ⟨OpenStatements.updated a state, .normal⟩ ∧
    Evm.run code {m with stack := (newer.toList ++ (OpenExpressions.encoded state).toList).map coreWord ++ caller} =
      .ok {m with stack := (newer.toList ++
        (a.packed.update (OpenExpressions.encoded state)).toList).map coreWord ++ caller} 0 :=
  ⟨OpenStatements.source a state,
    WordExecution.loweredStmt_machine a.packed.lowered depth program code emitted selected
      (OpenExpressions.encoded state) newer m caller⟩

theorem actual_model_source (a : OpenStatements.Compiled fuel stmt policy)
    (program : Backend.Program) (code : List Evm.Instr)
    (emitted : a.packed.lowered.code depth = some program)
    (selected : WordMachine.selectCode program = some code)
    (state : WordState X n) (newer : Vector Scalar.Word depth)
    (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
    (ran : Evm.run code
      {m with stack := (newer.toList ++ (OpenExpressions.encoded state).toList).map coreWord ++ caller} =
      .ok final skip) :
    DirectBindings.eval fuel a.support policy state = some ⟨OpenStatements.updated a state, .normal⟩ ∧
      skip = 0 ∧ final = {m with stack := (newer.toList ++
        (a.packed.update (OpenExpressions.encoded state)).toList).map coreWord ++ caller} := by
  obtain ⟨source, model⟩ := actual_source_model a program code emitted selected state newer m caller
  have same := Evm.Out.ok.inj (model.symm.trans ran)
  exact ⟨source, same.2.symm, same.1.symm⟩

namespace Controls
open OpenExpressions.Controls (types flag state)
def source : Stmt [] types SourceLoop.Controls.root 1 :=
  .assign (fun _ : Fin 1 => .external flag.writeRef) (.local 0)
def sourcePolicy : Policy.StmtP .A source := by apply (Policy.stmt_iff .A _).mp; rfl
def producer : OpenStatements.Compiled 2 source sourcePolicy := (OpenStatements.compile 2 source sourcePolicy).get (by rfl)
def program := (producer.packed.lowered.code 0).get (by rfl)
def code := (WordMachine.selectCode program).get (by rfl)

theorem selected : prepare 0 producer = some (Statements.certify producer.packed 0 program code rfl rfl) :=
  prepared _ _ _ rfl rfl

theorem source_effect : (OpenStatements.updated producer state).cells flag = word 7 := by decide

theorem machine_source (input : WordState types 1) (m : Evm.Machine) (caller : List Evm.Word) :
    DirectBindings.eval 2 producer.support sourcePolicy input = some ⟨OpenStatements.updated producer input, .normal⟩ ∧
    Evm.run code {m with stack := (OpenExpressions.encoded input).toList.map coreWord ++ caller} =
      .ok {m with stack := (producer.packed.update (OpenExpressions.encoded input)).toList.map coreWord ++ caller} 0 := by
  simpa only [Vector.toList_empty, List.nil_append] using
    actual_source_model producer program code rfl rfl input #v[] m caller

theorem refused_emission : producer.packed.lowered.code 16 = none := rfl
theorem refused_preparation : (Artifact.toPreparationImage (prepare 16) producer).artifact = none :=
  Statements.emission_none producer.packed refused_emission
theorem refused_original : Artifact.recoverPreparation
    (Artifact.toPreparationImage (prepare 16) producer) = producer :=
  Artifact.preparation_source_roundtrip (prepare 16) producer

theorem source_completes (input : WordState types 1) :
    DirectBindings.eval 2 producer.support sourcePolicy input = some ⟨OpenStatements.updated producer input, .normal⟩ :=
  OpenStatements.source producer input
#guard (OpenStatements.compile 0 source sourcePolicy).isNone
end Controls

#print axioms prepare
#print axioms prepared
#print axioms actual_source_model
#print axioms actual_model_source
#print axioms Controls.selected
#print axioms Controls.source_effect
#print axioms Controls.machine_source
#print axioms Controls.refused_emission
#print axioms Controls.refused_preparation
#print axioms Controls.refused_original
#print axioms Controls.source_completes
end Solidity.Yul.Compilation.H55ControlFamilies.OpenStatement

/-! Expressions instantiate the shared typed-result certificate. The original
expression evaluator is retained, including its arity witness and profile;
no assignment wrapper or alternative source computation is substituted. -/
namespace Solidity.Yul.Compilation.H55ControlFamilies.Expressions
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {n r fuel depth : Nat} {expr : Expr [] [] n r}

abbrev Frame (depth : Nat) := Vector Scalar.Word depth × Evm.Machine × List Evm.Word

def inputFrame (locals : Vector Scalar.Word n) (frame : Frame depth) : Evm.Machine :=
  {frame.2.1 with stack := (frame.1.toList ++ locals.toList).map coreWord ++ frame.2.2}

def outputFrame (a : Compiled fuel expr) (locals : Vector Scalar.Word n)
    (result : Values r) (frame : Frame depth) : Evm.Machine :=
  {frame.2.1 with stack := coreWord (BitVec.ofFin (result (Fin.cast a.one.symm 0))) ::
    ((frame.1.toList ++ locals.toList).map coreWord ++ frame.2.2)}

def certify (a : Compiled fuel expr) (depth : Nat) (program : Backend.Program)
    (code : List Evm.Instr) (emitted : a.lowered.code depth = some program)
    (selected : WordMachine.selectCode program = some code) :
    Artifact.Realization
      (fun locals => evalExpr fuel .nil True.intro expr a.profile (sourceLocals locals))
      (inputFrame (depth := depth)) (outputFrame a) :=
  Artifact.Realization.ofTotalRun code (fun locals _ => (a.value locals).toFin) a.source
    (fun locals frame => WordExecution.loweredExpr_machine a.lowered depth program code
      emitted selected locals frame.1 frame.2.1 frame.2.2)

def prepare (depth : Nat) (a : Compiled fuel expr) :=
  Artifact.prepareResult (fun a : Compiled fuel expr => a.lowered.code depth)
    WordMachine.selectCode
    (fun a program emitted code selected => certify a depth program code emitted selected) a

abbrev Preparation (fuel depth : Nat) (expr : Expr [] [] n r) :=
  Artifact.ResultImage (prepare (fuel := fuel) (expr := expr) depth)

theorem prepared (a : Compiled fuel expr) (program : Backend.Program)
    (code : List Evm.Instr) (emitted : a.lowered.code depth = some program)
    (selected : WordMachine.selectCode program = some code) :
    prepare depth a = some (certify a depth program code emitted selected) :=
  Artifact.prepareResult_some _ _ _ a program code emitted selected

theorem emission_none (a : Compiled fuel expr) (refused : a.lowered.code depth = none) :
    prepare depth a = none :=
  Artifact.prepareResult_none
    (fun a : Compiled fuel expr => a.lowered.code depth) WordMachine.selectCode
    (fun a program emitted code selected => certify a depth program code emitted selected) a refused

namespace Controls
def source : Expr [] [] 1 1 :=
  .builtin (.pure .add) (Fin.cases (.local 0) (fun _ => .literal 3))
def producer : Compiled 2 source := (ProducerExpressions.compile 2 source).get (by rfl)
def program := (producer.lowered.code 2).get (by rfl)
def code := (WordMachine.selectCode program).get (by rfl)
def artifact := certify producer 2 program code rfl rfl

theorem selected : prepare 2 producer = some artifact := prepared _ _ _ rfl rfl

theorem effectful (locals : Vector Scalar.Word 1) (newer : Vector Scalar.Word 2)
    (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run artifact.code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
      .ok {m with stack := coreWord (producer.value locals) ::
        ((newer.toList ++ locals.toList).map coreWord ++ caller)} 0 :=
  artifact.source_to_model locals (fun _ => (producer.value locals).toFin)
    (producer.source locals) (newer, m, caller)

theorem reflected (locals : Vector Scalar.Word 1) (frame : Frame 2)
    (final : Evm.Machine) (skip : Nat)
    (ran : Evm.run artifact.code (inputFrame locals frame) = .ok final skip) :
    ∃ result, evalExpr 2 .nil True.intro source producer.profile (sourceLocals locals) = some result ∧
      skip = 0 ∧ final = outputFrame producer locals result frame :=
  artifact.model_to_source locals frame final skip ran

#guard producer.value #v[7] = 10

theorem refused_emission : producer.lowered.code 16 = none := rfl
theorem refused_preparation : (Artifact.toResultImage (prepare 16) producer).payload = none :=
  emission_none producer refused_emission
theorem refused_original : Artifact.recoverResult
    (Artifact.toResultImage (prepare 16) producer) = producer :=
  Artifact.result_source_roundtrip (prepare 16) producer

theorem source_completes (locals : Vector Scalar.Word 1) :
    evalExpr 2 .nil True.intro source producer.profile (sourceLocals locals) =
      some (fun _ => (producer.value locals).toFin) := producer.source locals
#guard (ProducerExpressions.compile 0 source).isNone
end Controls

#print axioms certify
#print axioms prepare
#print axioms prepared
#print axioms emission_none
#print axioms Controls.selected
#print axioms Controls.effectful
#print axioms Controls.reflected
#print axioms Controls.refused_emission
#print axioms Controls.refused_preparation
#print axioms Controls.refused_original
#print axioms Controls.source_completes
#print axioms Artifact.Realization.ofTotalRun
#print axioms Artifact.prepareResult
#print axioms Artifact.prepareResult_none
#print axioms Artifact.prepareResult_some
#print axioms Artifact.result_source_roundtrip
#print axioms Artifact.result_image_roundtrip
end Solidity.Yul.Compilation.H55ControlFamilies.Expressions

/-! Actual selected sequence leaves and concatenations have total selection.
This is accepted-object totality, not visitor admission or source termination. -/
namespace Solidity.Yul.Compilation.H55ControlFamilies.Sequence
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}

def encode (a : SequenceCompilation.Artifact fuel stmt) : Artifact 0 stmt :=
  Artifact.ofZero a.compiled.profile a.code
    (SequenceCompilation.source_to_model a.compiled a.block a.code a.emitted a.selected)
    (SequenceCompletion.artifact_reflected a)

abbrev Image (fuel : Nat) (stmt : Stmt [] [] c n) := Artifact.Image (encode (fuel := fuel) (stmt := stmt))

theorem source_roundtrip (a : SequenceCompilation.Artifact fuel stmt) :
    Artifact.fromImage (Artifact.toImage encode a) = a := Artifact.source_roundtrip encode a

theorem image_roundtrip (a : Image fuel stmt) :
    Artifact.toImage encode (Artifact.fromImage a) = a := Artifact.image_roundtrip a

theorem code_total (a : SequenceCompilation.Compiled c fuel stmt) :
    ∃ block code, a.emit = some block ∧ WordControl.blockCode block = some code := by
  induction a with
  | scopeLeaf artifact => exact ⟨artifact.block, artifact.code, rfl, artifact.selected⟩
  | switch_ artifact => exact ⟨artifact.block, artifact.code, rfl, artifact.selected⟩
  | seq left right ihLeft ihRight =>
    obtain ⟨a, qa, ha, sa⟩ := ihLeft
    obtain ⟨b, qb, hb, sb⟩ := ihRight
    refine ⟨.seq a b, qa ++ qb, ?_, ?_⟩
    · change (do
        let a ← left.emit
        let b ← right.emit
        pure (Backend.Block.seq a b)) = some (.seq a b)
      rw [ha, hb]
      rfl
    · change (WordControl.blockCode a).bind (fun qa =>
        (WordControl.blockCode b).map (fun qb => qa ++ qb)) = some (qa ++ qb)
      rw [sa, sb]
      rfl

def selectRaw (a : SequenceCompilation.Compiled c fuel stmt) :
    Option (SequenceCompilation.Artifact fuel stmt) :=
  Artifact.prepareResult (P := fun _ => SequenceCompilation.Artifact fuel stmt)
    SequenceCompilation.Compiled.emit WordControl.blockCode
    (fun compiled block emitted code selected => ⟨compiled, block, code, emitted, selected⟩) a

theorem selectRaw_some (a : SequenceCompilation.Artifact fuel stmt) :
    selectRaw a.compiled = some a :=
  Artifact.prepareResult_some _ _ _ a.compiled a.block a.code a.emitted a.selected

theorem selection_total (a : SequenceCompilation.Compiled c fuel stmt) :
    ∃ payload, selectRaw a = some payload := by
  obtain ⟨block, code, emitted, selected⟩ := code_total a
  exact ⟨⟨a, block, code, emitted, selected⟩,
    Artifact.prepareResult_some _ _ _ a block code emitted selected⟩

noncomputable def encodeRaw (a : SequenceCompilation.Compiled c fuel stmt) : Artifact 0 stmt :=
  Artifact.ofTotalSelection selectRaw (fun _ payload _ => encode payload) selection_total a

abbrev RawImage (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.Image (encodeRaw (fuel := fuel) (stmt := stmt))

theorem raw_source_roundtrip (a : SequenceCompilation.Compiled c fuel stmt) :
    Artifact.fromImage (Artifact.toImage encodeRaw a) = a := Artifact.source_roundtrip encodeRaw a

theorem raw_image_roundtrip (a : RawImage fuel stmt) :
    Artifact.toImage encodeRaw (Artifact.fromImage a) = a := Artifact.image_roundtrip a

theorem selected_raw (a : SequenceCompilation.Artifact fuel stmt) :
    encodeRaw a.compiled = encode a := by
  have total := Artifact.select_total selectRaw (fun _ payload _ => encode payload) selection_total a.compiled
  have selected := Artifact.select_some selectRaw (fun _ payload _ => encode payload)
    a.compiled a (selectRaw_some a)
  exact Option.some.inj (total.symm.trans selected)

theorem no_accepted_refusal (a : SequenceCompilation.Compiled c fuel stmt) : selectRaw a ≠ none := by
  obtain ⟨payload, selected⟩ := selection_total a
  intro refused
  cases selected.symm.trans refused

namespace Controls
theorem raw_effectful (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encodeRaw SequenceCompilation.Controls.artifact.compiled).code
      {m with stack := coreWord 0 :: coreWord 0 :: caller} =
      .ok {m with stack := coreWord 0 :: coreWord 9 :: caller} 0 := by
  rw [selected_raw]
  exact SequenceCompilation.Controls.target_done m caller

theorem selected_effectful (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode SequenceCompilation.Controls.mixedArtifact).code
      {m with stack := coreWord 0 :: coreWord 0 :: caller} =
      .ok {m with stack := coreWord 0 :: coreWord 9 :: caller} 0 :=
  SequenceCompilation.Controls.mixed_target m caller

#guard (SequenceCompilation.compile 0 SequenceCompilation.Controls.source).isNone
#guard (SequenceCompilation.lower 1 SequenceCompilation.Controls.source).isNone
end Controls

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_total
#print axioms selectRaw
#print axioms selectRaw_some
#print axioms selection_total
#print axioms encodeRaw
#print axioms raw_source_roundtrip
#print axioms raw_image_roundtrip
#print axioms selected_raw
#print axioms no_accepted_refusal
#print axioms Controls.raw_effectful
#print axioms Controls.selected_effectful
end Solidity.Yul.Compilation.H55ControlFamilies.Sequence

/-! Structured binders reuse zero-prefix certificates and actual optional
emission; accepted guard/initializer objects may genuinely refuse emission. -/
namespace Solidity.Yul.Compilation.H55ControlFamilies.StructuredSequence
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}

def encode (a : StructuredSequenceCompilation.Artifact fuel stmt) : Artifact 0 stmt :=
  Artifact.ofZero a.compiled.profile a.code a.source_to_model
    (StructuredSequenceCompletion.artifact_reflected a)

abbrev Image (fuel : Nat) (stmt : Stmt [] [] c n) := Artifact.Image (encode (fuel := fuel) (stmt := stmt))

theorem source_roundtrip (a : StructuredSequenceCompilation.Artifact fuel stmt) :
    Artifact.fromImage (Artifact.toImage encode a) = a := Artifact.source_roundtrip encode a

theorem image_roundtrip (a : Image fuel stmt) :
    Artifact.toImage encode (Artifact.fromImage a) = a := Artifact.image_roundtrip a

def prepare (a : StructuredSequenceCompilation.Compiled c fuel stmt) : Option (Artifact 0 stmt) :=
  Artifact.afterSelection StructuredSequenceCompilation.Compiled.emit WordControl.blockCode
    (fun compiled block emitted code selected => encode ⟨compiled, block, code, emitted, selected⟩) a

abbrev Preparation (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.PreparationImage (prepare (fuel := fuel) (stmt := stmt))

theorem prepared (a : StructuredSequenceCompilation.Artifact fuel stmt) :
    prepare a.compiled = some (encode a) :=
  Artifact.afterSelection_some _ _ _ a.compiled a.block a.code a.emitted a.selected

namespace Controls
theorem selected : prepare StructuredSequenceCompilation.Controls.innerArtifact.compiled =
    some (encode StructuredSequenceCompilation.Controls.innerArtifact) := prepared _

theorem effectful (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode StructuredSequenceCompilation.Controls.innerArtifact).code
      {m with stack := coreWord 0 :: caller} = .ok {m with stack := coreWord 9 :: caller} 0 :=
  StructuredSequenceCompilation.Controls.inner_target m caller

theorem false_identity (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode StructuredSequenceCompilation.Controls.falseArtifact).code
      {m with stack := coreWord 0 :: caller} = .ok {m with stack := coreWord 0 :: caller} 0 :=
  StructuredSequenceCompilation.Controls.false_target m caller

theorem outer_retirement (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode StructuredSequenceCompilation.Controls.artifact).code
      {m with stack := caller} = .ok {m with stack := caller} 0 :=
  StructuredSequenceCompilation.Controls.target_done m caller

def refusedSource : Stmt [] [] ⟨false, false⟩ 17 := .if_ (.local 16) .skip
def refused : StructuredSequenceCompilation.Compiled ⟨false, false⟩ 3 refusedSource :=
  (StructuredSequenceCompilation.compile 3 refusedSource).get (by rfl)
theorem refused_emission : refused.emit = none := rfl
theorem refused_preparation : (Artifact.toPreparationImage prepare refused).artifact = none :=
  Artifact.afterSelection_first_none StructuredSequenceCompilation.Compiled.emit WordControl.blockCode
    (fun compiled block emitted code selected => encode ⟨compiled, block, code, emitted, selected⟩)
    refused refused_emission

theorem refused_original : Artifact.recoverPreparation
    (Artifact.toPreparationImage prepare refused) = refused :=
  Artifact.preparation_source_roundtrip prepare refused

theorem source_completes : evalStmt 2 .nil True.intro refusedSource refused.profile
    (sourceLocals (Vector.replicate 17 0)) =
      some ⟨sourceLocals (Vector.replicate 17 0), .normal⟩ := rfl
#guard (StructuredSequenceCompilation.compile 0 refusedSource).isNone
end Controls

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms prepare
#print axioms prepared
#print axioms Controls.selected
#print axioms Controls.effectful
#print axioms Controls.false_identity
#print axioms Controls.outer_retirement
#print axioms Controls.refused_emission
#print axioms Controls.refused_preparation
#print axioms Controls.refused_original
#print axioms Controls.source_completes
end Solidity.Yul.Compilation.H55ControlFamilies.StructuredSequence

/-! One-case/default switches instantiate shared certificates and optional
preparation with original full-word selector and scoped arm evidence. -/
namespace Solidity.Yul.Compilation.H55ControlFamilies.Switch
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}

def encode (a : SwitchCompilation.Artifact fuel stmt) : Artifact 0 stmt :=
  Artifact.ofZero a.compiled.profile a.code a.source_to_model (SwitchCompletion.model_to_source a)

abbrev Image (fuel : Nat) (stmt : Stmt [] [] c n) := Artifact.Image (encode (fuel := fuel) (stmt := stmt))

theorem source_roundtrip (a : SwitchCompilation.Artifact fuel stmt) :
    Artifact.fromImage (Artifact.toImage encode a) = a := Artifact.source_roundtrip encode a

theorem image_roundtrip (a : Image fuel stmt) :
    Artifact.toImage encode (Artifact.fromImage a) = a := Artifact.image_roundtrip a

def prepare (a : SwitchCompilation.Compiled fuel stmt) : Option (Artifact 0 stmt) :=
  Artifact.afterSelection SwitchCompilation.Compiled.emit WordControl.blockCode
    (fun compiled block emitted code selected => encode ⟨compiled, block, code, emitted, selected⟩) a

abbrev Preparation (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.PreparationImage (prepare (fuel := fuel) (stmt := stmt))

theorem prepared (a : SwitchCompilation.Artifact fuel stmt) :
    prepare a.compiled = some (encode a) :=
  Artifact.afterSelection_some _ _ _ a.compiled a.block a.code a.emitted a.selected

namespace Controls
theorem selected : prepare SwitchCompilation.Controls.artifact.compiled =
    some (encode SwitchCompilation.Controls.artifact) := prepared _

theorem matching (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode SwitchCompilation.Controls.artifact).code
      {m with stack := coreWord SourceLoop.Controls.dirty :: coreWord c :: caller} =
      .ok {m with stack := coreWord (ScopedControlCompilation.Controls.update SourceLoop.Controls.dirty) :: coreWord c :: caller} 0 := SwitchCompilation.Controls.matching_target c m caller

theorem default (b c : Scalar.Word) (different : b.toFin ≠ SourceLoop.Controls.dirty.toFin)
    (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode SwitchCompilation.Controls.artifact).code
      {m with stack := coreWord b :: coreWord c :: caller} =
      .ok {m with stack := coreWord b :: coreWord c :: caller} 0 :=
  SwitchCompilation.Controls.default_target b c different m caller

theorem low_alias_default (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode SwitchCompilation.Controls.artifact).code
      {m with stack := coreWord SwitchCompilation.Controls.lowOnly :: coreWord c :: caller} =
      .ok {m with stack := coreWord SwitchCompilation.Controls.lowOnly :: coreWord c :: caller} 0 :=
  SwitchCompilation.Controls.low_alias_target c m caller

def refusedSource : Stmt [] [] ⟨false, false⟩ 17 := .switch (.local 16) (.cons 0 .skip .nil) .skip
def refused : SwitchCompilation.Compiled 1 refusedSource :=
  (SwitchCompilation.compile 1 refusedSource).get (by rfl)
theorem refused_emission : refused.emit = none := rfl
theorem refused_preparation : (Artifact.toPreparationImage prepare refused).artifact = none :=
  Artifact.afterSelection_first_none SwitchCompilation.Compiled.emit WordControl.blockCode
    (fun compiled block emitted code selected => encode ⟨compiled, block, code, emitted, selected⟩)
    refused refused_emission

theorem refused_original : Artifact.recoverPreparation
    (Artifact.toPreparationImage prepare refused) = refused :=
  Artifact.preparation_source_roundtrip prepare refused

theorem source_completes : evalStmt 3 .nil True.intro refusedSource refused.profile
    (sourceLocals (Vector.replicate 17 0)) =
      some ⟨sourceLocals (Vector.replicate 17 0), .normal⟩ := rfl
#guard (SwitchCompilation.compile 0 refusedSource).isNone
#guard (SwitchCompilation.lower 10 SwitchCompilation.Controls.multipleSource).isNone
#guard (SwitchCompilation.lower 10 SwitchCompilation.Controls.emptySource).isNone
end Controls

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms prepare
#print axioms prepared
#print axioms Controls.selected
#print axioms Controls.matching
#print axioms Controls.default
#print axioms Controls.low_alias_default
#print axioms Controls.refused_emission
#print axioms Controls.refused_preparation
#print axioms Controls.refused_original
#print axioms Controls.source_completes
end Solidity.Yul.Compilation.H55ControlFamilies.Switch

/-! The common joined-sequence certificate retains full original component
data in its exact image; phase reflection remains explicitly available. -/
namespace Solidity.Yul.Compilation.H55ControlFamilies.SwitchSequence
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n f g : Nat} {left right : Stmt [] [] c n}

def encode (a : Compilation.SwitchSequence.Artifact f g left right) : Artifact 0 (.seq left right) :=
  Artifact.ofZero a.profile a.code a.source_to_model (by
    intro locals m final caller skip ran
    obtain ⟨ha, hb, mid, out, first, second, boundary, source, done, frame⟩ :=
      SwitchSequenceCompletion.model_to_source a locals m final caller skip ran
    exact ⟨max ha hb+1, out, source, done, frame⟩)

abbrev Image (f g : Nat) (left right : Stmt [] [] c n) :=
  Artifact.Image (encode (f := f) (g := g) (left := left) (right := right))

theorem source_roundtrip (a : Compilation.SwitchSequence.Artifact f g left right) :
    Artifact.fromImage (Artifact.toImage encode a) = a := Artifact.source_roundtrip encode a

theorem image_roundtrip (a : Image f g left right) :
    Artifact.toImage encode (Artifact.fromImage a) = a := Artifact.image_roundtrip a

theorem code_preserved (a : Compilation.SwitchSequence.Artifact f g left right) : (encode a).code = a.code := rfl

theorem components_preserved (a : Compilation.SwitchSequence.Artifact f g left right) :
    (Artifact.fromImage (Artifact.toImage encode a)).left = a.left ∧
    (Artifact.fromImage (Artifact.toImage encode a)).right = a.right := ⟨rfl, rfl⟩

/-- Preserve the stronger original observation of both source phases and the
actual intermediate machine frame, not just the common joined result. -/
theorem phase_reflection (a : Compilation.SwitchSequence.Artifact f g left right)
    (locals : Vector Scalar.Word n) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
    (ran : Evm.run (encode a).code {m with stack := locals.toList.map coreWord ++ caller} = .ok final skip) :
    ∃ (ha hb : Nat) (mid out : Vector Scalar.Word n),
      evalStmt ha .nil True.intro left a.left.compiled.profile (sourceLocals locals) =
        some ⟨sourceLocals mid, .normal⟩ ∧
      evalStmt hb .nil True.intro right a.right.compiled.profile (sourceLocals mid) =
        some ⟨sourceLocals out, .normal⟩ ∧
      Evm.run a.left.code {m with stack := locals.toList.map coreWord ++ caller} =
        .ok {m with stack := mid.toList.map coreWord ++ caller} 0 ∧
      evalStmt (max ha hb+1) .nil True.intro (.seq left right) a.profile (sourceLocals locals) =
        some ⟨sourceLocals out, .normal⟩ ∧
      skip = 0 ∧ final = {m with stack := out.toList.map coreWord ++ caller} :=
  SwitchSequenceCompletion.model_to_source a locals m final caller skip ran

namespace Controls
theorem ordered (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode Compilation.SwitchSequence.Controls.artifact).code
      {m with stack := coreWord 0 :: coreWord 0 :: caller} =
      .ok {m with stack := coreWord 0 :: coreWord 6 :: caller} 0 :=
  Compilation.SwitchSequence.Controls.target_done m caller

#guard (Compilation.SwitchSequence.lower 0 12 MultiSwitchCompilation.Controls.source
  Compilation.SwitchSequence.Controls.second).isNone
#guard (Compilation.SwitchSequence.lower 12 0 MultiSwitchCompilation.Controls.source
  Compilation.SwitchSequence.Controls.second).isNone
end Controls

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_preserved
#print axioms components_preserved
#print axioms phase_reflection
#print axioms Controls.ordered
end Solidity.Yul.Compilation.H55ControlFamilies.SwitchSequence

/-! Zero/control accepted body evidence is already selected. Only the actual
prefix entry/retirement selector remains, and the shared laws prove it total. -/
namespace Solidity.Yul.Compilation.H55ControlFamilies.ZeroControl
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}

def encode (a : ZeroControlCompilation.Artifact fuel stmt) : Artifact 0 stmt :=
  Artifact.ofZero a.compiled.profile a.code a.source_to_model (ZeroControlCompletion.model_to_source a)

abbrev Image (fuel : Nat) (stmt : Stmt [] [] c n) := Artifact.Image (encode (fuel := fuel) (stmt := stmt))

theorem source_roundtrip (a : ZeroControlCompilation.Artifact fuel stmt) :
    Artifact.fromImage (Artifact.toImage encode a) = a := Artifact.source_roundtrip encode a

theorem image_roundtrip (a : Image fuel stmt) :
    Artifact.toImage encode (Artifact.fromImage a) = a := Artifact.image_roundtrip a

theorem code_total (a : ZeroControlCompilation.Compiled fuel stmt) : ∃ code, a.code = some code := by
  cases a with
  | @scope fresh bodyStmt body =>
    obtain ⟨begin, entering⟩ := Artifact.pushPrefix_selection_total
      (Vector.replicate fresh (0 : Scalar.Word)).toList
    change WordMachine.selectCode (ZeroLoopScope.entry fresh) = some begin at entering
    have exiting := Artifact.popPrefix_selected fresh
    refine ⟨begin ++ body.code ++ List.replicate fresh Evm.Instr.pop, ?_⟩
    change (do
      let begin ← WordMachine.selectCode (ZeroLoopScope.entry fresh)
      let finish ← WordMachine.selectCode (popPrefix fresh)
      pure (begin ++ body.code ++ finish)) = _
    rw [entering, exiting]
    rfl

noncomputable def encodeRaw (a : ZeroControlCompilation.Compiled fuel stmt) : Artifact 0 stmt :=
  Artifact.ofTotalSelection ZeroControlCompilation.Compiled.code
    (fun compiled code selected => encode ⟨compiled, code, selected⟩) code_total a

abbrev RawImage (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.Image (encodeRaw (fuel := fuel) (stmt := stmt))

theorem raw_source_roundtrip (a : ZeroControlCompilation.Compiled fuel stmt) :
    Artifact.fromImage (Artifact.toImage encodeRaw a) = a := Artifact.source_roundtrip encodeRaw a

theorem raw_image_roundtrip (a : RawImage fuel stmt) :
    Artifact.toImage encodeRaw (Artifact.fromImage a) = a := Artifact.image_roundtrip a

theorem selected_raw (a : ZeroControlCompilation.Artifact fuel stmt) : encodeRaw a.compiled = encode a := by
  have total := Artifact.select_total ZeroControlCompilation.Compiled.code
    (fun compiled code selected => encode ⟨compiled, code, selected⟩) code_total a.compiled
  have selected := Artifact.select_some ZeroControlCompilation.Compiled.code
    (fun compiled code selected => encode ⟨compiled, code, selected⟩) a.compiled a.code a.lowered
  exact Option.some.inj (total.symm.trans selected)

theorem no_accepted_refusal (a : ZeroControlCompilation.Compiled fuel stmt) : a.code ≠ none := by
  obtain ⟨code, selected⟩ := code_total a
  intro refused
  cases selected.symm.trans refused

namespace Controls
theorem effectful (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encodeRaw ZeroControlCompilation.Controls.artifact.compiled).code
      {m with stack := coreWord b :: caller} =
      .ok {m with stack := coreWord (ZeroControlCompilation.Controls.update b) :: caller} 0 := by
  rw [selected_raw]
  exact ZeroControlCompilation.Controls.target_done b m caller
#guard (ZeroControlCompilation.lower 0 ZeroControlCompilation.Controls.source).isNone
#guard (ZeroControlCompilation.lower 9 ZeroControlCompilation.Controls.beyondSource).isNone
end Controls

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_total
#print axioms encodeRaw
#print axioms raw_source_roundtrip
#print axioms raw_image_roundtrip
#print axioms selected_raw
#print axioms no_accepted_refusal
#print axioms Controls.effectful
#print axioms Artifact.selectCode_append
#print axioms Artifact.pushPrefix_selection_total
#print axioms Artifact.popPrefix_selected
end Solidity.Yul.Compilation.H55ControlFamilies.ZeroControl

/-! The other accepted zero-body family reuses the same prefix totality. -/
namespace Solidity.Yul.Compilation.H55ControlFamilies.ZeroScope
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}

def encode (a : ZeroScopeCompilation.Artifact fuel stmt) : Artifact 0 stmt :=
  Artifact.ofZero a.compiled.profile a.code (by
    rcases a with ⟨compiled, code, lowered⟩
    cases compiled with
    | scope body => exact ZeroLoopScope.source_to_model body code lowered) a.reflected

abbrev Image (fuel : Nat) (stmt : Stmt [] [] c n) := Artifact.Image (encode (fuel := fuel) (stmt := stmt))

theorem source_roundtrip (a : ZeroScopeCompilation.Artifact fuel stmt) :
    Artifact.fromImage (Artifact.toImage encode a) = a := Artifact.source_roundtrip encode a

theorem image_roundtrip (a : Image fuel stmt) :
    Artifact.toImage encode (Artifact.fromImage a) = a := Artifact.image_roundtrip a

theorem code_total (a : ZeroScopeCompilation.Compiled fuel stmt) : ∃ code, a.code = some code := by
  cases a with
  | @scope fresh bodyStmt body =>
    obtain ⟨begin, entering⟩ := Artifact.pushPrefix_selection_total
      (Vector.replicate fresh (0 : Scalar.Word)).toList
    change WordMachine.selectCode (ZeroLoopScope.entry fresh) = some begin at entering
    have exiting := Artifact.popPrefix_selected fresh
    refine ⟨begin ++ body.code ++ List.replicate fresh Evm.Instr.pop, ?_⟩
    change (do
      let begin ← WordMachine.selectCode (ZeroLoopScope.entry fresh)
      let finish ← WordMachine.selectCode (popPrefix fresh)
      pure (begin ++ body.code ++ finish)) = _
    rw [entering, exiting]
    rfl

noncomputable def encodeRaw (a : ZeroScopeCompilation.Compiled fuel stmt) : Artifact 0 stmt :=
  Artifact.ofTotalSelection ZeroScopeCompilation.Compiled.code
    (fun compiled code selected => encode ⟨compiled, code, selected⟩) code_total a

abbrev RawImage (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.Image (encodeRaw (fuel := fuel) (stmt := stmt))

theorem raw_source_roundtrip (a : ZeroScopeCompilation.Compiled fuel stmt) :
    Artifact.fromImage (Artifact.toImage encodeRaw a) = a := Artifact.source_roundtrip encodeRaw a

theorem raw_image_roundtrip (a : RawImage fuel stmt) :
    Artifact.toImage encodeRaw (Artifact.fromImage a) = a := Artifact.image_roundtrip a

theorem selected_raw (a : ZeroScopeCompilation.Artifact fuel stmt) : encodeRaw a.compiled = encode a := by
  have total := Artifact.select_total ZeroScopeCompilation.Compiled.code
    (fun compiled code selected => encode ⟨compiled, code, selected⟩) code_total a.compiled
  have selected := Artifact.select_some ZeroScopeCompilation.Compiled.code
    (fun compiled code selected => encode ⟨compiled, code, selected⟩) a.compiled a.code a.lowered
  exact Option.some.inj (total.symm.trans selected)

theorem no_accepted_refusal (a : ZeroScopeCompilation.Compiled fuel stmt) : a.code ≠ none := by
  obtain ⟨code, selected⟩ := code_total a
  intro refused
  cases selected.symm.trans refused

namespace Controls
theorem effectful (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encodeRaw ZeroScopeCompilation.Controls.artifact.compiled).code
      {m with stack := coreWord b :: caller} =
      .ok {m with stack := coreWord ((~~~(~~~b+3)+3)+3) :: caller} 0 := by
  rw [selected_raw]
  exact ZeroScopeCompilation.Controls.target b m caller
#guard (ZeroScopeCompilation.lower 0 ZeroScopeCompletion.Controls.retiringSource).isNone
#guard (ZeroScopeCompilation.lower 10 ZeroScopeCompilation.Controls.nestedSource).isNone
end Controls

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_total
#print axioms encodeRaw
#print axioms raw_source_roundtrip
#print axioms raw_image_roundtrip
#print axioms selected_raw
#print axioms no_accepted_refusal
#print axioms Controls.effectful
end Solidity.Yul.Compilation.H55ControlFamilies.ZeroScope

/-! Zero scopes around sequence bodies retain actual entry/body/exit evidence
through the generic certificate and exact original image. -/
namespace Solidity.Yul.Compilation.H55ControlFamilies.ZeroSequence
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fresh fuel : Nat} {body : Stmt [] [] c (fresh+n)}

def encode (a : ZeroSequenceCompilation.Artifact fresh fuel body) : Artifact 0 (.zero fresh body) :=
  Artifact.ofZero a.profile a.code a.source_to_model a.model_to_source

abbrev Image (fresh fuel : Nat) (body : Stmt [] [] c (fresh+n)) :=
  Artifact.Image (encode (fresh := fresh) (fuel := fuel) (body := body))

theorem source_roundtrip (a : ZeroSequenceCompilation.Artifact fresh fuel body) :
    Artifact.fromImage (Artifact.toImage encode a) = a := Artifact.source_roundtrip encode a

theorem image_roundtrip (a : Image fresh fuel body) :
    Artifact.toImage encode (Artifact.fromImage a) = a := Artifact.image_roundtrip a

theorem code_preserved (a : ZeroSequenceCompilation.Artifact fresh fuel body) : (encode a).code = a.code := rfl

theorem components_preserved (a : ZeroSequenceCompilation.Artifact fresh fuel body) :
    (Artifact.fromImage (Artifact.toImage encode a)).compiledBody = a.compiledBody ∧
    (Artifact.fromImage (Artifact.toImage encode a)).beginCode = a.beginCode ∧
    (Artifact.fromImage (Artifact.toImage encode a)).finishCode = a.finishCode := ⟨rfl, rfl, rfl⟩

namespace Controls
theorem outer_update (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode ZeroSequenceCompilation.Controls.one).code
      {m with stack := coreWord 0 :: caller} = .ok {m with stack := coreWord 9 :: caller} 0 :=
  ZeroSequenceCompilation.Controls.one_target m caller

theorem full_retirement (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode ZeroSequenceCompilation.Controls.two).code
      {m with stack := caller} = .ok {m with stack := caller} 0 :=
  ZeroSequenceCompilation.Controls.two_target m caller

#guard (ZeroSequenceCompilation.lower (n := 1) 1 0 ZeroSequenceCompilation.Controls.body).isNone
end Controls

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_preserved
#print axioms components_preserved
#print axioms Controls.outer_update
#print axioms Controls.full_retirement
end Solidity.Yul.Compilation.H55ControlFamilies.ZeroSequence
