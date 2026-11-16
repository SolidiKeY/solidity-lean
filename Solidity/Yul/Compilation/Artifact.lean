import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.ClosedHorizon
/-! Intrinsic normal-completion artifact for the existing Yul/Compilation
source and model. Both directions retain the complete frame and newer prefix.
Concrete producer adapters must derive these fields from their existing proofs;
this type is not a new compiler or an assertion that every statement compiles.
Image retains original producer data for explicitly lossless transport. -/
namespace Solidity.Yul.Compilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

structure Artifact {c : Control} {n : Nat} (depth : Nat) (stmt : Stmt [] [] c n) where
  profile : StmtWordP stmt
  code : List Evm.Instr
  source_to_model : ∀ (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n),
    evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) = some result →
    ∀ (newer : Vector Scalar.Word depth) (m : Evm.Machine) (caller : List Evm.Word),
    ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
      Evm.run code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
        .ok {m with stack := (newer.toList ++ out.toList).map coreWord ++ caller} 0
  model_to_source : ∀ (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat),
    Evm.run code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} = .ok final skip →
    ∃ (horizon : Nat) (out : Vector Scalar.Word n),
      evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) =
        some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧
        final = {m with stack := (newer.toList ++ out.toList).map coreWord ++ caller}

namespace Artifact
variable {c : Control} {n depth : Nat} {stmt : Stmt [] [] c n}

/-- Reuse an existing empty-newer-prefix certificate without inventing a
stronger calling convention. The two laws retain every source horizon, local
word and arbitrary machine/caller frame. Other depths need their own proof. -/
def ofZero (profile : StmtWordP stmt) (code : List Evm.Instr)
    (forward : ∀ (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n),
      evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) = some result →
      ∀ (m : Evm.Machine) (caller : List Evm.Word),
      ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out, .normal⟩ ∧
        Evm.run code {m with stack := locals.toList.map coreWord ++ caller} =
          .ok {m with stack := out.toList.map coreWord ++ caller} 0)
    (backward : ∀ (locals : Vector Scalar.Word n) (m final : Evm.Machine)
      (caller : List Evm.Word) (skip : Nat),
      Evm.run code {m with stack := locals.toList.map coreWord ++ caller} = .ok final skip →
      ∃ (horizon : Nat) (out : Vector Scalar.Word n),
        evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) =
          some ⟨sourceLocals out, .normal⟩ ∧ skip = 0 ∧
          final = {m with stack := out.toList.map coreWord ++ caller}) : Artifact 0 stmt where
  profile := profile
  code := code
  source_to_model := by
    intro horizon locals result ran newer m caller
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    simpa only [empty, List.nil_append] using forward horizon locals result ran m caller
  model_to_source := by
    intro locals newer m final caller skip ran
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    simp only [empty, List.nil_append] at ran
    simpa only [empty, List.nil_append] using backward locals m final caller skip ran

/-- A proved total source update and its actual complete machine run give
both certificate directions. This is a proof combinator, not compiler totality. -/
def ofTotalRun (profile : StmtWordP stmt) (code : List Evm.Instr) (horizon : Nat)
    (update : Vector Scalar.Word n → Vector Scalar.Word n)
    (source : ∀ locals, evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) =
      some ⟨sourceLocals (update locals), .normal⟩)
    (model : ∀ (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
      (m : Evm.Machine) (caller : List Evm.Word),
      Evm.run code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
        .ok {m with stack := (newer.toList ++ (update locals).toList).map coreWord ++ caller} 0) :
    Artifact depth stmt where
  profile := profile
  code := code
  source_to_model := by
    intro actualHorizon locals result ran newer m caller
    exact ⟨update locals,
      evalStmt_completed_unique .nil True.intro stmt profile (sourceLocals locals) ran (source locals),
      model locals newer m caller⟩
  model_to_source := by
    intro locals newer m final caller skip ran
    have same := Evm.Out.ok.inj ((model locals newer m caller).symm.trans ran)
    exact ⟨horizon, update locals, source locals, same.2.symm, same.1.symm⟩

theorem normal_to_model (artifact : Artifact depth stmt) (horizon : Nat)
    (locals out : Vector Scalar.Word n)
    (ran : evalStmt horizon .nil True.intro stmt artifact.profile (sourceLocals locals) =
      some ⟨sourceLocals out,.normal⟩) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run artifact.code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
      .ok {m with stack := (newer.toList ++ out.toList).map coreWord ++ caller} 0 := by
  exact CompletionControls.normal_output out _
    (artifact.source_to_model horizon locals ⟨sourceLocals out,.normal⟩ ran newer m caller)

theorem completion_iff (artifact : Artifact depth stmt) (locals out : Vector Scalar.Word n)
    (newer : Vector Scalar.Word depth) (m : Evm.Machine) (caller : List Evm.Word) :
    (∃ horizon, evalStmt horizon .nil True.intro stmt artifact.profile (sourceLocals locals) =
      some ⟨sourceLocals out,.normal⟩) ↔
    Evm.run artifact.code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
      .ok {m with stack := (newer.toList ++ out.toList).map coreWord ++ caller} 0 :=
  CompletionControls.completion_iff stmt artifact.profile artifact.code
    artifact.normal_to_model artifact.model_to_source locals out newer m caller

/-- The exact image keeps the original constructor evidence, not just code. -/
structure Image {E : Type} (encode : E → Artifact depth stmt) where
  original : E
  artifact : Artifact depth stmt
  agrees : artifact = encode original

def toImage {E : Type} (encode : E → Artifact depth stmt) (original : E) : Image encode :=
  ⟨original,encode original,rfl⟩

def fromImage {E : Type} {encode : E → Artifact depth stmt} (image : Image encode) : E := image.original

theorem source_roundtrip {E : Type} (encode : E → Artifact depth stmt) (original : E) :
    fromImage (toImage encode original) = original := rfl

theorem image_roundtrip {E : Type} {encode : E → Artifact depth stmt} (image : Image encode) :
    toImage encode (fromImage image) = image := by
  rcases image with ⟨original,artifact,agrees⟩
  cases agrees
  rfl
/-- Typed result certificates extend the common interface to computations whose
stack effect differs from normal statement completion. Source, input and output
observations are the actual existing typed evaluators and machine frames; this
interface introduces no source syntax, state or compiler. -/
structure Realization {Input Output Frame : Type}
    (source : Input → Option Output) (before : Input → Frame → Evm.Machine)
    (after : Input → Output → Frame → Evm.Machine) where
  code : List Evm.Instr
  source_to_model : ∀ input output, source input = some output → ∀ frame,
    Evm.run code (before input frame) = .ok (after input output frame) 0
  model_to_source : ∀ input frame final skip,
    Evm.run code (before input frame) = .ok final skip →
    ∃ output, source input = some output ∧ skip = 0 ∧ final = after input output frame

namespace Realization
variable {Input Output Frame : Type} {source : Input → Option Output}
    {before : Input → Frame → Evm.Machine} {after : Input → Output → Frame → Evm.Machine}

/-- The result is constrained by the actual source evaluator. Full target
result injectivity reflects the complete machine and pending-skip observation. -/
def ofTotalRun (code : List Evm.Instr) (value : Input → Output)
    (sourceRun : ∀ input, source input = some (value input))
    (modelRun : ∀ input frame, Evm.run code (before input frame) =
      .ok (after input (value input) frame) 0) : Realization source before after where
  code := code
  source_to_model := by
    intro input output ran frame
    have same : value input = output := Option.some.inj ((sourceRun input).symm.trans ran)
    cases same
    exact modelRun input frame
  model_to_source := by
    intro input frame final skip ran
    have same := Evm.Out.ok.inj ((modelRun input frame).symm.trans ran)
    exact ⟨value input, sourceRun input, same.2.symm, same.1.symm⟩

end Realization
end Artifact
end Solidity.Yul.Compilation
