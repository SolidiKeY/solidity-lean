import Solidity.Yul.Compilation.CompletionControls
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

theorem normal_to_model (artifact : Artifact depth stmt) (horizon : Nat)
    (locals out : Vector Scalar.Word n)
    (ran : evalStmt horizon .nil True.intro stmt artifact.profile (sourceLocals locals) =
      some ⟨sourceLocals out,.normal⟩) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run artifact.code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
      .ok {m with stack := (newer.toList ++ out.toList).map coreWord ++ caller} 0 := by
  obtain ⟨actual,same,target⟩ := artifact.source_to_model horizon locals ⟨sourceLocals out,.normal⟩ ran newer m caller
  have equal : out = actual := CompletionControls.sourceLocals_injective (congrArg Outcome.vars same)
  cases equal
  exact target

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
end Artifact
end Solidity.Yul.Compilation
