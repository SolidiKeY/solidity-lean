import Solidity.Yul.Compilation.Artifact

/-! Exact provenance for a producer stage before successful code selection.
The optional payload is the existing common Artifact, not another execution
state or semantics. None remains preparation failure, never a runtime verdict. -/
namespace Solidity.Yul.Compilation.Artifact
variable {c : Control} {n depth : Nat} {stmt : Stmt [] [] c n}

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
