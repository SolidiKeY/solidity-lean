import tests.h55.«yul-artifact».PreparationImage
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let some info := env.find? ``Solidity.Yul.Compilation.Artifact.PreparationImage | throwError "missing declaration"
  logInfo m!"DECL Solidity.Yul.Compilation.Artifact.PreparationImage TYPE {repr info.type}"
  let some info := env.find? ``Solidity.Yul.Compilation.Artifact.PreparationImage.mk | throwError "missing declaration"
  logInfo m!"DECL Solidity.Yul.Compilation.Artifact.PreparationImage.mk TYPE {repr info.type}"
  let some info := env.find? ``Solidity.Yul.Compilation.Artifact.PreparationImage.original | throwError "missing declaration"
  logInfo m!"DECL Solidity.Yul.Compilation.Artifact.PreparationImage.original TYPE {repr info.type}"
  let some info := env.find? ``Solidity.Yul.Compilation.Artifact.PreparationImage.artifact | throwError "missing declaration"
  logInfo m!"DECL Solidity.Yul.Compilation.Artifact.PreparationImage.artifact TYPE {repr info.type}"
  let some info := env.find? ``Solidity.Yul.Compilation.Artifact.PreparationImage.agrees | throwError "missing declaration"
  logInfo m!"DECL Solidity.Yul.Compilation.Artifact.PreparationImage.agrees TYPE {repr info.type}"
  let some info := env.find? ``Solidity.Yul.Compilation.Artifact.toPreparationImage | throwError "missing declaration"
  logInfo m!"DECL Solidity.Yul.Compilation.Artifact.toPreparationImage TYPE {repr info.type}"
  let some info := env.find? ``Solidity.Yul.Compilation.Artifact.recoverPreparation | throwError "missing declaration"
  logInfo m!"DECL Solidity.Yul.Compilation.Artifact.recoverPreparation TYPE {repr info.type}"
  let some info := env.find? ``Solidity.Yul.Compilation.Artifact.preparation_source_roundtrip | throwError "missing declaration"
  logInfo m!"DECL Solidity.Yul.Compilation.Artifact.preparation_source_roundtrip TYPE {repr info.type}"
  let some info := env.find? ``Solidity.Yul.Compilation.Artifact.preparation_image_roundtrip | throwError "missing declaration"
  logInfo m!"DECL Solidity.Yul.Compilation.Artifact.preparation_image_roundtrip TYPE {repr info.type}"
#print axioms Solidity.Yul.Compilation.Artifact.preparation_source_roundtrip
#print axioms Solidity.Yul.Compilation.Artifact.preparation_image_roundtrip
