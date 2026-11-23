import Solidity.Examples.ExecutableRequestData
import Solidity.Frontend.ExecutableCounterexampleMetadataV2

open Lean Elab Command Meta Solidity Solidity.Tools
namespace ExecutableBindingControls

def checkQuotation : CommandElabM Unit := do
  for type in [``RawTy, ``RawExpr, ``RawInv, ``RawLoopSpec, ``OFMode,
      ``RawStmt, ``SpecExpr, ``SpecLoc, ``FunSpec, ``ModApp, ``FunDecl, ``EvalOrder] do
    let provider? ← liftTermElabM <| synthInstance? (mkApp (mkConst ``ToExpr [0]) (mkConst type))
    if provider?.isSome then throwError "raw quotation instance leaked after import"
  let expected := mkConst ``quotationContract
  let quoted := Solidity.Frontend.ExecutableMetadataV2.Internal.quoteContract quotationContract
  if quoted.hasFVar || quoted.hasMVar || quoted.hasLevelMVar || quoted.hasSorry then
    throwError "unclosed quotation"
  let options ← getOptions
  if options.getBool `debug.skipKernelTC false then
    throwError "kernel checking must be enabled"
  let current := maxHeartbeats.get options
  let options := maxHeartbeats.set options (if current == 0 then 100000 else min current 100000)
  let positive := Declaration.thmDecl {
    name := `ExecutableBindingControls.quotationRoundTrip,
    levelParams := [], type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Contract) expected quoted,
    value := quoteRefl (mkConst ``Contract) expected }
  let .ok checked := Kernel.Environment.addDecl (← getEnv).toKernelEnv options positive
    | throwError "full quotation failed kernel round trip"
  let axioms ← liftTermElabM do
    addDecl positive
    let dependencies ← collectAxioms `ExecutableBindingControls.quotationRoundTrip
    pure dependencies
  unless axioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "quotation control has nonstandard axioms"
  logInfo m!"EXECUTABLE_QUOTATION quotation control axioms: {axioms}"
  let changedSource := { quotationFunction with sourceDecl := none }
  let mutants : List (String × Contract) := [
    ("sourceDecl", { quotationContract with funs := [("model", changedSource)] }),
    ("binaryOrder", { quotationContract with evalOrder := { EvalOrder.viaIR with binaryLeftToRight := false } }),
    ("modularOrder", { quotationContract with evalOrder := { EvalOrder.viaIR with modularLeftToRight := false } }),
    ("modifierFrames", { quotationContract with evalOrder := { EvalOrder.viaIR with modifierFrames := false } }),
    ("transientRoots", { quotationContract with transientRoots := [] }),
    ("funs", { quotationContract with funs := [] }),
    ("enums", { quotationContract with enums := [] }),
    ("invariants", { quotationContract with inv := [] }),
    ("widths", { quotationContract with widths := [] }),
    ("constructor", { quotationContract with ctor := none }),
    ("initializers", { quotationContract with inits := [] }),
    ("structs", { quotationContract with structs := [] }),
    ("errors", { quotationContract with errors := [] })]
  for (label, mutant) in mutants do
    let changed := Solidity.Frontend.ExecutableMetadataV2.Internal.quoteContract mutant
    let declaration := Declaration.thmDecl {
      name := Name.str `ExecutableBindingControls.quotationWrong label,
      levelParams := [], type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Contract) expected changed,
      value := quoteRefl (mkConst ``Contract) expected }
    match Kernel.Environment.addDecl checked options declaration with
    | .ok _ => throwError m!"changed {label} accepted as original quotation"
    | .error (.declTypeMismatch ..) => logInfo m!"EXECUTABLE_QUOTATION quotation mismatch refused: {label}"
    | .error _ => throwError m!"changed {label} failed for an unrelated reason"

run_cmd checkQuotation
end ExecutableBindingControls
