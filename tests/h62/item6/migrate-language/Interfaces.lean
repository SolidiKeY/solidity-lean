import Lean
import Solidity.Language.FeatureInfo
import Solidity.Language.FixedPoint.Conformance
import Solidity.Language.FixedPoint.Storage

/-! Read-only elaborated interface and axiom transcript, including generated
constants. Names/types are printed with Lean; version-specific pretty printing
is evidence to inspect, not a claim of cross-version kernel identity. -/
open Lean Elab Command
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    match env.getModuleIdxFor? n with
    | some i => if (`Solidity.Language).isPrefixOf env.header.moduleNames[i.toNat]!
        then acc.push n else acc
    | none => acc
  for n in names.toList.mergeSort (fun a b => a.toString < b.toString) do
    let some ci := env.find? n | throwError "missing {n}"
    logInfo m!"INTERFACE {n} : {ci.type}"
    let axioms ← collectAxioms n
    if axioms.contains `sorryAx then throwError "unproved constant: {n}"
    logInfo m!"AXIOMS {n} : {axioms.toList}"
  logInfo m!"INTERFACE_COUNT {names.size}"
