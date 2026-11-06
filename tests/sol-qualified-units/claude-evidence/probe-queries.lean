import Lean
import Solidity.Frontend.QualifiedUnits.DifferentialControls
import Solidity.Frontend.QualifiedUnits.SignatureResolution
open Lean Solidity.Source Solidity.Frontend.QualifiedUnits
namespace QualifiedUnitsQueryAudit
def symbolJson : Sym → Json
  | .decl i => Json.mkObj [("kind", toJson "decl"), ("unit", toJson i.unit), ("index", toJson i.idx)]
  | .unit u => Json.mkObj [("kind", toJson "unit"), ("unit", toJson u)]
def reason : Failure → String
  | .missing => "missing"
  | .ambiguous => "ambiguous"
  | .invalidScope => "invalidScope"
  | .localShadow _ => "localShadow"
def answerJson : Except Failure (List Sym) → Json
  | .ok symbols => Json.mkObj [("status", toJson "ok"), ("symbols", Json.arr (symbols.map symbolJson).toArray)]
  | .error error => Json.mkObj [("status", toJson "error"), ("reason", toJson (reason error)),
      ("local_index", match error with | .localShadow i => toJson i | _ => Json.null)]
def queryJson (caseId reference : String) (answer : Except Failure (List Sym)) : Json :=
  Json.mkObj [("id", toJson caseId), ("reference", toJson reference), ("answer", answerJson answer)]
#eval do
  let report := ("RESOLVER_QUERY_REPORT " ++ (Json.arr #[queryJson "multi-hop" "N.M.T" (Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve Solidity.Frontend.QualifiedUnits.DifferentialControls.hopsInput [] "A.sol" none [] ⟨"N", ["M", "T"]⟩),
queryJson "missing-symbol" "N.M.Missing" (Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve Solidity.Frontend.QualifiedUnits.DifferentialControls.missingInput [] "A.sol" none [] ⟨"N", ["M", "Missing"]⟩),
queryJson "ambiguous-namespace" "N.T" (Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve Solidity.Frontend.QualifiedUnits.DifferentialControls.ambiguousInput [] "A.sol" none [] ⟨"N", ["T"]⟩),
queryJson "same-spelling-units" "L.T" (Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve Solidity.Frontend.QualifiedUnits.DifferentialControls.spellingInput [] "A.sol" none [] ⟨"L", ["T"]⟩),
queryJson "same-spelling-units" "R.T" (Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve Solidity.Frontend.QualifiedUnits.DifferentialControls.spellingInput [] "A.sol" none [] ⟨"R", ["T"]⟩),
queryJson "symbol-namespace-alias" "N.T" (Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve Solidity.Frontend.QualifiedUnits.DifferentialControls.aliasInput [] "A.sol" none [] ⟨"N", ["T"]⟩),
queryJson "transitive-all" "N.T" (Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve Solidity.Frontend.QualifiedUnits.DifferentialControls.allInput [] "A.sol" none [] ⟨"N", ["T"]⟩),
queryJson "diamond-identity" "T" (Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve Solidity.Frontend.QualifiedUnits.DifferentialControls.diamondInput [] "A.sol" none [] ⟨"T", []⟩),
queryJson "cyclic-namespace" "N.Back.N.T" (Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve Solidity.Frontend.QualifiedUnits.DifferentialControls.cycleInput [] "A.sol" none [] ⟨"N", ["Back", "N", "T"]⟩),
queryJson "private-base-fallback" "N.T" (Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve (Solidity.Frontend.QualifiedUnits.DifferentialControls.shadowInput .priv) [] "A.sol" (some ⟨"A.sol", 2⟩) [] ⟨"N", ["T"]⟩),
queryJson "visible-base-shadow" "N.T" (Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve (Solidity.Frontend.QualifiedUnits.DifferentialControls.shadowInput .internal) [] "A.sol" (some ⟨"A.sol", 2⟩) [] ⟨"N", ["T"]⟩),
queryJson "local-shadow" "N.T" (Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve Solidity.Frontend.QualifiedUnits.DifferentialControls.localInput [] "A.sol" (some ⟨"A.sol", 0⟩) ["N"] ⟨"N", ["T"]⟩),
queryJson "inherited-type" "N.Base" (Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve Solidity.Frontend.QualifiedUnits.DifferentialControls.inheritedInput [] "A.sol" none [] ⟨"N", ["Base"]⟩),
queryJson "inherited-type" "D.S" (Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve Solidity.Frontend.QualifiedUnits.DifferentialControls.inheritedInput [] "A.sol" none [] ⟨"D", ["S"]⟩),
queryJson "ambiguous-base" "D.S" (Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve Solidity.Frontend.QualifiedUnits.DifferentialControls.ambiguousBaseInput [] "A.sol" none [] ⟨"D", ["S"]⟩),
queryJson "inherited-overload-gap" "f" (Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve Solidity.Frontend.QualifiedUnits.DifferentialControls.inheritedOverloadInput [] "A.sol" (some ⟨"A.sol", 0⟩) [] ⟨"f", []⟩),
queryJson "qualified-parameter-overload-gap" "f" (Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve Solidity.Frontend.QualifiedUnits.DifferentialControls.qualifiedOverloadInput [] "A.sol" (some ⟨"A.sol", 0⟩) [] ⟨"f", []⟩)]).compress)
  IO.FS.writeFile "tests/sol-qualified-units/claude-evidence/probe-queries.out" (report ++ "\n")
  IO.println report
end QualifiedUnitsQueryAudit
