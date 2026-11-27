import Solidity.Frontend.Source
import Solidity.Frontend.SolcJson.IrImport
/-! External execution boundary, separate from structural validator correctness.
`Environment` is interpreted by the caller against an actual execution record;
choosing predicates that merely accept metadata does not authenticate a run. -/
namespace Solidity.Interfaces.FrontendExecution
open Lean
open Solidity.Frontend.Source (Compiler)
open Solidity.SolcValidation (IrMode)
/-- External observations: SHA-256 of the bytes actually loaded, their reported
version, and the successfully completed standard-JSON invocation and returned text. `completed`
includes all source resolution (including callbacks), with no unrecorded inputs.
These fields specify the trusted boundary; they assert no compiler semantics. -/
structure Environment where
  /-- Independently established exact release bytes, not untrusted hash metadata. -/
  pinnedArtifact : Compiler → ByteArray
  sha256 : ByteArray → String
  version : ByteArray → String
  completed : ByteArray → String → String → Prop
/-- Authentic execution and faithful decoding. Compiler errors are checked in
JSON, since process success alone does not imply successful compilation. -/
def Faithful (env : Environment) (compiler : Compiler) (artifact : ByteArray)
    (inputText outputText : String) (input output : Json) : Prop :=
  artifact = env.pinnedArtifact compiler ∧
  env.sha256 artifact = compiler.sha256 ∧ env.version artifact = compiler.version ∧
  env.completed artifact inputText outputText ∧
  Json.parse inputText = .ok input ∧ Json.parse outputText = .ok output ∧
  ((output.getObjVal? "errors").toOption = none ∨
    ∃ errors, output.getObjValAs? (Array Json) "errors" = .ok errors ∧
      ∀ diagnostic ∈ errors.toList, ∃ severity,
        diagnostic.getObjValAs? String "severity" = .ok severity ∧ severity ≠ "error")
/-- The selected IR must be the exact channel of the same compiler output. -/
def SelectedIr (output : Json) (source contract : String) (mode : IrMode)
    (text : String) : Prop :=
  Solidity.Frontend.SolcJson.Ir.lookup output source contract mode = .ok text
end Solidity.Interfaces.FrontendExecution
