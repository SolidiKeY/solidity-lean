import Lean
import Solidity.Frontend.NumericLiteralProofs.Controls
import Solidity.Frontend.NumericLiteralProofs.Span
import Solidity.Frontend.NumericLiteralProofs.Fixtures

/-!
# Environment-level declaration and transitive axiom inventory

This command records every imported declaration owned by a NumericLiteralProofs
module, including generated constructors, recursors and equation helpers. It
introduces no proof declarations. The external acceptance checker compares the
fresh output with the committed exact inventory, rather than editing the shared
axiom-pin registry.
-/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut entries : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx.toNat]!
      if owner.toString.startsWith "Solidity.Frontend.NumericLiteralProofs." then
        let axioms ← Lean.collectAxioms name
        let signature ← liftTermElabM do
          withOptions (fun opts => (opts.setBool `pp.proofs true).setBool `pp.universes true) do
            return toString (← Lean.Meta.ppExpr info.type)
        let kind := match info with
          | .axiomInfo _ => r"axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        entries := entries.push (Json.mkObj [
          ("name", toJson name.toString), ("module", toJson owner.toString),
          ("kind", toJson kind), ("signature", toJson signature),
          ("levels", toJson (info.levelParams.map Name.toString)),
          ("isUnsafe", toJson info.isUnsafe), ("isPartial", toJson info.isPartial),
          ("axioms", toJson (axioms.map Name.toString).toList)])
  let mut root := System.FilePath.mk (← getFileName)
  for _ in [:4] do root := root.parent.getD "."
  liftIO <| IO.FS.writeFile (root / "tests/sol-numeric-literals/evidence/kernel-inventory.actual.json")
    (Json.pretty (Json.arr entries))
  logInfo m!"numeric literal audit: {entries.size} declarations recorded"
