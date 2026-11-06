import Solidity.Frontend.SolcJson.IrImport
open Lean Solidity.SolcValidation Solidity.Frontend.SolcJson.Ir

example : (select (Json.mkObj [("ir", .str "raw"), ("irOptimized", .str "optimized")])
    .unoptimized).toOption.map Selection.text = some "raw" := rfl
example : (select (Json.mkObj [("ir", .str "raw"), ("irOptimized", .str "optimized")])
    .optimized).toOption.map Selection.text = some "optimized" := rfl
example : (select (Json.mkObj [("ir", .num 7)]) .unoptimized).isOk = false := rfl
example : (select (Json.mkObj [("irOptimized", .str "optimized")]) .unoptimized).isOk = false := rfl
example : (selectContract (Json.mkObj []) "absent.sol" "C" .unoptimized).isOk = false := rfl

private def paths : Json := Json.mkObj [("contracts", Json.mkObj [
  ("real.sol", Json.mkObj [("Real", Json.mkObj [("ir", .str "actual")])])])]
example : (selectContract paths "wrong.sol" "Real" .unoptimized).isOk = false := rfl
example : (selectContract paths "real.sol" "Wrong" .unoptimized).isOk = false := rfl

#print axioms Solidity.Frontend.SolcJson.Ir.Selection.sound
#print axioms Solidity.Frontend.SolcJson.Ir.Selection.complete
#print axioms Solidity.Frontend.SolcJson.Ir.ContractSelection.sound

-- External I/O regression: the theorem above concerns arbitrary JSON, while
-- this test exercises the exact saved compiler fixture through Lean's parser.
#eval do
  let raw ← IO.FS.readFile "tests/fullscope-20261104/vt1/fixtures/output.json"
  let output ← IO.ofExcept (Json.parse raw)
  for name in ["Census", "LinkedMath"] do
    for (mode, suffix) in [(IrMode.unoptimized, "unoptimized"), (.optimized, "optimized")] do
      let selected ← IO.ofExcept (selectContract output "Census.sol" name mode)
      let expected ← IO.FS.readFile s!"tests/fullscope-20261104/vt1/fixtures/{name}.{suffix}.yul"
      unless selected.selection.text == expected do
        throw (IO.userError "IR channel changed")
  IO.println "IR_CHANNEL_FIXTURES_PASS 4"
