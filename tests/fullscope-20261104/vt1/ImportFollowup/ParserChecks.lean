import Solidity.Frontend.SolcJson.IrImportControls
open Lean Solidity.Frontend.SolcJson.Ir
-- Json.parse is a partial parser: these are executable boundary checks,
-- not kernel theorems or compiler authentication.
#eval do
  let parsed ← IO.ofExcept (Json.parse "\"raw\\n\\\"quoted\\\"\"")
  unless parsed == Json.str "raw\n\"quoted\"" do throw (IO.userError "escape decoding changed")
  unless (Json.parse "{broken").isOk == false do throw (IO.userError "malformed JSON accepted")
  IO.println "IR_PARSER_CONTROLS_PASS 2"
