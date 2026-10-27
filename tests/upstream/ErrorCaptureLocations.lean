import Solidity.Tools.Upstream
open Solidity Solidity.Frontend Lean
solc_import "ErrorCaptureLocations.legacy.ast.json" hash 0x55e768aad87df724 as Group10.CaptureLegacy.ErrorCaptureLocations testing
solc_import "ErrorCaptureLocations.viaIR.ast.json" hash 0x482a1e0757be03b1 as Group10.CaptureIR.ErrorCaptureLocations testing
-- Pin actual compiler slice metadata and the frontend's generated declaration
-- independently of whether later slice-origin admission is available.
#eval (do
  for (mode,ir) in [("legacy",false),("viaIR",true)] do
    let data ← IO.ofExcept (Json.parse (← IO.FS.readFile s!"tests/upstream/ErrorCaptureLocations.{mode}.ast.json"))
    let ast ← IO.ofExcept (data.getObjVal? "ast")
    let C ← IO.ofExcept ((Frontend.readContract ast "ErrorCaptureLocations" [] true
      (namedErrorSourceOrder := ir)).mapError toString)
    unless C.funs.length == 2 do throw (IO.userError "capture source observations disappeared")
    for f in C.funs do
      let body ← IO.ofExcept (f.body.mapError (·.msg))
      let text := String.intercalate ";" (body.map (·.2))
      unless (text.splitOn " calldata «solcErrorCapture").length == 2 &&
          (text.splitOn " memory «solcErrorCapture").length == 1 do
        throw (IO.userError s!"slice provenance changed: {text}")
  : IO Unit)
