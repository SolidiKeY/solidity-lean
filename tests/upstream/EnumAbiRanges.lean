import Solidity.Tools.Upstream

open Solidity Solidity.Frontend Solidity.Tools.Upstream Lean

/- ABI names erase enums to uint8; preserve their source ranges at entry.
   Out-of-domain inputs stay blocked, never successful expected failures. -/
solc_import "../solc/EnumAbiRanges.ast.json" hash 0xf6bd45346389f6b1 as AbiLegacy.EnumAbiRanges testing
solc_import "../solc/EnumAbiRanges.ast.json" hash 0xf6bd45346389f6b1 as AbiLegacy.EnumAbiCtorRanges testing
solc_import "../solc/EnumAbiRanges-viaIR.ast.json" hash 0x69f221831ab49e48 as AbiIR.EnumAbiRanges testing
solc_import "../solc/EnumAbiRanges-viaIR.ast.json" hash 0x69f221831ab49e48 as AbiIR.EnumAbiCtorRanges testing

private def check (C : Contract) (rows : List ImportRow) (text expected : String) : IO Unit := do
  let .ok data := Json.parse text | throw (IO.userError "invalid range test JSON")
  let actual := replay C rows data
  unless (actual.getObjValAs? String "status").toOption == some expected do
    throw (IO.userError actual.pretty)
  if expected == "blocked" then
    unless (actual.getObjValAs? String "reason").toOption == some "noncanonical ranged ABI argument" do
      throw (IO.userError actual.pretty)

#eval check AbiLegacy.EnumAbiRanges AbiLegacy.EnumAbiRanges.report "{\"vectors\":[{\"signature\":\"read(uint8)\",\"args\":[\"1\"],\"failure\":false,\"expected\":[\"1\"]}]}" "working"

#eval check AbiLegacy.EnumAbiRanges AbiLegacy.EnumAbiRanges.report "{\"vectors\":[{\"signature\":\"read(uint8)\",\"args\":[\"2\"],\"failure\":true,\"expected\":[]}]}" "blocked"

#eval check AbiLegacy.EnumAbiCtorRanges AbiLegacy.EnumAbiCtorRanges.report "{\"vectors\":[{\"signature\":\"constructor\",\"args\":[\"1\"],\"failure\":false,\"expected\":[]},{\"signature\":\"read()\",\"args\":[],\"failure\":false,\"expected\":[\"1\"]}]}" "working"

#eval check AbiLegacy.EnumAbiCtorRanges AbiLegacy.EnumAbiCtorRanges.report "{\"vectors\":[{\"signature\":\"constructor\",\"args\":[\"2\"],\"failure\":true,\"expected\":[]}]}" "blocked"

#eval check AbiIR.EnumAbiRanges AbiIR.EnumAbiRanges.report "{\"vectors\":[{\"signature\":\"read(uint8)\",\"args\":[\"1\"],\"failure\":false,\"expected\":[\"1\"]}]}" "working"

#eval check AbiIR.EnumAbiRanges AbiIR.EnumAbiRanges.report "{\"vectors\":[{\"signature\":\"read(uint8)\",\"args\":[\"2\"],\"failure\":true,\"expected\":[]}]}" "blocked"

#eval check AbiIR.EnumAbiCtorRanges AbiIR.EnumAbiCtorRanges.report "{\"vectors\":[{\"signature\":\"constructor\",\"args\":[\"1\"],\"failure\":false,\"expected\":[]},{\"signature\":\"read()\",\"args\":[],\"failure\":false,\"expected\":[\"1\"]}]}" "working"

#eval check AbiIR.EnumAbiCtorRanges AbiIR.EnumAbiCtorRanges.report "{\"vectors\":[{\"signature\":\"constructor\",\"args\":[\"2\"],\"failure\":true,\"expected\":[]}]}" "blocked"
