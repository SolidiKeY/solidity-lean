import Solidity.Tools.Upstream

open Solidity Solidity.Frontend Solidity.Tools.Upstream Lean

/- ABI names erase enums to uint8; preserve their source ranges at entry.
   Out-of-domain inputs reject before the body; matching an expected rejection
   is replay agreement, not successful execution of the source body. -/
solc_import "../solc/EnumAbiRanges.ast.json" hash 0xf6bd45346389f6b1 as AbiLegacy.EnumAbiRanges testing
solc_import "../solc/EnumAbiRanges.ast.json" hash 0xf6bd45346389f6b1 as AbiLegacy.EnumAbiCtorRanges testing
solc_import "../solc/EnumAbiRanges-viaIR.ast.json" hash 0x69f221831ab49e48 as AbiIR.EnumAbiRanges testing
solc_import "../solc/EnumAbiRanges-viaIR.ast.json" hash 0x69f221831ab49e48 as AbiIR.EnumAbiCtorRanges testing

private def check (C : Contract) (rows : List ImportRow) (text expected : String) : IO Unit := do
  let .ok data := Json.parse text | throw (IO.userError "invalid range test JSON")
  let actual := replay C rows data
  unless (actual.getObjValAs? String "status").toOption == some expected do
    throw (IO.userError actual.pretty)

#eval check AbiLegacy.EnumAbiRanges AbiLegacy.EnumAbiRanges.report "{\"vectors\":[{\"signature\":\"read(uint8)\",\"args\":[\"1\"],\"failure\":false,\"expected\":[\"1\"]}]}" "working"

#eval check AbiLegacy.EnumAbiRanges AbiLegacy.EnumAbiRanges.report "{\"vectors\":[{\"signature\":\"read(uint8)\",\"args\":[\"2\"],\"failure\":true,\"expected\":[]}]}" "working"

#eval check AbiLegacy.EnumAbiCtorRanges AbiLegacy.EnumAbiCtorRanges.report "{\"vectors\":[{\"signature\":\"constructor\",\"args\":[\"1\"],\"failure\":false,\"expected\":[]},{\"signature\":\"read()\",\"args\":[],\"failure\":false,\"expected\":[\"1\"]}]}" "working"

#eval check AbiLegacy.EnumAbiCtorRanges AbiLegacy.EnumAbiCtorRanges.report "{\"vectors\":[{\"signature\":\"constructor\",\"args\":[\"2\"],\"failure\":true,\"expected\":[]}]}" "working"

#eval check AbiIR.EnumAbiRanges AbiIR.EnumAbiRanges.report "{\"vectors\":[{\"signature\":\"read(uint8)\",\"args\":[\"1\"],\"failure\":false,\"expected\":[\"1\"]}]}" "working"

#eval check AbiIR.EnumAbiRanges AbiIR.EnumAbiRanges.report "{\"vectors\":[{\"signature\":\"read(uint8)\",\"args\":[\"2\"],\"failure\":true,\"expected\":[]}]}" "working"

#eval check AbiIR.EnumAbiCtorRanges AbiIR.EnumAbiCtorRanges.report "{\"vectors\":[{\"signature\":\"constructor\",\"args\":[\"1\"],\"failure\":false,\"expected\":[]},{\"signature\":\"read()\",\"args\":[],\"failure\":false,\"expected\":[\"1\"]}]}" "working"

#eval check AbiIR.EnumAbiCtorRanges AbiIR.EnumAbiCtorRanges.report "{\"vectors\":[{\"signature\":\"constructor\",\"args\":[\"2\"],\"failure\":true,\"expected\":[]}]}" "working"

#eval check AbiLegacy.EnumAbiRanges AbiLegacy.EnumAbiRanges.report "{\"vectors\":[{\"signature\":\"read(uint8)\",\"args\":[\"2\"],\"failure\":false,\"expected\":[\"2\"]}]}" "broken"

#eval check AbiLegacy.EnumAbiRanges AbiLegacy.EnumAbiRanges.report "{\"vectors\":[{\"signature\":\"read(uint8)\",\"args\":[\"2\"],\"failure\":true,\"expected\":[\"1\"]}]}" "broken"

#eval check AbiIR.EnumAbiRanges AbiIR.EnumAbiRanges.report "{\"vectors\":[{\"signature\":\"read(uint8)\",\"args\":[\"2\"],\"failure\":false,\"expected\":[\"2\"]}]}" "broken"

#eval check AbiIR.EnumAbiRanges AbiIR.EnumAbiRanges.report "{\"vectors\":[{\"signature\":\"read(uint8)\",\"args\":[\"2\"],\"failure\":true,\"expected\":[\"1\"]}]}" "broken"

-- Raw vectors keep the nominal enum bound: the typed entry decoder reads the
-- declared cardinality (`Semantics/AbiEntry.lean` `Kind.enumBelow`), so an
-- out-of-range word is an empty revert before the body (as solc's
-- `validator_revert_t_enum_*`), an in-range word runs, and neither can be
-- certified against the other outcome.
#eval (do
  for (C, rows) in [(AbiLegacy.EnumAbiRanges, AbiLegacy.EnumAbiRanges.report),
      (AbiIR.EnumAbiRanges, AbiIR.EnumAbiRanges.report)] do
    for (n, failure, expected, status) in
        [(1, false, [1], "working"), (2, true, [], "working"), (2^256 - 1, true, [], "working"),
         (1, true, [], "broken"), (2, false, [2], "broken")] do
      let v := Json.mkObj [("signature", toJson "read(uint8)"),
        ("calldata", toJson ((Semantics.wordBytes n).map UInt8.toNat)),
        ("inputTypes", toJson ["uint8"]), ("outputTypes", toJson ["uint256"]),
        ("expectedBytes", toJson ((expected.flatMap Semantics.wordBytes).map UInt8.toNat)),
        ("failure", toJson failure)]
      let report := replay C rows (Json.mkObj [("vectors", toJson [v])])
      unless (report.getObjValAs? String "status").toOption == some status do
        throw (IO.userError report.pretty) : IO Unit)
