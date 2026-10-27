import Solidity.Tools.Upstream

open Solidity Solidity.Semantics

solc_import "../solc/CloudIntegration.ast.json" hash 0xc345662e8c262923 as Combined.CloudIntegration testing entrypoints

solc_import "../solc/CloudIntegrationIR.ast.json" hash 0x13121b6acaf879f6 as CombinedIR.CloudIntegration testing entrypoints

/-- Inherited entries appear once, with both enum carrier widths executable. -/
private def checkCombined (C : Contract) (rows : List Frontend.ImportRow) : IO Unit := do
  unless (rows.filter (·.sourceName == "inherited")).length == 1 do
    throw (IO.userError "inherited ABI entry is duplicated or missing")
  let data ← IO.ofExcept (Lean.Json.parse "{\"vectors\":[
    {\"signature\":\"inherited()\",\"args\":[],\"failure\":false,\"expected\":[\"7\"]},
    {\"signature\":\"plainInline()\",\"args\":[],\"failure\":false,\"expected\":[\"1\"]},
    {\"signature\":\"packedInline()\",\"args\":[],\"failure\":false,\"expected\":[\"1\"]}
  ]}")
  let report := Solidity.Tools.Upstream.replay C rows data
  unless (report.getObjValAs? String "status").toOption == some "working" do
    throw (IO.userError report.pretty)

#eval checkCombined Combined.CloudIntegration Combined.CloudIntegration.report
#eval checkCombined CombinedIR.CloudIntegration CombinedIR.CloudIntegration.report
