import Solidity.Tools.Upstream
open Solidity Solidity.Frontend Solidity.Tools Solidity.Tools.Upstream Lean
solc_import "RequireAggregateControls.legacy.ast.json" hash 0xe735cd5ad6d2630c as Group10.RequireLegacy.RequireAggregateControls testing
solc_import "RequireAggregateControls.viaIR.ast.json" hash 0xa58e9a1539b4bfab as Group10.RequireIR.RequireAggregateControls testing
example : Group10.RequireLegacy.RequireAggregateControls.report.all (·.status == .elaborated) = true := by decide +kernel
example : Group10.RequireIR.RequireAggregateControls.report.all (·.status == .elaborated) = true := by decide +kernel
private def words (xs : List Nat) := (xs.flatMap Semantics.wordBytes).map UInt8.toNat
private def selector (s : String) := (Semantics.selectorBytes (Semantics.customSelector s)).map UInt8.toNat
private def fail (sig : String) (bs : List Nat) := Json.mkObj [
  ("signature",toJson sig),("args",toJson ([] : List String)),("failure",toJson true),
  ("expected",toJson ([] : List String)),("revertBytes",toJson bs)]
private def ok (sig : String) (values : List String) := Json.mkObj [
  ("signature",toJson sig),("args",toJson ([] : List String)),("failure",toJson false),("expected",toJson values)]
private def rows : List ImportRow := ["array","pair","pass","get","initialize","size","later","laterTrue"].map fun n =>
  {name := n,sourceSignature := n++"()",tag := .diamond,params := [],status := .elaborated,reason := ""}
private def check (C : Contract) (vectors : List Json) (status : String) : IO Unit := do
  let out := replay C rows (Json.mkObj [("vectors",toJson vectors)])
  unless (out.getObjValAs? String "status").toOption == some status do throw (IO.userError out.pretty)
#eval (do
  let a := selector "ArrayRequired(uint256[],uint256)" ++ words [64,3,2,7,8]
  let p := selector "PairRequired((uint16,string),uint256)" ++ words [64,3,9,64,3] ++ [97,98,99] ++ List.replicate 29 0
  for C in [Group10.RequireLegacy.RequireAggregateControls,Group10.RequireIR.RequireAggregateControls] do
    check C [fail "array()" a,ok "get()" ["0"],fail "pair()" p,ok "get()" ["0"],ok "pass()" [],ok "get()" ["7"]] "working"
    let empty := selector "ArrayRequired(uint256[],uint256)" ++ words [64,5,0]
    check C [ok "initialize()" [],fail "later()" empty,ok "size()" ["1"],ok "get()" ["0"],
      ok "laterTrue()" [],ok "size()" ["0"],ok "get()" ["99"]] "working"
    check C [ok "initialize()" [],fail "later()" (selector "ArrayRequired(uint256[],uint256)" ++ words [64,5,1,7])] "broken"
    for (sig,bs) in [("array()",a),("pair()",p)] do
      for wrong in [[],bs.drop 1,bs.take (bs.length-1),bs++[0],[0]++bs.drop 1] do
        check C [fail sig wrong] "broken"
  : IO Unit)
