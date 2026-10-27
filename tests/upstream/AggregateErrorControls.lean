import Solidity.Tools.Upstream
open Solidity Solidity.Frontend Solidity.Tools Solidity.Tools.Upstream Lean
solc_import "AggregateErrorControls.legacy.ast.json" hash 0x323ea6f54c3796de as Group10.AggregateLegacy.AggregateErrorControls testing
solc_import "AggregateErrorControls.viaIR.ast.json" hash 0x4e0b11581b66a097 as Group10.AggregateIR.AggregateErrorControls testing


namespace AggregateErrorControls
private def words (xs : List Nat) := (xs.flatMap Semantics.wordBytes).map UInt8.toNat
private def selector (s : String) := (Semantics.selectorBytes (Semantics.customSelector s)).map UInt8.toNat
private def failure (sig : String) (args : List String) (bs : List Nat) := Json.mkObj [
  ("signature",toJson sig),("args",toJson args),("failure",toJson true),
  ("expected",toJson ([] : List String)),("revertBytes",toJson bs)]
private def success (sig : String) (args values : List String) := Json.mkObj [
  ("signature",toJson sig),("args",toJson args),("failure",toJson false),("expected",toJson values)]
private def sigs := ["initialize()","length()","field()","count()","context()","arrayStorage()","arrayNamed()",
  "pairStorage()","pairNamed()","arrayEmpty()","arrayMemory()","pairMemory()","pairEmpty()",
  "arrayCalldata(uint256[])","pairCalldata((uint16,string))","memoryLater()","namedMemoryLater()","nestedMemory()","pairMemoryLater()","pairNamedMemoryLater()",
  "indexedStorage()","indexedNamed()","beforeEncoding()"]
private def rows : List ImportRow := sigs.map fun sig =>
  {name := (sig.splitOn "(").head!,sourceSignature := sig,tag := .diamond,params := [],status := .elaborated,reason := ""}
private def check (C : Contract) (vectors : List Json) (expected : String) : IO Unit := do
  let out := replay C rows (Json.mkObj [("vectors",toJson vectors)])
  unless (out.getObjValAs? String "status").toOption == some expected do throw (IO.userError out.pretty)
private def arrayPayload (xs : List Nat) (n : Nat) :=
  selector "ArrayError(uint256[],uint256)" ++ words ([64,n,xs.length] ++ xs)
private def pairPayload (n a : Nat) (bs : List Nat) :=
  selector "PairError(uint256,(uint16,string),int8)" ++ words [n,96,2^256-1,a,64,bs.length] ++
    bs ++ List.replicate ((32-bs.length%32)%32) 0
#eval (do
  for report in [Group10.AggregateLegacy.AggregateErrorControls.report,Group10.AggregateIR.AggregateErrorControls.report] do
    for row in report do
      if ["arrayCalldata(uint[])","pairCalldata(struct AggregateErrorControls.ErrorPair)"].contains row.sourceSignature then
        unless row.status == .unsupported && (row.reason.splitOn "a calldata slice ordinary alias without a known calldata origin").length > 1 do
          throw (IO.userError s!"calldata provenance refusal changed: {row.sourceSignature}: {row.reason}")
      else unless row.status == .elaborated do
        throw (IO.userError s!"control import failed: {row.sourceSignature}: {row.reason}")
  for C in [Group10.AggregateLegacy.AggregateErrorControls,Group10.AggregateIR.AggregateErrorControls] do
    let init := success "initialize()" [] []
    let rollback := [success "length()" [] ["1"],success "field()" [] ["9"],success "count()" [] ["0"]]
    let cases := [("arrayEmpty()",arrayPayload [] 3),("arrayMemory()",arrayPayload [7,8] 3),
      ("arrayStorage()",arrayPayload [] 5),("arrayNamed()",arrayPayload [] 5),
      ("pairStorage()",pairPayload 5 0 []),("pairNamed()",pairPayload 5 0 []),
      ("pairMemory()",pairPayload 3 9 [97,98,99]),("pairEmpty()",pairPayload 3 9 []),
      ("memoryLater()",arrayPayload [11] 5),("namedMemoryLater()",arrayPayload [11] 5),
      ("pairMemoryLater()",pairPayload 9 10 [97,98,99]),("pairNamedMemoryLater()",pairPayload 9 10 [97,98,99]),
      ("indexedStorage()",arrayPayload [11] 5),("indexedNamed()",arrayPayload [11] 5),
      ("beforeEncoding()",(Semantics.encodePanic 1).map UInt8.toNat),
      ("nestedMemory()",selector "NestedError(uint256[][])" ++ words [32,2,64,128,1,7,0])]
    for (sig,bs) in cases do
      check C ([init,failure sig [] bs] ++ rollback) "working"
      if sig == "arrayMemory()" || sig == "pairMemory()" then
        for wrong in [[],bs.drop 1,bs.take (bs.length-1),bs++[0],[0]++bs.drop 1] do
          check C ([init,failure sig [] wrong] ++ rollback) "broken"
    -- Reject early snapshots, tuple offsets, element lengths and field order.
    for sig in ["arrayStorage()","arrayNamed()"] do
      check C [init,failure sig [] (arrayPayload [7] 5)] "broken"
    for sig in ["pairStorage()","pairNamed()"] do
      check C [init,failure sig [] (pairPayload 5 9 [97,98,99])] "broken"
    for wrong in [selector "ArrayError(uint256[],uint256)" ++ words [32,3,2,7,8],
        selector "ArrayError(uint256[],uint256)" ++ words [64,3,1,7,8],
        selector "ArrayError(uint256[],uint256)" ++ words [64,3,2,8,7]] do
      check C [failure "arrayMemory()" [] wrong] "broken"
    for wrong in [selector "PairError(uint256,(uint16,string),int8)" ++ words [3,64,2^256-1,9,64,0],
        selector "PairError(uint256,(uint16,string),int8)" ++ words [3,96,255,9,64,0]] do
      check C [failure "pairEmpty()" [] wrong] "broken"
    -- Calldata captures retain their location and remain explicitly refused
    -- by the existing slice-origin gate, rather than being copied to memory.
    let ss := [← IO.ofExcept (runStmt C "context" [])]
    let ⟨_,Q⟩ ← IO.ofExcept (entryProg C ss)
    for (sender,value,want) in [(37,5,42),(38,5,43),(37,6,43)] do
      let changed : TTx := {msgSender := PrimTy.ofIntD .uint sender, msgValue := PrimTy.ofIntD .uint value}
      let .ok out := Q.runF 1000 (State.deploy C changed) | throw (IO.userError "context failed")
      unless Semantics.lookupBy (Var.ofName retLocal) (localVals (Q.outNames []) out.st.env) ==
          some (.uint (PrimTy.ofIntD .uint want)) do throw (IO.userError "context changed")
  : IO Unit)
/-- The encoder buffer is forwarded byte for byte, with no alternate evaluator. -/
theorem raw_error_exact {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (i : Idx Γ (.mem bytesR)) (r : HRef σ.H bytesR)
    (h : TEnv.get i σ.env = some r) :
    TRun.revertData [.mem .raw i] σ = .error
      (THalt.ofData ((σ.heap.get r).1.map (fun v => UInt8.ofNat v.val.toNat))) :=
  TRun.revertData_mem σ .raw i r h
#print axioms raw_error_exact
end AggregateErrorControls

-- Malformed internal declarations cannot broaden the accepted error boundary.
#eval (do
  for C in [Group10.AggregateLegacy.AggregateErrorControls,Group10.AggregateIR.AggregateErrorControls] do
    let negatives : List (Ty × List (String × Nat)) := [
      (.array .int,[]),(.array .uint,[("a[]",8)]),
      (.array .uint,[("a[]#enum",1)]),(.mapping .uint .uint,[]),
      (.fixed .uint 2,[])]
    for (T,ws) in negatives do
      let bad := {C with errors := C.errors.map fun (e,d) =>
        if e == "ArrayError" then (e,{d with params := [("a",T),("n",.uint)],widths := ws}) else (e,d)}
      let program : Except String (Blk bad []) := do entryProg bad [← runStmt bad "arrayMemory" []]
      if program.isOk then throw (IO.userError "malformed reference declaration admitted")
    let bad := {C with errors := C.errors.map fun (e,d) =>
      if e == "PairError" then (e,{d with params := d.params.map fun (n,T) =>
        match T with
        | .ref (.struct s) => (n,.ref (.struct (s.replace "ErrorPair" "OtherPair")))
        | _ => (n,T)}) else (e,d)}
    let program : Except String (Blk bad []) := do entryProg bad [← runStmt bad "pairMemory" []]
    if program.isOk then throw (IO.userError "different nominal struct admitted")
  unless errorAbiHasEnum (.array .uint) [("[]#enum",1)] "" do
    throw (IO.userError "aggregate enum refusal missing")
  if (AbiTy.of (.mapping .uint .uint) [] "").isSome then throw (IO.userError "mapping ABI admitted")
  : IO Unit)
