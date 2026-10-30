import Solidity.Frontend.SolcJson

/-! # Complete declaration-resolved source payment shapes
No source statements are dropped. This deliberately bounded reader admits two
compositions: local creation then stipend send, or a contract-valued initializer
and direct stipend transfers plus a balance getter. Receive bodies must be empty
or a direct literal revert; unsupported effects, dispatch and full-gas calls are
refused. The receiver body itself is executed by the ordinary typed importer. -/
namespace Solidity.Frontend.PaymentPlan
open Lean

structure Method where
  name : String
  id : Int
  callId : Int
  amount : Nat
  deriving Repr, ToExpr

structure Plan where
  owner : String
  ownerId : Int
  target : String
  targetId : Int
  receiveId : Int
  creationId : Int
  referenceId : Int
  root : Option String
  sendName : String
  sendId : Option Int
  sendCallId : Option Int
  ownerReceive : Option Int
  getter : Option (String × Int)
  methods : List Method
  deriving Repr, ToExpr

private def require (p : Bool) (why : String) : Except String Unit :=
  if p then .ok () else .error ("solidity.paymentSource: " ++ why)
private def id (j : Json) : Except String Int :=
  match J.id? j with | some i => .ok i | none => .error "solidity.paymentSource: missing declaration identity"
private def field (j : Json) (key : String) : Except String Json :=
  (j.getObjVal? key).mapError (fun _ => "solidity.paymentSource: missing " ++ key)
private def statements (f : Json) : Except String (List Json) := do
  let b ← field f "body"
  require (J.kind b == "Block") "function body must be an ordinary block"
  return (J.arrD b "statements").toList
private def header (f : Json) (returns : Nat) : Except String Unit := do
  require (J.kind f == "FunctionDefinition" && (J.arrD f "modifiers").isEmpty) "unmodified function required"
  require ((J.arrD (← field f "parameters") "parameters").isEmpty) "parameters are outside this payment fragment"
  require ((J.arrD (← field f "returnParameters") "parameters").size == returns) "unexpected source return shape"
private def newTarget (e : Json) : Except String (Int × Int) := do
  require (J.kind e == "FunctionCall" && (J.arrD e "arguments").isEmpty) "zero-argument creation required"
  let n ← field e "expression"
  require (J.kind n == "NewExpression") "direct contract creation required"
  let t ← field n "typeName"
  require (J.kind t == "UserDefinedTypeName") "contract type required"
  let some r := J.ref? t | throw "solidity.paymentSource: creation target identity missing"
  return (← id e, r)
private def castReceiver (e : Json) : Except String Json := do
  require (J.kind e == "FunctionCall" && J.str? e "kind" == some "typeConversion") "payable receiver conversion required"
  let c ← field e "expression"
  let t ← field c "typeName"
  require (J.kind c == "ElementaryTypeNameExpression" && J.str? t "name" == some "address") "address conversion required"
  let [a] := (J.arrD e "arguments").toList | throw "solidity.paymentSource: one receiver required"
  require (J.kind a == "Identifier") "declaration-resolved receiver required"
  return a
private def payment (e : Json) (member : String) (reference : Int) : Except String Nat := do
  require (J.kind e == "FunctionCall") "payment invocation required"
  let m ← field e "expression"
  require (J.kind m == "MemberAccess" && J.str? m "memberName" == some member &&
    (J.tyId m).startsWith ("t_function_" ++ member ++ "_")) "native stipend payment required"
  let r ← castReceiver (← field m "expression")
  require (J.ref? r == some reference) "payment receiver declaration mismatch"
  let [a] := (J.arrD e "arguments").toList | throw "solidity.paymentSource: exactly one payment amount required"
  require (J.kind a == "Literal" && J.str? a "kind" == some "number") "literal payment required"
  let some n := ((J.str? a "value").getD "").toNat? | throw "solidity.paymentSource: decimal amount required"
  let scale ← match (J.str? a "subdenomination").getD "" with
    | "" | "wei" => pure 1
    | "ether" => pure (10^18)
    | _ => throw "solidity.paymentSource: unsupported denomination"
  require (n * scale < 2^256) "amount outside uint256"
  return n * scale
private def receive (f : Json) : Except String Int := do
  header f 0
  require (J.str? f "kind" == some "receive" && J.str? f "stateMutability" == some "payable") "payable receive required"
  let ss ← statements f
  if !ss.isEmpty then
    let [s] := ss | throw "solidity.paymentSource: receive must be empty or literal revert"
    require (J.kind s == "ExpressionStatement") "direct receive revert required"
    let e ← field s "expression"
    let c ← field e "expression"
    require (J.kind e == "FunctionCall" && J.kind c == "Identifier" &&
      J.str? c "name" == some "revert" && (J.ref? c).any (· < 0)) "builtin receive revert required"
    let [a] := (J.arrD e "arguments").toList | throw "solidity.paymentSource: literal reason required"
    require (J.kind a == "Literal" && J.str? a "kind" == some "string") "literal receive reason required"
  id f

/-- Recognize every declaration and statement of the whole two-contract unit. -/
def read (ast : Json) : Except String Plan := do
  let units := (J.arrD ast "nodes").toList
  require (units.all (fun n => ["PragmaDirective", "ContractDefinition"].contains (J.kind n))) "unhandled source-unit declaration"
  let [target, owner] := units.filter (fun n => J.kind n == "ContractDefinition")
    | throw "solidity.paymentSource: ordered two-contract unit required"
  for c in [target, owner] do
    require (J.str? c "contractKind" == some "contract" &&
      J.opt c "abstract" == some (.bool false) && (J.arrD c "baseContracts").isEmpty) "noninheriting concrete contracts required"
  let [recv] := (J.arrD target "nodes").toList | throw "solidity.paymentSource: target must contain only receive"
  let recvId ← receive recv
  let targetId ← id target
  let ownerId ← id owner
  let base : Plan := {
    owner := (J.str? owner "name").getD "", ownerId := ownerId,
    target := (J.str? target "name").getD "", targetId := targetId, receiveId := recvId,
    creationId := -1, referenceId := -1, root := none, sendName := "", sendId := none, sendCallId := none,
    ownerReceive := none, getter := none, methods := []}
  let ns := (J.arrD owner "nodes").toList
  if let [ctor, method] := ns then
    header ctor 0
    require (J.str? ctor "kind" == some "constructor" && J.str? ctor "stateMutability" == some "payable" && (← statements ctor).isEmpty) "empty payable constructor required"
    header method 1
    require ([some "public", some "external"].contains (J.str? method "visibility")) "send entry must be externally visible"
    require (J.str? method "kind" == some "function" && J.str? method "stateMutability" == some "nonpayable") "ordinary send method required"
    let [decl, ret] ← statements method | throw "solidity.paymentSource: complete creation-then-return body required"
    require (J.kind decl == "VariableDeclarationStatement" && J.kind ret == "Return") "local creation then return required"
    let [binding] := (J.arrD decl "declarations").toList | throw "solidity.paymentSource: one local receiver required"
    let localId ← id binding
    require ((J.opt binding "typeName").bind J.ref? == some targetId) "local contract kind mismatch"
    let (creationId, kind) ← newTarget (← field decl "initialValue")
    require (kind == targetId) "creation target mismatch"
    let amount ← payment (← field ret "expression") "send" localId
    require (amount == 0) "only zero-value creation-then-send is admitted"
    return { base with
      creationId := creationId, referenceId := localId, sendName := (J.str? method "name").getD "", sendId := some (← id method), sendCallId := some (← id (← field ret "expression"))}
  else
    let [root, ownReceive, first, second, getter] := ns | throw "solidity.paymentSource: complete initializer/receive/transfer/getter declarations required"
    require (J.kind root == "VariableDeclaration" && J.opt root "stateVariable" == some (.bool true) &&
      (J.opt root "typeName").bind J.ref? == some targetId) "contract-valued initializer required"
    let rootId ← id root
    let (creationId, kind) ← newTarget (← field root "value")
    require (kind == targetId) "initializer target mismatch"
    let ownRecv ← receive ownReceive
    require ((← statements ownReceive).isEmpty) "owner receive must be empty"
    let methods ← [first, second].mapM fun f => do
      header f 0
      require ([some "public", some "external"].contains (J.str? f "visibility")) "transfer entry must be externally visible"
      require (J.str? f "kind" == some "function" && J.str? f "stateMutability" == some "nonpayable") "ordinary transfer method required"
      let [s] ← statements f | throw "solidity.paymentSource: one transfer statement required"
      require (J.kind s == "ExpressionStatement") "direct transfer required"
      let amount ← payment (← field s "expression") "transfer" rootId
      pure {name := (J.str? f "name").getD "", id := ← id f, callId := ← id (← field s "expression"), amount : Method}
    header getter 1
    require ([some "public", some "external"].contains (J.str? getter "visibility")) "getter entry must be externally visible"
    require (J.str? getter "stateMutability" == some "view") "balance getter must be view"
    let [ret] ← statements getter | throw "solidity.paymentSource: direct balance return required"
    require (J.kind ret == "Return") "getter return required"
    let b ← field ret "expression"
    require (J.kind b == "MemberAccess" && J.str? b "memberName" == some "balance") "self balance getter required"
    let this ← castReceiver (← field b "expression")
    require (J.ref? this == some (-28)) "getter must read actual this balance"
    return { base with
      creationId := creationId, referenceId := rootId, root := J.str? root "name",
      ownerReceive := some ownRecv, getter := some ((J.str? getter "name").getD "", ← id getter), methods := methods }
end Solidity.Frontend.PaymentPlan
