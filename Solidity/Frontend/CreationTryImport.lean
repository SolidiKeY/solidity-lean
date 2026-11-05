import Solidity.Frontend.Import
import Solidity.Semantics.CreationTryFrame

/-! A narrow complete-declaration adapter for the original zero-value,
stateless creation-try fixture. Constructor bodies, arguments and both caller
branches are compiled to existing intrinsic programs, not interpreted as ASTs. -/
namespace Solidity.Frontend.CreationTry
open Lean Elab Command Term Meta Semantics ContractWorld

/-- Compile a caller/constructor block at its actual named local context.
Only data retention differs from ordinary quotation, never self-frame flags. -/
def quoteBlock (closed : Bool) (C : Contract) (q : Lean.Expr) (ctx : ECtx) (ss : List RawStmt) : Except String Lean.Expr := do
  let Γ := (ECtx.toNCtx ctx).ctx
  let names := (ECtx.toNCtx ctx).names
  let action : ElabM (SProg C) := elabStmtsP C ss
  let P ← action.runFrom' { funs := C.funs, retainFailureData := true } (ctx, RawStmt.maxIdxs ss + 1)
  let b ← SProg.chain names Γ P
  if closed then pure (Prog.quoteShared q (Prog.cons (Stmt.block b.2) Prog.nil)).1
  else pure (Prog.quoteShared q (show Prog C Γ b.1 from b.2)).1

syntax "creation_block[" term "," term "]{" (sol_stmt solSemi)* "}" : term
elab_rules : term
 | `(creation_block[$c, $ctx]{ $[$ss:sol_stmt;]* }) => do
   let raw ← `(sol_raw!{ $[$ss;]* })
   elabAgainst c fun q => `(quoteBlock false $c $q $ctx $raw)

syntax "creation_scoped[" term "," term "]{" (sol_stmt solSemi)* "}" : term
elab_rules : term
 | `(creation_scoped[$c, $ctx]{ $[$ss:sol_stmt;]* }) => do
   let raw ← `(sol_raw!{ $[$ss;]* })
   elabAgainst c fun q => `(quoteBlock true $c $q $ctx $raw)

/-- All identities and text are read from the complete source declarations. -/
structure Method where
  name : String
  target : String
  created : String
  text : String
  argument : String
  initial : String
  handle : String
  reason : String
  successText : String
  caughtText : String

private def require (b : Bool) (why : String) : Except String Unit :=
  if b then .ok () else .error ("solidity.creationTry." ++ why)
private def get (j : Json) (key : String) : Except String Json := j.getObjVal? key
private def one (xs : List Json) (why : String) : Except String Json :=
  match xs with | [x] => .ok x | _ => .error ("solidity.creationTry." ++ why)
private def nm (j : Json) : String := (J.str? j "name").getD ""
private def ref (j : Json) : Option Int := J.ref? j <|> ((J.opt j "pathNode").bind J.ref?)
private def params (j : Json) (key := "parameters") : Except String (List Json) := do
  return (J.arrD (← get j key) "parameters").toList
private def sameRef (j declaration : Json) : Bool :=
  J.kind j == "Identifier" && (J.id? declaration).isSome && J.ref? j == J.id? declaration
private def uint (j : Json) : Bool := J.tyStr j == "uint256"
private def stringMemory (j : Json) : Bool := J.tyStr j == "string" && J.str? j "storageLocation" == some "memory"
private def statements (j : Json) : Except String (List Json) := do
  require (J.kind j == "Block") "block: complete ordinary block required"
  return (J.arrD j "statements").toList
private def literal (j : Json) : Bool := J.kind j == "Literal"
private def assignment (j destination : Json) : Except String Json := do
  require (J.kind j == "ExpressionStatement") "branch: assignment statement required"
  let a ← get j "expression"
  require (J.kind a == "Assignment" && J.str? a "operator" == some "=" && sameRef (← get a "leftHandSide") destination)
    "branch: exact resolved return assignment required"
  get a "rightHandSide"
private def addressArg (j : Json) : Except String Json := do
  require (J.kind j == "FunctionCall" && J.str? j "kind" == some "typeConversion") "address: cast required"
  let e ← get j "expression"
  require (J.kind e == "ElementaryTypeNameExpression" && nm (← get e "typeName") == "address") "address: address cast required"
  one (J.arrD j "arguments").toList "address: one operand required"

/-- Accept an entire stateless constructor, never skip an unsupported member. -/
private def closedTarget (target : Json) : Except String Unit := do
  require (J.str? target "contractKind" == some "contract" && J.opt target "abstract" == some (.bool false) &&
    (J.arrD target "baseContracts").isEmpty) "target: concrete noninheriting contract required"
  let ctor ← one (J.arrD target "nodes").toList "target: only one explicit constructor supported"
  require (J.kind ctor == "FunctionDefinition" && J.str? ctor "kind" == some "constructor" &&
    J.str? ctor "stateMutability" == some "nonpayable" && (J.arrD ctor "modifiers").isEmpty)
    "constructor: exact unmodified nonpayable constructor required"
  let arg ← one (← params ctor) "constructor: one uint parameter required"
  require (uint arg) "constructor: uint256 parameter required"
  require ((← params ctor "returnParameters").isEmpty) "constructor: no returns required"
  let ss ← statements (← get ctor "body")
  if ss.isEmpty then return
  let statement ← one ss "constructor: only empty body or revert(string literal) supported"
  require (J.kind statement == "ExpressionStatement") "constructor: complete revert statement required"
  let call ← get statement "expression"
  require (J.kind call == "FunctionCall" && builtinNamed (← get call "expression") "revert") "constructor: actual builtin revert required"
  let reason ← one (J.arrD call "arguments").toList "constructor: one actual reason required"
  require (literal reason && J.str? reason "kind" == some "string") "constructor: string literal reason required"

/-- Whole caller method: one evaluated uint local, then one typed creation try.
Return/argument/target/handler references are matched by compiler identities. -/
def readMethod (units : List Json) (owner method : Json) : Except String Method := do
  require (J.kind method == "FunctionDefinition" && J.str? method "kind" == some "function" &&
    [some "public", some "external"].contains (J.str? method "visibility") &&
    J.str? method "stateMutability" == some "nonpayable" && (J.arrD method "modifiers").isEmpty &&
    (← params method).isEmpty) "method: no-argument nonpayable unmodified ABI method required"
  let [created, text] ← params method "returnParameters" | throw "solidity.creationTry.result: bool and string memory required"
  require (J.tyStr created == "bool" && stringMemory text && !((nm created).isEmpty) && !((nm text).isEmpty))
    "result: named bool and string memory required"
  let [before, tried] ← statements (← get method "body") | throw "solidity.creationTry.body: exact uint prefix and try required"
  require (J.kind before == "VariableDeclarationStatement" && J.kind tried == "TryStatement") "body: exact uint prefix and try required"
  let argument ← one (J.arrD before "declarations").toList "prefix: one bound uint required"
  let initial ← get before "initialValue"
  require (uint argument && literal initial && J.str? initial "kind" == some "number" &&
    ((J.str? initial "value").bind String.toNat?).isSome &&
    !((J.str? initial "subdenomination").any (· != ""))) "prefix: decimal uint literal required"
  let call ← get tried "externalCall"
  require (J.kind call == "FunctionCall" && (J.arrD call "names").isEmpty) "creation: positional call required"
  let sourceArg ← one (J.arrD call "arguments").toList "creation: exactly one argument required"
  require (sameRef sourceArg argument) "creation: actual evaluated prefix argument required"
  let newExpr ← get call "expression"
  require (J.kind newExpr == "NewExpression") "creation: options/payment/other calls unsupported"
  let ty ← get newExpr "typeName"
  let target ← one (units.filter fun n => (ref ty).isSome && J.id? n == ref ty) "target: exact declaration required"
  require (J.id? target != J.id? owner) "target: distinct owner required"
  closedTarget target
  let [ok, err] := (J.arrD tried "clauses").toList | throw "solidity.creationTry.catch: success and Error only"
  require (J.str? ok "errorName" == some "" && J.str? err "errorName" == some "Error") "catch: Error(string) required"
  let handle ← one (← params ok) "success: one target handle required"
  require (ref (← get handle "typeName") == J.id? target) "success: wrong target handle type"
  let reason ← one (← params err) "catch: one reason binder required"
  require (stringMemory reason) "catch: string memory binder required"
  let okBlock ← get ok "block"
  let [assignCreated, assignText] ← statements okBlock | throw "solidity.creationTry.success: complete two-assignment body required"
  let comparison ← assignment assignCreated created
  let comparison := if J.kind comparison == "TupleExpression" && J.opt comparison "isInlineArray" == some (.bool false) then
    match (J.arrD comparison "components").toList with | [inner] => inner | _ => comparison
    else comparison
  require (J.kind comparison == "BinaryOperation" && J.str? comparison "operator" == some "!=") "success: actual address comparison required"
  let actualHandle ← addressArg (← get comparison "leftExpression")
  let zero ← addressArg (← get comparison "rightExpression")
  require (sameRef actualHandle handle && literal zero && J.str? zero "value" == some "0") "success: actual handle versus zero required"
  let successText ← assignment assignText text
  require (literal successText && J.str? successText "kind" == some "string") "success: actual string literal required"
  let errBlock ← get err "block"
  let copied ← one (← statements errBlock) "catch: one reason assignment required"
  require (sameRef (← assignment copied text) reason) "catch: actual decoded reason must be assigned"
  let names := [nm created, nm text, nm argument, nm handle, nm reason]
  require (names.eraseDups.length == names.length && !(names.any (·.startsWith "__creation_")))
    "names: distinct source binders and reserved adapter names required"
  let readBlock (b : Json) : Except String String :=
    ((block b).run' { declarations := J.nodes owner }).mapError Gap.msg
  let successText ← readBlock okBlock
  let caughtText ← readBlock errBlock
  return ⟨nm method, nm target, nm created, nm text, nm argument,
    (J.str? initial "value").getD "", nm handle, nm reason, successText, caughtText⟩

syntax (name := solcCreationTry) "solc_creation_try " str " hash " num
  " from_contract " str " as " ident : command

/-- Compile each complete admitted method, retaining source constructor and
caller bodies as intrinsic programs with separate typed world/local frames. -/
@[command_elab solcCreationTry]
def elabCreationTry : CommandElab := fun stx => do
  let path : TSyntax `str := ⟨stx[1]⟩
  let fixtureHash : TSyntax `num := ⟨stx[3]⟩
  let file := System.FilePath.mk (← getFileName)
  let bytes ← IO.FS.readBinFile ((file.parent.getD ".") / path.getString)
  unless (fnv1a64 bytes).toNat == fixtureHash.getNat do throwError "solidity.creationTry.hash: fixture bytes changed"
  let some text := String.fromUTF8? bytes | throwError "solidity.creationTry.fixture: UTF-8 required"
  let json ← ofExcept (Json.parse text)
  let ast ← ofExcept (json.getObjVal? "ast")
  let units := (J.arrD ast "nodes").toList.filter (J.kind · == "ContractDefinition")
  let ownerName := stx[5].isStrLit?.getD ""
  let owner ← ofExcept (one (units.filter (nm · == ownerName)) "owner: exact declaration required")
  ofExcept <| require (J.str? owner "contractKind" == some "contract" && J.opt owner "abstract" == some (.bool false) &&
    (J.arrD owner "baseContracts").isEmpty && (J.arrD owner "nodes").all (J.kind · == "FunctionDefinition"))
    "owner: stateless concrete caller with implicit constructor required"
  let methods ← ofExcept ((J.arrD owner "nodes").toList.mapM (readMethod units owner))
  unless !methods.isEmpty do throwError "solidity.creationTry.owner: methods required"
  unless units.all (fun u => nm u == ownerName || methods.any (·.target == nm u)) do
    throwError "solidity.creationTry.catalog: untracked source declaration"
  let output := stx[7].getId.toString
  let full := (← getCurrNamespace) ++ stx[7].getId
  let cmd (text : String) : CommandElabM Unit := do
    let parsed ← ofExcept (Parser.runParserCategory (← getEnv) `command text)
    elabCommand (atRef stx parsed)
  let source (name : String) := s!"{full}.Source.{identText name}"
  for unit in units do
    let name := mkIdent (full ++ `Source ++ Name.mkSimple (nm unit))
    elabCommand (← `(solc_import $path hash $fixtureHash as $name testing))
  let kinds := units.zipIdx |>.map fun (_, i) => s!" | c{i}"
  cmd s!"inductive {output}.Code where\n{String.intercalate "\n" kinds}\n deriving DecidableEq"
  let rows := units.zipIdx |>.map fun (unit, i) => s!" | .c{i} => {source (nm unit)}"
  cmd s!"def {output}.contracts : {output}.Code → Solidity.Contract\n{String.intercalate "\n" rows}"
  let ownerIdx := units.findIdx (nm · == ownerName)
  let O := s!"{output}.contracts .c{ownerIdx}"
  cmd s!"def {output}.deploy (w : Solidity.ContractWorld.World {output}.contracts) (self : Solidity.ContractWorld.Address) (ctx : Solidity.ContractWorld.Context) := w.create {output}.Code.c{ownerIdx} self Solidity.Prog.nil ctx"
  for (method, i) in methods.zipIdx do
    let ns := s!"{output}.m{i}"
    let n := s!"{full}.m{i}"
    let targetIdx := units.findIdx (nm · == method.target)
    let T := s!"{output}.contracts .c{targetIdx}"
    let created := identText method.created
    let txt := identText method.text
    let arg := identText method.argument
    let ctx := s!"[({toJson method.argument |>.compress}, .val .uint 256), ({toJson method.text |>.compress}, .mem Solidity.bytesR [(\"[]\", 8), (\"[]#bytes\", 1)]), ({toJson method.created |>.compress}, .val .bool 256)]"
    cmd s!"def {ns}.before : Solidity.Prog ({O}) [] [.val .uint, .mem Solidity.bytesR, .val .bool] := creation_block[{source ownerName}, ([] : Solidity.ECtx)]\{ bool {created}; string memory {txt}; uint {arg} = {method.initial}; }"
    cmd s!"def {ns}.constructorBody : Solidity.Prog ({T}) [.val .uint] [.val .uint] := creation_block[{source method.target}, [(\"__creation_argument\", .val .uint 256)]]\{ constructor(__creation_argument); }"
    cmd s!"def {ns}.ok : Solidity.Prog ({O}) [.val .uint, .val .uint, .mem Solidity.bytesR, .val .bool] [.val .uint, .val .uint, .mem Solidity.bytesR, .val .bool] := creation_scoped[{source ownerName}, ({toJson method.handle |>.compress}, .val .uint 160) :: ({ctx} : Solidity.ECtx)]\{ {method.successText} }"
    cmd s!"def {ns}.err : Solidity.Prog ({O}) [.mem Solidity.bytesR, .val .uint, .mem Solidity.bytesR, .val .bool] [.mem Solidity.bytesR, .val .uint, .mem Solidity.bytesR, .val .bool] := creation_scoped[{source ownerName}, ({toJson method.reason |>.compress}, .mem Solidity.bytesR [(\"[]\", 8), (\"[]#bytes\", 1)]) :: ({ctx} : Solidity.ECtx)]\{ {method.caughtText} }"
    cmd s!"def {ns}.encoderBody : Solidity.Prog ({O}) [.mem Solidity.bytesR, .val .uint, .mem Solidity.bytesR, .val .bool] [.mem Solidity.bytesR, .val .uint, .mem Solidity.bytesR, .val .bool] := creation_scoped[{source ownerName}, (\"__creation_encoded\", .mem Solidity.bytesR [(\"[]\",8), (\"[]#bytes\",1)]) :: ({ctx} : Solidity.ECtx)]\{ __creation_encoded = abi.encode({created}, {txt}); }"
    cmd s!"def {ns}.encode : Solidity.Prog ({O}) [.val .uint, .mem Solidity.bytesR, .val .bool] [.mem Solidity.bytesR, .val .uint, .mem Solidity.bytesR, .val .bool] := .cons (.declMem Solidity.bytesR (.user \"__creation_encoded\") none rfl rfl) {full}.m{i}.encoderBody"
    cmd s!"def {ns}.runWith (bounded : Bool) (w : Solidity.ContractWorld.World {output}.contracts) (self : Solidity.ContractWorld.Handle {output}.Code.c{ownerIdx}) (ctx : Solidity.ContractWorld.Context) (fresh : Solidity.ContractWorld.Address) : Solidity.TRes (Solidity.ContractWorld.World {output}.contracts × List Nat) := do\n if w.isLibrary .c{ownerIdx} || ctx.isStatic || ctx.value.1 != 0 || !ctx.ext.isEmpty then .error .revert else do\n let st ← Solidity.TRes.ofOpt (w.storage? self)\n let entry ← w.enter (k := .c{ownerIdx}) self.address ctx st false\n Solidity.ContractWorld.CreationTryFrame.execute (caller := .c{ownerIdx}) (α := Solidity.ContractWorld.Word) w entry self.address (if bounded then {n}.before.runF 1000 else {n}.before.runR) (fun (start : Solidity.State ({O}) [.val .uint, .mem Solidity.bytesR, .val .bool]) => .ok (Solidity.TEnv.get .here start.env)) .c{targetIdx} (fun _ => fresh) (fun a => Solidity.ContractWorld.CreationTryFrame.constructorArg {n}.constructorBody a) (fun _ => \{ sender := self.address, ext := ctx.ext }) (.push .refl) (fun handle => Solidity.TRun.seq (Solidity.TRun.declLocal .uint (some (.simple (.lit handle.address.1.1 handle.address.1.2)))) (if bounded then {n}.ok.runF 1000 else {n}.ok.runR)) (.push .refl) (fun halt => Solidity.ContractWorld.CreationTryFrame.errorData halt (if bounded then {n}.err.runF 1000 else {n}.err.runR)) (if bounded then {n}.encode.runF 1000 else {n}.encode.runR) (fun st => ((Solidity.RevPart.mem .raw .here).evalT st).map (List.map UInt8.toNat))"
    cmd s!"def {ns}.run := {full}.m{i}.runWith true"
    cmd s!"def {ns}.runOrdinary := {full}.m{i}.runWith false"
    cmd s!"theorem {ns}.run_approx (w : Solidity.ContractWorld.World {output}.contracts) (self : Solidity.ContractWorld.Handle {output}.Code.c{ownerIdx}) (ctx : Solidity.ContractWorld.Context) (fresh : Solidity.ContractWorld.Address) : Solidity.TRes.Approx ({n}.run w self ctx fresh) ({n}.runOrdinary w self ctx fresh) := by\n unfold {n}.run {n}.runOrdinary {n}.runWith\n split\n · exact .refl _\n · apply Solidity.TRes.Approx.bind (Solidity.TRes.Approx.refl _)\n   intro st\n   apply Solidity.TRes.Approx.bind (Solidity.TRes.Approx.refl _)\n   intro entry\n   simp only [Bool.false_eq_true, ↓reduceIte]\n   apply Solidity.ContractWorld.CreationTryFrame.execute_approx\n   · exact Solidity.Prog.runF_approx 1000 {n}.before\n   · intro handle; exact Solidity.TRun.seq_approx (fun _ => .refl _) (Solidity.Prog.runF_approx 1000 {n}.ok)\n   · intro halt; exact Solidity.ContractWorld.CreationTryFrame.errorData_approx (Solidity.Prog.runF_approx 1000 {n}.err) halt\n   · exact Solidity.Prog.runF_approx 1000 {n}.encode"

  let choices := methods.zipIdx |>.map fun (method,i) => s!" | {toJson (method.name ++ "()") |>.compress} => {full}.m{i}.run w self ctx fresh"
  cmd s!"def {output}.run (w : Solidity.ContractWorld.World {output}.contracts) (self : Solidity.ContractWorld.Handle {output}.Code.c{ownerIdx}) (ctx : Solidity.ContractWorld.Context) (fresh : Solidity.ContractWorld.Address) (signature : String) : Solidity.TRes (Solidity.ContractWorld.World {output}.contracts × List Nat) := match signature with\n{String.intercalate "\n" choices}\n | _ => .error .revert"

end Solidity.Frontend.CreationTry
