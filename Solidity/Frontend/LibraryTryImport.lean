import Solidity.Frontend.CreationTryImport
import Solidity.Semantics.LibraryTryFrame

/-! Complete-declaration admission for the closed linked-library try fragment.
The source bodies become intrinsic caller-typed programs. No library storage,
oracle outcome, compiler bytecode or expected observation supplies their results. -/
namespace Solidity.Frontend.LibraryTry
open Lean Elab Command Term Meta Semantics ContractWorld

/-- Existing return lowering and typed quotations, retaining actual halt data. -/
def quoteBody (C : Contract) (q : Lean.Expr) (ctx : ECtx) (rets : List String)
    (ss : List RawStmt) : Except String Lean.Expr := do
  CreationTry.quoteBlock true C q ctx (← lowerReturns rets ss)
syntax "library_body[" term "," term "," term "]{" (sol_stmt solSemi)* "}" : term
elab_rules : term
 | `(library_body[$c, $ctx, $rets]{ $[$ss:sol_stmt;]* }) => do
   let raw ← `(sol_raw!{ $[$ss;]* })
   elabAgainst c fun q => `(quoteBody $c $q $ctx $rets $raw)

/-- Resolve a source storage formal to the actual typed caller root. The alias
is live only inside this library body; it is not a copied library storage. -/
def quoteStorageBody (C : Contract) (q : Lean.Expr) (ctx : ECtx) (rets : List String)
    (root formal : String) (ss : List RawStmt) : Except String Lean.Expr := do
  let some (.ref (.struct encoding)) := C.rootType root
    | throw "library storage mapping requires an actual caller struct root"
  let fresh := "__library_storage_formal"
  quoteBody C q ctx rets (.declStorage (.named encoding) fresh (some (.name root)) ::
    ss.map (RawStmt.renameName formal fresh))
syntax "library_storage_body[" term "," term "," term "," term "," term "]{" (sol_stmt solSemi)* "}" : term
elab_rules : term
 | `(library_storage_body[$c, $ctx, $rets, $root, $formal]{ $[$ss:sol_stmt;]* }) => do
   let raw ← `(sol_raw!{ $[$ss;]* })
   elabAgainst c fun q => `(quoteStorageBody $c $q $ctx $rets $root $formal $raw)

private def req (b : Bool) (why : String) : Except String Unit :=
  if b then .ok () else .error ("solidity.libraryTry." ++ why)
private def get (j : Json) (s : String) := j.getObjVal? s
private def one (xs : List Json) (why : String) : Except String Json :=
  match xs with | [x] => .ok x | _ => .error ("solidity.libraryTry." ++ why)
private def nm (j : Json) := (J.str? j "name").getD ""
private def ref (j : Json) := J.ref? j <|> ((J.opt j "pathNode").bind J.ref?)
private def same (j d : Json) := J.kind j == "Identifier" && (J.id? d).isSome && J.ref? j == J.id? d && nm j == nm d
private def ps (j : Json) (key := "parameters") : Except String (List Json) := do
  return (J.arrD (← get j key) "parameters").toList
private def ss (j : Json) : Except String (List Json) := do
  req (J.kind j == "Block") "ordinary complete block required"
  return (J.arrD j "statements").toList
private def uint (j : Json) := J.tyStr j == "uint256"
private def bool (j : Json) := J.tyStr j == "bool"
private def string (j : Json) := J.tyStr j == "string" && J.str? j "storageLocation" == some "memory"
private def number (j : Json) := J.kind j == "Literal" && J.str? j "kind" == some "number" &&
  (J.str? j "subdenomination").getD "" == "" && ((J.str? j "value").bind String.toNat?).isSome
private def member (j root field : Json) := J.kind j == "MemberAccess" && J.ref? j == J.id? field && J.str? j "memberName" == some (nm field) &&
  (J.opt j "expression").any (same · root)
private def ret (b : Json) : Except String Json := do
  let r ← one (← ss b) "one complete return required"
  req (J.kind r == "Return") "return required"
  get r "expression"
private def stmtText (b : Json) : Except String String :=
  ((stmt b).run' {}).map (String.intercalate "; ") |>.mapError Gap.msg
private def text (b : Json) : Except String String :=
  ((block b).run' {}).mapError Gap.msg

/-- Source identities and actual blocks of one complete try method. -/
structure Method where
  name : String
  argument : String
  prefixBody : String
  scalar : String
  formal : String
  flag : String
  result : String
  reason : String
  libraryBody : String
  successBody : String
  caughtBody : String
  storage : Bool

/-- Read the entire caller/library catalog, including the exact storage
method, so no unknown source member is silently erased. -/
def read (ast : Json) (ownerName : String) : Except String (String × String × String × List Method) := do
  let units := (J.arrD ast "nodes").toList.filter (J.kind · == "ContractDefinition")
  let owner ← one (units.filter (nm · == ownerName)) "unique owner required"
  let lib ← one (units.filter (J.str? · "contractKind" == some "library")) "unique source library required"
  req (units.length == 2 && J.str? owner "contractKind" == some "contract" &&
    [owner,lib].all (fun c => J.opt c "abstract" == some (.bool false) && (J.arrD c "baseContracts").isEmpty)) "closed concrete catalog required"
  let ln := (J.arrD lib "nodes").toList
  let structDecl ← one (ln.filter (J.kind · == "StructDefinition")) "one library struct required"
  let field ← one (J.arrD structDecl "members").toList "one struct field required"
  req (uint field && ln.length == 3) "uint256 field and two library methods required"
  let on := (J.arrD owner "nodes").toList
  let root ← one (on.filter (J.kind · == "VariableDeclaration")) "one caller root required"
  req (J.opt root "stateVariable" == some (.bool true) && (J.opt root "value").isNone &&
    J.opt root "constant" == some (.bool false) && ref (← get root "typeName") == J.id? structDecl) "exact default caller struct root required"
  let usingDecl ← one (on.filter (J.kind · == "UsingForDirective")) "one exact using declaration required"
  req (J.opt usingDecl "global" == some (.bool false) && ref (← get usingDecl "libraryName") == J.id? lib &&
    ref (← get usingDecl "typeName") == J.id? structDecl && on.length == 4) "exact library/struct using required"
  let methods := on.filter (J.kind · == "FunctionDefinition")
  req (methods.length == 2) "two complete caller methods required"
  let mut used : List Int := []
  let mut result := []
  for method in methods do
    req (J.str? method "kind" == some "function" && J.str? method "visibility" == some "public" &&
      J.str? method "stateMutability" == some "nonpayable" && (J.arrD method "modifiers").isEmpty) "public nonpayable method required"
    let input ← one (← ps method) "one bool caller argument required"
    req (bool input) "bool caller argument required"
    let [r0,r1] ← ps method "returnParameters" | throw "solidity.libraryTry.uint/string result required"
    req (uint r0 && string r1 && nm r0 == "" && nm r1 == "") "unnamed uint/string results required"
    let [leading,attempt] ← ss (← get method "body") | throw "solidity.libraryTry.prefix and try required"
    req (J.kind attempt == "TryStatement") "actual try required"
    let call ← get attempt "externalCall"
    req (J.kind call == "FunctionCall" && (J.arrD call "names").isEmpty) "positional call required"
    let callee ← get call "expression"
    req (J.kind callee == "MemberAccess") "resolved library call required"
    let fn ← one (ln.filter (fun n => J.kind n == "FunctionDefinition" && J.id? n == J.ref? callee)) "exact library declaration required"
    req (J.str? callee "memberName" == some (nm fn)) "matching library member spelling required"
    req (J.str? fn "visibility" == some "public" && J.str? fn "stateMutability" == some "view" &&
      J.str? fn "kind" == some "function" && (J.arrD fn "modifiers").isEmpty) "unmodified public view library entry required"
    let [formal,flag] ← ps fn | throw "solidity.libraryTry.two ordered library parameters required"
    let output ← one (← ps fn "returnParameters") "one library result required"
    req (bool flag && uint output && nm output == "") "actual bool flag and uint result required"
    let storage := J.str? formal "storageLocation" == some "storage"
    let mut scalar := ""
    if storage then
      req (ref (← get formal "typeName") == J.id? structDecl && same (← get callee "expression") root) "exact caller receiver/formal struct required"
      let a ← one (J.arrD call "arguments").toList "one using flag required"
      req (same a input) "actual using flag required"
      let assign ← get leading "expression"
      req (J.kind leading == "ExpressionStatement" && J.kind assign == "Assignment" && J.str? assign "operator" == some "=" &&
        member (← get assign "leftHandSide") root field && number (← get assign "rightHandSide")) "exact caller root/field prefix required"
    else
      req (uint formal && same (← get callee "expression") lib && J.kind leading == "VariableDeclarationStatement") "scalar direct library call required"
      let localDecl ← one (J.arrD leading "declarations").toList "one scalar prefix required"
      req (uint localDecl && number (← get leading "initialValue")) "evaluated uint prefix required"
      scalar := nm localDecl
      let [a,b] := (J.arrD call "arguments").toList | throw "solidity.libraryTry.two ordered arguments required"
      req (same a localDecl && same b input) "actual ordered scalar/bool arguments required"
    let branch ← one (← ss (← get fn "body")) "one complete library if required"
    req (J.kind branch == "IfStatement" && same (← get branch "condition") flag) "actual library flag required"
    let returned ← ret (← get branch "trueBody")
    req (if storage then member returned formal field else same returned formal) "actual formal/root member return required"
    let failure ← one (← ss (← get branch "falseBody")) "one revert required"
    let reverted ← get failure "expression"
    req (J.kind failure == "ExpressionStatement" && J.kind reverted == "FunctionCall" &&
      builtinNamed (← get reverted "expression") "revert") "actual builtin revert required"
    let message ← one (J.arrD reverted "arguments").toList "one revert reason required"
    req (J.kind message == "Literal" && J.str? message "kind" == some "string") "actual literal Error reason required"
    let [ok,err] := (J.arrD attempt "clauses").toList | throw "solidity.libraryTry.success and Error required"
    let bound ← one (← ps ok) "one actual uint return binder required"
    let reason ← one (← ps err) "one Error binder required"
    req (J.str? ok "errorName" == some "" && uint bound && J.str? err "errorName" == some "Error" && string reason) "typed success/Error clauses required"
    let success ← ret (← get ok "block")
    let [v,t] := (J.arrD success "components").toList | throw "solidity.libraryTry.exact success pair required"
    req (J.kind success == "TupleExpression" && J.opt success "isInlineArray" == some (.bool false) && same v bound &&
      J.kind t == "Literal" && J.str? t "kind" == some "string") "actual success value/string required"
    let caught ← ret (← get err "block")
    let [v,t] := (J.arrD caught "components").toList | throw "solidity.libraryTry.exact catch pair required"
    req (J.kind caught == "TupleExpression" && J.opt caught "isInlineArray" == some (.bool false) && number v && same t reason) "actual caught number/reason required"
    req (![nm input,nm formal,nm flag,nm bound,nm reason,scalar].any (·.startsWith "__library_")) "reserved adapter names refused"
    let some id := J.id? fn | throw "solidity.libraryTry.missing declaration identity"
    used := id :: used
    result := result ++ [⟨nm method,nm input,← stmtText leading,scalar,nm formal,nm flag,nm bound,nm reason,
      ← text (← get fn "body"),← text (← get ok "block"),← text (← get err "block"),storage⟩]
  req (used.eraseDups.length == 2 && result.any (·.storage) && result.any (! ·.storage)) "complete distinct library mappings required"
  return (nm lib,nm root,nm field,result)

syntax (name := solcLibraryTry) "solc_library_try " str " hash " num " from_contract " str " as " ident : command

/-- Compile the complete linked source declarations with scalar and exact storage-formal
mappings, retaining caller-typed bodies and actual result/catch continuations. -/
@[command_elab solcLibraryTry]
def elabLibraryTry : CommandElab := fun stx => do
  let path : TSyntax `str := ⟨stx[1]⟩
  let fixtureHash : TSyntax `num := ⟨stx[3]⟩
  let file := System.FilePath.mk (← getFileName)
  let bytes ← IO.FS.readBinFile ((file.parent.getD ".") / path.getString)
  unless (fnv1a64 bytes).toNat == fixtureHash.getNat do throwError "solidity.libraryTry.hash: changed fixture"
  let some text := String.fromUTF8? bytes | throwError "solidity.libraryTry.UTF8"
  let json ← ofExcept (Json.parse text)
  let ast ← ofExcept (json.getObjVal? "ast")
  let owner := stx[5].isStrLit?.getD ""
  let (lib,root,field,methods) ← ofExcept (read ast owner)
  let out := stx[7].getId.toString
  let full := (← getCurrNamespace) ++ stx[7].getId
  let cmd (s : String) : CommandElabM Unit := do
    let parsed ← ofExcept (Parser.runParserCategory (← getEnv) `command s)
    elabCommand (atRef stx parsed)
  let source (n : String) := s!"{full}.Source.{identText n}"
  for n in [owner,lib] do
    let name := mkIdent (full ++ `Source ++ Name.mkSimple n)
    elabCommand (← `(solc_import $path hash $fixtureHash as $name testing))
  cmd s!"inductive {out}.Code where\n | caller | library\n deriving DecidableEq"
  cmd s!"def {out}.contracts : {out}.Code → Solidity.Contract\n | .caller => {source owner}\n | .library => {source lib}"
  cmd s!"def {out}.roles : {out}.Code → Solidity.ContractWorld.Role\n | .caller => .contractCode\n | .library => .libraryCode"
  cmd s!"def {out}.deployCaller (w : Solidity.ContractWorld.World {out}.contracts) (a : Solidity.ContractWorld.Address) (ctx : Solidity.ContractWorld.Context) := w.create {out}.Code.caller a Solidity.Prog.nil ctx"
  cmd s!"def {out}.deployLibrary (w : Solidity.ContractWorld.World {out}.contracts) (a : Solidity.ContractWorld.Address) (ctx : Solidity.ContractWorld.Context) := w.deployLibrary {out}.Code.library a ctx"
  cmd s!"def {out}.storageProgram : Solidity.Prog ({out}.contracts .caller) [] [.val .uint] := creation_block[{source owner}, ([] : Solidity.ECtx)]\{ uint __library_field_read = {identText root}.{identText field}; }"
  cmd s!"def {out}.readStorage (w : Solidity.ContractWorld.World {out}.contracts) (self : Solidity.ContractWorld.Handle {out}.Code.caller) : Solidity.TRes Int := do\n let storage ← Solidity.TRes.ofOpt (w.storage? self)\n let out ← {full}.storageProgram.runF 1000 (\{ Solidity.State.init ({out}.contracts .caller) with storage } : Solidity.State ({out}.contracts .caller) [])\n pure ((Solidity.TEnv.get .here out.st.env : Solidity.ContractWorld.Word).1)"
  for (method,i) in methods.zipIdx do
    let ns := s!"{out}.m{i}"
    let n := s!"{full}.m{i}"
    let C := s!"{out}.contracts .caller"
    let q := fun (s : String) => toJson s |>.compress
    let ctx := s!"[({q method.scalar}, .val .uint), ({q method.argument}, .val .bool), (\"__library_text\", .mem Solidity.bytesR [(\"[]\",8),(\"[]#bytes\",1)]), (\"__library_out\", .val .uint)]"
    let baseCtx := s!"[({q method.argument}, .val .bool), (\"__library_text\", .mem Solidity.bytesR [(\"[]\",8),(\"[]#bytes\",1)]), (\"__library_out\", .val .uint)]"
    let ctx := if method.storage then baseCtx else ctx
    let Γ := if method.storage then "[.val .bool, .mem Solidity.bytesR, .val .uint]" else "[.val .uint, .val .bool, .mem Solidity.bytesR, .val .uint]"
    let ArgTy := if method.storage then "Bool" else "Solidity.ContractWorld.Word × Bool"
    let args := if method.storage then "Solidity.TEnv.get .here st.env" else "(Solidity.TEnv.get .here st.env, Solidity.TEnv.get (.there .here) st.env)"
    cmd s!"def {ns}.prefixBody : Solidity.Prog ({C}) [.val .bool, .mem Solidity.bytesR, .val .uint] {Γ} := creation_block[{source owner}, ({baseCtx} : Solidity.ECtx)]\{ {method.prefixBody}; }"
    cmd s!"def {ns}.before (b : Bool) : Solidity.Prog ({C}) [] {Γ} := .cons (.declLocal .uint (.user \"__library_out\") none) (.cons (.declMem Solidity.bytesR (.user \"__library_text\") none rfl rfl) (.cons (.declLocal .bool (.user {q method.argument}) (some (.simple (.bool b)))) {n}.prefixBody))"
    if method.storage then
      let lc := s!"[({q method.flag}, .val .bool), (\"__library_value\", .val .uint)]"
      cmd s!"def {ns}.libraryBody : Solidity.Prog ({C}) [.val .bool, .val .uint] [.val .bool, .val .uint] := library_storage_body[{source owner}, ({lc} : Solidity.ECtx), [\"__library_value\"], {q root}, {q method.formal}]\{ {method.libraryBody} }"
      cmd s!"def {ns}.libraryProgram (b : Bool) : Solidity.Prog ({C}) [] [.val .uint] := .cons (.declLocal .uint (.user \"__library_value\") none) (.cons (.block (.cons (.declLocal .bool (.user {q method.flag}) (some (.simple (.bool b)))) {n}.libraryBody)) .nil)"
    else
      let lc := s!"[({q method.flag}, .val .bool), ({q method.formal}, .val .uint), (\"__library_value\", .val .uint)]"
      cmd s!"def {ns}.libraryBody : Solidity.Prog ({C}) [.val .bool, .val .uint, .val .uint] [.val .bool, .val .uint, .val .uint] := library_body[{source owner}, ({lc} : Solidity.ECtx), [\"__library_value\"]]\{ {method.libraryBody} }"
      cmd s!"def {ns}.libraryProgram (a : Solidity.ContractWorld.Word) (b : Bool) : Solidity.Prog ({C}) [] [.val .uint] := .cons (.declLocal .uint (.user \"__library_value\") none) (.cons (.block (.cons (.declLocal .uint (.user {q method.formal}) (some (.simple (.lit a.1 a.2)))) (.cons (.declLocal .bool (.user {q method.flag}) (some (.simple (.bool b)))) {n}.libraryBody))) .nil)"
    let application := if method.storage then s!"{n}.libraryProgram a" else s!"{n}.libraryProgram a.1 a.2"
    cmd s!"def {ns}.linked (address : Solidity.ContractWorld.Address) (a : {ArgTy}) : Solidity.ContractWorld.LibraryTryFrame.RawLibrary {out}.contracts .caller := ⟨⟨.library, address, ⟨[.val .uint], {application}, fun st => .ok [Solidity.TEnv.get .here st.env], false⟩⟩, fun st => ⟨[Solidity.TEnv.get .here st.env], rfl⟩⟩"
    cmd s!"def {ns}.decode (words : List Solidity.ContractWorld.Word) : Solidity.TRes Solidity.ContractWorld.Word := ((Solidity.Binders.snoc .nil .uint (.user {q method.result})).decodeT (C := {C}) (H := []) words).map (fun x => x.1.1)"
    cmd s!"def {ns}.ok : Solidity.Prog ({C}) (.val .uint :: {Γ}) (.val .uint :: {Γ}) := library_body[{source owner}, ({q method.result}, .val .uint) :: ({ctx} : Solidity.ECtx), [\"__library_out\",\"__library_text\"]]\{ {method.successBody} }"
    cmd s!"def {ns}.err : Solidity.Prog ({C}) (.mem Solidity.bytesR :: {Γ}) (.mem Solidity.bytesR :: {Γ}) := library_body[{source owner}, ({q method.reason}, .mem Solidity.bytesR [(\"[]\",8),(\"[]#bytes\",1)]) :: ({ctx} : Solidity.ECtx), [\"__library_out\",\"__library_text\"]]\{ {method.caughtBody} }"
    cmd s!"def {ns}.encoderBody : Solidity.Prog ({C}) (.mem Solidity.bytesR :: {Γ}) (.mem Solidity.bytesR :: {Γ}) := creation_scoped[{source owner}, (\"__library_encoded\", .mem Solidity.bytesR [(\"[]\",8),(\"[]#bytes\",1)]) :: ({ctx} : Solidity.ECtx)]\{ __library_encoded = abi.encode(__library_out, __library_text); }"
    cmd s!"def {ns}.encode : Solidity.Prog ({C}) {Γ} (.mem Solidity.bytesR :: {Γ}) := .cons (.declMem Solidity.bytesR (.user \"__library_encoded\") none rfl rfl) {n}.encoderBody"
    cmd s!"def {ns}.runWith (bounded : Bool) (w : Solidity.ContractWorld.World {out}.contracts) (self : Solidity.ContractWorld.Handle {out}.Code.caller) (ctx : Solidity.ContractWorld.Context) (address : Solidity.ContractWorld.Address) (b : Bool) : Solidity.TRes (Solidity.ContractWorld.World {out}.contracts × List Nat) := do\n if ctx.isStatic || ctx.value.1 != 0 || !ctx.ext.isEmpty then .error .revert else do\n let storage ← Solidity.TRes.ofOpt (w.storage? self)\n let initial ← w.enter (k := .caller) self.address ctx storage false\n Solidity.ContractWorld.LibraryTryFrame.execute (contracts := {out}.contracts) (caller := {out}.Code.caller) (α := {ArgTy}) (β := Solidity.ContractWorld.Word) (γ := List Nat) (Γ := {Γ}) (Δ := .mem Solidity.bytesR :: {Γ}) w self initial (if bounded then ({n}.before b).runF 1000 else ({n}.before b).runR) (fun (st : Solidity.State ({C}) {Γ}) => .ok ({args})) ({n}.linked address) ctx {n}.decode (fun value => Solidity.TRun.seq (Solidity.TRun.block (.push .refl) (Solidity.TRun.seq (Solidity.TRun.declLocal .uint (some (.simple (.lit value.1 value.2)))) (if bounded then {n}.ok.runF 1000 else {n}.ok.runR))) (if bounded then {n}.encode.runF 1000 else {n}.encode.runR)) (fun halt => Solidity.TRun.seq (Solidity.TRun.block (.push .refl) (Solidity.ContractWorld.CreationTryFrame.errorData halt (if bounded then {n}.err.runF 1000 else {n}.err.runR))) (if bounded then {n}.encode.runF 1000 else {n}.encode.runR)) (fun st => ((Solidity.RevPart.mem .raw .here).evalT st).map (List.map UInt8.toNat))"
    cmd s!"def {ns}.run := {n}.runWith true"
    cmd s!"def {ns}.runOrdinary := {n}.runWith false"
    cmd s!"theorem {ns}.run_approx (w : Solidity.ContractWorld.World {out}.contracts) (self : Solidity.ContractWorld.Handle {out}.Code.caller) (ctx : Solidity.ContractWorld.Context) (address : Solidity.ContractWorld.Address) (b : Bool) : Solidity.TRes.Approx ({n}.run w self ctx address b) ({n}.runOrdinary w self ctx address b) := by\n unfold {n}.run {n}.runOrdinary {n}.runWith\n split\n · exact .refl _\n · apply Solidity.TRes.Approx.bind (.refl _)\n   intro storage\n   apply Solidity.TRes.Approx.bind (.refl _)\n   intro initial\n   simp only [Bool.false_eq_true, ↓reduceIte]\n   apply Solidity.ContractWorld.LibraryTryFrame.execute_approx\n   · exact Solidity.Prog.runF_approx 1000 ({n}.before b)\n   · intro value\n     apply Solidity.TRun.seq_approx\n     · apply Solidity.TRun.block_approx\n       exact Solidity.TRun.seq_approx (fun _ => .refl _) (Solidity.Prog.runF_approx 1000 {n}.ok)\n     · exact Solidity.Prog.runF_approx 1000 {n}.encode\n   · intro halt\n     apply Solidity.TRun.seq_approx\n     · apply Solidity.TRun.block_approx\n       exact Solidity.ContractWorld.CreationTryFrame.errorData_approx (Solidity.Prog.runF_approx 1000 {n}.err) halt\n     · exact Solidity.Prog.runF_approx 1000 {n}.encode"
  let choices := methods.zipIdx |>.map fun (m,i) => s!" | {toJson (m.name ++ "(bool)") |>.compress} => {full}.m{i}.run w self ctx address b"
  cmd s!"def {out}.run (w : Solidity.ContractWorld.World {out}.contracts) (self : Solidity.ContractWorld.Handle {out}.Code.caller) (ctx : Solidity.ContractWorld.Context) (address : Solidity.ContractWorld.Address) (signature : String) (b : Bool) : Solidity.TRes (Solidity.ContractWorld.World {out}.contracts × List Nat) := match signature with\n{String.intercalate "\n" choices}\n | _ => .error .revert"
end Solidity.Frontend.LibraryTry
