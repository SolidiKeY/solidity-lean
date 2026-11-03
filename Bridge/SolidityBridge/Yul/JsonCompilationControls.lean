import SolidityBridge.Yul.JsonCompilation
import SolidityBridge.Yul.ArithmeticSelectionControls
/-! Synthetic JSON ingress/kernel-model controls, not external solc evidence
or proof of source attachment/whole frontend admission. -/
namespace SolidityBridge.Yul.JsonCompilation.Controls
open Solidity Backend Scalar Selection
open Lean (Json)
open Solidity.Frontend.YulJson
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe

def lit (value : String) : Json := Json.mkObj
  [("nodeType",.str "YulLiteral"),("kind",.str "number"),("type",.str ""),("value",.str value)]
def ident (name : String) : Json := Json.mkObj [("nodeType",.str "YulIdentifier"),("name",.str name)]
def call (name : String) (args : Array Json) : Json := Json.mkObj
  [("nodeType",.str "YulFunctionCall"),("functionName",ident name),("arguments",.arr args)]
def decl (name : String) (value : Json) : Json := Json.mkObj
  [("nodeType",.str "YulVariableDeclaration"),("variables",.arr #[Json.mkObj
    [("nodeType",.str "YulTypedName"),("name",.str name),("type",.str "")]]),("value",value)]
def assign (name : String) (value : Json) : Json := Json.mkObj
  [("nodeType",.str "YulAssignment"),("variableNames",.arr #[ident name]),("value",value)]
def block (body : Array Json) : Json := Json.mkObj
  [("nodeType",.str "YulBlock"),("statements",.arr body)]
def node (body : Array Json) (flags : Array Json := #[.str "memory-safe"])
    (evmVersion : String := "osaka") : Json := Json.mkObj
  [("nodeType",.str "InlineAssembly"),("evmVersion",.str evmVersion),("externalReferences",.arr #[]),
   ("flags",.arr flags),("src",.str "0:1:0"),("AST",block body)]
def arithmetic := node #[decl "x" (lit "7"),
  assign "x" (call "add" #[ident "x",lit "9"]),
  assign "x" (call "mul" #[ident "x",lit "3"])]
def synList {c : Solidity.Source.Cat} (items : List (Solidity.Source.Syn c)) : Solidity.Source.Syn (.list c) :=
  items.foldr Solidity.Source.Syn.cons Solidity.Source.Syn.nil

def tree : Solidity.Source.Syn (.list .yulStmt) := synList [
  .yulLet "x" [] (.some (.yulLit (.dec 7))),
  .yulAssign ["x"] [] (.yulCall "add" (synList [.yulPath "x" [],.yulLit (.dec 9)])),
  .yulAssign ["x"] [] (.yulCall "mul" (synList [.yulPath "x" [],.yulLit (.dec 3)]))]
def prepared : Solidity.Yul.WordSyntax.Prepared [] tree :=
  ((Solidity.Yul.WordSyntax.prepare [] tree).toOption).get (by decide)
def imported : Metadata Words.emptyDeclarations := ⟨⟨[],by decide⟩,["memory-safe"],none⟩
def ast := block #[decl "x" (lit "7"),
  assign "x" (call "add" #[ident "x",lit "9"]),
  assign "x" (call "mul" #[ident "x",lit "3"])]
private theorem splitSpan : "0:1:0".splitOn ":" = ["0","1","0"] := by
  simp only [String.splitOn]
  rw [show (":" == "") = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [String.splitOnAux]
  rw [show "0:1:0".atEnd 0 = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show ("0:1:0".get 0 == ":".get 0) = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show "0:1:0".next (0-0) = ⟨1⟩ by decide]
  rw [String.splitOnAux]
  rw [show "0:1:0".atEnd ⟨1⟩ = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show ("0:1:0".get ⟨1⟩ == ":".get 0) = true by decide]
  simp only [eq_self,if_true]
  rw [show "0:1:0".next ⟨1⟩ = ⟨2⟩ by decide, show ":".next 0 = ⟨1⟩ by decide]
  rw [show ":".atEnd ⟨1⟩ = true by decide]
  simp only [eq_self,if_true]
  rw [String.splitOnAux]
  rw [show "0:1:0".atEnd ⟨2⟩ = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show ("0:1:0".get ⟨2⟩ == ":".get 0) = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show "0:1:0".next (⟨2⟩-0) = ⟨3⟩ by decide]
  rw [String.splitOnAux]
  rw [show "0:1:0".atEnd ⟨3⟩ = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show ("0:1:0".get ⟨3⟩ == ":".get 0) = true by decide]
  simp only [eq_self,if_true]
  rw [show "0:1:0".next ⟨3⟩ = ⟨4⟩ by decide, show ":".next 0 = ⟨1⟩ by decide]
  rw [show ":".atEnd ⟨1⟩ = true by decide]
  simp only [eq_self,if_true]
  rw [String.splitOnAux]
  rw [show "0:1:0".atEnd ⟨4⟩ = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show ("0:1:0".get ⟨4⟩ == ":".get 0) = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show "0:1:0".next (⟨4⟩-0) = ⟨5⟩ by decide]
  rw [String.splitOnAux]
  rw [show "0:1:0".atEnd ⟨5⟩ = true by decide]
  simp only [eq_self,if_true]
  rfl

private theorem splitX : "x".splitOn "." = ["x"] := by
  simp only [String.splitOn]
  rw [show ("." == "") = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [String.splitOnAux]
  rw [show "x".atEnd 0 = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show ("x".get 0 == ".".get 0) = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show "x".next (0-0) = ⟨1⟩ by decide]
  rw [String.splitOnAux]
  rw [show "x".atEnd ⟨1⟩ = true by decide]
  simp only [eq_self,if_true]
  rfl

private theorem splitAdd : "add".splitOn "." = ["add"] := by
  simp only [String.splitOn]
  rw [show ("." == "") = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [String.splitOnAux]
  rw [show "add".atEnd 0 = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show ("add".get 0 == ".".get 0) = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show "add".next (0-0) = ⟨1⟩ by decide]
  rw [String.splitOnAux]
  rw [show "add".atEnd ⟨1⟩ = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show ("add".get ⟨1⟩ == ".".get 0) = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show "add".next (⟨1⟩-0) = ⟨2⟩ by decide]
  rw [String.splitOnAux]
  rw [show "add".atEnd ⟨2⟩ = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show ("add".get ⟨2⟩ == ".".get 0) = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show "add".next (⟨2⟩-0) = ⟨3⟩ by decide]
  rw [String.splitOnAux]
  rw [show "add".atEnd ⟨3⟩ = true by decide]
  simp only [eq_self,if_true]
  rfl

private theorem splitMul : "mul".splitOn "." = ["mul"] := by
  simp only [String.splitOn]
  rw [show ("." == "") = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [String.splitOnAux]
  rw [show "mul".atEnd 0 = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show ("mul".get 0 == ".".get 0) = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show "mul".next (0-0) = ⟨1⟩ by decide]
  rw [String.splitOnAux]
  rw [show "mul".atEnd ⟨1⟩ = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show ("mul".get ⟨1⟩ == ".".get 0) = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show "mul".next (⟨1⟩-0) = ⟨2⟩ by decide]
  rw [String.splitOnAux]
  rw [show "mul".atEnd ⟨2⟩ = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show ("mul".get ⟨2⟩ == ".".get 0) = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show "mul".next (⟨2⟩-0) = ⟨3⟩ by decide]
  rw [String.splitOnAux]
  rw [show "mul".atEnd ⟨3⟩ = true by decide]
  simp only [eq_self,if_true]
  rfl

private theorem natZero : "0".isNat = true := by
 simp only [String.isNat, String.all, String.any,
  show "0".isEmpty = false by decide,
  show "0".endPos = ⟨1⟩ by decide]
 rw [String.anyAux]
 simp only [show (0 : String.Pos) < (⟨1⟩ : String.Pos) by decide, dif_pos,
   show "0".get 0 = '0' by decide, show Char.isDigit '0' = true by decide,
   Bool.not_true, Bool.false_eq_true, if_false, show "0".next 0 = ⟨1⟩ by decide]
 rw [String.anyAux]
 rfl
private theorem parseZero : "0".toNat? = some 0 := by
 simp only [String.toNat?,natZero,if_true,String.foldl,
  show "0".endPos = ⟨1⟩ by decide]
 rw [String.foldlAux]
 simp only [show (0 : String.Pos) < (⟨1⟩ : String.Pos) by decide,dif_pos,
  show "0".next 0 = ⟨1⟩ by decide,show "0".get 0 = '0' by decide]
 rw [String.foldlAux]
 rfl
private theorem decimalZero : decimal "0" = some 0 := by
  simp only [decimal,
    show (!"0".isEmpty && "0".toUTF8.data.all (fun b => 48 ≤ b && b ≤ 57)) = true by decide,
    if_true,parseZero]

private theorem natOne : "1".isNat = true := by
 simp only [String.isNat, String.all, String.any,
  show "1".isEmpty = false by decide,
  show "1".endPos = ⟨1⟩ by decide]
 rw [String.anyAux]
 simp only [show (0 : String.Pos) < (⟨1⟩ : String.Pos) by decide, dif_pos,
   show "1".get 0 = '1' by decide, show Char.isDigit '1' = true by decide,
   Bool.not_true, Bool.false_eq_true, if_false, show "1".next 0 = ⟨1⟩ by decide]
 rw [String.anyAux]
 rfl
private theorem parseOne : "1".toNat? = some 1 := by
 simp only [String.toNat?,natOne,if_true,String.foldl,
  show "1".endPos = ⟨1⟩ by decide]
 rw [String.foldlAux]
 simp only [show (0 : String.Pos) < (⟨1⟩ : String.Pos) by decide,dif_pos,
  show "1".next 0 = ⟨1⟩ by decide,show "1".get 0 = '1' by decide]
 rw [String.foldlAux]
 rfl
private theorem decimalOne : decimal "1" = some 1 := by
  simp only [decimal,
    show (!"1".isEmpty && "1".toUTF8.data.all (fun b => 48 ≤ b && b ≤ 57)) = true by decide,
    if_true,parseOne]

private theorem pathX : identifierPath (ident "x") = .ok ("x",[]) := by
  change (do
    let parts := "x".splitOn "."
    if !(parts.all fun part => match Solidity.Frontend.Checked.yulTok (bytes part) with
       | some (.ident actual) => actual == part | _ => false) then throw (Solidity.Frontend.YulJson.Error.identifier "x")
    match parts with | head :: tail => pure (head,tail) | [] => throw (Solidity.Frontend.YulJson.Error.identifier "x")) = _
  rw [splitX]
  rfl
private theorem pathAdd : identifierPath (ident "add") = .ok ("add",[]) := by
  change (do
    let parts := "add".splitOn "."
    if !(parts.all fun part => match Solidity.Frontend.Checked.yulTok (bytes part) with
       | some (.ident actual) => actual == part | _ => false) then throw (Solidity.Frontend.YulJson.Error.identifier "add")
    match parts with | head :: tail => pure (head,tail) | [] => throw (Solidity.Frontend.YulJson.Error.identifier "add")) = _
  rw [splitAdd]
  rfl
private theorem pathMul : identifierPath (ident "mul") = .ok ("mul",[]) := by
  change (do
    let parts := "mul".splitOn "."
    if !(parts.all fun part => match Solidity.Frontend.Checked.yulTok (bytes part) with
       | some (.ident actual) => actual == part | _ => false) then throw (Solidity.Frontend.YulJson.Error.identifier "mul")
    match parts with | head :: tail => pure (head,tail) | [] => throw (Solidity.Frontend.YulJson.Error.identifier "mul")) = _
  rw [splitMul]
  rfl


private theorem declarationParsed : statementAux 11 (decl "x" (lit "7")) = .ok (.yulLet "x" [] (.some (.yulLit (.dec 7)))) := by rfl
private theorem addParsed : expressionAux 10 (call "add" #[ident "x",lit "9"]) = .ok (.yulCall "add" (synList [.yulPath "x" [],.yulLit (.dec 9)])) := by
  change (do
    let name ← functionName (ident "add")
    let args ← [ident "x",lit "9"].mapM (expressionAux 9)
    pure (Solidity.Source.Syn.yulCall name (Solidity.Frontend.Checked.toSynList args))) = _
  simp only [functionName,pathAdd,bind,Except.bind,List.isEmpty,if_true]
  change (do
    let args ← [ident "x",lit "9"].mapM (expressionAux 9)
    pure (Solidity.Source.Syn.yulCall "add" (Solidity.Frontend.Checked.toSynList args))) = _
  have localEq : expressionAux 9 (ident "x") = .ok (.yulPath "x" []) := by
    change (do let (head,tail) ← identifierPath (ident "x"); pure (Solidity.Source.Syn.yulPath head tail)) = _
    rw [pathX]
    rfl
  simp only [List.mapM_cons,List.mapM_nil,localEq]
  rfl
private theorem mulParsed : expressionAux 10 (call "mul" #[ident "x",lit "3"]) = .ok (.yulCall "mul" (synList [.yulPath "x" [],.yulLit (.dec 3)])) := by
  change (do
    let name ← functionName (ident "mul")
    let args ← [ident "x",lit "3"].mapM (expressionAux 9)
    pure (Solidity.Source.Syn.yulCall name (Solidity.Frontend.Checked.toSynList args))) = _
  simp only [functionName,pathMul,bind,Except.bind,List.isEmpty,if_true]
  change (do
    let args ← [ident "x",lit "3"].mapM (expressionAux 9)
    pure (Solidity.Source.Syn.yulCall "mul" (Solidity.Frontend.Checked.toSynList args))) = _
  have localEq : expressionAux 9 (ident "x") = .ok (.yulPath "x" []) := by
    change (do let (head,tail) ← identifierPath (ident "x"); pure (Solidity.Source.Syn.yulPath head tail)) = _
    rw [pathX]
    rfl
  simp only [List.mapM_cons,List.mapM_nil,localEq]
  rfl
private theorem addAssignment : statementAux 11 (assign "x" (call "add" #[ident "x",lit "9"])) =
    .ok (.yulAssign ["x"] [] (.yulCall "add" (synList [.yulPath "x" [],.yulLit (.dec 9)]))) := by
  change (do
    let paths : List (String × List String) ← [ident "x"].mapM identifierPath
    let paths := paths.map (fun (pair : String × List String) => pair.1 :: pair.2)
    match paths with
    | [] => throw (Solidity.Frontend.YulJson.Error.node "empty assignment")
    | first :: rest => pure (Solidity.Source.Syn.yulAssign first rest
        (← expressionAux 10 (call "add" #[ident "x",lit "9"])))) = _
  simp only [List.mapM_cons,List.mapM_nil,pathX,bind,Except.bind,addParsed]
  rfl

private theorem mulAssignment : statementAux 11 (assign "x" (call "mul" #[ident "x",lit "3"])) =
    .ok (.yulAssign ["x"] [] (.yulCall "mul" (synList [.yulPath "x" [],.yulLit (.dec 3)]))) := by
  change (do
    let paths : List (String × List String) ← [ident "x"].mapM identifierPath
    let paths := paths.map (fun (pair : String × List String) => pair.1 :: pair.2)
    match paths with
    | [] => throw (Solidity.Frontend.YulJson.Error.node "empty assignment")
    | first :: rest => pure (Solidity.Source.Syn.yulAssign first rest
        (← expressionAux 10 (call "mul" #[ident "x",lit "3"])))) = _
  simp only [List.mapM_cons,List.mapM_nil,pathX,bind,Except.bind,mulParsed]
  rfl

def checked : Words.Checked [] 12 arithmetic where
  imported := imported
  imported_eq := by rfl
  rawSpan := "0:1:0"
  rawSpan_eq := by rfl
  span := ⟨0,1,0⟩
  span_eq := by
    rw [sourceSpan,splitSpan]
    simp only [decimalZero,decimalOne]
    rfl
  ast := ast
  ast_eq := by rfl
  shaped := ⟨⟨tree,by
    change (do
      let statements ← [decl "x" (lit "7"), assign "x" (call "add" #[ident "x",lit "9"]),
        assign "x" (call "mul" #[ident "x",lit "3"])].mapM (statementAux 11)
      pure (Solidity.Frontend.Checked.toSynList statements)) = _
    simp only [List.mapM_cons,List.mapM_nil,declarationParsed,addAssignment,mulAssignment,bind,Except.bind]
    rfl⟩,by decide⟩
  safe := ⟨.flag (by decide)⟩
  prepared := prepared
def compiled := ((compile checked 5).toOption).get (by decide)
def packet : Packet [] 12 5 arithmetic := ⟨checked,compiled⟩
-- The same original JSON/compiler call returns this factored certificate.
theorem arithmetic_compiles : checkCompile [] 12 5 arithmetic = .ok packet := by
  simp only [checkCompile,checked.complete,Except.mapError,bind,Except.bind]
  rfl
#check packet.compiled.source
#check packet.compiled.model [dirty,77] (machine [dirty,77]) rfl
#check (OccurrenceSelection.lowering packet.compiled.code packet.compiled.selected).success
  [dirty,77] [dirty,77] (machine [dirty,77]) rfl
#guard packet.checked.imported.references.entries.isEmpty
#guard (packet.checked.run 5).map (fun result => result.flow.isNormal) == some true
#guard packet.compiled.code.length == 12
#guard Scalar.run (packet.compiled.code.take 4) [dirty,77] == some [16,7,dirty,77]
#guard Scalar.run (packet.compiled.code.take 11) [dirty,77] == some [48,dirty,77]
#guard Scalar.run packet.compiled.code [dirty,77] == some [dirty,77]
#guard observe (Evm.run packet.compiled.selected.ir (machine [dirty,77])) ==
  some ([some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard Scalar.stackBound packet.compiled.code 1021
#guard !(Scalar.stackBound packet.compiled.code 1022)
#guard (Scalar.run packet.compiled.code (List.replicate 1025 dirty)).isSome
#guard match checkCompile [] 12 1 arithmetic with | .error .statement => true | _ => false
#guard match checkCompile [] 0 5 arithmetic with | .error (.input _) => true | _ => false
#guard match checkCompile [] 12 5 (node #[decl "x" (lit "7")] #[]) with
  | .error (.input _) => true | _ => false
#guard match checkCompile [] 12 5 (node #[] #[.str "memory-safe",.str "memory-safe"]) with
  | .error (.input _) => true | _ => false
#guard match checkCompile [] 12 5 (node #[] #[.str "memory-safe"] "cancun") with
  | .error (.input _) => true | _ => false
#guard match checkCompile [] 12 5 (node #[decl "x" (call "gas" #[])]) with
  | .error (.input _) => true | _ => false
#guard match checkCompile [] 12 5 (node #[decl "x" (call "codesize" #[])]) with
  | .error (.input _) => true | _ => false
#guard match checkCompile [] 12 5 (node #[decl "x" (lit "7"),decl "x" (lit "9")]) with
  | .error (.input _) => true | _ => false

def ifNode := node #[Json.mkObj [("nodeType",.str "YulIf"),("condition",lit "0"),("body",block #[])]]
#guard (Words.check [] 12 ifNode).isOk
#guard match checkCompile [] 12 5 ifNode with | .error .statement => true | _ => false
/-- info: 'SolidityBridge.Yul.JsonCompilation.Controls.arithmetic_compiles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms arithmetic_compiles
end SolidityBridge.Yul.JsonCompilation.Controls
