import Solidity.SolcValidation.IrParse
import Solidity.SolcValidation.DataLayout
import Solidity.SolcValidation.IrRename
import Solidity.SolcValidation.IrCensusParse
import Solidity.SolcValidation.IrCensusUnique

/-! Literal and lexer boundary controls for the frozen solc validator inventory.
All inputs are inline; these checks assert reader behavior, not compiler fidelity. -/
namespace Solidity.Examples.FrontendValidation.SolcValidation
open Solidity.SolcValidation.IrSyntax

#guard hexDigit? 'F' == some 15
#guard hexDigit? 'g' == none
#guard (toByte? 255).isSome
#guard (toByte? 256).isNone
#guard (escapeByte 'n').map Fin.val == some 10
#guard (escapeByte 'q').isNone
#guard (decodeString "\\x41".toList).map (List.map Fin.val) == some [65]
#guard (decodeString "\\x4z".toList).isNone
#guard (stringWord []).isSome
#guard (stringWord (List.replicate 33 0)).isNone
#guard (LitTok.num 7).decode.isSome
#guard (LitTok.num (2 ^ 256)).decode.isNone
#guard isIdStart '$'
#guard !isIdStart '0'
#guard isIdChar '.'
#guard !isIdChar '-'
#guard lexString [] "ok\" tail".toList == some ("ok", " tail".toList)
#guard (lexString [] "unterminated".toList).isNone
#guard ((lexHex "41\"".toList []).map fun p => p.1.map Fin.val) == some [65]
#guard (lexHex "4\"".toList []).isNone
#guard dropBlock "*/tail".toList == some "tail".toList
#guard (dropBlock "missing".toList).isNone
#guard hexValue "aF".toList == some 175
#guard hexValue "ax".toList == none
#guard lexNumber '0' "x2a ".toList == some (42, " ".toList)
#guard (lexNumber '0' "1".toList).isNone
#guard (lexGo 2 "x".toList []).isSome
#guard (lexGo 0 "x".toList []).isNone
#guard (lex "{ let x := 42 }").isSome
#guard (lex "@").isNone

/-! Name resolution, arities, grammar and control-context refusals. -/
#guard (findVar ["x"] "x").isSome
#guard (findVar ["x"] "missing").isNone
#guard (findFn [⟨"f", [], []⟩] "f").isSome
#guard (findFn [⟨"f", [], []⟩] "missing").isNone
#guard (mkLit (.num 7)).isOk
#guard !(mkLit (.num (2 ^ 256))).isOk
#guard (litTok? (.ident "true")).isSome
#guard (litTok? .lbrace).isNone
#guard reserved "let"
#guard !reserved "fresh"
#guard (freshNames [] ["x"]).isOk
#guard !(freshNames ["x"] ["x"]).isOk
#guard (single (F := []) (L := []) ⟨1, .op (.object (.datasize "x")) .nil⟩).isOk
#guard !(single (F := []) (L := []) ⟨0, .op (.evm .«stop») .nil⟩).isOk
#guard (parseExpr [] [] 12 [.num 1]).isOk
#guard !(parseExpr [] [] 12 [.ident "missing"]).isOk
#guard (parseArgs [] [] 12 [.rparen]).isOk
#guard !(parseArgs [] [] 12 [.num 1]).isOk
#guard (parseArgs1 [] [] 12 [.num 1, .rparen]).isOk
#guard !(parseArgs1 [] [] 12 [.num 1]).isOk
#guard (parseCall [] [] 12 "datasize" [.str "x", .rparen]).isOk
#guard !(parseCall [] [] 12 "datasize" [.num 0, .rparen]).isOk
#guard (parseHeader [.ident "f", .lparen, .rparen]).isOk
#guard !(parseHeader [.ident "f", .lparen]).isOk
#guard (scanSigs 12 0 [.rbrace]).isOk
#guard !(scanSigs 12 0 []).isOk
#guard (assemble [] [] []).isOk
#guard !(assemble [] [⟨"f", [], []⟩] []).isOk
#guard (resolveTargets ["x"] ["x"]).isOk
#guard !(resolveTargets ["x"] ["missing"]).isOk
#guard (parseInit [] [] ["x"] 12 [.assign, .num 1]).isOk
#guard !(parseInit [] [] ["x"] 12 [.assign, .ident "missing"]).isOk
#guard (parseBlock [] ⟨false, false⟩ [] 12 [.lbrace, .rbrace]).isOk
#guard !(parseBlock [] ⟨false, false⟩ [] 12 [.lbrace]).isOk
#guard (parseItems [] ⟨false, false⟩ [] [] 0 12 [.rbrace]).isOk
#guard !(parseItems [] ⟨false, false⟩ [] [] 0 12 [.ident "let", .rbrace]).isOk
#guard (parseStmt [] ⟨true, false⟩ [] 12 [.ident "leave"]).isOk
#guard !(parseStmt [] ⟨false, false⟩ [] 12 [.ident "leave"]).isOk
#guard (parseCases [] ⟨false, false⟩ [] 12
  [.ident "case", .num 0, .lbrace, .rbrace]).isOk
#guard !(parseCases [] ⟨false, false⟩ [] 12
  [.ident "case", .ident "x", .lbrace, .rbrace]).isOk
#guard (parseLoop [] ⟨false, false⟩ [] 12
  [.rbrace, .num 1, .lbrace, .rbrace, .lbrace, .rbrace]).isOk
#guard !(parseLoop [] ⟨false, false⟩ [] 12 [.ident "function"]).isOk
#guard (parseObject 12 12
  [.ident "object", .str "x", .lbrace, .ident "code", .lbrace, .rbrace, .rbrace]).isOk
#guard !(parseObject 12 12 [.ident "object"]).isOk
#guard (parseChildren 12 12 [.rbrace]).isOk
#guard !(parseChildren 12 12 [.ident "data", .str "x", .str "plain", .rbrace]).isOk

/-! Structural checks are also tested on intrinsic trees that the parser
must refuse, rather than assuming that every well-typed tree is well formed. -/
open Solidity.SolcValidation

private def dataRef : DataRef [7] := ⟨0, 1, by decide⟩
private def dataTable : DataTable [7] := ⟨[("payload", dataRef)], by decide⟩
#guard (selectData "payload" [("payload", dataRef)]).isSome
#guard (selectData "missing" [("payload", dataRef)]).isNone
#guard (dataTable.select "payload").isSome
#guard (dataTable.select "missing").isNone

#guard nodupNames ["x", "y"]
#guard !nodupNames ["x", "x"]
#guard declOk [] [] ["x"]
#guard !declOk [] [] ["let"]
#guard nodupWords [1, 2]
#guard !nodupWords [1, 1]

private def first : Expr [] ["x", "x"] 1 := .var "x" .here
private def second : Expr [] ["x", "x"] 1 := .var "x" (.there .here)
#guard first.wf
#guard !second.wf
#guard (Solidity.SolcValidation.IrSyntax.Args.cons first .nil).wf
#guard !(Solidity.SolcValidation.IrSyntax.Args.cons second .nil).wf
#guard initWf (xs := ["r"]) (some first)
#guard !initWf (xs := ["r"]) (some second)

private def emptyBlock {F c L} : Block F c L := .mk [] .nil .nil
private def emptyDeclBlock {F c L} : Block F c L := .mk [] .nil (.let_ [] none .nil)
private def literal : Lit := ⟨.num 1, 1, by decide⟩
private def value {F L} : Expr F L 1 := .lit literal
private def goodStmt : Solidity.SolcValidation.IrSyntax.Stmt [] ⟨false, false⟩ [] := .block emptyBlock
private def badStmt : Solidity.SolcValidation.IrSyntax.Stmt [] ⟨false, false⟩ [] := .block emptyDeclBlock
private def goodCases : Cases [] ⟨false, false⟩ [] := .cons literal emptyBlock .nil
private def badCases : Cases [] ⟨false, false⟩ [] := .cons literal emptyDeclBlock .nil
private def goodLoop : Loop [] ⟨false, false⟩ [] := .run value emptyBlock emptyBlock
private def badLoop : Loop [] ⟨false, false⟩ [] := .run value emptyBlock emptyDeclBlock
private def goodItems : Items [] ⟨false, false⟩ [] 0 := .stmt goodStmt .nil
private def badItems : Items [] ⟨false, false⟩ [] 0 := .stmt badStmt .nil
private def goodBodies : Bodies [] [⟨"f", [], []⟩] := .cons emptyBlock .nil
private def badBodies : Bodies [] [⟨"f", [], []⟩] := .cons emptyDeclBlock .nil
private def goodObject : Object Code := .object "O" emptyBlock []
private def badObject : Object Code := .object "O" emptyDeclBlock []

#guard goodStmt.wf false
#guard !badStmt.wf false
#guard goodCases.wf false
#guard !badCases.wf false
#guard goodCases.nonempty
#guard !(Cases.nil (F := []) (c := ⟨false, false⟩) (L := [])).nonempty
#guard goodLoop.wf
#guard !badLoop.wf
#guard goodItems.wf false 0
#guard !badItems.wf false 0
#guard (emptyBlock (F := []) (c := ⟨false, false⟩) (L := [])).wf false
#guard !(emptyDeclBlock (F := []) (c := ⟨false, false⟩) (L := [])).wf false
#guard goodBodies.wf
#guard !badBodies.wf
#guard objectWf goodObject
#guard !objectWf badObject
#guard objectsWf [goodObject]
#guard !objectsWf [badObject]
#guard (parse "object \"O\" { code {} }").isOk
#guard !(parse "object \"O\" { code { let } }").isOk
#guard parsesTo "object \"O\" { code {} }" goodObject
#guard !parsesTo "object \"Other\" { code {} }" goodObject
#guard namesNodup [⟨"f", [], []⟩, ⟨"g", [], []⟩]
#guard !namesNodup [⟨"f", [], []⟩, ⟨"f", ["x"], []⟩]

/-! Every renamer must retain a mapped call and reject the same call when its
function is absent from the partial map, including calls nested in bodies. -/
private def callee : FnSig := ⟨"f", [], ["r"]⟩
private def keep : Ren [callee] [callee] := fun m => some m
private def drop : Ren [callee] [callee] := fun _ => none
private def callExpr : Expr [callee] [] 1 := .call .here .nil
private def callArgs : Solidity.SolcValidation.IrSyntax.Args [callee] [] 1 := .cons callExpr .nil
private def callStmt {c} : Solidity.SolcValidation.IrSyntax.Stmt [callee] c [] := .if_ callExpr emptyBlock
private def callBlock {c} : Block [callee] c [] := .mk [] .nil (.stmt callStmt .nil)
private def callCases : Cases [callee] ⟨false, false⟩ [] := .cons literal callBlock .nil
private def callLoop : Loop [callee] ⟨false, false⟩ [] := .run callExpr emptyBlock emptyBlock
private def callItems : Items [callee] ⟨false, false⟩ [] 0 := .stmt callStmt .nil
private def callBodies : Bodies [callee] [⟨"g", [], []⟩] := .cons callBlock .nil

#guard (callExpr.ren keep).isSome
#guard (callExpr.ren drop).isNone
#guard (callArgs.ren keep).isSome
#guard (callArgs.ren drop).isNone
#guard (initRen (xs := ["r"]) keep (some callExpr)).isSome
#guard (initRen (xs := ["r"]) drop (some callExpr)).isNone
#guard ((callStmt (c := ⟨false, false⟩)).ren keep).isSome
#guard ((callStmt (c := ⟨false, false⟩)).ren drop).isNone
#guard (callCases.ren keep).isSome
#guard (callCases.ren drop).isNone
#guard (callLoop.ren keep).isSome
#guard (callLoop.ren drop).isNone
#guard (callItems.ren keep).isSome
#guard (callItems.ren drop).isNone
#guard ((callBlock (c := ⟨false, false⟩)).ren keep).isSome
#guard ((callBlock (c := ⟨false, false⟩)).ren drop).isNone
#guard (callBodies.ren keep).isSome
#guard (callBodies.ren drop).isNone

end Solidity.Examples.FrontendValidation.SolcValidation
