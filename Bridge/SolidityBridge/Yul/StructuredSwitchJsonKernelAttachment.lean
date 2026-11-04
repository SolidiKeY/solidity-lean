import SolidityBridge.Yul.StructuredSwitchJsonKernelControls
/-! Exact finite decoder equations for the unchanged NJ1 fixture. Existing
parser/typing/compiler definitions are reused; no new parser or source AST. -/
namespace SolidityBridge.Yul.StructuredSwitchJson.KernelControls
open Solidity Backend Scalar Selection
open Solidity.Frontend.YulJson
open Solidity.Source (Syn)
open JsonCompilation.Controls (synList pathX pathAdd pathMul)

private theorem splitY : "y".splitOn "." = ["y"] := by
  simp only [String.splitOn]
  rw [show ("." == "") = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [String.splitOnAux]
  rw [show "y".atEnd 0 = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show ("y".get 0 == ".".get 0) = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show "y".next (0-0) = ⟨1⟩ by decide]
  rw [String.splitOnAux]
  rfl

private theorem pathY : identifierPath (Controls.ident "y") = .ok ("y",[]) := by
  change (do
    let parts := "y".splitOn "."
    if !(parts.all fun part => match Solidity.Frontend.Checked.yulTok (bytes part) with
       | some (.ident actual) => actual == part | _ => false) then throw (Solidity.Frontend.YulJson.Error.identifier "y")
    match parts with | head :: tail => pure (head,tail) | [] => throw (Solidity.Frontend.YulJson.Error.identifier "y")) = _
  rw [splitY]
  rfl

private theorem splitEq : "eq".splitOn "." = ["eq"] := by
  simp only [String.splitOn]
  rw [show ("." == "") = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [String.splitOnAux]
  rw [show "eq".atEnd 0 = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show ("eq".get 0 == ".".get 0) = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show "eq".next (0-0) = ⟨1⟩ by decide]
  rw [String.splitOnAux]
  rw [show "eq".atEnd ⟨1⟩ = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show ("eq".get ⟨1⟩ == ".".get 0) = false by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show "eq".next (⟨1⟩-0) = ⟨2⟩ by decide]
  rw [String.splitOnAux]
  rfl

private theorem pathEq : identifierPath (Controls.ident "eq") = .ok ("eq",[]) := by
  change (do
    let parts := "eq".splitOn "."
    if !(parts.all fun part => match Solidity.Frontend.Checked.yulTok (bytes part) with
       | some (.ident actual) => actual == part | _ => false) then throw (Solidity.Frontend.YulJson.Error.identifier "eq")
    match parts with | head :: tail => pure (head,tail) | [] => throw (Solidity.Frontend.YulJson.Error.identifier "eq")) = _
  rw [splitEq]
  rfl

private theorem identParsed (fuel : Nat) (name : String)
    (path : identifierPath (Controls.ident name) = .ok (name,[])) :
    expressionAux (fuel+1) (Controls.ident name) = .ok (.yulPath name []) := by
  change (do let (head,tail) ← identifierPath (Controls.ident name)
             pure (Syn.yulPath head tail)) = _
  rw [path]
  rfl

private theorem callParsed (fuel : Nat) (name : String) (raw : Array Lean.Json)
    (args : List (Syn .yulExpr))
    (path : identifierPath (Controls.ident name) = .ok (name,[]))
    (children : raw.toList.mapM (expressionAux fuel) = .ok args) :
    expressionAux (fuel+1) (Controls.call name raw) =
      .ok (.yulCall name (Solidity.Frontend.Checked.toSynList args)) := by
  change (do
    let fn ← functionName (Controls.ident name)
    let actual ← raw.toList.mapM (expressionAux fuel)
    pure (Syn.yulCall fn (Solidity.Frontend.Checked.toSynList actual))) = _
  simp only [functionName,path,bind,Except.bind,List.isEmpty,if_true,children]
  rfl

private theorem assignmentParsed (fuel : Nat) (raw : Lean.Json) (rhs : Syn .yulExpr)
    (child : expressionAux fuel raw = .ok rhs) :
    statementAux (fuel+1) (Controls.assign "x" raw) = .ok (.yulAssign ["x"] [] rhs) := by
  change (do
    let paths : List (String × List String) ← [Controls.ident "x"].mapM identifierPath
    let paths := paths.map (fun (pair : String × List String) => pair.1 :: pair.2)
    match paths with
    | [] => throw (Solidity.Frontend.YulJson.Error.node "empty assignment")
    | first :: rest => pure (Syn.yulAssign first rest (← expressionAux fuel raw))) = _
  simp only [List.mapM_cons,List.mapM_nil,pathX,bind,Except.bind,child]
  rfl

private theorem blockParsed (fuel : Nat) (raw : Array Lean.Json) (items : List (Syn .yulStmt))
    (children : raw.toList.mapM (statementAux fuel) = .ok items) :
    blockAux (fuel+1) (Controls.block raw) =
      .ok (Solidity.Frontend.Checked.toSynList items) := by
  change (do
    let actual ← raw.toList.mapM (statementAux fuel)
    pure (Solidity.Frontend.Checked.toSynList actual)) = _
  rw [children]
  rfl

private theorem addParsed : expressionAux 14 (Controls.call "add" #[Controls.ident "x",Controls.lit "2"]) = .ok addTree := by
  apply callParsed 13 "add" #[Controls.ident "x",Controls.lit "2"] [x,.yulLit (.dec 2)] pathAdd
  change [Controls.ident "x",Controls.lit "2"].mapM (expressionAux 13) = .ok [x,.yulLit (.dec 2)]
  simp only [List.mapM_cons,List.mapM_nil,identParsed 12 "x" pathX]
  rfl
private theorem mulParsed : expressionAux 16 (Controls.call "mul" #[Controls.ident "x",Controls.lit "7"]) = .ok mulTree := by
  apply callParsed 15 "mul" #[Controls.ident "x",Controls.lit "7"] [x,.yulLit (.dec 7)] pathMul
  change [Controls.ident "x",Controls.lit "7"].mapM (expressionAux 15) = .ok [x,.yulLit (.dec 7)]
  simp only [List.mapM_cons,List.mapM_nil,identParsed 14 "x" pathX]
  rfl
private theorem eqParsed : expressionAux 18 (Controls.call "eq" #[Controls.ident "x",Controls.lit "3"]) = .ok eqTree := by
  apply callParsed 17 "eq" #[Controls.ident "x",Controls.lit "3"] [x,.yulLit (.dec 3)] pathEq
  change [Controls.ident "x",Controls.lit "3"].mapM (expressionAux 17) = .ok [x,.yulLit (.dec 3)]
  simp only [List.mapM_cons,List.mapM_nil,identParsed 16 "x" pathX]
  rfl

private theorem dirtyDeclaration : statementAux 17
    (Controls.decl "y" (Controls.lit (toString dirty.toNat))) =
    .ok (.yulLet "y" [] (.some (.yulLit (.dec dirty.toNat)))) := by rfl
private theorem xDeclaration : statementAux 19 (Controls.decl "x" (Controls.lit "1")) =
    .ok (.yulLet "x" [] (.some (.yulLit (.dec 1)))) := by rfl

private theorem literalBlock (fuel : Nat) (raw : String) (n : Nat)
    (child : expressionAux (fuel+1) (Controls.lit raw) = .ok (.yulLit (.dec n))) :
    blockAux (fuel+3) (Controls.block #[Controls.assign "x" (Controls.lit raw)]) =
    .ok (synList [.yulAssign ["x"] [] (.yulLit (.dec n))]) := by
  apply blockParsed (fuel+2) #[Controls.assign "x" (Controls.lit raw)]
    [.yulAssign ["x"] [] (.yulLit (.dec n))]
  change [Controls.assign "x" (Controls.lit raw)].mapM (statementAux (fuel+2)) = _
  simp only [List.mapM_cons,List.mapM_nil,assignmentParsed (fuel+1) _ _ child,bind,Except.bind]
  rfl

private theorem addBlock : blockAux 16 (Controls.block #[
    Controls.assign "x" (Controls.call "add" #[Controls.ident "x",Controls.lit "2"])]) =
    .ok (synList [.yulAssign ["x"] [] addTree]) := by
  apply blockParsed 15 _ [.yulAssign ["x"] [] addTree]
  change [Controls.assign "x" (Controls.call "add" #[Controls.ident "x",Controls.lit "2"])].mapM
    (statementAux 15) = _
  simp only [List.mapM_cons,List.mapM_nil,assignmentParsed 14 _ _ addParsed,bind,Except.bind]
  rfl
private theorem mulBlock : blockAux 18 (Controls.block #[
    Controls.assign "x" (Controls.call "mul" #[Controls.ident "x",Controls.lit "7"])]) =
    .ok (synList [.yulAssign ["x"] [] mulTree]) := by
  apply blockParsed 17 _ [.yulAssign ["x"] [] mulTree]
  change [Controls.assign "x" (Controls.call "mul" #[Controls.ident "x",Controls.lit "7"])].mapM
    (statementAux 17) = _
  simp only [List.mapM_cons,List.mapM_nil,assignmentParsed 16 _ _ mulParsed,bind,Except.bind]
  rfl

private def decimalLiteral (n : Nat) (bound : n < 2^256) : Literal :=
  ⟨.dec n,Solidity.Yul.word n,.dec bound⟩

private theorem defaultCase (body : Lean.Json → Except Error (Syn (.list .yulStmt)))
    (raw : Array Lean.Json) (seen : List Solidity.Yul.Word) (items : Syn (.list .yulStmt))
    (parsed : body (Controls.block raw) = .ok items) :
    switchCases body [Controls.caseNode (.str "default") raw] seen = .ok (.nil,.some items) := by
  rw [switchCases]
  change (do let actual ← body (Controls.block raw); pure (Syn.nil,Syn.some actual)) = _
  rw [parsed]
  rfl

private theorem ordinaryCase (body : Lean.Json → Except Error (Syn (.list .yulStmt)))
    (raw : String) (rawBody : Array Lean.Json) (rest : List Lean.Json)
    (seen : List Solidity.Yul.Word) (l : Literal) (items : Syn (.list .yulStmt))
    (cases : Syn (.list .yulCase)) (fallback : Syn (.opt (.list .yulStmt)))
    (decoded : literal (Controls.lit raw) = .ok l)
    (fresh : seen.contains l.value = false)
    (bodyParsed : body (Controls.block rawBody) = .ok items)
    (tailParsed : switchCases body rest (l.value::seen) = .ok (cases,fallback)) :
    switchCases body (Controls.caseNode (Controls.lit raw) rawBody :: rest) seen =
      .ok (.cons (.yulCase l.tree items) cases,fallback) := by
  rw [switchCases]
  change (do
    let actual ← literal (Controls.lit raw)
    if seen.contains actual.value then throw (Error.node "duplicate case word") else do
      let parsedBody ← body (Controls.block rawBody)
      let (cs,d) ← switchCases body rest (actual.value::seen)
      pure (Syn.cons (.yulCase actual.tree parsedBody) cs,d)) = _
  rw [decoded]
  simp only [fresh,Bool.false_eq_true,if_false,bodyParsed,tailParsed,bind,Except.bind]
  rfl

private theorem switchParsed (fuel : Nat) (raw : Lean.Json) (rawCases : Array Lean.Json)
    (selector : Syn .yulExpr) (cases : Syn (.list .yulCase))
    (fallback : Syn (.opt (.list .yulStmt)))
    (nonempty : rawCases.isEmpty = false)
    (exprParsed : expressionAux fuel raw = .ok selector)
    (casesParsed : switchCases (blockAux fuel) rawCases.toList [] = .ok (cases,fallback)) :
    statementAux (fuel+1) (Controls.switchNode raw rawCases) = .ok (.yulSwitch selector cases fallback) := by
  change (do
    let actual ← expressionAux fuel raw
    if rawCases.isEmpty then throw (Error.node "empty switch") else do
      let (cs,d) ← switchCases (blockAux fuel) rawCases.toList []
      pure (Syn.yulSwitch actual cs d)) = _
  rw [exprParsed]
  simp only [nonempty,Bool.false_eq_true,if_false,casesParsed,bind,Except.bind]
  rfl

private theorem innerCases : switchCases (blockAux 16)
    [Controls.caseNode (Controls.lit (toString dirty.toNat)) #[
       Controls.assign "x" (Controls.call "add" #[Controls.ident "x",Controls.lit "2"])],
     Controls.caseNode (.str "default") #[Controls.assign "x" (Controls.lit "99")]] [] =
    .ok (synList [.yulCase (.dec dirty.toNat) (synList [.yulAssign ["x"] [] addTree])],
      .some (synList [.yulAssign ["x"] [] (.yulLit (.dec 99))])) := by
  apply ordinaryCase (blockAux 16) (toString dirty.toNat) _ _ []
    (decimalLiteral dirty.toNat (by decide)) _ .nil _
  · rfl
  · rfl
  · exact addBlock
  · exact defaultCase (blockAux 16) _ _ _ (literalBlock 13 "99" 99 (by rfl))
private theorem innerParsed : statementAux 17 Controls.inner = .ok innerTree := by
  apply switchParsed 16 (Controls.ident "y") #[
    Controls.caseNode (Controls.lit (toString dirty.toNat)) #[
      Controls.assign "x" (Controls.call "add" #[Controls.ident "x",Controls.lit "2"])],
    Controls.caseNode (.str "default") #[Controls.assign "x" (Controls.lit "99")]]
    y _ _ (by rfl) (identParsed 15 "y" pathY)
  exact innerCases
private theorem firstBlock : blockAux 18 (Controls.block #[
    Controls.decl "y" (Controls.lit (toString dirty.toNat)),Controls.inner]) =
    .ok (synList [.yulLet "y" [] (.some (.yulLit (.dec dirty.toNat))),innerTree]) := by
  apply blockParsed 17 _ [.yulLet "y" [] (.some (.yulLit (.dec dirty.toNat))),innerTree]
  change [Controls.decl "y" (Controls.lit (toString dirty.toNat)),Controls.inner].mapM (statementAux 17) = _
  simp only [List.mapM_cons,List.mapM_nil,dirtyDeclaration,innerParsed,bind,Except.bind]
  rfl

private theorem defaultCases : switchCases (blockAux 16)
    [Controls.caseNode (Controls.lit "8") #[Controls.assign "x" (Controls.lit "42")],
     Controls.caseNode (.str "default") #[Controls.assign "x" (Controls.lit "17")]] [] =
    .ok (synList [.yulCase (.dec 8) (synList [.yulAssign ["x"] [] (.yulLit (.dec 42))])],
      .some (synList [.yulAssign ["x"] [] (.yulLit (.dec 17))])) := by
  apply ordinaryCase (blockAux 16) "8" _ _ [] (decimalLiteral 8 (by decide)) _ .nil _
  · rfl
  · rfl
  · exact literalBlock 13 "42" 42 (by rfl)
  · exact defaultCase (blockAux 16) _ _ _ (literalBlock 13 "17" 17 (by rfl))
private theorem defaultParsed : statementAux 17 Controls.defaultSwitch = .ok defaultTree := by
  apply switchParsed 16 (Controls.ident "x") #[
    Controls.caseNode (Controls.lit "8") #[Controls.assign "x" (Controls.lit "42")],
    Controls.caseNode (.str "default") #[Controls.assign "x" (Controls.lit "17")]]
    x _ _ (by rfl) (identParsed 15 "x" pathX)
  exact defaultCases
private theorem fallbackBlock : blockAux 18 (Controls.block #[Controls.defaultSwitch]) =
    .ok (synList [defaultTree]) := by
  apply blockParsed 17 _ [defaultTree]
  change [Controls.defaultSwitch].mapM (statementAux 17) = _
  simp only [List.mapM_cons,List.mapM_nil,defaultParsed,bind,Except.bind]
  rfl

private theorem outerCases : switchCases (blockAux 18)
    [Controls.caseNode (Controls.lit "1") #[Controls.decl "y" (Controls.lit (toString dirty.toNat)),Controls.inner],
     Controls.caseNode (Controls.lit "3") #[Controls.assign "x" (Controls.lit "999")],
     Controls.caseNode (.str "default") #[Controls.defaultSwitch]] [] =
    .ok (synList [
      .yulCase (.dec 1) (synList [.yulLet "y" [] (.some (.yulLit (.dec dirty.toNat))),innerTree]),
      .yulCase (.dec 3) (synList [.yulAssign ["x"] [] (.yulLit (.dec 999))])],
      .some (synList [defaultTree])) := by
  apply ordinaryCase (blockAux 18) "1" _ _ [] (decimalLiteral 1 (by decide)) _ _ _
  · rfl
  · rfl
  · exact firstBlock
  · apply ordinaryCase (blockAux 18) "3" _ _ [Solidity.Yul.word 1]
      (decimalLiteral 3 (by decide)) _ .nil _
    · rfl
    · decide
    · exact literalBlock 15 "999" 999 (by rfl)
    · exact defaultCase (blockAux 18) _ _ _ fallbackBlock
private theorem outerParsed : statementAux 19 Controls.outer = .ok outerTree := by
  apply switchParsed 18 (Controls.ident "x") #[
    Controls.caseNode (Controls.lit "1") #[Controls.decl "y" (Controls.lit (toString dirty.toNat)),Controls.inner],
    Controls.caseNode (Controls.lit "3") #[Controls.assign "x" (Controls.lit "999")],
    Controls.caseNode (.str "default") #[Controls.defaultSwitch]]
    x _ _ (by rfl) (identParsed 17 "x" pathX)
  exact outerCases
private theorem conditionalParsed : statementAux 19 Controls.conditional = .ok conditionalTree := by
  change (do
    let condition ← expressionAux 18 (Controls.call "eq" #[Controls.ident "x",Controls.lit "3"])
    let body ← blockAux 18 (Controls.block #[Controls.assign "x"
      (Controls.call "mul" #[Controls.ident "x",Controls.lit "7"])])
    pure (Syn.yulIf condition body)) = _
  rw [eqParsed,mulBlock]
  rfl

/-- Exact existing decoder equality for the original, unchanged NJ1 fixture. -/
theorem raw_nested_parsed : blockAux 20 ast = .ok tree := by
  apply blockParsed 19 #[Controls.decl "x" (Controls.lit "1"),Controls.outer,Controls.conditional]
    [.yulLet "x" [] (.some (.yulLit (.dec 1))),outerTree,conditionalTree]
  change [Controls.decl "x" (Controls.lit "1"),Controls.outer,Controls.conditional].mapM (statementAux 19) = _
  simp only [List.mapM_cons,List.mapM_nil,xDeclaration,outerParsed,conditionalParsed,bind,Except.bind]
  rfl

/-- Concrete checked packet for the original NJ1 raw JSON, no parser premise. -/
def raw_nested_packet : StructuredJson.Packet [] 20 16 (Controls.fixture "1") :=
  packetFromParse raw_nested_parsed

theorem raw_nested_compiles : StructuredJson.checkCompile [] 20 16 (Controls.fixture "1") =
    .ok raw_nested_packet := compilesFromParse raw_nested_parsed

theorem raw_nested_source : raw_nested_packet.checked.run 16 =
    some (⟨Fin.elim0,.normal⟩ : Solidity.Yul.Closed.Outcome Solidity.Yul.ClosedSyntax.rootControl 0) :=
  raw_nested_packet.compiled.source

theorem raw_nested_model (tail : Scalar.Stack) (m : Evm.Machine)
    (represented : m.stack = irStack tail) :
    Evm.run raw_nested_packet.compiled.selected.realization.ir m = .ok m 0 :=
  raw_nested_packet.compiled.model tail m represented

#check raw_nested_source
#check raw_nested_model [dirty,77] (Controls.machine [dirty,77]) rfl
#guard (raw_nested_packet.checked.run 16).map (fun out => out.flow.isNormal) == some true
#guard Controls.observe (Evm.run raw_nested_packet.compiled.selected.realization.ir
  (Controls.machine [dirty,77])) ==
  some ([some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
/-- info: 'SolidityBridge.Yul.StructuredSwitchJson.KernelControls.raw_nested_parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms raw_nested_parsed
/-- info: 'SolidityBridge.Yul.StructuredSwitchJson.KernelControls.raw_nested_packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms raw_nested_packet
/-- info: 'SolidityBridge.Yul.StructuredSwitchJson.KernelControls.raw_nested_compiles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms raw_nested_compiles
/-- info: 'SolidityBridge.Yul.StructuredSwitchJson.KernelControls.raw_nested_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms raw_nested_source
/-- info: 'SolidityBridge.Yul.StructuredSwitchJson.KernelControls.raw_nested_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms raw_nested_model

/-- Exact budget-refusal transport for the same well-checked raw fixture;
this is a compiler refusal, not a general revert/divergence transport theorem. -/
theorem raw_nested_low_fuel : StructuredJson.checkCompile [] 20 2 (Controls.fixture "1") =
    .error .statement := by
  simp only [StructuredJson.checkCompile,raw_nested_packet.checked.complete,
    Except.mapError,bind,Except.bind]
  rfl
/-- info: 'SolidityBridge.Yul.StructuredSwitchJson.KernelControls.raw_nested_low_fuel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms raw_nested_low_fuel
end SolidityBridge.Yul.StructuredSwitchJson.KernelControls
