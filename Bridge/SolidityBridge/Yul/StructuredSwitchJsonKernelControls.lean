import SolidityBridge.Yul.StructuredSwitchJsonControls
/-! Kernel components for NJ1. The concrete syntax/preparation/lowering below
are inhabited independently. Raw JSON attachment is asserted only when the
exact existing decoder equality is supplied/proved; no replacement parser,
source AST, admission or native/G24 claim. -/
namespace SolidityBridge.Yul.StructuredSwitchJson.KernelControls
open Solidity Backend Scalar Selection
open Solidity.Frontend.YulJson
open Solidity.Source (Syn)
abbrev dirty := Controls.dirty
open JsonCompilation.Controls (synList)

def x : Syn .yulExpr := .yulPath "x" []
def y : Syn .yulExpr := .yulPath "y" []
def addTree : Syn .yulExpr := .yulCall "add" (synList [x,.yulLit (.dec 2)])
def mulTree : Syn .yulExpr := .yulCall "mul" (synList [x,.yulLit (.dec 7)])
def eqTree : Syn .yulExpr := .yulCall "eq" (synList [x,.yulLit (.dec 3)])
def innerTree : Syn .yulStmt := .yulSwitch y
  (synList [.yulCase (.dec dirty.toNat) (synList [.yulAssign ["x"] [] addTree])])
  (.some (synList [.yulAssign ["x"] [] (.yulLit (.dec 99))]))
def defaultTree : Syn .yulStmt := .yulSwitch x
  (synList [.yulCase (.dec 8) (synList [.yulAssign ["x"] [] (.yulLit (.dec 42))])])
  (.some (synList [.yulAssign ["x"] [] (.yulLit (.dec 17))]))
def outerTree : Syn .yulStmt := .yulSwitch x
  (synList [.yulCase (.dec 1) (synList [
    .yulLet "y" [] (.some (.yulLit (.dec dirty.toNat))),innerTree]),
    .yulCase (.dec 3) (synList [.yulAssign ["x"] [] (.yulLit (.dec 999))])])
  (.some (synList [defaultTree]))
def conditionalTree : Syn .yulStmt := .yulIf eqTree
  (synList [.yulAssign ["x"] [] mulTree])
def tree : Syn (.list .yulStmt) := synList [
  .yulLet "x" [] (.some (.yulLit (.dec 1))),outerTree,conditionalTree]
def prepared : Solidity.Yul.WordSyntax.Prepared [] tree :=
  ((Solidity.Yul.WordSyntax.prepare [] tree).toOption).get (by decide)
def lowered := (NestedSwitch.compile 16 prepared.program.code).get (by decide)
def block := lowered.emit.get (by decide)
def selected := (LoopSelection.selectBlock block).get (by decide)
#check lowered.source (#v[] : Vector Scalar.Word 0)
#check lowered.structured block rfl (#v[] : Vector Scalar.Word 0) [dirty,77]
#guard (prepared.run 16).map (fun out => out.flow.isNormal) == some true
#guard Controls.observe (Evm.run selected.realization.ir (Controls.machine [dirty,77])) ==
  some ([some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)

def ast := Controls.block #[Controls.decl "x" (Controls.lit "1"),Controls.outer,Controls.conditional]

/-- Only the exact remaining existing decoder equation is an input. All
metadata, safety, typed preparation and actual compilation are constructed. -/
def checkedFromParse (parsed : blockAux 20 ast = .ok tree) :
    Words.Checked [] 20 (Controls.fixture "1") where
  imported := JsonCompilation.Controls.imported
  imported_eq := by rfl
  rawSpan := "0:1:0"
  rawSpan_eq := by rfl
  span := ⟨0,1,0⟩
  span_eq := JsonCompilation.Controls.checked.span_eq
  ast := ast
  ast_eq := by rfl
  shaped := ⟨⟨tree,parsed⟩,show tree.prec = true from by decide⟩
  safe := ⟨.flag (by decide)⟩
  prepared := prepared

def compiledFromParse (parsed : blockAux 20 ast = .ok tree) :
    StructuredJson.Compiled (checkedFromParse parsed) 16 where
  statement := lowered
  block := block
  emitted := by rfl
  selected := selected

def packetFromParse (parsed : blockAux 20 ast = .ok tree) :
    StructuredJson.Packet [] 20 16 (Controls.fixture "1") :=
  ⟨checkedFromParse parsed,compiledFromParse parsed⟩

/-- Conditional preparation only: this does not supply its parser premise. -/
theorem compilesFromParse (parsed : blockAux 20 ast = .ok tree) :
    StructuredJson.checkCompile [] 20 16 (Controls.fixture "1") =
    .ok (packetFromParse parsed) := by
  simp only [StructuredJson.checkCompile,(checkedFromParse parsed).complete,
    Except.mapError,bind,Except.bind]
  rfl

#check fun parsed => (compiledFromParse parsed).source
#check fun parsed => (compiledFromParse parsed).model [dirty,77] (Controls.machine [dirty,77]) rfl
#guard (NestedSwitch.compile 2 prepared.program.code).isNone
/-- info: 'SolidityBridge.Yul.StructuredSwitchJson.KernelControls.prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms prepared
/-- info: 'SolidityBridge.Yul.StructuredSwitchJson.KernelControls.lowered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lowered
/-- info: 'SolidityBridge.Yul.StructuredSwitchJson.KernelControls.checkedFromParse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checkedFromParse
/-- info: 'SolidityBridge.Yul.StructuredSwitchJson.KernelControls.compiledFromParse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms compiledFromParse
/-- info: 'SolidityBridge.Yul.StructuredSwitchJson.KernelControls.packetFromParse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms packetFromParse
/-- info: 'SolidityBridge.Yul.StructuredSwitchJson.KernelControls.compilesFromParse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms compilesFromParse

-- These target controls use the independently kernel-inhabited tree compiler,
-- not any assumed/raw JSON parsing proof.
def prefixObserved := do
  let partialBlock ← Controls.beforeRetirement block
  let code ← LoopSelection.selectBlock partialBlock
  pure (Controls.observe (Evm.run code.realization.ir (Controls.machine [dirty,77])))
#guard prefixObserved ==
  some (some ([some 21,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false))
#guard (Controls.observe (Evm.run selected.realization.ir
  (Controls.machine (List.replicate 1025 dirty)))).isSome
end SolidityBridge.Yul.StructuredSwitchJson.KernelControls
