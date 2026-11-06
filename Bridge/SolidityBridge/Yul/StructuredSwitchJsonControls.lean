import SolidityBridge.Yul.StructuredJson
import SolidityBridge.Yul.StructuredJsonControls
/-! Synthetic actual checked-JSON ingress controls for nested switch lowering.
Not external solc output, Solidity Body admission or native/G24 adequacy.
The analysis-only prefix extractor below inspects this emitted fixture before
its final one-word retirement; it is not a compiler transformation theorem. -/
namespace SolidityBridge.Yul.StructuredSwitchJson.Controls
open Solidity Backend Scalar Selection
open Lean (Json)
open Solidity.Frontend.YulJson
open SolidityBridge.Yul.StructuredJson
abbrev dirty := JsonCompilation.Controls.dirty
abbrev machine := JsonCompilation.Controls.machine
abbrev observe := JsonCompilation.Controls.observe
abbrev lit := JsonCompilation.Controls.lit
abbrev ident := JsonCompilation.Controls.ident
abbrev call := JsonCompilation.Controls.call
abbrev decl := JsonCompilation.Controls.decl
abbrev assign := JsonCompilation.Controls.assign
abbrev block := JsonCompilation.Controls.block
def node (body : Array Json) (flags : Array Json := #[.str "memory-safe"])
    (evmVersion : String := "osaka") : Json := JsonCompilation.Controls.node body flags evmVersion

def caseNode (value : Json) (statements : Array Json) : Json := Json.mkObj
  [("nodeType",.str "YulCase"),("value",value),("body",block statements)]
def switchNode (selector : Json) (cases : Array Json) : Json := Json.mkObj
  [("nodeType",.str "YulSwitch"),("expression",selector),("cases",.arr cases)]
def inner := switchNode (ident "y") #[
  caseNode (lit (toString dirty.toNat)) #[assign "x" (call "add" #[ident "x",lit "2"])],
  caseNode (.str "default") #[assign "x" (lit "99")]]
def defaultSwitch := switchNode (ident "x") #[
  caseNode (lit "8") #[assign "x" (lit "42")],
  caseNode (.str "default") #[assign "x" (lit "17")]]
def outer := switchNode (ident "x") #[
  caseNode (lit "1") #[decl "y" (lit (toString dirty.toNat)),inner],
  caseNode (lit "3") #[assign "x" (lit "999")],
  caseNode (.str "default") #[defaultSwitch]]
def conditional := Json.mkObj [("nodeType",.str "YulIf"),
  ("condition",call "eq" #[ident "x",lit "3"]),
  ("body",block #[assign "x" (call "mul" #[ident "x",lit "7"])])]
def fixture (initial : String) := node #[decl "x" (lit initial),outer,conditional]
-- New-fixture budgets fixed up front; no old bounds or expected verdict changed.
def result (initial : String) := checkCompile [] 20 16 (fixture initial)
#guard (result "1").isOk
#guard (result "3").isOk
#guard (result "8").isOk
#guard match result "1" with
  | .ok packet => (packet.checked.run 16).map (fun out => out.flow.isNormal) == some true
  | .error _ => false
#guard ((result "1").toOption.map (fun packet =>
  observe (Evm.run packet.compiled.selected.realization.ir (machine [dirty,77])))) ==
  some (some ([some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false))

/-- Inspect only an actual emitted fixture, retaining the final local value
before its existing POP. Zero-prefix wrappers are skipped structurally. -/
def beforeRetirement : Backend.Block → Option Backend.Block
  | .seq (.code []) (.seq body (.code [])) => beforeRetirement body
  | .seq (.code init) (.seq body (.code [.op .POP])) => some (.seq (.code init) body)
  | _ => none

def prefixObserved (initial : String) := do
  let packet ← (result initial).toOption
  let partialBlock ← beforeRetirement packet.compiled.block
  let selected ← LoopSelection.selectBlock partialBlock
  pure (observe (Evm.run selected.realization.ir (machine [dirty,77])))
-- 1->3 inside the first case must not fall through to outercase3=999.
-- A cleaned y would miss the dirty label and yield99 instead of21.
#guard prefixObserved "1" ==
  some (some ([some 21,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false))
#guard prefixObserved "3" ==
  some (some ([some 999,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false))
#guard prefixObserved "8" ==
  some (some ([some 42,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false))
#guard prefixObserved (toString dirty.toNat) ==
  some (some ([some 17,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false))

#guard match checkCompile [] 20 2 (fixture "1") with | .error .statement => true | _ => false
#guard match checkCompile [] 0 16 (fixture "1") with | .error (.input _) => true | _ => false
#guard match checkCompile [] 20 16 (node #[decl "x" (lit "1"),outer,conditional] #[]) with | .error (.input _) => true | _ => false
#guard match checkCompile [] 20 16 (node #[] #[.str "memory-safe",.str "memory-safe"]) with
  | .error (.input _) => true | _ => false
#guard match checkCompile [] 20 16 (node #[] #[.str "memory-safe"] "cancun") with
  | .error (.input _) => true | _ => false
#guard match checkCompile [] 20 16 (node #[decl "x" (call "gas" #[])]) with
  | .error (.input _) => true | _ => false
#guard match checkCompile [] 20 16 (node #[decl "x" (call "codesize" #[])]) with
  | .error (.input _) => true | _ => false
#guard match checkCompile [] 20 16 (node #[switchNode (lit "1") #[
  caseNode (lit "1") #[],caseNode (lit "1") #[]]]) with
  | .error (.input _) => true | _ => false
#guard match checkCompile [] 20 16 (node #[switchNode (lit "1") #[
  caseNode (.str "default") #[],caseNode (lit "1") #[]]]) with
  | .error (.input _) => true | _ => false
-- Full model success on a huge caller does not prove EVM capacity.
#guard match result "1" with
  | .ok packet => (observe (Evm.run packet.compiled.selected.realization.ir
      (machine (List.replicate 1025 dirty)))).isSome
  | .error _ => false
end SolidityBridge.Yul.StructuredSwitchJson.Controls
