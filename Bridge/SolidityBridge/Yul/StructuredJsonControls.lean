import SolidityBridge.Yul.StructuredJson
import SolidityBridge.Yul.JsonCompilationControls
/-! Synthetic checked-JSON structured compilation with an actual arithmetic
body under a true conditional. Decoder certificates are derived from the real
child fixture; this is not external solc evidence or Source admission. -/
namespace SolidityBridge.Yul.StructuredJson.Controls
open Solidity Backend Scalar Selection
open Lean (Json)
open Solidity.Frontend.YulJson
abbrev dirty := JsonCompilation.Controls.dirty
abbrev machine := JsonCompilation.Controls.machine
abbrev observe := JsonCompilation.Controls.observe

def conditional : Json := Json.mkObj [("nodeType",.str "YulIf"),
  ("condition",JsonCompilation.Controls.lit "1"),("body",JsonCompilation.Controls.ast)]
def node := JsonCompilation.Controls.node #[conditional]
def tree : Solidity.Source.Syn (.list .yulStmt) :=
  .cons (.yulIf (.yulLit (.dec 1)) JsonCompilation.Controls.tree) .nil
def prepared : Solidity.Yul.WordSyntax.Prepared [] tree :=
  ((Solidity.Yul.WordSyntax.prepare [] tree).toOption).get (by decide)
private theorem conditionalParsed : statementAux 13 conditional =
    .ok (.yulIf (.yulLit (.dec 1)) JsonCompilation.Controls.tree) := by
  change (do
    let condition ← expressionAux 12 (JsonCompilation.Controls.lit "1")
    let body ← blockAux 12 JsonCompilation.Controls.ast
    pure (Solidity.Source.Syn.yulIf condition body)) = _
  have child : blockAux 12 JsonCompilation.Controls.ast = .ok JsonCompilation.Controls.tree :=
    JsonCompilation.Controls.checked.shaped.parsed
  rw [child]
  rfl

def checked : Words.Checked [] 14 node where
  imported := JsonCompilation.Controls.imported
  imported_eq := by rfl
  rawSpan := "0:1:0"
  rawSpan_eq := by rfl
  span := ⟨0,1,0⟩
  span_eq := JsonCompilation.Controls.checked.span_eq
  ast := JsonCompilation.Controls.block #[conditional]
  ast_eq := by rfl
  shaped := ⟨⟨tree,by
    change (do
      let items ← [conditional].mapM (statementAux 13)
      pure (Solidity.Frontend.Checked.toSynList items)) = _
    simp only [List.mapM_cons,List.mapM_nil,conditionalParsed]
    rfl⟩,by decide⟩
  safe := ⟨.flag (by decide)⟩
  prepared := prepared

def compiled := ((compile checked 6).toOption).get (by decide)
def packet : Packet [] 14 6 node := ⟨checked,compiled⟩
theorem conditional_compiles : checkCompile [] 14 6 node = .ok packet := by
  simp only [checkCompile,checked.complete,Except.mapError,bind,Except.bind]
  rfl
#check packet.compiled.source
#check packet.compiled.model [dirty,77] (machine [dirty,77]) rfl
#guard (packet.checked.run 6).map (fun result => result.flow.isNormal) == some true
#guard observe (Evm.run packet.compiled.selected.realization.ir (machine [dirty,77])) ==
  some ([some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard match packet.compiled.block with | .ite _ _ _ => true | _ => false
#guard match packet.compiled.block with
  | .ite condition _ _ => Scalar.run condition [dirty,77] == some [1,dirty,77]
  | _ => false
#guard match checkCompile [] 14 2 node with | .error .statement => true | _ => false
#guard match checkCompile [] 0 6 node with | .error (.input _) => true | _ => false
#guard match checkCompile [] 14 6 (JsonCompilation.Controls.node #[conditional] #[]) with
  | .error (.input _) => true | _ => false
#guard match checkCompile [] 14 6 (JsonCompilation.Controls.node #[] #[.str "memory-safe",.str "memory-safe"]) with
  | .error (.input _) => true | _ => false
#guard match checkCompile [] 14 6 (JsonCompilation.Controls.node #[] #[.str "memory-safe"] "cancun") with
  | .error (.input _) => true | _ => false
#guard match checkCompile [] 14 6 (JsonCompilation.Controls.node #[JsonCompilation.Controls.decl "x" (JsonCompilation.Controls.call "gas" #[])]) with
  | .error (.input _) => true | _ => false
#guard match checkCompile [] 14 6 (JsonCompilation.Controls.node #[JsonCompilation.Controls.decl "x" (JsonCompilation.Controls.call "codesize" #[])]) with
  | .error (.input _) => true | _ => false
-- The prior scalar-only API keeps its exact conservative refusal.
#guard match JsonCompilation.checkCompile [] 12 5 JsonCompilation.Controls.ifNode with | .error .statement => true | _ => false
#guard (checkCompile [] 12 5 JsonCompilation.Controls.ifNode).isOk
#guard !(Scalar.stackBound [pushWord 1] 1024)
#guard (observe (Evm.run packet.compiled.selected.realization.ir
  (machine (List.replicate 1025 dirty)))).isSome
/-- info: 'SolidityBridge.Yul.StructuredJson.Controls.conditional_compiles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms conditional_compiles
end SolidityBridge.Yul.StructuredJson.Controls
