import Solidity.Yul.Compilation.NormalControl
import Solidity.Backend.Selection.Interface
/-! Original Yul normal-control compilation to the existing StructuredExec
relation. No replacement AST, block semantics or source state is introduced.
This is not native/LabelExec realization, capacity or general Source/G24. -/
namespace SolidityBridge.Yul.StructuredSource
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation

theorem structured :
∀ {c : Solidity.Yul.Control} {n fuel : Nat} {stmt : Solidity.Yul.Stmt [] [] c n}
    (compiled : Solidity.Yul.Compilation.NormalControl.Derivation fuel stmt)
    (depth : Nat) (block : Solidity.Backend.Block),
    compiled.emit depth = some block →
    ∀ (locals : Vector Solidity.Backend.Scalar.Word n) (newer : Vector Solidity.Backend.Scalar.Word depth)
      (tail : Solidity.Backend.Scalar.Stack),
    Solidity.Backend.Selection.StructuredExec block (newer.toList ++ (locals.toList ++ tail))
      (newer.toList ++ ((compiled.update locals).toList ++ tail)) := by
  intro c n fuel stmt compiled depth block emitted locals newer tail
  induction compiled generalizing block locals with
  | scalar leaf =>
    change (leaf.lowered.code depth).map Backend.Block.code = some block at emitted
    cases hp : leaf.lowered.code depth with
    | none => simp only [hp,Option.map_none,reduceCtorEq] at emitted
    | some p =>
      simp only [hp,Option.map_some,Option.some.injEq] at emitted
      subst block
      exact StructuredExec.code (leaf.lowered.correct depth p hp locals newer tail)
  | seq first second ihFirst ihSecond =>
    change (do
      let a ← first.emit depth
      let b ← second.emit depth
      pure (Backend.Block.seq a b)) = some block at emitted
    cases ha : first.emit depth with
    | none => simp only [ha] at emitted; cases emitted
    | some a =>
      cases hb : second.emit depth with
      | none => simp only [ha,hb] at emitted; cases emitted
      | some b =>
        simp only [ha,hb] at emitted
        have same : Backend.Block.seq a b = block := Option.some.inj emitted
        subst block
        exact StructuredExec.seq (ihFirst a ha locals) (ihSecond b hb (first.update locals))
  | branch condition arm ih =>
    change (do
      let cc ← condition.lowered.code depth
      let bb ← arm.emit depth
      pure (Backend.Block.ite cc bb (.code []))) = some block at emitted
    cases hc : condition.lowered.code depth with
    | none => simp only [hc] at emitted; cases emitted
    | some cc =>
      cases hb : arm.emit depth with
      | none => simp only [hc,hb] at emitted; cases emitted
      | some bb =>
        simp only [hc,hb] at emitted
        have same : Backend.Block.ite cc bb (.code []) = block := Option.some.inj emitted
        subst block
        have test := condition.lowered.correct depth cc hc locals newer tail
        by_cases zero : condition.value locals = 0
        · change StructuredExec (.ite cc bb (.code [])) _
            (newer.toList ++ ((if condition.value locals = 0 then locals else arm.update locals).toList ++ tail))
          rw [if_pos zero]
          apply StructuredExec.iteFalse
          · simpa only [zero] using test
          · exact StructuredExec.code rfl
        · change StructuredExec (.ite cc bb (.code [])) _
            (newer.toList ++ ((if condition.value locals = 0 then locals else arm.update locals).toList ++ tail))
          rw [if_neg zero]
          exact StructuredExec.iteTrue test zero (ih bb hb locals)

def increment : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .assign (fun _ : Fin 1 => .local 1)
    (.builtin (.pure .add) (Fin.cases (.local 1) (fun _ => .literal (Solidity.Yul.word 1))))
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 := .if_ (.local 0) increment
def compiled := (NormalControl.compile 4 statement).get (by rfl)
def block := (compiled.emit 0).get (by rfl)

def firstAssign : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .assign (fun _ : Fin 1 => .local 0) (.local 1)
def sequenceStatement := Solidity.Yul.Stmt.seq firstAssign statement
def sequenceCompiled := (NormalControl.compile 5 sequenceStatement).get (by rfl)
def sequenceBlock := (sequenceCompiled.emit 0).get (by rfl)

def nestedStatement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .if_ (.local 0) (.if_ (.local 1) increment)
def nestedCompiled := (NormalControl.compile 5 nestedStatement).get (by rfl)
def nestedBlock := (nestedCompiled.emit 0).get (by rfl)
def prefixedBlock := (compiled.emit 2).get (by rfl)

/-- Actual compiler instances, not assumed target condition/arm runs. -/
abbrev branch_execution := structured compiled 0 block (by rfl)
abbrev sequence_execution := structured sequenceCompiled 0 sequenceBlock (by rfl)
abbrev nested_execution := structured nestedCompiled 0 nestedBlock (by rfl)
abbrev prefixed_execution := structured compiled 2 prefixedBlock (by rfl)

end SolidityBridge.Yul.StructuredSource
