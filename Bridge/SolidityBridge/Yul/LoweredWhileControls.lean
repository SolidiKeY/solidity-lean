import SolidityBridge.Yul.LoweredWhile
import Solidity.Yul.Compilation.PureStatements
import SolidityBridge.Yul.ArithmeticSelectionControls

/-! Finite target-loop witnesses from the actual pure AST compilers. Condition
and body have source certificates; no source FOR-loop theorem is claimed. -/
namespace SolidityBridge.Yul.LoweredWhile.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe

def condition : Solidity.Yul.Expr [] [] 2 1 := .local 0
def body : Solidity.Yul.Stmt [] [] ⟨false,true⟩ 2 :=
  .assign (fun _ : Fin 1 => .local 0)
    (.builtin (.pure .sub) (Fin.cases (.local 0) (fun _ => .literal (Solidity.Yul.word 1))))
def test := (PureExpressions.compile 1 condition).get (by rfl)
def step := (PureStatements.compile 3 body).get (by rfl)
def target := (lowerWhile test.lowered step.lowered 2).get (by rfl)
def selected := (LoopSelection.selectBlock target).get (by rfl)

-- Real source leaf theorems, not a replacement expression/update evaluator.
#check test.source
#check step.source

private theorem two_running : ∀ j, j < 2 →
    test.value (Nat.repeat step.update j #v[2,dirty]) ≠ 0 := by
  intro j bound
  have cases : j = 0 ∨ j = 1 := by omega
  rcases cases with same | same <;> subst j <;> decide

/-- Two body executions with arbitrary caller words, two dirty-preserved locals
in different scope regions, and the full two-word newer prefix. -/
theorem two_turns (tail : Stack) :
    StructuredExec target ([99,dirty] ++ ([2,dirty] ++ tail))
      ([99,dirty] ++ ([0,dirty] ++ tail)) :=
  structured test.lowered step.lowered 2 target rfl 2 #v[2,dirty] #v[99,dirty] tail
    two_running (by decide)

theorem two_turns_model (tail : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([99,dirty] ++ ([2,dirty] ++ tail))) :
    Evm.run selected.realization.ir m =
      .ok {m with stack := irStack ([99,dirty] ++ ([0,dirty] ++ tail))} 0 :=
  model test.lowered step.lowered 2 target rfl selected 2 #v[2,dirty] #v[99,dirty] tail
    two_running (by decide) m represented

theorem zero_turns (tail : Stack) :
    StructuredExec target ([99,dirty] ++ ([0,dirty] ++ tail))
      ([99,dirty] ++ ([0,dirty] ++ tail)) :=
  structured test.lowered step.lowered 2 target rfl 0 #v[0,dirty] #v[99,dirty] tail
    (by intro j bound; omega) (by decide)

#guard observe (Evm.run selected.realization.ir (machine [99,dirty,2,dirty,77])) ==
  some ([some 99,some dirty.toNat,some 0,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard match Evm.run selected.realization.ir (machine []) with | .fault => true | _ => false
#guard (lowerWhile test.lowered step.lowered 16).isNone
-- The condition remains accessible at depth15; RHS's extra word makes the
-- body's old-local read inaccessible. Emission must refuse the whole loop.
#guard (test.lowered.code 15).isSome
#guard (step.lowered.code 15).isNone
#guard (lowerWhile test.lowered step.lowered 15).isNone
#guard (lowerWhile (lowerLocal (n := 16) ⟨15,by decide⟩) (lowerSkip 16) 0).isSome
#guard (lowerWhile (lowerLocal (n := 16) ⟨15,by decide⟩) (lowerSkip 16) 1).isNone
-- Exact scalar success does not certify 1024-word physical capacity.
def testCode := (test.lowered.code 2).get (by rfl)
#guard (Scalar.run testCode (List.replicate 1024 dirty)).isSome
#guard !(Scalar.stackBound testCode 1024)
#guard Scalar.stackBound testCode 1023
#guard (Scalar.run testCode [99,dirty]).isNone

/-- info: 'SolidityBridge.Yul.LoweredWhile.Controls.two_turns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_turns
/-- info: 'SolidityBridge.Yul.LoweredWhile.Controls.two_turns_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_turns_model
/-- info: 'SolidityBridge.Yul.LoweredWhile.Controls.zero_turns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_turns
end SolidityBridge.Yul.LoweredWhile.Controls
