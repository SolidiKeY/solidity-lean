import SolidityBridge.Yul.NormalFor
import SolidityBridge.Yul.ArithmeticSelectionControls

/-! Original intrinsic FOR: pre initializes counter2; body decrements it;
post adds the UPDATED counter to the dirty second local. Two iterations give
dirty+1, not dirty+3 (post-before-body), with prefix/caller unchanged. -/
namespace SolidityBridge.Yul.NormalFor.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed
open Solidity.Yul.Compilation ProducerExpressions
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe

def pre : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .assign (fun _ : Fin 1 => .local 0) (.literal (Solidity.Yul.word 2))
def condition : Solidity.Yul.Expr [] [] 2 1 := .local 0
def body : Solidity.Yul.Stmt [] [] ⟨false,true⟩ 2 :=
  .assign (fun _ : Fin 1 => .local 0)
    (.builtin (.pure .sub) (Fin.cases (.local 0) (fun _ => .literal (Solidity.Yul.word 1))))
def post : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .assign (fun _ : Fin 1 => .local 1)
    (.builtin (.pure .add) (Fin.cases (.local 1) (fun _ => .local 0)))
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 := .for_ pre condition post body
def prepared := (prepare 3 (c := ⟨false,false⟩) pre condition post body).get (by rfl)
def test := prepared.test
def after := prepared.after
def inside := prepared.inside
def before := prepared.before
def actualProfile := profile (c := ⟨false,false⟩) test after inside before
def target := (emit (c := ⟨false,false⟩) test after inside before 2).get (by rfl)
def selected := (LoopSelection.selectBlock target).get (by rfl)

private theorem two_running : ∀ j, j < 2 → test.value
    (Nat.repeat (fun l => after.update (inside.update l)) j (before.update #v[99,dirty])) ≠ 0 := by
  intro j bound
  have cases : j = 0 ∨ j = 1 := by omega
  rcases cases with same | same <;> subst j <;> decide

/-- A kernel source execution for the actual original FOR, not four isolated
leaf runs or an assumed source evaluation equality. Horizon7 is sufficient;
no claim that it is the least sufficient horizon. -/
theorem source_seven :
    evalStmt 7 .nil True.intro statement actualProfile (sourceLocals #v[99,dirty]) =
      some ⟨sourceLocals #v[0,dirty+1],.normal⟩ :=
  source (c := ⟨false,false⟩) test after inside before 3 2 (by decide) (by decide) (by decide) (by decide)
    #v[99,dirty] two_running (by decide)

theorem target_two (tail : Stack) :
    StructuredExec target ([77,dirty] ++ ([99,dirty] ++ tail))
      ([77,dirty] ++ ([0,dirty+1] ++ tail)) :=
  structured (c := ⟨false,false⟩) test after inside before 2 target rfl 2 #v[99,dirty] #v[77,dirty] tail
    two_running (by decide)

theorem model_two (tail : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([77,dirty] ++ ([99,dirty] ++ tail))) :
    Evm.run selected.realization.ir m =
      .ok {m with stack := irStack ([77,dirty] ++ ([0,dirty+1] ++ tail))} 0 :=
  model (c := ⟨false,false⟩) test after inside before 2 target rfl selected 2 #v[99,dirty] #v[77,dirty] tail
    two_running (by decide) m represented

-- Distinct source exhaustion, compiler refusal and target underflow controls.
#guard (evalStmt 2 .nil True.intro statement actualProfile (sourceLocals #v[99,dirty])).isNone
#guard (prepare 2 (c := ⟨false,false⟩) pre condition post body).isNone
#guard (prepare 3 (c := ⟨false,false⟩) pre condition post (Solidity.Yul.Stmt.break_)).isNone
#guard (prepare 3 (c := ⟨false,false⟩) pre condition post (Solidity.Yul.Stmt.continue_)).isNone
#guard (emit (c := ⟨false,false⟩) test after inside before 15).isNone
#guard (test.lowered.code 15).isSome
#guard (inside.lowered.code 15).isNone
#guard match Evm.run selected.realization.ir (machine []) with | .fault => true | _ => false
#guard observe (Evm.run selected.realization.ir (machine [77,dirty,99,dirty,88])) ==
  some ([some 77,some dirty.toNat,some 0,some (dirty+1).toNat,some 88],some dirty.toNat,23,99,99,7,11,19,31,false)
-- Numeric model success has no 1024-word capacity claim.
def preCode := (before.lowered.code 2).get (by rfl)
#guard (Scalar.run preCode (List.replicate 1024 dirty)).isSome
#guard !(Scalar.stackBound preCode 1024)
#guard (observe (Evm.run selected.realization.ir
  (machine ([77,dirty,99,dirty] ++ List.replicate 1021 88)))).isSome

/-- info: 'SolidityBridge.Yul.NormalFor.Controls.source_seven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_seven
/-- info: 'SolidityBridge.Yul.NormalFor.Controls.target_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_two
/-- info: 'SolidityBridge.Yul.NormalFor.Controls.model_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_two
end SolidityBridge.Yul.NormalFor.Controls
