import SolidityBridge.Yul.StructuredFor
import SolidityBridge.Yul.ArithmeticSelectionControls

/-! Original FOR with branches in prelude, body and postlude. A high-only
word flag must be true; post sees the updated counter. These are finite
closed-word/source and selected mathematical-model controls, not native/G24. -/
namespace SolidityBridge.Yul.StructuredFor.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed
open Solidity.Yul.Compilation ProducerExpressions
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
def high : Scalar.Word := BitVec.ofNat 256 (2^200)

def pre : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .if_ (.local 2) (.assign (fun _ : Fin 1 => .local 0) (.literal (Solidity.Yul.word 2)))
def condition : Solidity.Yul.Expr [] [] 3 1 := .local 0
def body : Solidity.Yul.Stmt [] [] ⟨false,true⟩ 3 :=
  .if_ (.local 2) (.assign (fun _ : Fin 1 => .local 0)
    (.builtin (.pure .sub) (Fin.cases (.local 0) (fun _ => .literal (Solidity.Yul.word 1)))))
def post : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .if_ (.local 0) (.assign (fun _ : Fin 1 => .local 1)
    (.builtin (.pure .add) (Fin.cases (.local 1) (fun _ => .literal (Solidity.Yul.word 1)))))
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 := .for_ pre condition post body
def prepared := (prepare 4 (c := ⟨false,false⟩) pre condition post body).get (by rfl)
def test := prepared.test
def after := prepared.after
def inside := prepared.inside
def before := prepared.before
def actualProfile := profile (c := ⟨false,false⟩) test after inside before
def target := (emit (c := ⟨false,false⟩) test after inside before 2).get (by rfl)
def selected := (LoopSelection.selectBlock target).get (by rfl)

private theorem two_running : ∀ j, j < 2 → test.value
    (Nat.repeat (fun l => after.update (inside.update l)) j (before.update #v[99,dirty,high])) ≠ 0 := by
  intro j bound
  have cases : j = 0 ∨ j = 1 := by omega
  rcases cases with same | same <;> subst j <;> decide

/-- Genuine original FOR execution with three branch-bearing components.
Horizon8 is sufficient by component4/count2; minimality is not claimed. -/
theorem source_eight :
    evalStmt 8 .nil True.intro statement actualProfile (sourceLocals #v[99,dirty,high]) =
      some ⟨sourceLocals #v[0,dirty+1,high],.normal⟩ :=
  source (c := ⟨false,false⟩) test after inside before 4 2
    (by decide) (by decide) (by decide) (by decide) #v[99,dirty,high] two_running (by decide)

theorem target_two (tail : Stack) :
    StructuredExec target ([77,dirty] ++ ([99,dirty,high] ++ tail))
      ([77,dirty] ++ ([0,dirty+1,high] ++ tail)) :=
  structured (c := ⟨false,false⟩) test after inside before 2 target rfl 2
    #v[99,dirty,high] #v[77,dirty] tail two_running (by decide)

theorem model_two (tail : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([77,dirty] ++ ([99,dirty,high] ++ tail))) :
    Evm.run selected.realization.ir m =
      .ok {m with stack := irStack ([77,dirty] ++ ([0,dirty+1,high] ++ tail))} 0 :=
  model (c := ⟨false,false⟩) test after inside before 2 target rfl selected 2
    #v[99,dirty,high] #v[77,dirty] tail two_running (by decide) m represented

/-- False prelude branch and zero loop guard execute no body/post. -/
theorem zero_source :
    evalStmt 6 .nil True.intro statement actualProfile (sourceLocals #v[0,dirty,0]) =
      some ⟨sourceLocals #v[0,dirty,0],.normal⟩ :=
  source (c := ⟨false,false⟩) test after inside before 4 0
    (by decide) (by decide) (by decide) (by decide) #v[0,dirty,0]
    (by intro j bound; omega) (by decide)

theorem zero_target (tail : Stack) :
    StructuredExec target ([77,dirty] ++ ([0,dirty,0] ++ tail))
      ([77,dirty] ++ ([0,dirty,0] ++ tail)) :=
  structured (c := ⟨false,false⟩) test after inside before 2 target rfl 0
    #v[0,dirty,0] #v[77,dirty] tail (by intro j bound; omega) (by decide)

#guard high.toNat % 256 = 0
#guard high != 0
#guard observe (Evm.run selected.realization.ir (machine [77,dirty,99,dirty,high,88])) ==
  some ([some 77,some dirty.toNat,some 0,some (dirty+1).toNat,some high.toNat,some 88],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.run selected.realization.ir (machine [77,dirty,0,dirty,0,88]))).map (fun out => out.1) ==
  some [some 77,some dirty.toNat,some 0,some dirty.toNat,some 0,some 88]
#guard (prepare 3 (c := ⟨false,false⟩) pre condition post body).isNone
#guard (prepare 4 (c := ⟨false,false⟩) pre condition post (Solidity.Yul.Stmt.break_)).isNone
#guard (prepare 4 (c := ⟨false,false⟩) pre condition post (Solidity.Yul.Stmt.continue_)).isNone
#guard (emit (c := ⟨false,false⟩) test after inside before 13).isSome
#guard (emit (c := ⟨false,false⟩) test after inside before 14).isNone
#guard (evalStmt 3 .nil True.intro statement actualProfile (sourceLocals #v[99,dirty,high])).isNone
-- Only finite source exhaustion is observed; never run the unending target.
#guard (evalStmt 8 .nil True.intro statement actualProfile (sourceLocals #v[99,dirty,0])).isNone
#guard match Evm.run selected.realization.ir (machine []) with | .fault => true | _ => false
-- Numeric model success carries no native expansion/stack-capacity certificate.
#guard (observe (Evm.run selected.realization.ir
  (machine ([77,dirty,99,dirty,high] ++ List.replicate 1021 88)))).isSome

/-- info: 'SolidityBridge.Yul.StructuredFor.Controls.source_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_eight
/-- info: 'SolidityBridge.Yul.StructuredFor.Controls.target_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_two
/-- info: 'SolidityBridge.Yul.StructuredFor.Controls.model_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_two
/-- info: 'SolidityBridge.Yul.StructuredFor.Controls.zero_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_source
/-- info: 'SolidityBridge.Yul.StructuredFor.Controls.zero_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_target
end SolidityBridge.Yul.StructuredFor.Controls
