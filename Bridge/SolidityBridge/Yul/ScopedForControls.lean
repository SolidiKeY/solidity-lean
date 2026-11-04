import SolidityBridge.Yul.ScopedFor
import SolidityBridge.Yul.ArithmeticSelectionControls

/-! Actual lexical temporary and switch/default within FOR components.
Source horizon10 comes from actual componentfuel6 plus2turns+2, not a budget
increase or native gas. No frontend admission or physical capacity claim. -/
namespace SolidityBridge.Yul.ScopedFor.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed Solidity.Yul.Compilation ProducerExpressions
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe

def pre : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .zero 1 (.assign (fun _ : Fin 1 => .local 1) (.literal (Solidity.Yul.word 2)))
def condition : Solidity.Yul.Expr [] [] 2 1 := .local 0
def body : Solidity.Yul.Stmt [] [] ⟨false,true⟩ 2 := .zero 1
  (.seq (.assign (fun _ : Fin 1 => .local 0) (.local 1))
    (.assign (fun _ : Fin 1 => .local 1)
      (.builtin (.pure .sub) (Fin.cases (.local 0) (fun _ => .literal (Solidity.Yul.word 1))))))
def post : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .switch (.local 0)
    (.cons (Solidity.Yul.word 0)
      (.assign (fun _ : Fin 1 => .local 1)
        (.builtin (.pure .add) (Fin.cases (.local 1) (fun _ => .literal (Solidity.Yul.word 10))))) .nil)
    (.assign (fun _ : Fin 1 => .local 1)
      (.builtin (.pure .add) (Fin.cases (.local 1) (fun _ => .literal (Solidity.Yul.word 1)))))
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 := .for_ pre condition post body
def prepared := (prepare 6 (c := ⟨false,false⟩) pre condition post body).get (by rfl)
def target := (emit prepared).get (by rfl)
def selected := (LoopSelection.selectBlock target).get (by rfl)
def packet : Packet prepared := ⟨target,(Option.some_get (by rfl)).symm,selected⟩
def produced : Σ p : Prepared 6 (c := ⟨false,false⟩) pre condition post body, Packet p := ⟨prepared,packet⟩

/-- The separated proof bindings still describe the real combined compiler. -/
theorem compile_entry : compile 6 (c := ⟨false,false⟩) pre condition post body = some produced := by
  have hp : prepare 6 (c := ⟨false,false⟩) pre condition post body = some prepared :=
    (Option.some_get (by rfl)).symm
  have he : emit prepared = some target := (Option.some_get (by rfl)).symm
  have hs : LoopSelection.selectBlock target = some selected := (Option.some_get (by rfl)).symm
  have actual : select prepared = some packet := by
    unfold select
    split
    · rename_i missing
      rw [he] at missing
      cases missing
    · rename_i block emitted
      have same : block = target := Option.some.inj (emitted.symm.trans he)
      subst block
      rw [hs]
      rfl
  unfold compile
  apply Option.bind_eq_some_iff.mpr
  refine ⟨prepared,hp,?_⟩
  apply Option.bind_eq_some_iff.mpr
  exact ⟨packet,actual,rfl⟩

/-- Prelude's overwritten counter is independent of its arbitrary raw input. -/
theorem reset (initial : Scalar.Word) : prepared.before.update #v[initial,dirty] = #v[2,dirty] := by rfl

theorem after_one : update prepared #v[2,dirty] = #v[1,dirty+1] := by decide

theorem after_two : update prepared #v[1,dirty+1] = #v[0,dirty+11] := by decide

theorem finish (initial : Scalar.Word) :
    Nat.repeat (update prepared) 2 (prepared.before.update #v[initial,dirty]) = #v[0,dirty+11] := by
  rw [reset]
  change update prepared (update prepared #v[2,dirty]) = _
  rw [after_one,after_two]

theorem two_running (initial : Scalar.Word) : ∀ j, j < 2 → prepared.test.value
    (Nat.repeat (update prepared) j (prepared.before.update #v[initial,dirty])) ≠ 0 := by
  intro j bound
  have cases : j = 0 ∨ j = 1 := by omega
  rcases cases with same | same
  · subst j
    rw [reset]
    change (2 : Scalar.Word) ≠ 0
    decide
  · subst j
    rw [reset]
    change prepared.test.value (update prepared #v[2,dirty]) ≠ 0
    rw [after_one]
    change (1 : Scalar.Word) ≠ 0
    decide

theorem source_ten (initial : Scalar.Word) :
    evalStmt 10 .nil True.intro statement (profile prepared) (sourceLocals #v[initial,dirty]) =
      some ⟨sourceLocals #v[0,dirty+11],.normal⟩ := by
  have stopped : prepared.test.value (Nat.repeat (update prepared) 2
      (prepared.before.update #v[initial,dirty])) = 0 := by rw [finish]; rfl
  have ran := source prepared 6 2 (by decide) #v[initial,dirty] (two_running initial) stopped
  rw [finish] at ran
  exact ran

theorem target_two (initial : Scalar.Word) (caller : Stack) :
    StructuredExec packet.block ([initial,dirty] ++ caller) ([0,dirty+11] ++ caller) := by
  have stopped : prepared.test.value (Nat.repeat (update prepared) 2
      (prepared.before.update #v[initial,dirty])) = 0 := by rw [finish]; rfl
  have ran := structured prepared packet.block packet.emitted 2 #v[initial,dirty] caller (two_running initial) stopped
  rw [finish] at ran
  exact ran

theorem model_two (initial : Scalar.Word) (caller : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([initial,dirty] ++ caller)) :
    Evm.run packet.selected.realization.ir m =
      .ok {m with stack := irStack ([0,dirty+11] ++ caller)} 0 := by
  have stopped : prepared.test.value (Nat.repeat (update prepared) 2
      (prepared.before.update #v[initial,dirty])) = 0 := by rw [finish]; rfl
  have ran := Packet.model prepared packet 2 #v[initial,dirty] caller (two_running initial) stopped m represented
  rw [finish] at ran
  exact ran

/-- Post after decrement reaches zero and adds10. Reversing that order would
miss the zero case and yield only dirty+2 for these two turns. -/
theorem final_order_control (initial : Scalar.Word) :
    (Nat.repeat (update prepared) 2 (prepared.before.update #v[initial,dirty]))[1] ≠ dirty+2 := by
  rw [finish]
  change dirty+11 ≠ dirty+2
  decide

/-- Break has genuine source meaning but no normal component certificate. -/
theorem break_refused : (compile 6 (c := ⟨false,false⟩) pre condition post
    (Solidity.Yul.Stmt.break_ (n := 2))).isNone = true := by decide

theorem zero_compiler_horizon : (compile 0 (c := ⟨false,false⟩) pre condition post body).isNone = true := by rfl

#guard observe (Evm.run packet.selected.realization.ir (machine [99,dirty,88])) ==
  some ([some 0,some (dirty+11).toNat,some 88],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run packet.selected.realization.ir (machine [0,dirty,88])) ==
  some ([some 0,some (dirty+11).toNat,some 88],some dirty.toNat,23,99,99,7,11,19,31,false)
#check source_ten 99
#check source_ten 0
#check model_two 99 [88,dirty]
/-- info: 'SolidityBridge.Yul.ScopedFor.Controls.compile_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile_entry
/-- info: 'SolidityBridge.Yul.ScopedFor.Controls.reset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reset
/-- info: 'SolidityBridge.Yul.ScopedFor.Controls.after_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms after_one
/-- info: 'SolidityBridge.Yul.ScopedFor.Controls.after_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms after_two
/-- info: 'SolidityBridge.Yul.ScopedFor.Controls.finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finish
/-- info: 'SolidityBridge.Yul.ScopedFor.Controls.two_running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_running
/-- info: 'SolidityBridge.Yul.ScopedFor.Controls.source_ten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_ten
/-- info: 'SolidityBridge.Yul.ScopedFor.Controls.target_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_two
/-- info: 'SolidityBridge.Yul.ScopedFor.Controls.model_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_two
/-- info: 'SolidityBridge.Yul.ScopedFor.Controls.final_order_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms final_order_control
/-- info: 'SolidityBridge.Yul.ScopedFor.Controls.break_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms break_refused
/-- info: 'SolidityBridge.Yul.ScopedFor.Controls.zero_compiler_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_compiler_horizon
end SolidityBridge.Yul.ScopedFor.Controls
