import SolidityBridge.Yul.ForCompletion
import SolidityBridge.Yul.StructuredUnique
import SolidityBridge.Yul.StructuredSource

/-! Reflection of actual finite target FOR executions into the original
closed-word source. No native/G24/resource/observation closure is asserted. -/
namespace SolidityBridge.Yul.ForReflection
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed
open Solidity.Yul.Compilation ProducerExpressions
section
variable {c : Solidity.Yul.Control} {n cf pf bf : Nat}
  {condition : Solidity.Yul.Expr [] [] n 1}
  {post : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  {body : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n}
  (test : ProducerExpressions.Compiled cf condition)
  (after : NormalControl.Derivation pf post)
  (inside : NormalControl.Derivation bf body)


private theorem loopAux (depth : Nat) (cc : Backend.Program) (postBlock bodyBlock : Backend.Block)
    (hc : test.lowered.code depth = some cc)
    (hp : after.emit depth = some postBlock) (hb : inside.emit depth = some bodyBlock)
    (block : Backend.Block) (input output : Stack) (executed : StructuredExec block input output) :
    block = .loop cc (.seq bodyBlock postBlock) →
    ∀ (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth) (tail : Stack),
    input = newer.toList ++ (locals.toList ++ tail) →
    ∃ count,
      (∀ j, j < count → test.value (Nat.repeat (fun l => after.update (inside.update l)) j locals) ≠ 0) ∧
      test.value (Nat.repeat (fun l => after.update (inside.update l)) count locals) = 0 ∧
      output = newer.toList ++ ((Nat.repeat (fun l => after.update (inside.update l)) count locals).toList ++ tail) := by
  induction executed with
  | code ran => intro same; cases same
  | seq a b ia ib => intro same; cases same
  | iteTrue tested nonzero body ih => intro same; cases same
  | iteFalse tested body ih => intro same; cases same
  | @loopDone actualCondition actualBody input output tested =>
    intro same locals newer tail represented
    obtain ⟨rfl,rfl⟩ := Backend.Block.loop.inj same
    subst input
    have expected := test.lowered.correct depth _ hc locals newer tail
    obtain ⟨zero,result⟩ := List.cons.inj (Option.some.inj (tested.symm.trans expected))
    exact ⟨0,(by intro j bound; omega),zero.symm,result⟩
  | @loopMore actualCondition actualBody input middle next output w tested nonzero body rest ihBody ihRest =>
    intro same locals newer tail represented
    obtain ⟨rfl,rfl⟩ := Backend.Block.loop.inj same
    subst input
    have expected := test.lowered.correct depth _ hc locals newer tail
    obtain ⟨wordSame,middleSame⟩ := List.cons.inj (Option.some.inj (tested.symm.trans expected))
    subst w
    subst middle
    have expectedBody := StructuredExec.seq
      (StructuredSource.structured inside depth bodyBlock hb locals newer tail)
      (StructuredSource.structured after depth postBlock hp (inside.update locals) newer tail)
    have nextSame := StructuredUnique.output_unique body expectedBody
    subst next
    obtain ⟨count,running,stopped,result⟩ := ihRest rfl (after.update (inside.update locals)) newer tail rfl
    refine ⟨count+1,?_,?_,?_⟩
    · intro j prior
      cases j with
      | zero => exact nonzero
      | succ j =>
        rw [←LoweredWhile.repeat_shift]
        exact running j (by omega)
    · rw [←LoweredWhile.repeat_shift]
      exact stopped
    · rw [←LoweredWhile.repeat_shift]
      exact result

/-- Recover actual compiler loop guards and output from finite target execution. -/
theorem loop_complete (depth : Nat) (cc : Backend.Program) (postBlock bodyBlock : Backend.Block)
    (hc : test.lowered.code depth = some cc)
    (hp : after.emit depth = some postBlock) (hb : inside.emit depth = some bodyBlock)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth) (tail output : Stack)
    (executed : StructuredExec (.loop cc (.seq bodyBlock postBlock))
      (newer.toList ++ (locals.toList ++ tail)) output) :
    ∃ count,
      (∀ j, j < count → test.value (Nat.repeat (fun l => after.update (inside.update l)) j locals) ≠ 0) ∧
      test.value (Nat.repeat (fun l => after.update (inside.update l)) count locals) = 0 ∧
      output = newer.toList ++ ((Nat.repeat (fun l => after.update (inside.update l)) count locals).toList ++ tail) :=
  loopAux test after inside depth cc postBlock bodyBlock hc hp hb _ _ _ executed rfl locals newer tail rfl

variable {af : Nat} {pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  (before : NormalControl.Derivation af pre)

/-- Reflect the actual prelude-plus-loop target block into original FOR source
execution, deriving every guard from the target execution rather than assuming it. -/
theorem source_of_structured (depth : Nat) (preBlock : Backend.Block) (cc : Backend.Program)
    (postBlock bodyBlock : Backend.Block)
    (ha : before.emit depth = some preBlock) (hc : test.lowered.code depth = some cc)
    (hp : after.emit depth = some postBlock) (hb : inside.emit depth = some bodyBlock)
    (base : Nat) (ba : af ≤ base) (bc : cf ≤ base) (bp : pf ≤ base) (bb : bf ≤ base)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth) (tail output : Stack)
    (executed : StructuredExec (.seq preBlock (.loop cc (.seq bodyBlock postBlock)))
      (newer.toList ++ (locals.toList ++ tail)) output) :
    ∃ count,
      evalStmt (base+(count+2)) .nil True.intro (.for_ (c := c) pre condition post body)
        (StructuredFor.profile test after inside before) (sourceLocals locals) =
        some ⟨sourceLocals (Nat.repeat (fun l => after.update (inside.update l))
          count (before.update locals)),.normal⟩ ∧
      output = newer.toList ++ ((Nat.repeat (fun l => after.update (inside.update l))
        count (before.update locals)).toList ++ tail) := by
  cases executed with
  | seq preRun loopRun =>
    have preSame := StructuredUnique.output_unique preRun
      (StructuredSource.structured before depth preBlock ha locals newer tail)
    subst preSame
    obtain ⟨count,running,stopped,result⟩ := loop_complete test after inside depth cc postBlock bodyBlock
      hc hp hb (before.update locals) newer tail output loopRun
    exact ⟨count,StructuredFor.source test after inside before base count ba bc bp bb locals running stopped,result⟩

/-- Successful selected MODEL execution determines a genuine source horizon,
exact source-result stack and unchanged nonstack frame. This is not native EVM
execution and supplies no gas/capacity/Source-G24 adequacy. -/
theorem source_of_model (depth : Nat) (preBlock : Backend.Block) (cc : Backend.Program)
    (postBlock bodyBlock : Backend.Block)
    (ha : before.emit depth = some preBlock) (hc : test.lowered.code depth = some cc)
    (hp : after.emit depth = some postBlock) (hb : inside.emit depth = some bodyBlock)
    (selected : OccurrenceControl.Selected (.seq preBlock (.loop cc (.seq bodyBlock postBlock))))
    (base : Nat) (ba : af ≤ base) (bc : cf ≤ base) (bp : pf ≤ base) (bb : bf ≤ base)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth) (tail : Stack)
    (m actual : Evm.Machine) (pending : Nat)
    (represented : m.stack = irStack (newer.toList ++ (locals.toList ++ tail)))
    (ran : Evm.run selected.realization.ir m = .ok actual pending) :
    ∃ count,
      evalStmt (base+(count+2)) .nil True.intro (.for_ (c := c) pre condition post body)
        (StructuredFor.profile test after inside before) (sourceLocals locals) =
        some ⟨sourceLocals (Nat.repeat (fun l => after.update (inside.update l))
          count (before.update locals)),.normal⟩ ∧
      actual = {m with stack := irStack (newer.toList ++
        ((Nat.repeat (fun l => after.update (inside.update l))
          count (before.update locals)).toList ++ tail))} ∧ pending = 0 := by
  rcases selected.classified (newer.toList ++ (locals.toList ++ tail)) m represented with
    fault | ⟨output,executed,completed⟩
  · rw [fault] at ran
    cases ran
  · obtain ⟨count,source,result⟩ := source_of_structured test after inside before depth preBlock cc
      postBlock bodyBlock ha hc hp hb base ba bc bp bb locals newer tail output executed
    have same := Evm.Out.ok.inj (ran.symm.trans completed)
    rw [result] at same
    exact ⟨count,source,same.1,same.2⟩

end
/-- info: 'SolidityBridge.Yul.ForReflection.loop_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms loop_complete
/-- info: 'SolidityBridge.Yul.ForReflection.source_of_structured' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_of_structured
/-- info: 'SolidityBridge.Yul.ForReflection.source_of_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_of_model
end SolidityBridge.Yul.ForReflection
