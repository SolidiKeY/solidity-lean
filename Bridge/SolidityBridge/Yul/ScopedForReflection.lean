import SolidityBridge.Yul.ScopedForCompletion
import SolidityBridge.Yul.StructuredUnique

/-! Finite target reflection for actual scope/switch FOR packets. This uses
StructuredExec and the selected mathematical model, not native EVM/G24. -/
namespace SolidityBridge.Yul.ScopedForReflection
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed Solidity.Yul.Compilation ProducerExpressions
section
variable {c : Solidity.Yul.Control} {n compilerFuel : Nat}
  {pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  {condition : Solidity.Yul.Expr [] [] n 1}
  {post : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  {body : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n}
  (compiled : ScopedFor.Prepared compilerFuel (c := c) pre condition post body)

private theorem loopAux (cc : Backend.Program) (postBlock bodyBlock : Backend.Block)
    (hc : compiled.test.lowered.code 0 = some cc)
    (hp : compiled.after.emit = some postBlock) (hb : compiled.inside.emit = some bodyBlock)
    (block : Backend.Block) (input output : Stack) (executed : StructuredExec block input output) :
    block = .loop cc (.seq bodyBlock postBlock) →
    ∀ (locals : Vector Scalar.Word n) (tail : Stack),
    input = locals.toList ++ tail →
    ∃ count,
      (∀ j, j < count → compiled.test.value (Nat.repeat (ScopedFor.update compiled) j locals) ≠ 0) ∧
      compiled.test.value (Nat.repeat (ScopedFor.update compiled) count locals) = 0 ∧
      output = (Nat.repeat (ScopedFor.update compiled) count locals).toList ++ tail := by
  induction executed with
  | code ran => intro same; cases same
  | seq a b ia ib => intro same; cases same
  | iteTrue tested nonzero body ih => intro same; cases same
  | iteFalse tested body ih => intro same; cases same
  | @loopDone actualCondition actualBody input output tested =>
    intro same locals tail represented
    obtain ⟨rfl,rfl⟩ := Backend.Block.loop.inj same
    subst input
    have expected : Scalar.run actualCondition (locals.toList ++ tail) = some (compiled.test.value locals :: (locals.toList ++ tail)) := by
      simpa only [Vector.toList_empty,List.nil_append] using compiled.test.lowered.correct 0 _ hc locals #v[] tail
    obtain ⟨zero,result⟩ := List.cons.inj (Option.some.inj (tested.symm.trans expected))
    exact ⟨0,(by intro j bound; omega),zero.symm,result⟩
  | @loopMore actualCondition actualBody input middle next output w tested nonzero body rest ihBody ihRest =>
    intro same locals tail represented
    obtain ⟨rfl,rfl⟩ := Backend.Block.loop.inj same
    subst input
    have expected : Scalar.run actualCondition (locals.toList ++ tail) = some (compiled.test.value locals :: (locals.toList ++ tail)) := by
      simpa only [Vector.toList_empty,List.nil_append] using compiled.test.lowered.correct 0 _ hc locals #v[] tail
    obtain ⟨wordSame,middleSame⟩ := List.cons.inj (Option.some.inj (tested.symm.trans expected))
    subst w
    subst middle
    have expectedBody := StructuredExec.seq
      (compiled.inside.structured bodyBlock hb locals tail)
      (compiled.after.structured postBlock hp (compiled.inside.update locals) tail)
    have nextSame := StructuredUnique.output_unique body expectedBody
    subst next
    obtain ⟨count,running,stopped,result⟩ := ihRest rfl (ScopedFor.update compiled locals) tail rfl
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
theorem loop_complete (cc : Backend.Program) (postBlock bodyBlock : Backend.Block)
    (hc : compiled.test.lowered.code 0 = some cc)
    (hp : compiled.after.emit = some postBlock) (hb : compiled.inside.emit = some bodyBlock)
    (locals : Vector Scalar.Word n) (tail output : Stack)
    (executed : StructuredExec (.loop cc (.seq bodyBlock postBlock))
      (locals.toList ++ tail) output) :
    ∃ count,
      (∀ j, j < count → compiled.test.value (Nat.repeat (ScopedFor.update compiled) j locals) ≠ 0) ∧
      compiled.test.value (Nat.repeat (ScopedFor.update compiled) count locals) = 0 ∧
      output = (Nat.repeat (ScopedFor.update compiled) count locals).toList ++ tail :=
  loopAux compiled cc postBlock bodyBlock hc hp hb _ _ _ executed rfl locals tail rfl


/-- Invert the actual emitted prelude/loop, obtaining a genuine original-source
horizon. The compiler fuel bound is explicit; no source run/count is assumed. -/
theorem source_of_structured (packet : ScopedFor.Packet compiled)
    (base : Nat) (bounded : compilerFuel ≤ base)
    (locals : Vector Scalar.Word n) (caller output : Stack)
    (executed : StructuredExec packet.block (locals.toList ++ caller) output) :
    ∃ count,
      evalStmt (base+(count+2)) .nil True.intro (.for_ (c := c) pre condition post body)
        (ScopedFor.profile compiled) (sourceLocals locals) =
        some ⟨sourceLocals (Nat.repeat (ScopedFor.update compiled) count (compiled.before.update locals)),.normal⟩ ∧
      output = (Nat.repeat (ScopedFor.update compiled) count (compiled.before.update locals)).toList ++ caller := by
  have emitted := packet.emitted
  unfold ScopedFor.emit at emitted
  cases ha : compiled.before.emit with
  | none => simp only [ha] at emitted; cases emitted
  | some preBlock =>
    cases hc : compiled.test.lowered.code 0 with
    | none => simp only [ha,hc] at emitted; cases emitted
    | some cc =>
      cases hb : compiled.inside.emit with
      | none => simp only [ha,hc,hb] at emitted; cases emitted
      | some bodyBlock =>
        cases hp : compiled.after.emit with
        | none => simp only [ha,hc,hb,hp] at emitted; cases emitted
        | some postBlock =>
          simp only [ha,hc,hb,hp] at emitted
          have same : Backend.Block.seq preBlock (.loop cc (.seq bodyBlock postBlock)) = packet.block := Option.some.inj emitted
          rw [←same] at executed
          cases executed with
          | seq preRun loopRun =>
            have preSame := StructuredUnique.output_unique preRun
              (compiled.before.structured preBlock ha locals caller)
            subst preSame
            obtain ⟨count,running,stopped,result⟩ := loop_complete compiled cc postBlock bodyBlock
              hc hp hb (compiled.before.update locals) caller output loopRun
            exact ⟨count,ScopedFor.source compiled base count bounded locals running stopped,result⟩

/-- Successful selected mathematical execution reflects to original source and
exact raw output/frame with pending zero. No native/capacity/G24 assertion. -/
theorem source_of_model (packet : ScopedFor.Packet compiled)
    (base : Nat) (bounded : compilerFuel ≤ base)
    (locals : Vector Scalar.Word n) (caller : Stack)
    (m actual : Evm.Machine) (pending : Nat)
    (represented : m.stack = irStack (locals.toList ++ caller))
    (ran : Evm.run packet.selected.realization.ir m = .ok actual pending) :
    ∃ count,
      evalStmt (base+(count+2)) .nil True.intro (.for_ (c := c) pre condition post body)
        (ScopedFor.profile compiled) (sourceLocals locals) =
        some ⟨sourceLocals (Nat.repeat (ScopedFor.update compiled) count (compiled.before.update locals)),.normal⟩ ∧
      actual = {m with stack := irStack ((Nat.repeat (ScopedFor.update compiled) count (compiled.before.update locals)).toList ++ caller)} ∧
      pending = 0 := by
  rcases packet.selected.classified (locals.toList ++ caller) m represented with
    fault | ⟨output,executed,completed⟩
  · rw [fault] at ran
    cases ran
  · obtain ⟨count,source,result⟩ := source_of_structured compiled packet base bounded locals caller output executed
    have same := Evm.Out.ok.inj (ran.symm.trans completed)
    rw [result] at same
    exact ⟨count,source,same.1,same.2⟩
end
/-- info: 'SolidityBridge.Yul.ScopedForReflection.loop_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms loop_complete
/-- info: 'SolidityBridge.Yul.ScopedForReflection.source_of_structured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_of_structured
/-- info: 'SolidityBridge.Yul.ScopedForReflection.source_of_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_of_model
end SolidityBridge.Yul.ScopedForReflection
