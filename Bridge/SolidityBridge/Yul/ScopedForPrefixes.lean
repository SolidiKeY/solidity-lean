import SolidityBridge.Yul.ScopedFor

/-! Exact finite model macro-turn prefixes for actual scoped/switch FOR
components. No native instruction-prefix, gas, capacity or G24 claim. -/
namespace SolidityBridge.Yul.ScopedForPrefixes
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed Solidity.Yul.Compilation ProducerExpressions
section
variable {c : Solidity.Yul.Control} {n compilerFuel : Nat}
  {pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  {condition : Solidity.Yul.Expr [] [] n 1}
  {post : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  {body : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n}
  (compiled : ScopedFor.Prepared compilerFuel (c := c) pre condition post body)

/-- Actual emitted condition/body/post certificates derive every finite turn.
The input locals are at loop entry, after any separately executed prelude. -/
theorem macro_prefix (cc : Backend.Program) (postBlock bodyBlock : Backend.Block)
    (hc : compiled.test.lowered.code 0 = some cc)
    (hp : compiled.after.emit = some postBlock) (hb : compiled.inside.emit = some bodyBlock)
    (condSlice : OccurrenceSelection.Slice cc)
    (bodyReal : ControlRealization.Realization (.seq bodyBlock postBlock))
    (count : Nat) (locals : Vector Scalar.Word n) (caller : Stack)
    (running : ∀ j, j < count → compiled.test.value (Nat.repeat (ScopedFor.update compiled) j locals) ≠ 0)
    (m : Evm.Machine) (represented : m.stack = irStack (locals.toList ++ caller)) :
    Evm.loopIterN (Evm.run condSlice.ir) (Evm.run bodyReal.ir) count m =
      .inl {m with stack := irStack ((Nat.repeat (ScopedFor.update compiled) count locals).toList ++ caller)} := by
  induction count generalizing locals m with
  | zero =>
    change (Sum.inl m : Evm.Machine ⊕ Evm.Out) = .inl {m with stack := irStack (locals.toList ++ caller)}
    rw [←represented]
  | succ count ih =>
    have nonzero : compiled.test.value locals ≠ 0 := running 0 (by omega)
    have conditionRun : Scalar.run cc (locals.toList ++ caller) =
        some (compiled.test.value locals :: (locals.toList ++ caller)) := by
      simpa only [Vector.toList_empty,List.nil_append] using
        compiled.test.lowered.correct 0 cc hc locals #v[] caller
    have bodyRun := StructuredExec.seq
      (compiled.inside.structured bodyBlock hb locals caller)
      (compiled.after.structured postBlock hp (compiled.inside.update locals) caller)
    have turn := LoopRealization.turn_more cc (.seq bodyBlock postBlock) condSlice bodyReal
      (locals.toList ++ caller) (locals.toList ++ caller)
      ((ScopedFor.update compiled locals).toList ++ caller) (compiled.test.value locals)
      m represented conditionRun nonzero bodyRun
    rw [Evm.loopIterN,turn]
    have restRunning : ∀ j, j < count → compiled.test.value
        (Nat.repeat (ScopedFor.update compiled) j (ScopedFor.update compiled locals)) ≠ 0 := by
      intro j bound
      rw [LoweredWhile.repeat_shift]
      exact running (j+1) (by omega)
    have rest := ih (ScopedFor.update compiled locals) restRunning
      {m with stack := irStack ((ScopedFor.update compiled locals).toList ++ caller)} rfl
    rw [LoweredWhile.repeat_shift] at rest
    exact rest

/-- The existing loop model denotes an unending sequence of genuine finite
macro-turns by fault; this is not native exceptional-halt correspondence. -/
theorem loop_no_finite_outcome (cc : Backend.Program) (postBlock bodyBlock : Backend.Block)
    (hc : compiled.test.lowered.code 0 = some cc)
    (hp : compiled.after.emit = some postBlock) (hb : compiled.inside.emit = some bodyBlock)
    (condSlice : OccurrenceSelection.Slice cc)
    (bodyReal : ControlRealization.Realization (.seq bodyBlock postBlock))
    (locals : Vector Scalar.Word n) (caller : Stack)
    (forever : ∀ j, compiled.test.value (Nat.repeat (ScopedFor.update compiled) j locals) ≠ 0)
    (m : Evm.Machine) (represented : m.stack = irStack (locals.toList ++ caller)) :
    Evm.loopRun (Evm.run condSlice.ir) (Evm.run bodyReal.ir) m = .fault := by
  apply Evm.loopRun_of_forall
  intro count
  exact ⟨_,macro_prefix compiled cc postBlock bodyBlock hc hp hb condSlice bodyReal
    count locals caller (fun j _ => forever j) m represented⟩
end
/-- info: 'SolidityBridge.Yul.ScopedForPrefixes.macro_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms macro_prefix
/-- info: 'SolidityBridge.Yul.ScopedForPrefixes.loop_no_finite_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_no_finite_outcome
end SolidityBridge.Yul.ScopedForPrefixes
