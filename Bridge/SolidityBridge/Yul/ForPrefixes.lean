import SolidityBridge.Yul.StructuredFor
import SolidityBridge.Yul.StructuredSource

/-! All-horizon source noncompletion and exact finite mathematical macro-turn
transport for actual compiled FOR components. These are not fetched/native
instruction prefixes or exceptional-halt correspondence. -/
namespace SolidityBridge.Yul.ForPrefixes
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


theorem source_loop_never (locals : Vector Scalar.Word n)
    (forever : ∀ j, test.value (Nat.repeat (fun l => after.update (inside.update l)) j locals) ≠ 0)
    (fuel : Nat) :
    evalLoop fuel (c := c) .nil True.intro condition test.profile post after.profile
      body inside.profile (sourceLocals locals) = none := by
  induction fuel generalizing locals with
  | zero => rfl
  | succ fuel ih =>
    rw [evalLoop]
    cases tested : evalExpr fuel .nil True.intro condition test.profile (sourceLocals locals) with
    | none => rfl
    | some values =>
      have same := evalExpr_completed_unique .nil True.intro condition test.profile
        (sourceLocals locals) tested (test.source locals)
      subst values
      change (if (test.value locals).toNat = 0 then _ else _) = none
      have nonzero : (test.value locals).toNat ≠ 0 := by
        intro zero
        exact forever 0 (BitVec.eq_of_toNat_eq zero)
      rw [if_neg nonzero]
      change (evalStmt fuel .nil True.intro body inside.profile (sourceLocals locals)).bind _ = none
      cases bodyRun : evalStmt fuel .nil True.intro body inside.profile (sourceLocals locals) with
      | none => rfl
      | some outcome =>
        have same := evalStmt_completed_unique .nil True.intro body inside.profile
          (sourceLocals locals) bodyRun (inside.source locals)
        subst outcome
        change (evalStmt fuel .nil True.intro post after.profile
          (sourceLocals (inside.update locals))).bind _ = none
        cases postRun : evalStmt fuel .nil True.intro post after.profile
            (sourceLocals (inside.update locals)) with
        | none => rfl
        | some outcome =>
          have same := evalStmt_completed_unique .nil True.intro post after.profile
            (sourceLocals (inside.update locals)) postRun (after.source (inside.update locals))
          subst outcome
          change evalLoop fuel .nil True.intro condition test.profile post after.profile
            body inside.profile (sourceLocals (after.update (inside.update locals))) = none
          apply ih
          intro j
          rw [LoweredWhile.repeat_shift]
          exact forever (j+1)

theorem macro_prefix (depth : Nat) (cc : Backend.Program) (postBlock bodyBlock : Backend.Block)
    (hc : test.lowered.code depth = some cc)
    (hp : after.emit depth = some postBlock) (hb : inside.emit depth = some bodyBlock)
    (condSlice : OccurrenceSelection.Slice cc)
    (bodyReal : ControlRealization.Realization (.seq bodyBlock postBlock))
    (count : Nat) (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth) (tail : Stack)
    (running : ∀ j, j < count → test.value (Nat.repeat (fun l => after.update (inside.update l)) j locals) ≠ 0)
    (m : Evm.Machine) (represented : m.stack = irStack (newer.toList ++ (locals.toList ++ tail))) :
    Evm.loopIterN (Evm.run condSlice.ir) (Evm.run bodyReal.ir) count m =
      .inl {m with stack := irStack (newer.toList ++
        ((Nat.repeat (fun l => after.update (inside.update l)) count locals).toList ++ tail))} := by
  induction count generalizing locals m with
  | zero =>
    change (Sum.inl m : Evm.Machine ⊕ Evm.Out) =
      .inl {m with stack := irStack (newer.toList ++ (locals.toList ++ tail))}
    rw [←represented]
  | succ count ih =>
    have nonzero : test.value locals ≠ 0 := running 0 (by omega)
    have bodyRun := StructuredExec.seq
      (StructuredSource.structured inside depth bodyBlock hb locals newer tail)
      (StructuredSource.structured after depth postBlock hp (inside.update locals) newer tail)
    have turn := LoopRealization.turn_more cc (.seq bodyBlock postBlock) condSlice bodyReal
      (newer.toList ++ (locals.toList ++ tail)) (newer.toList ++ (locals.toList ++ tail))
      (newer.toList ++ ((after.update (inside.update locals)).toList ++ tail))
      (test.value locals) m represented (test.lowered.correct depth cc hc locals newer tail) nonzero bodyRun
    rw [Evm.loopIterN,turn]
    have restRunning : ∀ j, j < count → test.value (Nat.repeat (fun l => after.update (inside.update l))
        j (after.update (inside.update locals))) ≠ 0 := by
      intro j bound
      rw [LoweredWhile.repeat_shift]
      exact running (j+1) (by omega)
    have rest := ih (after.update (inside.update locals)) restRunning
      {m with stack := irStack (newer.toList ++ ((after.update (inside.update locals)).toList ++ tail))} rfl
    rw [LoweredWhile.repeat_shift] at rest
    exact rest

/-- The existing model denotes a loop with no finite outcome by fault.
This is NOT an exceptional native halt, nor a source panic/revert theorem. -/
theorem model_loop_no_finite_outcome (depth : Nat) (cc : Backend.Program) (postBlock bodyBlock : Backend.Block)
    (hc : test.lowered.code depth = some cc)
    (hp : after.emit depth = some postBlock) (hb : inside.emit depth = some bodyBlock)
    (condSlice : OccurrenceSelection.Slice cc)
    (bodyReal : ControlRealization.Realization (.seq bodyBlock postBlock))
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth) (tail : Stack)
    (forever : ∀ j, test.value (Nat.repeat (fun l => after.update (inside.update l)) j locals) ≠ 0)
    (m : Evm.Machine) (represented : m.stack = irStack (newer.toList ++ (locals.toList ++ tail))) :
    Evm.loopRun (Evm.run condSlice.ir) (Evm.run bodyReal.ir) m = .fault := by
  apply Evm.loopRun_of_forall
  intro count
  exact ⟨_,macro_prefix test after inside depth cc postBlock bodyBlock hc hp hb condSlice bodyReal
    count locals newer tail (fun j _ => forever j) m represented⟩

variable {af : Nat} {pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  (before : NormalControl.Derivation af pre)

/-- Every original FOR source horizon fails to finish, not just a tested cutoff.
Normal compiler facts and completed-run uniqueness rule out spurious early flow. -/
theorem source_never (locals : Vector Scalar.Word n)
    (forever : ∀ j, test.value (Nat.repeat (fun l => after.update (inside.update l))
      j (before.update locals)) ≠ 0) (fuel : Nat) :
    evalStmt fuel .nil True.intro (.for_ (c := c) pre condition post body)
      (StructuredFor.profile test after inside before) (sourceLocals locals) = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    change (evalStmt fuel .nil True.intro pre before.profile (sourceLocals locals)).bind _ = none
    cases preRun : evalStmt fuel .nil True.intro pre before.profile (sourceLocals locals) with
    | none => rfl
    | some outcome =>
      have same := evalStmt_completed_unique .nil True.intro pre before.profile
        (sourceLocals locals) preRun (before.source locals)
      subst outcome
      exact source_loop_never test after inside (before.update locals) forever fuel

/-- info: 'SolidityBridge.Yul.ForPrefixes.source_loop_never' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_loop_never
/-- info: 'SolidityBridge.Yul.ForPrefixes.source_never' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_never
/-- info: 'SolidityBridge.Yul.ForPrefixes.macro_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms macro_prefix
/-- info: 'SolidityBridge.Yul.ForPrefixes.model_loop_no_finite_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_loop_no_finite_outcome
end
end SolidityBridge.Yul.ForPrefixes
