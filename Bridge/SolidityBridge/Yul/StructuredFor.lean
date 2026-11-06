import SolidityBridge.Yul.ForSource
import SolidityBridge.Yul.StructuredSource

/-! Original FOR components compiled by the existing branch/sequence-aware
normal-control compiler. No new source AST or target block semantics. Finite
guards and component horizons remain explicit; early flow/divergence, logical
Solidity Source/G24, native and capacity adequacy remain separate. -/
namespace SolidityBridge.Yul.StructuredFor
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

theorem source_loop (base count : Nat) (hc : cf ≤ base) (hp : pf ≤ base) (hb : bf ≤ base)
    (locals : Vector Scalar.Word n)
    (running : ∀ j, j < count → test.value (Nat.repeat (fun l => after.update (inside.update l)) j locals) ≠ 0)
    (stopped : test.value (Nat.repeat (fun l => after.update (inside.update l)) count locals) = 0) :
    evalLoop (base+(count+1)) (c := c) .nil True.intro condition test.profile
      post after.profile body inside.profile (sourceLocals locals) =
      some ⟨sourceLocals (Nat.repeat (fun l => after.update (inside.update l)) count locals),.normal⟩ := by
  exact ForSource.source_loop (c := c) test after.profile after.update after.source
    inside.profile inside.update inside.source base count hc hp hb locals running stopped

/-- Finite target loop over real branch-bearing component emissions. -/
theorem loop_structured (depth : Nat) (cc : Backend.Program) (postBlock bodyBlock : Backend.Block)
    (hc : test.lowered.code depth = some cc)
    (hp : after.emit depth = some postBlock) (hb : inside.emit depth = some bodyBlock)
    (count : Nat) (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth) (tail : Stack)
    (running : ∀ j, j < count → test.value (Nat.repeat (fun l => after.update (inside.update l)) j locals) ≠ 0)
    (stopped : test.value (Nat.repeat (fun l => after.update (inside.update l)) count locals) = 0) :
    StructuredExec (.loop cc (.seq bodyBlock postBlock)) (newer.toList ++ (locals.toList ++ tail))
      (newer.toList ++ ((Nat.repeat (fun l => after.update (inside.update l)) count locals).toList ++ tail)) := by
  induction count generalizing locals with
  | zero =>
    change test.value locals = 0 at stopped
    apply StructuredExec.loopDone
    simpa only [stopped] using test.lowered.correct depth cc hc locals newer tail
  | succ count ih =>
    have nonzero : test.value locals ≠ 0 := running 0 (by omega)
    have bodyRun := StructuredSource.structured inside depth bodyBlock hb locals newer tail
    have postRun := StructuredSource.structured after depth postBlock hp (inside.update locals) newer tail
    have restRunning : ∀ j, j < count → test.value
        (Nat.repeat (fun l => after.update (inside.update l)) j (after.update (inside.update locals))) ≠ 0 := by
      intro j bound
      rw [LoweredWhile.repeat_shift]
      exact running (j+1) (by omega)
    have restStopped : test.value (Nat.repeat (fun l => after.update (inside.update l)) count
        (after.update (inside.update locals))) = 0 := by
      rw [LoweredWhile.repeat_shift]
      exact stopped
    have rest := ih (after.update (inside.update locals)) restRunning restStopped
    rw [LoweredWhile.repeat_shift] at rest
    exact StructuredExec.loopMore (test.lowered.correct depth cc hc locals newer tail)
      nonzero (StructuredExec.seq bodyRun postRun) rest

variable {af : Nat} {pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  (before : NormalControl.Derivation af pre)

def profile : StmtWordP (Solidity.Yul.Stmt.for_ (c := c) pre condition post body) :=
  ⟨before.profile,test.profile,after.profile,inside.profile⟩

/-- Original order and the actual existing target Block constructors. -/
def emit (depth : Nat) : Option Backend.Block := do
  let preBlock ← before.emit depth
  let cc ← test.lowered.code depth
  let bodyBlock ← inside.emit depth
  let postBlock ← after.emit depth
  pure (.seq preBlock (.loop cc (.seq bodyBlock postBlock)))

theorem source (base count : Nat) (ha : af ≤ base) (hc : cf ≤ base)
    (hp : pf ≤ base) (hb : bf ≤ base) (locals : Vector Scalar.Word n)
    (running : ∀ j, j < count → test.value (Nat.repeat (fun l => after.update (inside.update l))
      j (before.update locals)) ≠ 0)
    (stopped : test.value (Nat.repeat (fun l => after.update (inside.update l))
      count (before.update locals)) = 0) :
    evalStmt (base+(count+2)) .nil True.intro (.for_ (c := c) pre condition post body)
      (profile test after inside before) (sourceLocals locals) =
      some ⟨sourceLocals (Nat.repeat (fun l => after.update (inside.update l))
        count (before.update locals)),.normal⟩ := by
  have preRun := evalStmt_stable (show af ≤ base+(count+1) by omega) .nil True.intro
    pre before.profile (sourceLocals locals) (before.source locals)
  change (evalStmt (base+(count+1)) .nil True.intro pre before.profile (sourceLocals locals)).bind _ = _
  rw [preRun]
  change evalLoop (base+(count+1)) .nil True.intro condition test.profile post after.profile
    body inside.profile (sourceLocals (before.update locals)) = _
  exact source_loop test after inside base count hc hp hb (before.update locals) running stopped

theorem structured (depth : Nat) (block : Backend.Block)
    (emitted : emit test after inside before depth = some block)
    (count : Nat) (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth) (tail : Stack)
    (running : ∀ j, j < count → test.value (Nat.repeat (fun l => after.update (inside.update l))
      j (before.update locals)) ≠ 0)
    (stopped : test.value (Nat.repeat (fun l => after.update (inside.update l))
      count (before.update locals)) = 0) :
    StructuredExec block (newer.toList ++ (locals.toList ++ tail))
      (newer.toList ++ ((Nat.repeat (fun l => after.update (inside.update l))
        count (before.update locals)).toList ++ tail)) := by
  unfold emit at emitted
  cases ha : before.emit depth with
  | none => simp only [ha] at emitted; cases emitted
  | some preBlock =>
    cases hc : test.lowered.code depth with
    | none => simp only [ha,hc] at emitted; cases emitted
    | some cc =>
      cases hb : inside.emit depth with
      | none => simp only [ha,hc,hb] at emitted; cases emitted
      | some bodyBlock =>
        cases hp : after.emit depth with
        | none => simp only [ha,hc,hb,hp] at emitted; cases emitted
        | some postBlock =>
          simp only [ha,hc,hb,hp] at emitted
          have same : Backend.Block.seq preBlock (.loop cc (.seq bodyBlock postBlock)) = block :=
            Option.some.inj emitted
          subst block
          exact StructuredExec.seq (StructuredSource.structured before depth preBlock ha locals newer tail)
            (loop_structured test after inside depth cc postBlock bodyBlock hc hp hb count
              (before.update locals) newer tail running stopped)

theorem model (depth : Nat) (block : Backend.Block)
    (emitted : emit test after inside before depth = some block)
    (selected : OccurrenceControl.Selected block)
    (count : Nat) (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth) (tail : Stack)
    (running : ∀ j, j < count → test.value (Nat.repeat (fun l => after.update (inside.update l))
      j (before.update locals)) ≠ 0)
    (stopped : test.value (Nat.repeat (fun l => after.update (inside.update l))
      count (before.update locals)) = 0)
    (m : Evm.Machine) (represented : m.stack = irStack (newer.toList ++ (locals.toList ++ tail))) :
    Evm.run selected.realization.ir m = .ok {m with stack := irStack (newer.toList ++
      ((Nat.repeat (fun l => after.update (inside.update l)) count (before.update locals)).toList ++ tail))} 0 :=
  selected.realization.execute _ _ m represented
    (structured test after inside before depth block emitted count locals newer tail running stopped)
end

/-- Actual compiler output indexed by original FOR components, including
branch-bearing normal components. It is not another source syntax. -/
structure Prepared (fuel : Nat) {c : Solidity.Yul.Control} {n : Nat}
    (pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n)
    (condition : Solidity.Yul.Expr [] [] n 1)
    (post : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n)
    (body : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n) where
  before : NormalControl.Derivation fuel pre
  test : ProducerExpressions.Compiled fuel condition
  after : NormalControl.Derivation fuel post
  inside : NormalControl.Derivation fuel body

def prepare (fuel : Nat) {c : Solidity.Yul.Control} {n : Nat}
    (pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n)
    (condition : Solidity.Yul.Expr [] [] n 1)
    (post : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n)
    (body : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n) :
    Option (Prepared fuel (c := c) pre condition post body) := do
  let before ← NormalControl.compile fuel pre
  let test ← PureExpressions.compile fuel condition
  let after ← NormalControl.compile fuel post
  let inside ← NormalControl.compile fuel body
  pure ⟨before,test,after,inside⟩

/-- info: 'SolidityBridge.Yul.StructuredFor.source_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_loop
/-- info: 'SolidityBridge.Yul.StructuredFor.source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source
/-- info: 'SolidityBridge.Yul.StructuredFor.loop_structured' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms loop_structured
/-- info: 'SolidityBridge.Yul.StructuredFor.structured' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms structured
/-- info: 'SolidityBridge.Yul.StructuredFor.model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model
/-- info: 'SolidityBridge.Yul.StructuredFor.prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepare
end SolidityBridge.Yul.StructuredFor
