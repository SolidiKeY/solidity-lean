import SolidityBridge.Yul.ForSource
import SolidityBridge.Yul.NestedSwitch
import SolidityBridge.Yul.LoopSelection

/-! FOR lowering using the actual scope/switch-aware component compiler.
Original AST, profiles, source evaluator and target blocks are unchanged.
This is a depth-zero local frame with arbitrary caller suffix; frontend
admission, early flow, native capacity and logical Source/G24 remain open. -/
namespace SolidityBridge.Yul.ScopedFor
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed Solidity.Yul.Compilation ProducerExpressions

structure Prepared (fuel : Nat) {c : Solidity.Yul.Control} {n : Nat}
    (pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n)
    (condition : Solidity.Yul.Expr [] [] n 1)
    (post : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n)
    (body : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n) where
  before : NestedSwitch.Compiled fuel pre
  test : ProducerExpressions.Compiled fuel condition
  after : NestedSwitch.Compiled fuel post
  inside : NestedSwitch.Compiled fuel body

def prepare (fuel : Nat) {c : Solidity.Yul.Control} {n : Nat}
    (pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n)
    (condition : Solidity.Yul.Expr [] [] n 1)
    (post : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n)
    (body : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n) :
    Option (Prepared fuel (c := c) pre condition post body) := do
  let before ← NestedSwitch.compile fuel pre
  let test ← PureExpressions.compile fuel condition
  let after ← NestedSwitch.compile fuel post
  let inside ← NestedSwitch.compile fuel body
  pure ⟨before,test,after,inside⟩

section
variable {c : Solidity.Yul.Control} {n fuel : Nat}
  {pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  {condition : Solidity.Yul.Expr [] [] n 1}
  {post : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  {body : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n}
  (compiled : Prepared fuel (c := c) pre condition post body)

def profile : StmtWordP (.for_ (c := c) pre condition post body) :=
  ⟨compiled.before.profile,compiled.test.profile,compiled.after.profile,compiled.inside.profile⟩

def update (locals : Vector Scalar.Word n) : Vector Scalar.Word n :=
  compiled.after.update (compiled.inside.update locals)

def emit : Option Backend.Block := do
  let preBlock ← compiled.before.emit
  let cc ← compiled.test.lowered.code 0
  let bodyBlock ← compiled.inside.emit
  let postBlock ← compiled.after.emit
  pure (.seq preBlock (.loop cc (.seq bodyBlock postBlock)))

structure Packet where
  block : Backend.Block
  emitted : emit compiled = some block
  selected : OccurrenceControl.Selected block

def select : Option (Packet compiled) := do
  match emitted : emit compiled with
  | none => none
  | some block => do
    let selected ← LoopSelection.selectBlock block
    pure ⟨block,emitted,selected⟩

theorem source (base count : Nat) (bounded : fuel ≤ base) (locals : Vector Scalar.Word n)
    (running : ∀ j, j < count → compiled.test.value
      (Nat.repeat (update compiled) j (compiled.before.update locals)) ≠ 0)
    (stopped : compiled.test.value (Nat.repeat (update compiled) count (compiled.before.update locals)) = 0) :
    evalStmt (base+(count+2)) .nil True.intro (.for_ (c := c) pre condition post body)
      (profile compiled) (sourceLocals locals) =
      some ⟨sourceLocals (Nat.repeat (update compiled) count (compiled.before.update locals)),.normal⟩ := by
  have preRun := evalStmt_stable (show fuel ≤ base+(count+1) by omega) .nil True.intro
    pre compiled.before.profile (sourceLocals locals) (compiled.before.source locals)
  change (evalStmt (base+(count+1)) .nil True.intro pre compiled.before.profile
    (sourceLocals locals)).bind _ = _
  rw [preRun]
  change evalLoop (base+(count+1)) .nil True.intro condition compiled.test.profile post compiled.after.profile
    body compiled.inside.profile (sourceLocals (compiled.before.update locals)) = _
  exact ForSource.source_loop (c := c) compiled.test compiled.after.profile compiled.after.update compiled.after.source
    compiled.inside.profile compiled.inside.update compiled.inside.source base count bounded bounded bounded
    (compiled.before.update locals) running stopped

/-- Actual scope/switch component emissions discharge both body and post runs. -/
theorem loop_structured (cc : Backend.Program) (postBlock bodyBlock : Backend.Block)
    (hc : compiled.test.lowered.code 0 = some cc)
    (hp : compiled.after.emit = some postBlock) (hb : compiled.inside.emit = some bodyBlock)
    (count : Nat) (locals : Vector Scalar.Word n) (caller : Stack)
    (running : ∀ j, j < count → compiled.test.value (Nat.repeat (update compiled) j locals) ≠ 0)
    (stopped : compiled.test.value (Nat.repeat (update compiled) count locals) = 0) :
    StructuredExec (.loop cc (.seq bodyBlock postBlock)) (locals.toList ++ caller)
      ((Nat.repeat (update compiled) count locals).toList ++ caller) := by
  have conditionRun (locals : Vector Scalar.Word n) : Scalar.run cc (locals.toList ++ caller) =
      some (compiled.test.value locals :: (locals.toList ++ caller)) := by
    simpa only [Vector.toList_empty,List.nil_append] using
      compiled.test.lowered.correct 0 cc hc locals #v[] caller
  induction count generalizing locals with
  | zero =>
    change compiled.test.value locals = 0 at stopped
    apply StructuredExec.loopDone
    simpa only [stopped] using conditionRun locals
  | succ count ih =>
    have nonzero : compiled.test.value locals ≠ 0 := running 0 (by omega)
    have actualBody := StructuredExec.seq
      (compiled.inside.structured bodyBlock hb locals caller)
      (compiled.after.structured postBlock hp (compiled.inside.update locals) caller)
    have restRunning : ∀ j, j < count → compiled.test.value
        (Nat.repeat (update compiled) j (update compiled locals)) ≠ 0 := by
      intro j bound
      rw [LoweredWhile.repeat_shift]
      exact running (j+1) (by omega)
    have restStopped : compiled.test.value (Nat.repeat (update compiled) count (update compiled locals)) = 0 := by
      rw [LoweredWhile.repeat_shift]
      exact stopped
    have rest := ih (update compiled locals) restRunning restStopped
    rw [LoweredWhile.repeat_shift] at rest
    exact StructuredExec.loopMore (conditionRun locals) nonzero actualBody rest

theorem structured (block : Backend.Block) (emitted : emit compiled = some block)
    (count : Nat) (locals : Vector Scalar.Word n) (caller : Stack)
    (running : ∀ j, j < count → compiled.test.value
      (Nat.repeat (update compiled) j (compiled.before.update locals)) ≠ 0)
    (stopped : compiled.test.value (Nat.repeat (update compiled) count (compiled.before.update locals)) = 0) :
    StructuredExec block (locals.toList ++ caller)
      ((Nat.repeat (update compiled) count (compiled.before.update locals)).toList ++ caller) := by
  unfold emit at emitted
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
          have same : Backend.Block.seq preBlock (.loop cc (.seq bodyBlock postBlock)) = block := Option.some.inj emitted
          subst block
          exact StructuredExec.seq (compiled.before.structured preBlock ha locals caller)
            (loop_structured compiled cc postBlock bodyBlock hc hp hb count
              (compiled.before.update locals) caller running stopped)

theorem Packet.model (packet : Packet compiled) (count : Nat) (locals : Vector Scalar.Word n) (caller : Stack)
    (running : ∀ j, j < count → compiled.test.value
      (Nat.repeat (update compiled) j (compiled.before.update locals)) ≠ 0)
    (stopped : compiled.test.value (Nat.repeat (update compiled) count (compiled.before.update locals)) = 0)
    (m : Evm.Machine) (represented : m.stack = irStack (locals.toList ++ caller)) :
    Evm.run packet.selected.realization.ir m =
      .ok {m with stack := irStack ((Nat.repeat (update compiled) count
        (compiled.before.update locals)).toList ++ caller)} 0 :=
  packet.selected.realization.execute _ _ m represented
    (structured compiled packet.block packet.emitted count locals caller running stopped)

end

/-- Actual component compilation, emission and opcode selection, not a supplied
simulation interface. Refused forms/depths stay refused. -/
def compile (fuel : Nat) {c : Solidity.Yul.Control} {n : Nat}
    (pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n)
    (condition : Solidity.Yul.Expr [] [] n 1)
    (post : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n)
    (body : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n) :
    Option (Σ prepared : Prepared fuel (c := c) pre condition post body, Packet prepared) := do
  let prepared ← prepare fuel pre condition post body
  let packet ← select prepared
  pure ⟨prepared,packet⟩

/-- info: 'SolidityBridge.Yul.ScopedFor.prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepare
/-- info: 'SolidityBridge.Yul.ScopedFor.emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms emit
/-- info: 'SolidityBridge.Yul.ScopedFor.select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms select
/-- info: 'SolidityBridge.Yul.ScopedFor.source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source
/-- info: 'SolidityBridge.Yul.ScopedFor.loop_structured' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms loop_structured
/-- info: 'SolidityBridge.Yul.ScopedFor.structured' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms structured
/-- info: 'SolidityBridge.Yul.ScopedFor.Packet.model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Packet.model
/-- info: 'SolidityBridge.Yul.ScopedFor.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile
end SolidityBridge.Yul.ScopedFor
