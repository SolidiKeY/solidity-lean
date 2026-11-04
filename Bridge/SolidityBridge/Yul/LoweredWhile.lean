import Solidity.Yul.Compilation.ControlLowering
import SolidityBridge.Yul.LoopSelection

/-! Finite execution for the existing `lowerWhile` emitter. The exact emitted
condition/body are recovered and their existing run laws are applied. Guard
hypotheses describe an actual finite exit, not source termination, divergence,
capacity, gas or native execution. No new AST, state or loop evaluator. -/
namespace SolidityBridge.Yul.LoweredWhile
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation

private theorem repeat_shift {α : Type} (f : α → α) (count : Nat) (a : α) :
    Nat.repeat f count (f a) = Nat.repeat f (count+1) a := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg f ih

/-- Successful emission determines the actual two scalar programs. -/
theorem parts {n : Nat} {condition : Vector Word n → Word}
    {update : Vector Word n → Vector Word n}
    (c : LoweredExpr n condition) (b : LoweredStmt n update)
    (depth : Nat) (block : Backend.Block)
    (emitted : lowerWhile c b depth = some block) :
    ∃ cc bb, c.code depth = some cc ∧ b.code depth = some bb ∧
      block = .loop cc (.code bb) := by
  unfold lowerWhile at emitted
  cases hc : c.code depth with
  | none => simp only [hc,Option.bind_none] at emitted; cases emitted
  | some cc =>
    cases hb : b.code depth with
    | none => simp only [hc,hb,Option.bind_some,Option.map_none] at emitted; cases emitted
    | some bb =>
      simp only [hc,hb,Option.bind_some,Option.map_some,Option.some.injEq] at emitted
      exact ⟨cc,bb,rfl,rfl,emitted.symm⟩

/-- Arbitrary finite exit, full words, identical newer prefix and caller tail.
The guard is tested BEFORE each body and once after the final body. -/
theorem slices {n : Nat} {condition : Vector Word n → Word}
    {update : Vector Word n → Vector Word n}
    (c : LoweredExpr n condition) (b : LoweredStmt n update)
    (depth : Nat) (cc bb : Backend.Program)
    (hc : c.code depth = some cc) (hb : b.code depth = some bb)
    (count : Nat) (locals : Vector Word n) (newer : Vector Word depth) (tail : Stack)
    (running : ∀ j, j < count → condition (Nat.repeat update j locals) ≠ 0)
    (stopped : condition (Nat.repeat update count locals) = 0) :
    StructuredExec (.loop cc (.code bb)) (newer.toList ++ (locals.toList ++ tail))
      (newer.toList ++ ((Nat.repeat update count locals).toList ++ tail)) := by
  induction count generalizing locals with
  | zero =>
    change condition locals = 0 at stopped
    apply StructuredExec.loopDone
    simpa only [stopped] using c.correct depth cc hc locals newer tail
  | succ count ih =>
    have nonzero : condition locals ≠ 0 := running 0 (by omega)
    have restRunning : ∀ j, j < count → condition (Nat.repeat update j (update locals)) ≠ 0 := by
      intro j bound
      rw [repeat_shift]
      exact running (j+1) (by omega)
    have restStopped : condition (Nat.repeat update count (update locals)) = 0 := by
      rw [repeat_shift]
      exact stopped
    have rest := ih (update locals) restRunning restStopped
    rw [repeat_shift] at rest
    exact StructuredExec.loopMore (c.correct depth cc hc locals newer tail) nonzero
      (StructuredExec.code (b.correct depth bb hb locals newer tail)) rest

/-- The finite-exit theorem for the actual emitter, not an assumed slice run. -/
theorem structured {n : Nat} {condition : Vector Word n → Word}
    {update : Vector Word n → Vector Word n}
    (c : LoweredExpr n condition) (b : LoweredStmt n update)
    (depth : Nat) (block : Backend.Block) (emitted : lowerWhile c b depth = some block)
    (count : Nat) (locals : Vector Word n) (newer : Vector Word depth) (tail : Stack)
    (running : ∀ j, j < count → condition (Nat.repeat update j locals) ≠ 0)
    (stopped : condition (Nat.repeat update count locals) = 0) :
    StructuredExec block (newer.toList ++ (locals.toList ++ tail))
      (newer.toList ++ ((Nat.repeat update count locals).toList ++ tail)) := by
  obtain ⟨cc,bb,hc,hb,rfl⟩ := parts c b depth block emitted
  exact slices c b depth cc bb hc hb count locals newer tail running stopped

/-- Any real selected realization transports that exit to the mathematical
machine. The represented-stack premise and selection are not native adequacy. -/
theorem model {n : Nat} {condition : Vector Word n → Word}
    {update : Vector Word n → Vector Word n}
    (c : LoweredExpr n condition) (b : LoweredStmt n update)
    (depth : Nat) (block : Backend.Block) (emitted : lowerWhile c b depth = some block)
    (selected : OccurrenceControl.Selected block)
    (count : Nat) (locals : Vector Word n) (newer : Vector Word depth) (tail : Stack)
    (running : ∀ j, j < count → condition (Nat.repeat update j locals) ≠ 0)
    (stopped : condition (Nat.repeat update count locals) = 0)
    (m : Evm.Machine) (represented : m.stack = irStack (newer.toList ++ (locals.toList ++ tail))) :
    Evm.run selected.realization.ir m =
      .ok {m with stack := irStack (newer.toList ++ ((Nat.repeat update count locals).toList ++ tail))} 0 :=
  selected.realization.execute _ _ m represented
    (structured c b depth block emitted count locals newer tail running stopped)

/-- info: 'SolidityBridge.Yul.LoweredWhile.parts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parts
/-- info: 'SolidityBridge.Yul.LoweredWhile.slices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms slices
/-- info: 'SolidityBridge.Yul.LoweredWhile.structured' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms structured
/-- info: 'SolidityBridge.Yul.LoweredWhile.model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model
end SolidityBridge.Yul.LoweredWhile
