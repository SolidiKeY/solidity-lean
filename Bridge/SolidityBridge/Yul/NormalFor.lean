import SolidityBridge.Yul.LoweredWhile
import Solidity.Yul.Compilation.PureStatements
import Solidity.Yul.ClosedHorizon
namespace SolidityBridge.Yul.NormalFor
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed
open Solidity.Yul.Compilation ProducerExpressions
section
variable {c : Solidity.Yul.Control} {n cf pf bf : Nat}
  {condition : Solidity.Yul.Expr [] [] n 1}
  {post : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  {body : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n}
  (test : ProducerExpressions.Compiled cf condition)
  (after : ProducerStatements.Compiled pf post)
  (inside : ProducerStatements.Compiled bf body)

/-! Normal-completing original Yul FOR components. All source statements and
horizons are the existing ones. Finite guard hypotheses are explicit; no
termination, early-control, native capacity or Source/G24 claim is introduced. -/

theorem source_loop (base count : Nat) (hc : cf ≤ base) (hp : pf ≤ base) (hb : bf ≤ base)
    (locals : Vector Scalar.Word n)
    (running : ∀ j, j < count → test.value (Nat.repeat (fun l => after.update (inside.update l)) j locals) ≠ 0)
    (stopped : test.value (Nat.repeat (fun l => after.update (inside.update l)) count locals) = 0) :
    evalLoop (base+(count+1)) (c := c) .nil True.intro condition test.profile
      post after.profile body inside.profile (sourceLocals locals) =
      some ⟨sourceLocals (Nat.repeat (fun l => after.update (inside.update l)) count locals),.normal⟩ := by
  induction count generalizing locals with
  | zero =>
    have testRun := evalExpr_stable hc .nil True.intro condition test.profile
      (sourceLocals locals) (test.source locals)
    change test.value locals = 0 at stopped
    rw [evalLoop,testRun]
    rw [stopped]
    rfl
  | succ count ih =>
    have testRun := evalExpr_stable (show cf ≤ base+(count+1) by omega) .nil True.intro
      condition test.profile (sourceLocals locals) (test.source locals)
    have bodyRun := evalStmt_stable (show bf ≤ base+(count+1) by omega) .nil True.intro
      body inside.profile (sourceLocals locals) (inside.source locals)
    have postRun := evalStmt_stable (show pf ≤ base+(count+1) by omega) .nil True.intro
      post after.profile (sourceLocals (inside.update locals)) (after.source (inside.update locals))
    have nonzero : (test.value locals).toNat ≠ 0 := by
      intro zero
      exact running 0 (by omega) (BitVec.eq_of_toNat_eq zero)
    rw [Nat.add_succ,evalLoop,testRun]
    change (if (test.value locals).toNat = 0 then _ else _) = _
    rw [if_neg nonzero]
    change (evalStmt (base+(count+1)) .nil True.intro body inside.profile
      (sourceLocals locals)).bind _ = _
    rw [bodyRun]
    change (evalStmt (base+(count+1)) .nil True.intro post after.profile
      (sourceLocals (inside.update locals))).bind _ = _
    rw [postRun]
    change evalLoop (base+(count+1)) .nil True.intro condition test.profile
      post after.profile body inside.profile (sourceLocals (after.update (inside.update locals))) = _
    have restRunning : ∀ j, j < count →
        test.value (Nat.repeat (fun l => after.update (inside.update l)) j
          (after.update (inside.update locals))) ≠ 0 := by
      intro j bound
      rw [LoweredWhile.repeat_shift]
      exact running (j+1) (by omega)
    have restStopped : test.value (Nat.repeat (fun l => after.update (inside.update l)) count
        (after.update (inside.update locals))) = 0 := by
      rw [LoweredWhile.repeat_shift]
      exact stopped
    have rest := ih (after.update (inside.update locals)) restRunning restStopped
    rw [LoweredWhile.repeat_shift] at rest
    exact rest

variable {af : Nat} {pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  (before : ProducerStatements.Compiled af pre)

def profile : StmtWordP (Solidity.Yul.Stmt.for_ (c := c) pre condition post body) :=
  ⟨before.profile,test.profile,after.profile,inside.profile⟩

/-- Prelude once, condition before body, post after body: the original FOR order. -/
def emit (depth : Nat) : Option Backend.Block := do
  let pp ← before.lowered.code depth
  let loop ← lowerWhile test.lowered (lowerSeq inside.lowered after.lowered) depth
  pure (.seq (.code pp) loop)

/-- Actual original FOR execution, including its prelude and child horizons.
The base bounds are lower bounds for already proved component horizons, not
new proof budgets or gas. Normal component certificates exclude early exits. -/
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

/-- Source-indexed component lowering produces an exact complete target run.
No source/target execution hypothesis is supplied by the caller. -/
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
  cases ha : before.lowered.code depth with
  | none => simp only [ha] at emitted; cases emitted
  | some pp =>
    cases hl : lowerWhile test.lowered (lowerSeq inside.lowered after.lowered) depth with
    | none => simp only [ha,hl] at emitted; cases emitted
    | some loop =>
      simp only [ha,hl] at emitted
      have same : Backend.Block.seq (.code pp) loop = block := Option.some.inj emitted
      subst block
      exact StructuredExec.seq (StructuredExec.code (before.lowered.correct depth pp ha locals newer tail))
        (LoweredWhile.structured test.lowered (lowerSeq inside.lowered after.lowered)
          depth loop hl count (before.update locals) newer tail running stopped)

/-- Concrete selected mathematical-machine execution for the same source update.
This is not charged/native/Source-session or G24 representation adequacy. -/
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

/-- Compiler output indexed by the original four FOR components. These are
actual producer certificates, not a replacement statement syntax. -/
structure Prepared (fuel : Nat) {c : Solidity.Yul.Control} {n : Nat}
    (pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n)
    (condition : Solidity.Yul.Expr [] [] n 1)
    (post : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n)
    (body : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n) where
  before : ProducerStatements.Compiled fuel pre
  test : ProducerExpressions.Compiled fuel condition
  after : ProducerStatements.Compiled fuel post
  inside : ProducerStatements.Compiled fuel body

/-- Run the actual pure component compilers; unsupported/early-flow components
refuse here, without changing source admission or frontend dispatch. -/
def prepare (fuel : Nat) {c : Solidity.Yul.Control} {n : Nat}
    (pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n)
    (condition : Solidity.Yul.Expr [] [] n 1)
    (post : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n)
    (body : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n) :
    Option (Prepared fuel (c := c) pre condition post body) := do
  let before ← PureStatements.compile fuel pre
  let test ← PureExpressions.compile fuel condition
  let after ← PureStatements.compile fuel post
  let inside ← PureStatements.compile fuel body
  pure ⟨before,test,after,inside⟩

/-- info: 'SolidityBridge.Yul.NormalFor.source_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_loop
/-- info: 'SolidityBridge.Yul.NormalFor.source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source
/-- info: 'SolidityBridge.Yul.NormalFor.structured' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms structured
/-- info: 'SolidityBridge.Yul.NormalFor.model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model
/-- info: 'SolidityBridge.Yul.NormalFor.prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepare
end SolidityBridge.Yul.NormalFor
