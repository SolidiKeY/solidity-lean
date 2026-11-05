import Solidity.Backend.MemoryOps.SourceRhsValue
import Solidity.Evm.MemoryExpr

/-! Short-circuit control around effectful memory expressions. These laws use
actual Source evaluation and the existing word branching program. The right
program may mutate memory; no pure-operand ValueSim premise is used. -/
namespace Solidity.Backend.MemoryOps

/-- A false local skips an arbitrary Bool expression, including its failures
and writes. No bounds or successful-execution premise is needed for the body. -/
theorem source_and_skip {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (guard : Source.Idx Γ .bool) (body : Source.RExpr E Γ .bool)
    (hg : y.1.get guard=.bool false) :
    (Source.evalE G F (fuel+2) (.binary .and (.local guard) body)).run y=
      (.ok (.val (.bool false)),y) := by
  first
  | solve | rfl | simp only [] | omega
  | rw [Source.evalE]
    simp only [reduceCtorEq,decide_true,decide_false,Bool.or_false,if_true]
    rw [Source.Hoare.run_bind,
      source_local_value_run G F fuel y guard (.bool false) hg]
    rfl

/-- The selected right expression starts in the actual initial state after
reading the guard. Its returned state is retained, rather than reset. -/
theorem source_and_enter {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y z : Source.EMState E Γ)
    (guard : Source.Idx Γ .bool) (body : Source.RExpr E Γ .bool) (v : Bool)
    (hg : y.1.get guard=.bool true)
    (bodyRun : (Source.evalE G F (fuel+1) body).run y=(.ok (.val (.bool v)),z)) :
    (Source.evalE G F (fuel+2) (.binary .and (.local guard) body)).run y=
      (.ok (.val (.bool v)),z) := by
  first
  | solve | rfl | simp only [] | omega
  | rw [Source.evalE]
    simp only [reduceCtorEq,decide_true,decide_false,Bool.or_false,if_true]
    rw [Source.Hoare.run_bind,
      source_local_value_run G F fuel y guard (.bool true) hg]
    change ((Source.evalE G F (fuel+1) body) >>= fun r => Source.getV r >>= fun v => pure (Source.RVal.val v)).run y=_
    rw [Source.Hoare.run_bind,bodyRun]
    rfl

/-- Propagation keeps the body's actual failure state; this says nothing
about a separate outer transaction rollback. -/
theorem source_and_error {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y z : Source.EMState E Γ)
    (guard : Source.Idx Γ .bool) (body : Source.RExpr E Γ .bool) (err : Source.Halt)
    (hg : y.1.get guard=.bool true)
    (bodyRun : (Source.evalE G F (fuel+1) body).run y=(.error err,z)) :
    (Source.evalE G F (fuel+2) (.binary .and (.local guard) body)).run y=(.error err,z) := by
  first
  | solve | rfl | simp only [] | omega
  | rw [Source.evalE]
    simp only [reduceCtorEq,decide_true,decide_false,Bool.or_false,if_true]
    rw [Source.Hoare.run_bind,
      source_local_value_run G F fuel y guard (.bool true) hg]
    change ((Source.evalE G F (fuel+1) body) >>= fun r => Source.getV r >>= fun v => pure (Source.RVal.val v)).run y=_
    rw [Source.Hoare.run_bind,bodyRun]

/-- The actual existing short-circuit jump skips the entire effectful body.
Only the false result is pushed; memory and the saved tail stay on m. -/
theorem word_and_skip (left right : List Evm.Instr) (m : Evm.Machine)
    (hleft : Evm.run left m=.ok (m.push (.val (Evm.bword false))) 0) :
    Evm.run (Evm.Memory.binaryCode .bool .and left right) m=
      .ok (m.push (.val (Evm.bword false))) 0 := by
  first
  | solve | rfl | simp only [] | omega
  | simp only [Evm.Memory.binaryCode,List.append_assoc]
    rw [Evm.run_append_ok hleft]
    rw [show [Evm.Instr.dup 1,.iszero,.jumpi (right.length+1),.pop] ++ right=
        [Evm.Instr.dup 1,.iszero,.jumpi (right.length+1)] ++ ([.pop] ++ right) from rfl,
      Evm.run_append_skip (m' := m.push (.val (Evm.bword false))) (k := right.length+1) rfl]
    exact Evm.exec_length ([.pop] ++ right) _

/-- A true result is removed before entering the effectful right program.
The equation covers success, revert and skip without inventing an error machine. -/
theorem word_and_enter (left right : List Evm.Instr) (m : Evm.Machine)
    (hleft : Evm.run left m=.ok (m.push (.val (Evm.bword true))) 0) :
    Evm.run (Evm.Memory.binaryCode .bool .and left right) m=Evm.run right m := by
  first
  | solve | rfl | simp only [] | omega
  | simp only [Evm.Memory.binaryCode,List.append_assoc]
    rw [Evm.run_append_ok hleft]
    rw [show [Evm.Instr.dup 1,.iszero,.jumpi (right.length+1),.pop] ++ right=
        [Evm.Instr.dup 1,.iszero,.jumpi (right.length+1),.pop] ++ right from rfl,
      Evm.run_append_ok (m' := m) rfl]

/-- info: 'Solidity.Backend.MemoryOps.source_and_skip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_and_skip
/-- info: 'Solidity.Backend.MemoryOps.source_and_enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_and_enter
/-- info: 'Solidity.Backend.MemoryOps.source_and_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_and_error
/-- info: 'Solidity.Backend.MemoryOps.word_and_skip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_and_skip
/-- info: 'Solidity.Backend.MemoryOps.word_and_enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_and_enter

end Solidity.Backend.MemoryOps
