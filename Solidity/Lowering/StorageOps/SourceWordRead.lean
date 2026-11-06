import Solidity.Lowering.StorageOps.SourceWordWrite

/-! Typed Source cell reads and actual SLOAD. Ordinary-cell contents are the
input observation; missing cells remain Source failures although SLOAD is total.
No address compiler, default encoding, liveness or world relation is inferred. -/
namespace Solidity.Lowering.StorageOps.SourceWordRead
open Solidity.Backend.StorageOps

/-- Total Source read equation, retaining both present and absent outcomes.
Reading needs neither a positive store budget nor a writable frame. -/
theorem read_total :
 ∀ (E : Source.Env) (Γ : Source.RCtx) (frame : Source.Fr) (path : Source.SPath)
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (_ordinary : E.transientRoot path=false),
 (Source.readAt (E:=E) (Γ:=Γ) frame path (E.cellTy path)).run (locals,state) =
 match (state.ex.world.accounts frame.this).storage.read path with
 | some value => (.ok value,(locals,state))
 | none => (.error (.stuck "storage cell without a value"),(locals,state)) := by
  intro E Γ frame path locals state ordinary
  simp only [Source.readAt, Source.Hoare.run_bind, SourceReadFrames.readCell_run,
    ordinary, Bool.false_eq_true, if_false]
  cases (state.ex.world.accounts frame.this).storage.read path <;> rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceWordRead.read_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_total
/-- Successful Source and target executions derived from raw input cell/word
agreement. No source success, target success or preservation result is assumed.
A defaulted cell is covered only when the existing Source read supplies a word. -/
theorem complete :
 ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx)
 (frame : Solidity.Source.Fr) (path : Solidity.Source.SPath)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_ordinary : E.transientRoot path=false)
 (value : Solidity.Source.Val E.layout (E.cellTy path))
 (_present : (state.ex.world.accounts frame.this).storage.read path=some value)
 (machine : Solidity.Evm.Machine) (slot : Solidity.Evm.Slot)
 (_coherent : value.word=some (machine.store.cells slot)),
 (Solidity.Source.readAt (E:=E) (Γ:=Γ) frame path (E.cellTy path)).run (locals,state)=
   (.ok value,(locals,state)) ∧
 Solidity.Evm.run (Solidity.Backend.StorageOps.TargetOperations.readCode slot) machine=
   .ok {machine with stack:=.val (machine.store.cells slot)::machine.stack} 0 ∧
 value.word=some (machine.store.cells slot) := by
  intro E Γ frame path locals state ordinary value present machine slot coherent
  exact ⟨by rw [read_total E Γ frame path locals state ordinary,present],
    TargetOperations.run_read slot machine,coherent⟩

/-- info: 'Solidity.Lowering.StorageOps.SourceWordRead.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Lowering.StorageOps.SourceWordRead
