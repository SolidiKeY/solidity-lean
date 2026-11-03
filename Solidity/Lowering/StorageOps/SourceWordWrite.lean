import Solidity.Lowering.StorageOps.SourceReadFrames
import Solidity.Backend.StorageOps.StackWordWrite

/-! Ordinary typed Source cell writes and runtime-word target operands.
Input word agreement is observational, not Source admission, value lowering,
address/liveness compilation or world/bytecode refinement. Function/reference
values are excluded by the existing Val.word observation. -/
namespace Solidity.Lowering.StorageOps.SourceWordWrite
open Solidity.Backend.StorageOps

def op {E : Source.Env} (frame : Source.Fr) (path : Source.SPath)
    (value : Source.Val E.layout (E.cellTy path)) : Source.Op E.layout E.lay E.lay :=
  .account frame.this (fun account => {account with storage := account.storage.set path (some value)})

def after {E : Source.Env} (frame : Source.Fr) (path : Source.SPath)
    (value : Source.Val E.layout (E.cellTy path)) (state : Source.St E) : Source.St E :=
  {state with ex := state.ex.apply (op frame path value)}

theorem source_write {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (path : Source.SPath) (value : Source.Val E.layout (E.cellTy path))
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (writable : frame.static=false) (ordinary : E.transientRoot path=false) :
    (Source.writeAt frame path value : Source.EM E Γ Unit).run (locals,state) =
      (.ok (), (locals,after frame path value state)) := by
  simp only [Source.writeAt,Source.setCell,ordinary,↓reduceIte,Source.applyOp,writable,
    Bool.false_eq_true,Source.EM.modSt,after,op]
  rfl

theorem read_after {E : Source.Env} (frame : Source.Fr) (path : Source.SPath)
    (value : Source.Val E.layout (E.cellTy path)) (state : Source.St E) :
    ((after frame path value state).ex.world.accounts frame.this).storage.read path = some value := by
  simpa only [after,op,Source.ExecState.apply,Source.World.set,dif_pos]
    using (Source.Storage.write_read (state.ex.world.accounts frame.this).storage path value)

/-- The free value index is generalized before constructor elimination.
Existing word observation excludes memory/storage/calldata and function values;
no source admission or encoding theorem is inferred. -/
theorem storeVal_word {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (budget : Nat) (τ : Source.STy) (path : Source.SPath) {σ : Source.STy}
    (value : Source.Val E.layout σ) (word : Roadmap.Word) (coherent : value.word=some word) :
    (Source.storeVal frame (budget+1) τ path value : Source.EM E Γ Unit) =
      Source.writeAt frame path value := by
  cases value <;> first | rfl | (simp only [Source.Val.word] at coherent; contradiction)

/-- info: 'Solidity.Lowering.StorageOps.SourceWordWrite.source_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_write
/-- info: 'Solidity.Lowering.StorageOps.SourceWordWrite.read_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_after
/-- info: 'Solidity.Lowering.StorageOps.SourceWordWrite.storeVal_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms storeVal_word
/-- Both actual independent executions and written-word observations.
The target operand is supplied on the stack. Word agreement is an INPUT;
no address/liveness, value-lowering, compiler or world result is assumed. -/
theorem complete :
 ∀ (E : Source.Env) (Γ : Source.RCtx) (frame : Source.Fr) (path : Source.SPath)
 (value : Source.Val E.layout (E.cellTy path)) (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (_writable : frame.static=false) (_ordinary : E.transientRoot path=false) (budget : Nat)
 (word : Fin Evm.W) (_coherent : value.word=some word) (machine : Evm.Machine) (slot : Evm.Slot),
 let sourceResult := (Source.storeVal frame (budget+1) (E.cellTy path) path value : Source.EM E Γ Unit).run (locals,state)
 let targetResult := {machine with store := Evm.WordStore.write machine.store slot word.val}
 sourceResult=(.ok (), (locals,after frame path value state)) ∧
 Evm.run (StackWordWrite.code slot) {machine with stack := .val word :: machine.stack}=.ok targetResult 0 ∧
 ((sourceResult.2.2.ex.world.accounts frame.this).storage.read path).bind Source.Val.word=some word ∧
 targetResult.store.cells slot=word := by
  intro E Γ frame path value locals state writable ordinary budget word coherent machine slot
  dsimp only
  rw [storeVal_word frame budget _ path value word coherent,
    source_write frame path value locals state writable ordinary]
  refine ⟨rfl,StackWordWrite.run slot word machine,?_,
    Evm.WordStore.write_cells_same machine.store slot word⟩
  rw [read_after]
  exact coherent

/-- info: 'Solidity.Lowering.StorageOps.SourceWordWrite.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Lowering.StorageOps.SourceWordWrite
