import Solidity.Lowering.StorageOps.SourceArrayIndex
import Solidity.Backend.StorageOps.TargetArrayWrite

/-! Actual fresh Source lvalue indexing followed by writeLoc. Primitive writes
retain their existing budget-independent semantics; aggregate copying, address
compilation and world rollback are separate obligations. -/
namespace Solidity.Lowering.StorageOps.SourceArrayWrite

def write {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr) (budget : Nat)
    (path : Source.SPath) (σ : Source.STy) (i : Nat) (value : Source.Val E.layout σ) : Source.EM E Γ Unit := do
  let location ← Source.indexLoc frame
    (.storRef (by rfl) path : Source.Val E.layout (.array .storage σ none)) i
  Source.writeLoc frame budget location value

/-- Source success follows from the current raw canonical header and actual
lvalue check. No positive fuel premise is imposed on existing by-value writeLoc.
The complete Source state/journal effect is the published ordinary cell operation. -/
theorem source_run :
 ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx)
 (frame : Solidity.Source.Fr) (path : Solidity.Source.SPath) (i : Nat)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_ordinary : E.transientRoot path=false)
 (typed : E.cellTy path = .int Solidity.Source.IntTy.u256)
 (header : Solidity.Source.Val E.layout (E.cellTy path)) (n : Int)
 (bound : Solidity.Source.IntTy.u256.lo ≤ n ∧ n ≤ Solidity.Source.IntTy.u256.hi)
 (_present : (state.ex.world.accounts frame.this).storage.read path=some header)
 (_cast : typed ▸ header = (.int n bound : Solidity.Source.Val E.layout (.int Solidity.Source.IntTy.u256)))
 (value : Solidity.Source.Val E.layout (E.cellTy (path.go (.index i))))
 (budget : Nat) (_byValue : (E.cellTy (path.go (.index i))).byRef=false)
 (_writable : frame.static=false) (_live : i<n.toNat),
 (Solidity.Lowering.StorageOps.SourceArrayWrite.write (E:=E) (Γ:=Γ) frame budget path
 (E.cellTy (path.go (.index i))) i value).run (locals,state)=
 (.ok (), (locals,Solidity.Lowering.StorageOps.SourceWordWrite.after frame (path.go (.index i)) value state)) := by
  intro E Γ frame path i locals state ordinary typed header n bound present cast value budget byValue writable live
  unfold Solidity.Lowering.StorageOps.SourceArrayWrite.write
  rw [Solidity.Source.Hoare.run_bind,Solidity.Lowering.StorageOps.SourceArrayIndex.locate E Γ frame path _ i locals state ordinary typed header n bound present cast,if_pos live]
  simp only [Solidity.Source.writeLoc,byValue,Bool.false_eq_true,if_false]
  exact Solidity.Lowering.StorageOps.SourceWordWrite.source_write frame (path.go (.index i)) value locals state writable ordinary

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWrite.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_run
open Solidity.Backend.StorageOps Solidity.TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph Solidity.Backend.StorageOps.TargetArrayWrite

/-- Paired Source and guarded-target facts sharing length, index and payload
 word. Representation/frame/numeric transport concern the graph and target;
 Source path and target base remain independent. No Source-path/layout relation
 is a premise or conclusion, so this is not compiler/address preservation. -/
theorem complete_numeric :
∀ {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (_run : FiniteRun N L R hash P locations)
    (old result : Value G (.array (.prim p))) (i : Index) (value : p.Denote)
    (_performed : writeAt old i value = some result)
    (queries : List (Query G (.array (.prim p)))) (base : Solidity.Storage.Loc)
    (baseFits : TargetOperations.KeysFit base) (store : Store) (numeric : WordStore)
    (machine : Evm.Machine) (tail : List Evm.Word)
    (_beforeHeader : Represented old [.length .nil] base store)
    (_before : Represented old queries base store)
    (_supported : PathSupported (TargetArrayRead.path (G := G) (p := p) i))
    (_apart : ∀ q ∈ queries, q.apart (TargetArrayRead.path (G := G) (p := p) i))
    (_nonalias : ∀ q ∈ queries, q.location base ≠ pathLoc (TargetArrayRead.path (G := G) (p := p) i) base)
    (_initial : Transport N hash locations store numeric)
    (_headerCovered : base ∈ locations) (_childCovered : pathLoc (TargetArrayRead.path (G := G) (p := p) i) base ∈ locations)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (_targetInitial : ∀ l (member : l ∈ locations), machine.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (E : Source.Env) (Γ : Source.RCtx) (frame : Source.Fr) (path : Source.SPath)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (_ordinary : E.transientRoot path=false)
    (typed : E.cellTy path=.int Source.IntTy.u256)
    (header : Source.Val E.layout (E.cellTy path)) (count : Int)
    (bound : Source.IntTy.u256.lo≤count ∧ count≤Source.IntTy.u256.hi)
    (_present : (state.ex.world.accounts frame.this).storage.read path=some header)
    (_cast : typed ▸ header=(.int count bound : Source.Val E.layout (.int Source.IntTy.u256)))
    (payload : Source.Val E.layout (E.cellTy (path.go (.index i.val)))) (budget : Nat)
    (_byValue : (E.cellTy (path.go (.index i.val))).byRef=false)
    (_writable : frame.static=false) (_length : count.toNat=old.length.val)
    (_word : payload.word=some (TargetOperations.encodeWord (PrimTy.toWord value))),

    (SourceArrayWrite.write (E:=E) (Γ:=Γ) frame budget path (E.cellTy (path.go (.index i.val))) i.val payload).run (locals,state)=
      (.ok (), (locals,SourceWordWrite.after frame (path.go (.index i.val)) payload state)) ∧
    (((SourceWordWrite.after frame (path.go (.index i.val)) payload state).ex.world.accounts frame.this).storage.read (path.go (.index i.val))).bind Source.Val.word=some (TargetOperations.encodeWord (PrimTy.toWord value)) ∧
    (    let dst := TargetArrayRead.path (G := G) (p := p) i
    let word := PrimTy.toWord value
    let child := pathLoc dst base
    let afterStore := Representation.write store child word
    let afterNumeric := writeWord numeric (child.word N hash) word
    let afterTarget := { machine with stack := tail, store := Evm.WordStore.write machine.store (TargetOperations.toSlot child (TargetOperations.path_keysFit dst base baseFits)) (TargetOperations.encodeWord word).val }
    Evm.run code { machine with stack := .val ⟨i.val,i.isLt⟩ :: .slot (TargetOperations.toSlot base baseFits) :: .val (TargetOperations.encodeWord word) :: tail } = .ok afterTarget 0 ∧
      Represented result (.length .nil :: .word dst :: queries) base afterStore ∧
      Transport N hash locations afterStore afterNumeric ∧
      (∀ l (member : l ∈ locations), afterTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (afterStore l)))
 := by
  intro n N L R G p hash P locations run old result i value performed queries base baseFits store numeric machine tail beforeHeader before supported apart nonalias initial headerCovered childCovered fitting targetInitial E Γ frame path locals state ordinary typed header count bound present cast payload budget byValue writable length word
  have live : i.val < count.toNat := by
    rw [length]
    exact (TargetArrayWrite.success old result i value performed).1
  refine ⟨SourceArrayWrite.source_run E Γ frame path i.val locals state ordinary typed header count bound present cast payload budget byValue writable live, ?_, ?_⟩
  · rw [SourceWordWrite.read_after]
    exact word
  · exact TargetArrayWrite.complete_numeric run old result i value performed queries base baseFits store numeric machine tail beforeHeader before supported apart nonalias initial headerCovered childCovered fitting targetInitial

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWrite.complete_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_numeric
end Solidity.Lowering.StorageOps.SourceArrayWrite
