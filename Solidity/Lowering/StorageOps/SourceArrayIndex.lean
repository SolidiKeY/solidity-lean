import Solidity.Lowering.StorageOps.SourceWordRead
import Solidity.Backend.StorageOps.TargetArrayRead

/-! Fresh dynamic storage indexing over the existing Source reference/location
constructors. Raw canonical header contents derive the actual check and path;
retained cell reads alone do not establish liveness. No expression/address
compiler, allocation or world relation is inferred. -/
namespace Solidity.Lowering.StorageOps.SourceArrayIndex
open Solidity.Backend.StorageOps

/-- The actual Source operations, without another evaluator or value layer. -/
def read {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (σ : Source.STy) (i : Nat) : Source.EM E Γ (Source.Val E.layout σ) := do
  let location ← Source.indexLoc frame
    (.storRef (by rfl) path : Source.Val E.layout (.array .storage σ none)) i
  Source.readLoc frame location

/-- Header evaluation is derived from raw cell/type/cast facts. Both outcomes
preserve the full input state; failure is the existing Source panic payload. -/
theorem locate :
 ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx)
 (frame : Solidity.Source.Fr) (path : Solidity.Source.SPath) (σ : Solidity.Source.STy) (i : Nat)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_ordinary : E.transientRoot path=false)
 (typed : E.cellTy path = .int Solidity.Source.IntTy.u256)
 (header : Solidity.Source.Val E.layout (E.cellTy path)) (n : Int)
 (bound : Solidity.Source.IntTy.u256.lo ≤ n ∧ n ≤ Solidity.Source.IntTy.u256.hi)
 (_present : (state.ex.world.accounts frame.this).storage.read path=some header)
 (_cast : typed ▸ header = (.int n bound : Solidity.Source.Val E.layout (.int Solidity.Source.IntTy.u256))),
 (Solidity.Source.indexLoc (E:=E) (Γ:=Γ) frame
   (.storRef (by rfl) path : Solidity.Source.Val E.layout (.array .storage σ none)) i).run (locals,state) =
 if i<n.toNat then (.ok (.stor (path.go (.index i))), (locals,state))
 else (.error (.revert (Solidity.Source.panicData .index)), (locals,state)) := by
  intro E Γ frame path σ i locals state ordinary typed header n bound present cast
  have input : (Solidity.Source.readAt (E:=E) (Γ:=Γ) frame path (.int Solidity.Source.IntTy.u256)).run (locals,state) =
      (.ok (.int n bound),(locals,state)) := by
    simp only [Solidity.Source.readAt,Solidity.Source.Hoare.run_bind,Solidity.Backend.StorageOps.SourceReadFrames.readCell_run,ordinary,Bool.false_eq_true,if_false,present,dif_pos typed]
    rw [cast]
    rfl
  have length : (Solidity.Source.lengthOf (E:=E) (Γ:=Γ) frame
      (.storRef (by rfl) path : Solidity.Source.Val E.layout (.array .storage σ none))).run (locals,state) =
      (.ok n.toNat,(locals,state)) := by
    change (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame path).run (locals,state) = _
    rw [Solidity.Source.readLen,Solidity.Source.Hoare.run_bind,input]
    rfl
  rw [Solidity.Source.indexLoc,Solidity.Source.Hoare.run_bind,length]
  by_cases live : i<n.toNat
  · simp only [if_pos live]
    rfl
  · simp only [if_neg live]
    rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayIndex.locate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms locate

/-- Actual Source index/read success and actual guarded target SLOAD from OLD
PUBLIC represented observations. Source header/leaf facts are raw inputs;
no successful Source operation or desired preservation is assumed. Word
agreement is not a general address/default/compiler/world relation. -/
theorem represented_read :
 ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx)
 (frame : Solidity.Source.Fr) (path : Solidity.Source.SPath)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_ordinary : E.transientRoot path=false)
 (typed : E.cellTy path = .int Solidity.Source.IntTy.u256)
 (header : Solidity.Source.Val E.layout (E.cellTy path)) (count : Int)
 (bound : Solidity.Source.IntTy.u256.lo ≤ count ∧ count ≤ Solidity.Source.IntTy.u256.hi)
 (_present : (state.ex.world.accounts frame.this).storage.read path=some header)
 (_cast : typed ▸ header = (.int count bound : Solidity.Source.Val E.layout (.int Solidity.Source.IntTy.u256)))
 (n : Nat) (G : Solidity.TypeGraph.Schema n)
 (old : Solidity.TypeGraph.Value G (.array (.prim .uint))) (i : Solidity.TypeGraph.Index)
 (value : Solidity.TypeGraph.Value G (.prim .uint))
 (_found : (Solidity.Backend.StorageOps.TargetArrayRead.path i).readLive Solidity.TypeGraph.Value.dflt old=some value)
 (_length : count.toNat=old.length.val)
 (leafTyped : E.cellTy (path.go (.index i.val)) = .int Solidity.Source.IntTy.u256)
 (leaf : Solidity.Source.Val E.layout (E.cellTy (path.go (.index i.val))))
 (_leafPresent : (state.ex.world.accounts frame.this).storage.read (path.go (.index i.val))=some leaf)
 (_word : (leafTyped ▸ leaf).word=some (Solidity.Backend.StorageOps.TargetOperations.encodeWord (Solidity.PrimTy.toWord (p:=.uint) value.head)))
 (base : Solidity.Storage.Loc) (fits : Solidity.Backend.StorageOps.TargetOperations.KeysFit base)
 (store : Solidity.Storage.Representation.Store) (machine : Solidity.Evm.Machine) (tail : List Solidity.Evm.Word)
 (_before : Solidity.Storage.Representation.Graph.Represented old (Solidity.Backend.StorageOps.PrimitivePop.queries [i]) base store)
 (_initial : ∀ q ∈ Solidity.Backend.StorageOps.PrimitivePop.queries (G:=G) (p:=.uint) [i],
 machine.store.cells (Solidity.Backend.StorageOps.TargetOperations.toSlot (q.location base) (Solidity.Backend.StorageOps.TargetOperations.query_keysFit q base fits)) = Solidity.Backend.StorageOps.TargetOperations.encodeWord (store (q.location base))),
 (Solidity.Lowering.StorageOps.SourceArrayIndex.read (E:=E) (Γ:=Γ) frame path (.int Solidity.Source.IntTy.u256) i.val).run (locals,state)=
  (.ok (leafTyped ▸ leaf),(locals,state)) ∧
 Solidity.Evm.run Solidity.Backend.StorageOps.TargetArrayRead.code
 {machine with stack:=.val ⟨i.val,i.isLt⟩ :: .slot (Solidity.Backend.StorageOps.TargetOperations.toSlot base fits) :: tail} =
 .ok {machine with stack:=.val (Solidity.Backend.StorageOps.TargetOperations.encodeWord (Solidity.PrimTy.toWord (p:=.uint) value.head)) :: tail} 0 ∧
 (leafTyped ▸ leaf).word=some (Solidity.Backend.StorageOps.TargetOperations.encodeWord (Solidity.PrimTy.toWord (p:=.uint) value.head)) := by
  intro E Γ frame path locals state ordinary typed header count bound present cast n G old i value found length leafTyped leaf leafPresent word base fits store machine tail before initial
  have live : i.val<count.toNat := by
    rw [length]
    by_cases good : i.val<old.length.val
    · exact good
    · have absent := (Solidity.Backend.StorageOps.TargetArrayRead.live_none_iff old i).mpr (by omega)
      rw [found] at absent
      cases absent
  have source : (Solidity.Lowering.StorageOps.SourceArrayIndex.read (E:=E) (Γ:=Γ) frame path (.int Solidity.Source.IntTy.u256) i.val).run (locals,state) =
      (.ok (leafTyped ▸ leaf),(locals,state)) := by
    unfold Solidity.Lowering.StorageOps.SourceArrayIndex.read
    rw [Solidity.Source.Hoare.run_bind,Solidity.Lowering.StorageOps.SourceArrayIndex.locate E Γ frame path _ i.val locals state ordinary typed header count bound present cast,if_pos live]
    change (Solidity.Source.readAt (E:=E) (Γ:=Γ) frame (path.go (.index i.val)) (.int Solidity.Source.IntTy.u256)).run (locals,state)=_
    have childOrdinary : E.transientRoot (path.go (.index i.val))=false := ordinary
    simp only [Solidity.Source.readAt,Solidity.Source.Hoare.run_bind,Solidity.Backend.StorageOps.SourceReadFrames.readCell_run,childOrdinary,Bool.false_eq_true,if_false,leafPresent,dif_pos leafTyped]
    rfl
  exact ⟨source,Solidity.Backend.StorageOps.TargetArrayRead.represented_read old i value found base fits store machine tail before initial,word⟩

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayIndex.represented_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_read

/-- Bounds fail before either selected-cell read. Existing Source panic0x32
and target revert are distinct outcomes; this is not world rollback. No child
presence, type, zero-default or whole-extent clearing premise is needed. -/
theorem bounds_failure :
 ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx)
 (frame : Solidity.Source.Fr) (path : Solidity.Source.SPath) (σ : Solidity.Source.STy) (i : Nat)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_ordinary : E.transientRoot path=false)
 (typed : E.cellTy path = .int Solidity.Source.IntTy.u256)
 (header : Solidity.Source.Val E.layout (E.cellTy path)) (n : Int)
 (bound : Solidity.Source.IntTy.u256.lo ≤ n ∧ n ≤ Solidity.Source.IntTy.u256.hi)
 (_present : (state.ex.world.accounts frame.this).storage.read path=some header)
 (_cast : typed ▸ header = (.int n bound : Solidity.Source.Val E.layout (.int Solidity.Source.IntTy.u256)))
 (machine : Solidity.Evm.Machine) (tail : List Solidity.Evm.Word) (slot : Solidity.Evm.Slot)
 (fits : i<Solidity.Evm.W) (_targetHeader : machine.store slot=n.toNat) (_outside : n.toNat≤i),
 (Solidity.Lowering.StorageOps.SourceArrayIndex.read (E:=E) (Γ:=Γ) frame path σ i).run (locals,state)=
  (.error (.revert (Solidity.Source.panicData .index)),(locals,state)) ∧
 Solidity.Evm.run Solidity.Backend.StorageOps.TargetArrayRead.code
 {machine with stack:=.val ⟨i,fits⟩ :: .slot slot :: tail}=.revert := by
  intro E Γ frame path σ i locals state ordinary typed header n bound present cast machine tail slot fits targetHeader outside
  have failed : ¬i<n.toNat := by omega
  constructor
  · unfold Solidity.Lowering.StorageOps.SourceArrayIndex.read
    rw [Solidity.Source.Hoare.run_bind,Solidity.Lowering.StorageOps.SourceArrayIndex.locate E Γ frame path σ i locals state ordinary typed header n bound present cast,if_neg failed]
  · rw [Solidity.Backend.StorageOps.TargetArrayRead.run_current machine tail slot i fits,targetHeader,if_neg failed]

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayIndex.bounds_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bounds_failure
end Solidity.Lowering.StorageOps.SourceArrayIndex
