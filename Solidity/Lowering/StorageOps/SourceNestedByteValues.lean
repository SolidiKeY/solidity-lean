import Solidity.Lowering.StorageOps.SourceByteStorageCopy
import Solidity.Lowering.StorageOps.SourceByteStorageBarrier
import Solidity.Lowering.StorageOps.SourceReadFrames

/-! Actual nonempty storage-reference byte snapshots. Existing Source heap
allocations are folded over the runtime prefix; no alternate values/state or
copy evaluator is introduced. Inner and outer lengths are arbitrary naturals. -/
namespace Solidity.Lowering.StorageOps.SourceNestedByteValues
open Solidity Solidity.Backend.StorageOps

/-- Existing typed allocation for the captured bytes at one outer index. -/
def allocateAt {E : Source.Env} (length : Nat) (payload : Nat → Nat → UInt8)
 (state : Source.St E) (j : Nat) : Source.St E :=
 {state with heap:=(state.heap.alloc ⟨.bytes .memory,Source.Data.bytes ((List.range' 0 length).map (payload j))⟩).1}

/-- Actual reference capture reads the entire OLD payload before allocating. -/
theorem capture {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (path : Source.SPath) (length padding : Nat)
 (payload : Nat → UInt8) (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (header : (Source.readLen (E:=E) (Γ:=Γ) frame path).run (locals,state)=(.ok length,(locals,state)))
 (reads : ∀ k<length,(Source.readAt (E:=E) (Γ:=Γ) frame (path.go (.index k)) (.fixedBytes 1 (by decide))).run (locals,state)=
  (.ok (Source.Val.fixedBytes (n:=1) (h:=by decide) [payload k] rfl),(locals,state))) :
 (Source.loadElem (E:=E) (Γ:=Γ) frame (length+padding+3) (.bytes .memory) path).run (locals,state)=
 (.ok (Source.Val.memRef (τ:=.bytes .memory) rfl state.heap.next),
  (locals,{state with heap:=(state.heap.alloc ⟨.bytes .memory,Source.Data.bytes ((List.range' 0 length).map payload)⟩).1})) := by
 simp only [Source.loadElem,Source.STy.byRef,Source.STy.loc?,Option.isSome_some,
   if_true,Source.loadMem,Source.Hoare.run_bind,header]
 rw [SourceByteStorageCopy.load_bytes frame path 0 length padding payload (locals,state) (by
   simpa only [Nat.zero_add] using reads)]
 rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceNestedByteValues.capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capture

/-- Distinct nonempty OLD payloads are allocated in order before the final
capture times out. Inner length and outer count are runtime parameters. -/
theorem timeout_prefix : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (path : Solidity.Source.SPath) (start count length : Nat)
 (payload : Nat → Nat → UInt8) (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_headers : ∀ j<count+1,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (path.go (.index (start+j)))).run (locals,state)=(.ok length,(locals,state)))
 (_reads : ∀ j<count+1,∀ k<length,(Solidity.Source.readAt (E:=E) (Γ:=Γ) frame ((path.go (.index (start+j))).go (.index k)) (.fixedBytes 1 (by decide))).run (locals,state)=
  (.ok (Solidity.Source.Val.fixedBytes (n:=1) (h:=by decide) [payload (start+j) k] rfl),(locals,state))),
 (Solidity.Source.loadElems (E:=E) (Γ:=Γ) frame (count+length+3) (.bytes .memory) path start (count+1)).run (locals,state)=
 (.error .timeout,(locals,(List.range' start count).foldl (Solidity.Lowering.StorageOps.SourceNestedByteValues.allocateAt length payload) state)) := by
 intro E Γ frame path start count length payload locals state headers reads
 induction count generalizing start state with
 | zero =>
   have header := headers 0 (by omega)
   simp only [Nat.add_zero] at header
   simp only [Nat.zero_add,Source.loadElems,Source.loadElem,Source.STy.byRef,Source.STy.loc?,
     Option.isSome_some,if_true,Source.loadMem,Source.Hoare.run_bind,header]
   rw [SourceByteStorageBarrier.load_timeout frame (path.go (.index start)) length 0 length
     (payload start) (locals,state) (Nat.le_refl _) (by
       simpa only [Nat.add_zero,Nat.zero_add] using reads 0 (by omega))]
   rfl
 | succ count ih =>
   have budget : count+1+length+3=(count+length+3)+1 := by omega
   rw [budget]
   change ((Source.loadElem frame (count+length+3) (.bytes .memory) (path.go (.index start)) >>= fun x =>
     Source.loadElems frame (count+length+3) (.bytes .memory) path (start+1) (count+1) >>= fun xs =>
     pure (Source.finCons (.val x) xs)).run (locals,state))=_
   have header := headers 0 (by omega)
   simp only [Nat.add_zero] at header
   have first := capture frame (path.go (.index start)) length count (payload start) locals state header (by
     simpa only [Nat.add_zero] using reads 0 (by omega))
   have fuel : length+count+3=count+length+3 := by omega
   rw [fuel] at first
   change (Source.loadElem frame (count+length+3) (.bytes .memory) (path.go (.index start))).run (locals,state)=
     (.ok (Source.Val.memRef (τ:=.bytes .memory) rfl state.heap.next),
       (locals,allocateAt length payload state start)) at first
   rw [Source.Hoare.run_bind,first]
   dsimp only
   rw [Source.Hoare.run_bind,ih (start+1) (allocateAt length payload state start) (by
     intro j member
     rw [SourceReadFrames.readLen_transport frame (path.go (.index ((start+1)+j)))
       locals state (allocateAt length payload state start) rfl rfl]
     have found := headers (j+1) (by omega)
     have index : start+(j+1)=(start+1)+j := by omega
     rw [index] at found
     rw [found]) (by
     intro j member k bound
     rw [SourceReadFrames.readAt_transport frame ((path.go (.index ((start+1)+j))).go (.index k))
       (.fixedBytes 1 (by decide)) locals state (allocateAt length payload state start) rfl rfl]
     have found := reads (j+1) (by omega) k bound
     have index : start+(j+1)=(start+1)+j := by omega
     rw [index] at found
     rw [found])]
   simp only [List.range'_succ,List.foldl_cons]

/-- info: 'Solidity.Lowering.StorageOps.SourceNestedByteValues.timeout_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms timeout_prefix
end Solidity.Lowering.StorageOps.SourceNestedByteValues
