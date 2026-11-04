import Solidity.Yul.Adapters.P6RetainedRegionCopy
import Solidity.Backend.MemoryOps.SourceIndexedDelete

/-! Exact owner byte-reference operations for synchronized byte/string cells.
Location formation, access validity and historical provenance remain separate.
Memory byte lvalues check bounds on access, not formation. String-backed byte
aliases keep the actual string constructor; no surface string indexing is added. -/
namespace Solidity.Yul.Adapters.P6ByteReferenceReads
open Solidity.Yul.Views
open Solidity.Backend Solidity.Backend.MemoryOps

/-- Actual bytes observation accepts either real byte/string heap constructor. -/
theorem heap_read {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (root : Nat) (string : Bool) (bs : Roadmap.Bytes)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bs⟩) :
    (Source.heapBytes root).run s=(.ok bs,s) := by
  cases string
  · exact heapBytes_known s root bs (Or.inr found)
  · exact heapBytes_known s root bs (Or.inl found)

theorem length_read {E : Source.Env} {Γ : Source.RCtx} (F : Source.Fr)
    (s : Source.EMState E Γ) (root : Nat) (string : Bool) (bs : Roadmap.Bytes)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bs⟩) :
    (Source.lengthOf F (Source.Val.memRef (τ:=.bytes .memory) rfl root)).run s=(.ok bs.length,s) := by
  cases string
  all_goals
    simp only [Source.lengthOf,Source.Hoare.run_bind]
    rw [heapObj_known s root _ found]
    rfl

theorem read_byte {E : Source.Env} {Γ : Source.RCtx} (F : Source.Fr)
    (s : Source.EMState E Γ) (root : Nat) (string : Bool) (bs : Roadmap.Bytes)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bs⟩)
    (i : Nat) (inside : i<bs.length) :
    (Source.readLoc F (.memByte root i)).run s=
      (.ok (Source.Val.fixedBytes (n:=1) (h:=by decide) [bs[i]] rfl),s) := by
  rw [Source.readLoc,Source.Hoare.run_bind,heap_read s root string bs found]
  dsimp only
  rw [List.getElem?_eq_getElem inside]
  rfl

theorem read_outside {E : Source.Env} {Γ : Source.RCtx} (F : Source.Fr)
    (s : Source.EMState E Γ) (root : Nat) (string : Bool) (bs : Roadmap.Bytes)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bs⟩)
    (i : Nat) (outside : bs.length≤i) :
    (Source.readLoc F (.memByte root i)).run s=
      (.error (.revert (Source.panicData .index)),s) := by
  rw [Source.readLoc,Source.Hoare.run_bind,heap_read s root string bs found]
  dsimp only
  rw [List.getElem?_eq_none outside]
  rfl

/-- The actual write retains the root's real byte/string type and whole caller
administration. This operation alone is not assembly/static-call adequacy. -/
theorem write_byte {E : Source.Env} {Γ : Source.RCtx} (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (root : Nat) (string : Bool) (bs : Roadmap.Bytes)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bs⟩)
    (i : Nat) (inside : i<bs.length) (b : UInt8) :
    (Source.writeLoc F n (.memByte root i) (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)).run s=
      (.ok (),withSourceHeap s (s.2.heap.write root (heapByteData E.layout string (bs.set i b))
        (heap_ty_of_get s.2.heap root _ _ found))) := by
  cases string
  all_goals
    rw [Source.writeLoc,Source.Hoare.run_bind,heapObj_known s root _ found]
    dsimp only [heapByteData,heapByteType]
    rw [if_pos inside]
    exact heapPutConcrete_run s root _ _

theorem write_outside {E : Source.Env} {Γ : Source.RCtx} (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (root : Nat) (string : Bool) (bs : Roadmap.Bytes)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bs⟩)
    (i : Nat) (outside : bs.length≤i) (b : UInt8) :
    (Source.writeLoc F n (.memByte root i) (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)).run s=
      (.error (.revert (Source.panicData .index)),s) := by
  cases string
  all_goals
    rw [Source.writeLoc,Source.Hoare.run_bind,heapObj_known s root _ found]
    dsimp only [heapByteData,heapByteType]
    rw [if_neg (by omega)]
    rfl

/-- Existing resolved Source lvalue; no new syntax or interpreter. -/
def byteLocation {E : Source.Env} {Γ : Source.RCtx}
    (root : Source.Idx Γ (.bytes .memory)) (index : Source.Idx Γ (.int .u256)) :
    Source.RLVal E Γ (.fixedBytes 1 (by decide)) :=
  .indexBytes (.local root) (by decide) (.local index) rfl

/-- Formation does NOT assert that the resulting location may be accessed at
this length. No successful historical index event or reachability is inferred. -/
theorem form_location {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (n : Nat) (s : Source.EMState E Γ) (root : Source.Idx Γ (.bytes .memory))
    (index : Source.Idx Γ (.int .u256)) (a : Nat) (i : Roadmap.Word)
    (reference : s.1.get root=Source.Val.memRef rfl a)
    (indexed : s.1.get index=uintValueOfWord E.layout i) :
    (Source.evalLoc G F (n+2) (byteLocation root index)).run s=(.ok (.memByte a i.val),s) := by
  rw [byteLocation,Source.evalLoc,Source.Hoare.run_bind,source_local_value_run G F n s root _ reference]
  change ((Source.evalE G F (n+1) (.local index)) >>= fun value =>
    Source.indexNat value >>= fun k => pure (Source.Loc.memByte a k)).run s=_
  rw [Source.Hoare.run_bind,source_local_value_run G F n s index _ indexed]
  rfl

end Solidity.Yul.Adapters.P6ByteReferenceReads
