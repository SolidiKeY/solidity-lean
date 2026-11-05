import Solidity.Yul.Views.InventorySourceReads

/-! Read-side facts for empty dynamic arrays at the reserved zero word.
Actual logical heap IDs stay distinct. Word96 is a physical observation, not
an ordinary Placement, pointer decoder, write-alias policy or allocator fact.
No source producer reachability or complete shared-zero writeback is inferred. -/
namespace Solidity.Yul.Views.SharedZeroRead

def pointer : Roadmap.Word := ⟨96,by decide⟩
def emptyArray (D : Source.Layout) (element : Source.STy) :
    Source.Data D (.array .memory element none) :=
  .array 0 (fun _ impossible=>nomatch impossible) (fun i=>nomatch i)

/-- Existing Source length reads the actual empty heap object, including when
its logical identity was retained across local/frame substitutions. -/
theorem length {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (frame : Source.Fr) (root : Nat) (element : Source.STy)
    (found : s.2.heap.get root=some ⟨.array .memory element none,emptyArray E.layout element⟩) :
    (Source.lengthOf frame (.memRef (τ:=.array .memory element none) rfl root)).run s=(.ok 0,s) := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold Source.lengthOf
  rw [Source.Hoare.run_bind,heapObj_known s root _ found]
  rfl

/-- The real index operation refuses every index with its exact Panic payload;
this is not a refusal invented from physical preparation. -/
theorem index {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (frame : Source.Fr) (root i : Nat) (element : Source.STy)
    (found : s.2.heap.get root=some ⟨.array .memory element none,emptyArray E.layout element⟩) :
    (Source.indexLoc frame (.memRef (τ:=.array .memory element none) rfl root) i).run s=
      (.error (.revert (Source.panicData .index)),s) := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold Source.indexLoc
  rw [Source.Hoare.run_bind,length s frame root element found]
  simp only [Nat.not_lt_zero,if_false]
  rfl

/-- ReservedOK already supplies every byte of the shared zero header. -/
theorem header (memory : ByteView) (free : Roadmap.Word) (reserved : ReservedOK memory free) :
    mload memory pointer.val=0 := by
  first | (simp only;done) | decide | omega | rfl | skip
  have same := mload_congr memory (fun _=>0) 96 (fun i=>reserved.2 i)
  exact same.trans (by decide)

/-- The current ordinary-object certificate cannot be reused for zero-slot
placement: its occupied-object start law would be false. -/
theorem not_ordinary {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (root : Nat) (element : Source.STy)
    (found : h.get root=some ⟨.array .memory element none,emptyArray D element⟩) :
    p.address root≠pointer.val := by
  first | omega | decide | skip
  have present : (h.cells root).isSome := by
    change (h.get root).isSome=true
    rw [found]
    rfl
  have start:=p.starts root present
  change p.address root≠96
  omega

/-- A raw pointer alone cannot recover both retained logical identities.
This is a nonexistence fact, not a choice of an alternative decoder policy. -/
theorem no_identity_inverse (D : Source.Layout) (element : Source.STy) (one two : Nat)
    (distinct : one≠two)
    (decode : Roadmap.Word → Option (Source.Val D (.array .memory element none))) :
    ¬(decode pointer=some (.memRef rfl one) ∧ decode pointer=some (.memRef rfl two)) := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro both
  have values := Option.some.inj (both.1.symm.trans both.2)
  injection values with sameType ids
  exact distinct ids
end Solidity.Yul.Views.SharedZeroRead
