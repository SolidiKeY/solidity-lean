import Solidity.Yul.Adapters.ObjectWriteback
import Solidity.Source.Semantics

namespace Solidity.Yul.Adapters.ObjectWriteback.Controls
open Solidity.Backend.MemoryOps
private def E : Source.Env := ⟨[]⟩
private def empty : Source.EMState E [] := (.nil,Source.St.init E)
private def rawBytes : Source.Data E.layout (.bytes .memory) := .bytes [1,255]
private def rawString : Source.Data E.layout (.string .memory) := .string [255,0]
private def refs : Source.Data E.layout (.array .memory (.bytes .memory) none) :=
  .array 2 (fun _ h=>by cases h) (fun _=>.val (.memRef rfl 0))
private def y1 : Source.EMState E [] := ((Source.allocRef rawBytes).run empty).2
private def y2 : Source.EMState E [] := ((Source.allocRef rawString).run y1).2
private def y3 : Source.EMState E [] := ((Source.allocRef (sourceBoolMemory [true,false])).run y2).2
private def y : Source.EMState E [] := ((Source.allocRef refs).run y3).2

private theorem alloc_mem {τ : Source.STy} (x : Source.Data E.layout τ)
    (top : x.Top) (inner : x.Inner) (s : Source.EMState E []) (H : Source.HeapTy)
    (ok : Source.MemOK E H s) (data : Source.DataOK E s.2.heap.ty x) :
    Source.MemOK E H ((Source.allocRef x).run s).2 := by
  have h:=Source.allocRef_mem' (E:=E) (Γ:=[]) (H:=H) x top inner s ⟨ok,data⟩
  cases run : (Source.allocRef x : Source.EM E [] (Source.Val E.layout τ)).run s with
  | mk result z=>
    rw [run] at h
    cases result with
    | ok v=>exact h.1
    | error e=>exact h

private theorem bool_inner (xs : List Bool) : (sourceBoolMemory (D:=E.layout) xs).Inner :=
  fun i=>⟨.bool xs[i],rfl⟩
private theorem bool_ok (H : Source.HeapTy) (xs : List Bool) :
    Source.DataOK E H (sourceBoolMemory xs) := .array (fun _=>.val trivial)
private theorem ref_ok : Source.DataOK E y3.2.heap.ty refs :=
  .array (fun _=>.val ⟨.bytes .memory,rfl,rfl⟩)

theorem initial_MemOK : Source.MemOK E y.2.heap.ty y := by
  have start : Source.MemOK E empty.2.heap.ty empty :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have first:=alloc_mem rawBytes trivial trivial empty _ start (.bytes _)
  have second:=alloc_mem rawString trivial trivial y1 _ first (.string _)
  have third:=alloc_mem (sourceBoolMemory [true,false]) trivial (bool_inner _) y2 _ second (bool_ok _ _)
  have fourth:=alloc_mem refs trivial (fun _=>⟨.memRef rfl 0,rfl⟩) y3 _ third ref_ok
  exact fourth.self

private def requests : List (Request E) :=
  [(0,⟨.bytes .memory,.bytes [9,8,7]⟩),(1,⟨.string .memory,.string [128,255]⟩),
    (2,⟨.array .memory .bool none,sourceBoolMemory [false,true]⟩),
    (3,⟨.array .memory (.bytes .memory) none,refs⟩)]
private theorem ready : ∀ request∈requests,
    y.2.heap.ty request.1=some request.2.1 ∧ Prepared y request.2 := by
  intro request member
  simp only [requests,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨rfl,.bytes _,trivial,trivial⟩
  · exact ⟨rfl,.string _,trivial,trivial⟩
  · exact ⟨rfl,bool_ok _ _,trivial,bool_inner _⟩
  · exact ⟨rfl,.array (fun _=>.val ⟨.bytes .memory,rfl,rfl⟩),trivial,fun _=>⟨.memRef rfl 0,rfl⟩⟩

theorem mixed_writeback : ∃ z,
    (putAll requests).run y=(.ok (),z) ∧ Source.MemOK E y.2.heap.ty z ∧
    z.2.heap.next=4 ∧ z.2.heap.ty=y.2.heap.ty := by
  obtain ⟨z,run,types,next,locals,state,other,mem⟩:=all_types y requests ready
  exact ⟨z,run,mem _ initial_MemOK,next,types⟩

theorem unchanged_whole_state : (Source.heapPut 3 ⟨_,refs⟩).run y=(.ok (),y) := unchanged y _ _ rfl

theorem wrong_type : (Source.heapPut 0 ⟨.string .memory,rawString⟩).run y=
    (.error (.stuck "memory write type"),y) := failure y _ _ (by decide)

theorem shared_child_reads :
    let z:=((putAll requests).run y).2
    (Source.memElem (E:=E) (Γ:=[]) 3 0 (.bytes .memory)).run z=(.ok (.memRef rfl 0),z) ∧
    (Source.memElem (E:=E) (Γ:=[]) 3 1 (.bytes .memory)).run z=(.ok (.memRef rfl 0),z) ∧
    (Source.heapBytes (E:=E) (Γ:=[]) 0).run z=(.ok [9,8,7],z) := ⟨rfl,rfl,rfl⟩

private def dangling : Source.Data E.layout (.array .memory (.bytes .memory) none) :=
  .array 2 (fun _ h=>by cases h) (fun _=>.val (.memRef rfl 9))
theorem dangling_not_prepared : ¬Prepared y ⟨_,dangling⟩ := by
  intro ready
  cases ready.1 with
  | array children=>
    have child:=children ⟨0,by decide⟩
    cases child with
    | val reference=>
      obtain ⟨ty,found,shape⟩:=reference
      change (none : Option Source.STy)=some ty at found
      cases found

theorem late_type_failure : ∃ z,
    (putAll requests).run y=(.ok (),z) ∧
    (putAll (requests++[(0,⟨.string .memory,rawString⟩)])).run y=
      (.error (.stuck "memory write type"),z) ∧ Source.MemOK E y.2.heap.ty z := by
  obtain ⟨z,run,failed,mem⟩:=late_type_error y requests ready 0 ⟨_,rawString⟩ (by decide)
  exact ⟨z,run,failed,mem _ initial_MemOK⟩

private def observed : List Nat :=
  let z:=((putAll requests).run y).2
  let bytes:=((Source.heapBytes (E:=E) (Γ:=[]) 0).run z).1
  let string:=((Source.heapBytes (E:=E) (Γ:=[]) 1).run z).1
  (match bytes with | .ok bs=>bs.map UInt8.toNat | _=>[])++
    (match string with | .ok bs=>bs.map UInt8.toNat | _=>[])
/-- info: [9, 8, 7, 128, 255] -/
#guard_msgs in #eval observed
/-- info: false -/
#guard_msgs in #eval decide (observed=[1,255,255,0])
private def accepted : List (Request E) := requests++[(0,⟨.bytes .memory,.bytes [77]⟩)]
private def failing : List (Request E) :=
  accepted++[(0,⟨.string .memory,.string [88]⟩),(0,⟨.bytes .memory,.bytes [99]⟩)]

/-- Heterogeneous roots, repeated same-root update and late type error use the
computed prefix, not a caller-supplied successful run. -/
theorem checked_mixed : ∃ z,
    (putAll accepted).run y=(.ok (),z) ∧
    (putAll failing).run y=(.error (.stuck "memory write type"),z) ∧
    z.2.heap.ty=y.2.heap.ty ∧ z.2.heap.next=4 ∧ Source.MemOK E y.2.heap.ty z := by
  have pre : failing.takeWhile (fun request=>decide (y.2.heap.ty request.1=some request.2.1))=accepted := by rfl
  have prepared : ∀ request∈failing.takeWhile (fun request=>decide (y.2.heap.ty request.1=some request.2.1)),
      Prepared y request.2 := by
    rw [pre]
    intro request member
    simp only [accepted,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with old | rfl
    · exact (ready request old).2
    · exact ⟨.bytes _,trivial,trivial⟩
  obtain ⟨z,run,failed,types,next,locals,state,other,mem⟩ := all_types_checked y failing prepared
  rw [pre] at run
  have failed' : (putAll failing).run y=(.error (.stuck "memory write type"),z) := failed
  exact ⟨z,run,failed',types,next,mem _ initial_MemOK⟩

/-- The two real shared-child reads survive the error and observe the final
successful same-root write; the later99 packet never executes. -/
theorem checked_shared_child :
    let z:=((putAll failing).run y).2
    (Source.memElem (E:=E) (Γ:=[]) 3 0 (.bytes .memory)).run z=(.ok (.memRef rfl 0),z) ∧
    (Source.memElem (E:=E) (Γ:=[]) 3 1 (.bytes .memory)).run z=(.ok (.memRef rfl 0),z) ∧
    (Source.heapBytes (E:=E) (Γ:=[]) 0).run z=(.ok [77],z) := ⟨rfl,rfl,rfl⟩

/-- info: ([77], [128, 255]) -/
#guard_msgs in #eval
  let z:=((putAll failing).run y).2
  (((Source.heapBytes (E:=E) (Γ:=[]) 0).run z).1.toOption.getD [],
   ((Source.heapBytes (E:=E) (Γ:=[]) 1).run z).1.toOption.getD [])
/-- info: (false, false) -/
#guard_msgs in #eval
  let z:=((putAll failing).run y).2
  let bs:=((Source.heapBytes (E:=E) (Γ:=[]) 0).run z).1.toOption.getD []
  (bs==[99],bs==[1,255])

/-- Four actual heterogeneous roots reverse with identical complete Source
results, including shared-child representation and all nonheap fields. -/
theorem reverse_runs : (putAll requests).run y=(putAll requests.reverse).run y := by
  apply putAll_perm y requests requests.reverse (List.reverse_perm requests).symm
  · intro request member
    exact (ready request member).1
  · decide

/-- Actual shared children also read the same object through the reversed run. -/
theorem reverse_shared_children :
    let z:=((putAll requests.reverse).run y).2
    (Source.memElem (E:=E) (Γ:=[]) 3 0 (.bytes .memory)).run z=(.ok (.memRef rfl 0),z) ∧
    (Source.memElem (E:=E) (Γ:=[]) 3 1 (.bytes .memory)).run z=(.ok (.memRef rfl 0),z) ∧
    (Source.heapBytes (E:=E) (Γ:=[]) 0).run z=(.ok [9,8,7],z) := by
  have states := congrArg Prod.snd reverse_runs
  dsimp only
  rw [←states]
  exact shared_child_reads

private def childAfter (xs : List (Request E)) : Roadmap.Bytes :=
  let z:=((putAll xs).run y).2
  ((Source.heapBytes (E:=E) (Γ:=[]) 0).run z).1.toOption.getD []
/-- info: false -/
#guard_msgs in #eval decide ((accepted.map Prod.fst).Nodup)
/-- info: (false, false) -/
#guard_msgs in #eval
  (childAfter accepted==childAfter accepted.reverse,
   childAfter failing==childAfter failing.reverse)

end Solidity.Yul.Adapters.ObjectWriteback.Controls
