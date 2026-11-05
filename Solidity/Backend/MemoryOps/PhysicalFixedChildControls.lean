import Solidity.Backend.MemoryOps.PhysicalFixedChildWrite
import Solidity.Source.SemanticsExamples

/-! Inhabited fixed-child controls. Repeated parent slots alias the same fixed
child; no Source parent-to-intrinsic observer or general byte compiler is assumed. -/
namespace Solidity.Backend.MemoryOps.Physical.FixedChildControls
open Evm Evm.Memory
open Source.SemanticsExamples (E0 F0 s0)
private abbrev A : RefTy := .fixed (.prim .uint) 3
private abbrev P : RefTy := .array (.ref A)
private abbrev N : RefTy := .fixed (.prim .uint) 2
private abbrev H : HTy := [P,A,N]
private def root : HRef H P := ⟨0,rfl⟩
private def child : HRef H A := ⟨1,rfl⟩
private def neighbor : HRef H N := ⟨2,rfl⟩
private def u (n : Nat) : PrimTy.uint.Denote := indexValue (wmod n)
private def hp : Heap H := (⟨[child,child],by decide⟩,⟨[u 7,u 0,u (W-1)],rfl⟩,⟨[u 8,u 9],rfl⟩,())
private def base (id : Nat) : Fin W := if id=0 then wmod 16 else if id=1 then wmod 8 else wmod 24
private def machine : Machine := {Machine.init with stack := [w[77],w[88]],mem := fun c =>
  if c=0 then w[32] else if c=16 then w[2] else if c=17 ∨ c=18 then w[8]
  else if c=8 then w[7] else if c=10 then (Word.val (wmod (W-1))) else if c=24 then w[8] else if c=25 then w[9] else w[0]}
private def image : List (Nat×Nat) := [(0,1024),(8,7),(9,0),(10,W-1),(16,2),(17,256),(18,256),(24,8),(25,9)]
private def bytes : Environment.Memory := image.foldl
  (fun memory cell => Environment.writeBytes memory (32*cell.1) (Semantics.wordBytes cell.2)) (fun _ => 0)
private def sourceHeap : Source.Heap E0.layout :=
  (((s0 (E := E0)).heap.alloc ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get child)⟩).1.alloc
    ⟨.array .memory (.int .u256) (some 2),sourceUintFixedObject (hp.get neighbor)⟩).1
private def y : Source.EMState E0 [] := (.nil,{s0 with heap := sourceHeap})
private theorem sourceAt : SourceUintFixedAt y 0 hp child := by rfl
private theorem sourceNeighbor : y.2.heap.get 1=some ⟨.array .memory (.int .u256) (some 2),sourceUintFixedObject (hp.get neighbor)⟩ := by rfl
private theorem image_read (c value : Nat) (hit : (c,value)∈image) :
    Environment.readMemory bytes (32*c) 32=Semantics.wordBytes value := by
  simp only [image,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hit
  rcases hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals
    simp only [bytes,image,List.foldl_cons,List.foldl_nil]
    repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length];omega)
    simpa only [Environment.wordBytes_length] using Environment.read_written (Semantics.wordBytes _) _ _
private theorem parentLength : hp.len root .dyn=2 := by
  simp only [Heap.len,MObj.elems_dyn]
  rfl
private theorem parentElements : MObj.elems .dyn (hp.get root)=[child,child] := by
  simp only [MObj.elems_dyn]
  rfl
private theorem parentAt : ReferenceArrayAt hp root base machine bytes := by
  constructor
  · constructor
    · rw [parentLength];decide
    · rw [parentLength];rfl
    · intro i q hit
      rw [parentElements] at hit
      cases i with
      | zero => cases hit;rfl
      | succ i => cases i with
        | zero => cases hit;rfl
        | succ i => cases hit
  · decide
  · exact ⟨wmod 2,rfl,image_read 16 2 (by decide)⟩
  · constructor
    · intro c hc
      obtain ⟨i,hi,eq⟩ := hc
      rw [parentLength] at hi
      change c=16+1+i at eq
      omega
    · intro c hc
      obtain ⟨i,hi,eq⟩ := hc
      rw [parentLength] at hi
      change c=16+1+i at eq
      have which : i=0 ∨ i=1 := by omega
      rcases which with rfl|rfl
      · subst c
        exact ⟨wmod 8,rfl,by decide,image_read 17 256 (by decide)⟩
      · subst c
        exact ⟨wmod 8,rfl,by decide,image_read 18 256 (by decide)⟩

/-- Actual source/intrinsic success uses cell9, not a dynamic header offset10.
The repeated typed parent, old neighbour and all other Source addresses frame. -/
theorem headerless_write (fuel : Nat) :
    ∃ (out : Heap H) (z : Source.EMState E0 []) (logical offset : Fin W),
      logical.val=9 ∧ offset.val=288 ∧
      hp.writeAddr (.index child .fixed (indexValue (wmod 1))) (u 42)=some out ∧
      (Source.writeLoc (E := E0) (Γ := []) F0 fuel (.mem 0 1) (sourceUint (u 42))).run y=(.ok (),z) ∧
      Evm.run [.mstoreAt] ((machine.push w[42]).push (.val logical))=.ok (writeMachine machine 9 w[42]) 0 ∧
      ReferenceArrayAt out root base (writeMachine machine 9 w[42])
        (Environment.writeBytes bytes 288 (Semantics.wordBytes 42)) ∧
      SourceUintFixedAt z 0 out child ∧ out.get neighbor=hp.get neighbor ∧
      z.2.heap.get 1=some ⟨.array .memory (.int .u256) (some 2),sourceUintFixedObject (hp.get neighbor)⟩ ∧
      (∀ a,a≠0 → z.2.heap.get a=y.2.heap.get a) ∧ z.1=y.1 ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | simp only [] | omega
  | have slots : ∀ c,ReferenceSlots hp root base c → c≠9 := by
      intro c hc
      obtain ⟨i,hi,eq⟩ := hc
      change c=16+1+i at eq
      omega
    obtain ⟨out,z,logical,offset,loc,off,typed,run,word,byte,parent,source,locals,objects,addresses,world,events,logs,fnLocals,frame⟩ :=
      parentAt.write_fixed_uint sourceAt F0 fuel (wmod 1) (wmod 42) (by decide) (by decide) (by decide) slots
    exact ⟨out,z,logical,offset,loc,off,typed,run,word,parent,source,objects neighbor (by decide),(addresses 1 (by decide)).trans sourceNeighbor,addresses,locals,world,events,logs,fnLocals⟩

/-- Real fixed endpoint rejection returns Source panic bytes and no typed heap.
Terminal MSTORE has no array guard; no target revert is claimed by this law. -/
theorem endpoint_rejected (fuel : Nat) :
    (Source.writeLoc (E := E0) (Γ := []) F0 fuel (.mem 0 3) (sourceUint (u 42))).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    hp.writeAddr (.index child .fixed (indexValue (wmod 3))) (u 42)=none := by
  exact sourceAt.write_bounds F0 fuel (indexValue (wmod 3)) (u 42) (by decide)

/-- Skipping the headerless rule changes a different cell and misses the write. -/
theorem wrong_dynamic_offset :
    writeMachine machine 10 w[42]≠writeMachine machine 9 w[42] := by
  first
  | solve | simp only [] | omega
  | intro same
    have cell := congrArg (fun m : Machine => m.mem 9) same
    change w[0]=w[42] at cell
    exact (by decide : (w[0] : Evm.Word)≠w[42]) cell

private def words (m : Machine) := image.map fun cv => m.mem cv.1
private def physical (memory : Environment.Memory) := image.map fun cv => Environment.readMemory memory (32*cv.1) 32

/-- Complete ordered represented-word observations include the free pointer,
all fixed child cells (including max), both shared slots and the neighbour. -/
theorem complete_vectors :
    words machine=[w[32],w[7],w[0],Word.val (wmod (W-1)),w[2],w[8],w[8],w[8],w[9]] ∧
    words (writeMachine machine 9 w[42])=[w[32],w[7],w[42],Word.val (wmod (W-1)),w[2],w[8],w[8],w[8],w[9]] ∧
    physical bytes=image.map (fun cv => Semantics.wordBytes cv.2) ∧
    physical (Environment.writeBytes bytes 288 (Semantics.wordBytes 42))=
      image.map (fun cv => Semantics.wordBytes (if cv.1=9 then 42 else cv.2)) := by
  first
  | solve | simp only [] | omega
  | refine ⟨rfl,rfl,?_,?_⟩
    · apply List.map_congr_left
      intro cv hit
      exact image_read cv.1 cv.2 hit
    · apply List.map_congr_left
      intro cv hit
      rcases cv with ⟨c,v⟩
      by_cases selected : c=9
      · subst c
        rw [if_pos rfl]
        simpa only [Environment.wordBytes_length] using Environment.read_written (Semantics.wordBytes 42) 288 bytes
      · rw [if_neg selected]
        have sep : 32*c+32≤288 ∨ 288+(Semantics.wordBytes 42).length≤32*c := by
          simp only [Environment.wordBytes_length]
          simp only [image,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hit
          rcases hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega
        exact (readMemory_write_frame bytes (32*c) 32 288 (Semantics.wordBytes 42) sep).trans (image_read c v hit)

/-- info: 'Solidity.Backend.MemoryOps.Physical.FixedChildControls.complete_vectors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_vectors
/-- info: 'Solidity.Backend.MemoryOps.Physical.FixedChildControls.headerless_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms headerless_write
/-- info: 'Solidity.Backend.MemoryOps.Physical.FixedChildControls.endpoint_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms endpoint_rejected
/-- info: 'Solidity.Backend.MemoryOps.Physical.FixedChildControls.wrong_dynamic_offset' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms wrong_dynamic_offset
end Solidity.Backend.MemoryOps.Physical.FixedChildControls
