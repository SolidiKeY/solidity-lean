import Solidity.Yul.Adapters.HeapWriteback
import Solidity.Source.Semantics
namespace Solidity.Yul.Adapters.HeapWriteback.Controls
open Solidity.Backend Solidity.Backend.MemoryOps Solidity.Backend.MemoryOps.Physical
open Solidity.Evm.TryByteImage
private def C : Contract := {vars:=[]}
private abbrev A : Source.STy := .array .memory (.int .u256) none
private abbrev Γ : Source.RCtx := [A,A,.int .u256]
private def E : Source.Env := ⟨[]⟩
private def u (n : Nat) : PrimTy.uint.Denote := Evm.Memory.indexValue (Evm.wmod n)
private def y0 : Source.EMState E [] := (.nil,Source.St.init E)
private def allocated := ((Source.allocRef (E:=E) (Γ:=[]) (sourceUintMemory [u 7])).run y0).2
private def source : Source.EMState E Γ :=
  (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (sourceUint (u 0)) .nil)),allocated.2)
private def F : Source.Fr := {this:=1,sender:=2,value:=0,static:=true,contract:="P6Consumer"}
private abbrev H : HTy := [.array (.prim .uint)]
private def root : HRef H (.array (.prim .uint)) := ⟨0,rfl⟩
private def hp : Heap H := (⟨[u 7],by decide⟩,())
private def m0 : Evm.Machine := {Evm.Machine.init with stack:=[.val (Evm.wmod 77)]}
private def m : Evm.Machine := Evm.Memory.writeMachine (Evm.Memory.writeMachine m0 1 (.val (Evm.wmod 1))) 2 (.val (Evm.wmod 7))
private def sentinel : Environment.Memory := fun k=>if k=127 then 170 else 0
private def bytes : Environment.Memory := Environment.writeBytes
  (Environment.writeBytes sentinel 32 (Semantics.wordBytes 1)) 64 (Semantics.wordBytes 7)
private def image : FrameMem C [] :=
  { st:=State.init C
    key:=⟨3,1,.viaIR,7,u 1,u 2,u 0⟩
    scalar:=by intro R i;cases i
    capacity:=128
    aligned:=⟨4,rfl⟩
    data:=fun i=>bytes i.val
    highWaterWords:=4
    resident:=by decide
    zeroAbove:=by intro i hi;have bound:=i.isLt;omega }

private theorem image_bytes : frameBytes image=bytes := by
  funext k
  change (if h : k<128 then bytes k else 0)=bytes k
  by_cases inside : k<128
  · exact dif_pos inside
  · rw [dif_neg inside]
    change 0=Environment.writeBytes (Environment.writeBytes sentinel 32 (Semantics.wordBytes 1)) 64 (Semantics.wordBytes 7) k
    rw [Environment.writeBytes_frame _ _ k _ (by rw [word_bytes_length];omega)]
    rw [Environment.writeBytes_frame _ _ k _ (by rw [word_bytes_length];omega)]
    change 0=(if k=127 then 170 else 0)
    rw [if_neg (by omega)]

private theorem frame : WordFrame m bytes (fun c=>(False ∨ c=1) ∨ c=2) := by
  have empty : WordFrame m0 sentinel (fun _=>False) := ⟨fun _ h=>h.elim,fun _ h=>h.elim⟩
  exact (empty.write 1 (Evm.wmod 1) (by decide)).write 2 (Evm.wmod 7) (by decide)

private theorem length : hp.len root .dyn=1 := by
  simp only [Heap.len,MObj.elems_dyn]
  rfl
private theorem initial : UintArrayAt source 0 hp root (Evm.wmod 1) m (frameBytes image) := by
  rw [image_bytes]
  constructor
  · unfold SourceUintMemoryAt
    simp only [MObj.elems_dyn]
    rfl
  · refine ⟨by rw [length];decide,by rw [length];rfl,?_⟩
    intro i v value
    simp only [MObj.elems_dyn] at value
    cases i with
    | zero => cases value;exact Evm.ReprV.uint_of rfl
    | succ i => cases i <;> cases value
  · constructor
    · intro c live
      have cell : c=1 ∨ c=2 := by rw [length] at live;change 1≤c ∧ c<1+1+1 at live;omega
      rcases cell with rfl | rfl <;> decide
    · intro c live
      apply frame.cells
      rw [length] at live
      change 1≤c ∧ c<1+1+1 at live
      omega

theorem source_initial_MemOK : Source.MemOK E source.2.heap.ty source := by
  have start : Source.MemOK E y0.2.heap.ty y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have keep := source_uint_alloc_memOK (E:=E) (Γ:=[]) y0.2.heap.ty [u 7] y0 start
  have allocatedOK : Source.MemOK E y0.2.heap.ty allocated := keep.1
  have self := allocatedOK.self
  refine ⟨⟨self.1.1,?_⟩,self.2⟩
  exact ⟨⟨A,rfl,rfl⟩,⟨⟨A,rfl,rfl⟩,trivial,trivial⟩⟩

private def writes : List Write := [(Evm.wmod 0,Evm.wmod 77),(Evm.wmod 0,Evm.wMax),(Evm.wmod 0,Evm.wmod 5)]
private theorem valid : ∀ x∈writes,x.1.val<hp.len root .dyn := by
  intro x hx
  simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl <;> rw [length] <;> decide

theorem actual_sequence : ∃ out z,
    (sourceWrites F 0 0 writes).run source=(.ok (),z) ∧
    UintArrayAt z 0 out root (Evm.wmod 1) (wordWrites (Evm.wmod 1) m writes)
      (byteWrites (Evm.wmod 1) (frameBytes image) writes) ∧
    Source.MemOK E source.2.heap.ty z := by
  obtain ⟨out,z,run,repr,len,locals,other,mem⟩:=run_writes initial F 0 writes valid
  exact ⟨out,z,run,repr,mem _ source_initial_MemOK⟩

theorem late_failure : ∃ out z,
    (sourceWrites F 0 0 writes).run source=(.ok (),z) ∧
    UintArrayAt z 0 out root (Evm.wmod 1) (wordWrites (Evm.wmod 1) m writes)
      (byteWrites (Evm.wmod 1) (frameBytes image) writes) ∧
    (sourceWrites F 0 0 (writes++[(Evm.wmod 1,Evm.wmod 9)])).run source=
      (.error (.revert (Source.panicData .index)),z) ∧
    Source.MemOK E source.2.heap.ty z := by
  obtain ⟨out,z,run,repr,failed,mem⟩:=late_bounds initial F 0 writes valid (Evm.wmod 1) (Evm.wmod 9)
    (by rw [length];decide)
  exact ⟨out,z,run,repr,failed,mem _ source_initial_MemOK⟩

theorem both_aliases (G : Source.Glob E) (n : Nat) : ∃ z,
    (sourceWrites F 0 0 writes).run source=(.ok (),z) ∧
    (Source.evalE G F (n+2) (.indexArray (.local .here)
      (.local (.there (.there .here))) rfl)).run z=
    (Source.evalE G F (n+2) (.indexArray (.local (.there .here))
      (.local (.there (.there .here))) rfl)).run z := by
  obtain ⟨out,z,same,run,reads⟩:=retained_aliases initial F 0 writes valid (Evm.wmod 0)
    (.there (.there .here)) rfl (by rw [length];decide)
  exact ⟨z,run,(reads G n .here rfl).trans (reads G n (.there .here) rfl).symm⟩

theorem whole_heap_identity :
    source.2.heap.write 0 (sourceUintMemory [u 7]) rfl=source.2.heap :=
  heap_write_same _ _ _ rfl rfl

private def observe (xs : List Write) : Nat × Nat × Nat :=
  let bytes:=byteWrites (Evm.wmod 1) (frameBytes image) xs
  (Source.beValue (Environment.readMemory bytes 64 32),bytes 127 |>.toNat,Source.beValue (Environment.readMemory bytes 32 32))
/-- info: (5, 170, 1) -/
#guard_msgs in #eval observe writes
/-- info: (77, 170, 1) -/
#guard_msgs in #eval observe writes.reverse
/-- info: false -/
#guard_msgs in #eval decide ((observe writes).1=77)
/-- One direct readLoc observation; actual two-local evalE alias control is both_aliases above. -/
private def sourceObservation (xs : List Write) : Nat × Nat :=
  let result:=(sourceWrites F 0 0 xs).run source
  let status:= match result.1 with | .ok _=>1 | .error _=>0
  let z:=result.2
  let read : Nat := match (Source.readLoc (E:=E) (Γ:=Γ) F (τ:=.int .u256) (.mem 0 0)).run z with
    | (.ok v,_)=> (calldataUint (.val v)).val.toNat
    | _=>999
  (status,read)
/-- info: (1, 5) -/
#guard_msgs in #eval sourceObservation writes
/-- info: (0, 5) -/
#guard_msgs in #eval sourceObservation (writes++[(Evm.wmod 1,Evm.wmod 9)])
/-- info: false -/
#guard_msgs in #eval decide ((sourceObservation (writes++[(Evm.wmod 1,Evm.wmod 9)])).2=7)
private def accepted : List Write := [(Evm.wmod 0,Evm.wmod 9),(Evm.wmod 0,Evm.wmod 17)]
private def withLateFailure : List Write :=
  accepted++[(Evm.wmod 1,Evm.wmod 88),(Evm.wmod 0,Evm.wmod 99)]

/-- Complete error plus coupled reached images; the suffix after the first
bad index cannot overwrite the caller's successful repeated-write prefix. -/
theorem checked_failure : ∃ (out : Heap H) (z : Source.EMState E Γ),
    (sourceWrites F 0 0 accepted).run source=(.ok (),z) ∧
    (sourceWrites F 0 0 withLateFailure).run source=
      (.error (.revert (Source.panicData .index)),z) ∧
    UintArrayAt z 0 out root (Evm.wmod 1) (wordWrites (Evm.wmod 1) m accepted)
      (byteWrites (Evm.wmod 1) (frameBytes image) accepted) ∧
    Source.MemOK E source.2.heap.ty z := by
  obtain ⟨out,z,run,failed,repr,len,locals,other,mem⟩ := run_checked initial F 0 withLateFailure
  have pre : withLateFailure.takeWhile (fun x=>decide (x.1.val<hp.len root .dyn))=accepted := by
    rw [length]
    decide
  have rest : withLateFailure.dropWhile (fun x=>decide (x.1.val<hp.len root .dyn))≠[] := by
    rw [length]
    decide
  rw [pre] at run repr
  rw [if_neg rest] at failed
  exact ⟨out,z,run,failed,repr,mem _ source_initial_MemOK⟩

/-- info: (0, 17) -/
#guard_msgs in #eval sourceObservation withLateFailure
/-- info: (17, 170, 1) -/
#guard_msgs in #eval observe accepted
/-- info: (false, false, false) -/
#guard_msgs in #eval
  ((sourceObservation withLateFailure).2==99,
   (sourceObservation withLateFailure).2==7,
   (observe accepted).2.1==0)
/-- info: true -/
#guard_msgs in #eval
  match (sourceWrites F 0 0 withLateFailure).run source with
  | (.error (.revert payload),_) => payload==Source.panicData .index
  | _ => false

/-- Both actual retained local expressions observe the reached prefix after
late failure, at every positive indexing horizon, with exact physical bytes. -/
theorem checked_aliases (G : Source.Glob E) (n : Nat) :
    let result := (sourceWrites F 0 0 withLateFailure).run source
    ∃ value : PrimTy.uint.Denote,
      result.1=.error (.revert (Source.panicData .index)) ∧
      (Source.evalE G F (n+2) (.indexArray (.local .here)
        (.local (.there (.there .here))) rfl)).run result.2=
        (.ok (.val (sourceUint value)),result.2) ∧
      (Source.evalE G F (n+2) (.indexArray (.local (.there .here))
        (.local (.there (.there .here))) rfl)).run result.2=
        (.ok (.val (sourceUint value)),result.2) ∧
      Environment.readMemory (byteWrites (Evm.wmod 1) (frameBytes image) accepted) 64 32=
        Semantics.wordBytes value.val.toNat ∧
      Source.MemOK E source.2.heap.ty result.2 := by
  obtain ⟨value,status,read,physical,aliases,mem⟩ := checked_reads initial F 0 withLateFailure
    (Evm.wmod 0) (.there (.there .here)) rfl (by rw [length];decide)
  have pre : withLateFailure.takeWhile (fun x=>decide (x.1.val<hp.len root .dyn))=accepted := by
    rw [length]
    decide
  have rest : withLateFailure.dropWhile (fun x=>decide (x.1.val<hp.len root .dyn))≠[] := by
    rw [length]
    decide
  rw [if_neg rest] at status
  rw [pre] at physical
  exact ⟨value,status,aliases G n .here rfl,aliases G n (.there .here) rfl,physical,mem _ source_initial_MemOK⟩

end Solidity.Yul.Adapters.HeapWriteback.Controls