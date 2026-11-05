import Solidity.Backend.CalldataPackets.RawBool.Execution
import Solidity.Source.Semantics

/-! Positive and negative controls execute the published Source operations on
raw bytes. Old heaps and aliases are inhabited; dirty words cannot be silently
cleaned. Entry refusal is distinct from standalone zero-padding behavior. -/
namespace Solidity.Backend.CalldataPackets.RawBool.Controls
open Solidity.Backend.MemoryOps

def E0 : Source.Env := ⟨[]⟩
def initial : Source.EMState E0 [] := (.nil,Source.St.init E0)
def old : Source.EMState E0 [] :=
  ((Source.allocRef (sourceBoolMemory [true,false,true])).run initial).2

def frame (bytes : List UInt8) : Source.Fr :=
  { this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨17,by decide⟩,
    static := false,contract := "RawBool",cd := bytes }

def raw : Source.Fr := frame ([171,205,239]++Source.natBytes 32 0++Source.natBytes 32 1)
def dirty : Source.Fr := frame ([171,205,239]++Source.natBytes 32 0++Source.natBytes 32 2++Source.natBytes 32 1)
def selectorBytes : List UInt8 := [222,173,190,239]
def args : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++
  Source.natBytes 32 0++Source.natBytes 32 1
def badArgs : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++
  Source.natBytes 32 0++Source.natBytes 32 2
def truncated : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++Source.natBytes 32 0
def zeroArgs : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 0
def oversized : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 (2^64)
def full : Source.Fr := frame (selectorBytes++args)
def badFull : Source.Fr := frame (selectorBytes++badArgs)

private theorem entry_guard (data : List UInt8) (n : Nat)
    (head : Source.wordAt data 0=32) (len : Source.wordAt (data.drop 32) 0=n)
    (bytes : data.length=64+32*n) (small : n<2^64) : Source.cdTail data 0 32=.ok (68,n) := by
  rw [Source.cdTail,head,if_neg (by omega),len,if_neg (by omega),if_pos (by omega)]
  rfl

theorem old_nonempty : old.2.heap.next=1 ∧
    old.2.heap.get 0=some ⟨ArrayTy,sourceBoolMemory [true,false,true]⟩ := by
  constructor <;> rfl

theorem prefix_valid : valid raw 3 2=true := by decide

theorem prefix_values : payload raw 3 2=[false,true] := by decide

theorem unequal : (false : Bool)≠true := by decide

theorem prefix_copy : (Source.cdToMem raw ArrayTy 3 2).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc
        ⟨ArrayTy,sourceBoolMemory [false,true]⟩).1})) := by
  rw [copy_run,if_pos prefix_valid,prefix_values]

theorem prefix_keeps_old :
    ((Source.cdToMem raw ArrayTy 3 2).run old).2.2.heap.get 0=old.2.heap.get 0 :=
  (copy_observations raw 3 2 old).1 0 (by decide)

theorem dirty_validation : valid dirty 3 3=false :=
  dirty_at dirty 3 3 1 (by decide) (by decide)

theorem dirty_copy : (Source.cdToMem dirty ArrayTy 3 3).run old=
    (.error (.revert []),old) := copy_dirty dirty 3 3 old dirty_validation

/-- The raw Boolean payload alone would mask two to false; validation prevents
that tempting but incorrect successful allocation. -/
theorem dirty_not_cleaned : payload dirty 3 3=[false,false,true] ∧
    (Source.cdToMem dirty ArrayTy 3 3).run old=(.error (.revert []),old) :=
  ⟨by decide,dirty_copy⟩

theorem reached_prefix :
    ([0].mapM (fun j => Source.EM.lift (E := E0) (Γ := [])
      (Source.decodeWord E0.layout (Source.cdWordAt dirty (3+32*j)) .bool))).run old=
      (.ok [Source.Val.bool false],old) ∧
    (Source.EM.lift (E := E0) (Γ := [])
      (Source.decodeWord E0.layout (Source.cdWordAt dirty 35) .bool)).run old=
      (.error (.revert []),old) := by
  have reached := source_raw_bool_copy_first_error dirty 3 3 old [0] [2] 1 rfl
    (by intro j hj;simp only [List.mem_cons,List.not_mem_nil,or_false] at hj;subst j;decide)
    (by decide)
  exact ⟨reached.1,reached.2.1⟩

def aliased : Source.EMState E0 [ArrayTy,ArrayTy] :=
  (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil),old.2)

theorem dirty_keeps_aliases : (Source.cdToMem dirty ArrayTy 3 3).run aliased=
    (.error (.revert []),aliased) := copy_dirty dirty 3 3 aliased dirty_validation

theorem maximum_dirty : valid (frame (List.replicate 32 255)) 0 1=false ∧
    (Source.cdToMem (frame (List.replicate 32 255)) ArrayTy 0 1).run old=
      (.error (.revert []),old) := by
  have bad : valid (frame (List.replicate 32 255)) 0 1=false := by decide
  exact ⟨bad,copy_dirty _ _ _ _ bad⟩

theorem entry_full : Source.cdTail args 0 32=.ok (68,2) :=
  entry_guard args 2 (by decide) (by decide)
    (by simp only [args,Source.natBytes,List.length_append,Source.beBytes_length]) (by decide)

theorem entry_values : payload full 68 2=[false,true] := by decide

theorem entry_valid : valid full 68 2=true := by decide

theorem full_entry :
    ((Source.EM.lift (Source.cdTail args 0 32)) >>= fun p =>
      Source.cdToMem full ArrayTy p.1 p.2).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc
        ⟨ArrayTy,sourceBoolMemory [false,true]⟩).1})) := by
  rw [guarded_run,entry_full]
  dsimp only
  rw [if_pos entry_valid,entry_values]

theorem bad_entry_guard_passes : Source.cdTail badArgs 0 32=.ok (68,2) :=
  entry_guard badArgs 2 (by decide) (by decide)
    (by simp only [badArgs,Source.natBytes,List.length_append,Source.beBytes_length]) (by decide)

theorem bad_entry :
    ((Source.EM.lift (Source.cdTail badArgs 0 32)) >>= fun p =>
      Source.cdToMem badFull ArrayTy p.1 p.2).run old=(.error (.revert []),old) := by
  rw [guarded_run,bad_entry_guard_passes]
  rfl

theorem missing_length_word : Source.cdTail [] 0 32=.error (.revert []) := by
  simp only [Source.cdTail,if_pos (show ([] : List UInt8).length<Source.wordAt [] 0+32 from by
    simp only [List.length_nil];omega)]

private theorem truncated_head : Source.wordAt truncated 0=32 := by decide
private theorem truncated_len : Source.wordAt (truncated.drop 32) 0=2 := by decide
private theorem truncated_bytes : truncated.length=96 := by
  simp only [truncated,Source.natBytes,List.length_append,Source.beBytes_length]

theorem entry_truncated : Source.cdTail truncated 0 32=.error (.revert []) := by
  unfold Source.cdTail
  rw [truncated_head,truncated_bytes]
  dsimp only
  rw [truncated_len]
  rfl

theorem truncated_entry :
    ((Source.EM.lift (Source.cdTail truncated 0 32)) >>= fun p =>
      Source.cdToMem (frame (selectorBytes++truncated)) ArrayTy p.1 p.2).run old=
      (.error (.revert []),old) := by
  rw [guarded_run,entry_truncated]

theorem truncated_standalone :
    (Source.cdToMem (frame (selectorBytes++truncated)) ArrayTy 68 2).run old=
      (.ok (.val (.memRef rfl old.2.heap.next)),
        (old.1,{old.2 with heap := (old.2.heap.alloc
          ⟨ArrayTy,sourceBoolMemory [false,false]⟩).1})) := by
  rw [copy_run,if_pos (show valid (frame (selectorBytes++truncated)) 68 2=true from by decide)]
  rfl

theorem zero_entry : Source.cdTail zeroArgs 0 32=.ok (68,0) :=
  entry_guard zeroArgs 0 (by decide) (by decide)
    (by simp only [zeroArgs,Source.natBytes,List.length_append,Source.beBytes_length]) (by decide)

theorem zero_guarded_copy :
    ((Source.EM.lift (Source.cdTail zeroArgs 0 32)) >>= fun p =>
      Source.cdToMem (frame (selectorBytes++zeroArgs)) ArrayTy p.1 p.2).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc ⟨ArrayTy,sourceBoolMemory []⟩).1})) := by
  rw [guarded_run,zero_entry]
  rfl

theorem zero_copy_even_dirty : (Source.cdToMem dirty ArrayTy 3 0).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc ⟨ArrayTy,sourceBoolMemory []⟩).1})) := by
  rw [copy_run]
  rfl

theorem empty_standalone_copy : (Source.cdToMem (frame []) ArrayTy 123 2).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc
        ⟨ArrayTy,sourceBoolMemory [false,false]⟩).1})) := by
  rw [copy_run,if_pos (show valid (frame []) 123 2=true from by decide)]
  rfl

theorem partial_word_dirty : valid (frame [1]) 0 1=false ∧
    (Source.cdToMem (frame [1]) ArrayTy 0 1).run old=(.error (.revert []),old) := by
  have bad : valid (frame [1]) 0 1=false := by decide
  exact ⟨bad,copy_dirty _ _ _ _ bad⟩

private theorem oversized_head : Source.wordAt oversized 0=32 := by decide
private theorem oversized_len : Source.wordAt (oversized.drop 32) 0=2^64 := by decide
private theorem oversized_bytes : oversized.length=64 := by
  simp only [oversized,Source.natBytes,List.length_append,Source.beBytes_length]

theorem oversized_entry : Source.cdTail oversized 0 32=.error (.revert []) := by
  unfold Source.cdTail
  rw [oversized_head,oversized_bytes]
  dsimp only
  rw [oversized_len]
  rfl

theorem oversized_guarded_copy :
    ((Source.EM.lift (Source.cdTail oversized 0 32)) >>= fun p =>
      Source.cdToMem (frame (selectorBytes++oversized)) ArrayTy p.1 p.2).run old=
      (.error (.revert []),old) := by
  rw [guarded_run,oversized_entry]

theorem dirty_does_not_panic : (Source.cdToMem dirty ArrayTy 3 3).run old≠
    (.error (.revert (Source.panicData .alloc)),old) := by
  rw [dirty_copy]
  intro h
  cases h

def localState : Source.EMState E0 [.array .calldata .bool none] :=
  (.cons (.cdRef rfl 68 2) .nil,old.2)

theorem local_expression (G : Source.Glob E0) (n : Nat) :
    (Source.evalE G full (n+2) (copyExpr (.here))).run localState=
    (.ok (.val (.memRef rfl localState.2.heap.next)),
      (localState.1,{localState.2 with heap := (localState.2.heap.alloc
        ⟨ArrayTy,sourceBoolMemory [false,true]⟩).1})) := by
  rw [eval_copy G full n localState .here 68 2 rfl,if_pos entry_valid,entry_values]

theorem local_dirty (G : Source.Glob E0) (n : Nat) :
    (Source.evalE G badFull (n+2) (copyExpr (.here))).run localState=
      (.error (.revert []),localState) := by
  rw [eval_copy G badFull n localState .here 68 2 rfl]
  rfl

theorem zero_horizon (G : Source.Glob E0) :
    (Source.evalE G full 0 (copyExpr (.here))).run localState=(.error .timeout,localState) := rfl

theorem one_horizon (G : Source.Glob E0) :
    (Source.evalE G full 1 (copyExpr (.here))).run localState=(.error .timeout,localState) := rfl

theorem wrong_order_rejected : payload raw 3 2≠[true,false] := by decide

private abbrev TargetTy : RefTy := .array (.prim .bool)
def targetRoot : HRef [TargetTy] TargetTy := ⟨0,rfl⟩
def targetHeap : Heap [TargetTy] := (⟨[true,true,false],by decide⟩,())
private theorem target_length : targetHeap.len targetRoot .dyn=3 := by
  simp only [Heap.len,Heap.get,Objs.get,targetRoot,targetHeap,MObj.elems_dyn]
  rfl

theorem raw_transfer :
    (checkedCalldataBools (table (D := E0.layout) raw 3 2) 3 targetHeap targetRoot
      .dyn 0 2 1).map (fun out => MObj.elems .dyn (out.get targetRoot))=
      some [true,false,true] := by
  rw [transfer raw 3 2 targetHeap targetRoot .dyn 0 2 1 ⟨by decide,by decide⟩
    (by rw [target_length];decide),if_pos prefix_valid]
  simp only [prefix_values,Option.map_some,overwriteSlice_elems]
  simp only [Heap.get,Objs.get,targetHeap,targetRoot,MObj.elems_dyn,replaceSlice]
  rfl

theorem dirty_transfer_rejected :
    checkedCalldataBools (table (D := E0.layout) dirty 3 3) 3 targetHeap targetRoot
      .dyn 0 2 1=none := by
  rw [transfer dirty 3 3 targetHeap targetRoot .dyn 0 2 1 ⟨by decide,by decide⟩
    (by rw [target_length];decide),dirty_validation]
  rfl

theorem highbit_dirty :
    valid (frame (Source.natBytes 32 (2^255+1))) 0 1=false ∧
    (Source.cdToMem (frame (Source.natBytes 32 (2^255+1))) ArrayTy 0 1).run old=
      (.error (.revert []),old) := by
  have bad : valid (frame (Source.natBytes 32 (2^255+1))) 0 1=false := by decide
  exact ⟨bad,copy_dirty _ _ _ _ bad⟩

theorem wrong_table_offset : calldataBools (D := E0.layout) (table raw 3 2) 4=none := rfl

theorem target_slice_rejected :
    checkedCalldataBools (table (D := E0.layout) raw 3 2) 3 targetHeap targetRoot
      .dyn 0 3 0=none := by
  unfold checkedCalldataBools
  rw [table_bools,if_pos prefix_valid]
  simp only [Bind.bind,Option.bind,payload_length,dif_neg (by decide : ¬(0≤3 ∧ 3≤2))]

theorem target_room_rejected :
    checkedCalldataBools (table (D := E0.layout) raw 3 2) 3 targetHeap targetRoot
      .dyn 0 2 2=none := by
  unfold checkedCalldataBools
  rw [table_bools,if_pos prefix_valid]
  simp only [Bind.bind,Option.bind,payload_length,dif_pos (by decide : 0≤2 ∧ 2≤2),
    dif_neg (show ¬2+(2-0)≤targetHeap.len targetRoot .dyn from by rw [target_length];decide)]


/-- info: '_private.Solidity.Backend.CalldataPackets.RawBool.Controls.0.Solidity.Backend.CalldataPackets.RawBool.Controls.entry_guard' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms entry_guard
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.old_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms old_nonempty
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.prefix_valid' does not depend on any axioms -/
#guard_msgs in
#print axioms prefix_valid
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.prefix_values' does not depend on any axioms -/
#guard_msgs in
#print axioms prefix_values
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.unequal' does not depend on any axioms -/
#guard_msgs in
#print axioms unequal
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.prefix_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms prefix_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.prefix_keeps_old' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms prefix_keeps_old
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.dirty_validation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dirty_validation
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.dirty_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dirty_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.dirty_not_cleaned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dirty_not_cleaned
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.reached_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reached_prefix
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.dirty_keeps_aliases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dirty_keeps_aliases
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.maximum_dirty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms maximum_dirty
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.entry_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms entry_full
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.entry_values' does not depend on any axioms -/
#guard_msgs in
#print axioms entry_values
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.entry_valid' does not depend on any axioms -/
#guard_msgs in
#print axioms entry_valid
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.full_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms full_entry
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.bad_entry_guard_passes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bad_entry_guard_passes
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.bad_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bad_entry
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.missing_length_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms missing_length_word
/-- info: '_private.Solidity.Backend.CalldataPackets.RawBool.Controls.0.Solidity.Backend.CalldataPackets.RawBool.Controls.truncated_head' does not depend on any axioms -/
#guard_msgs in
#print axioms truncated_head
/-- info: '_private.Solidity.Backend.CalldataPackets.RawBool.Controls.0.Solidity.Backend.CalldataPackets.RawBool.Controls.truncated_len' does not depend on any axioms -/
#guard_msgs in
#print axioms truncated_len
/-- info: '_private.Solidity.Backend.CalldataPackets.RawBool.Controls.0.Solidity.Backend.CalldataPackets.RawBool.Controls.truncated_bytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms truncated_bytes
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.entry_truncated' depends on axioms: [propext] -/
#guard_msgs in
#print axioms entry_truncated
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.truncated_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms truncated_entry
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.truncated_standalone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms truncated_standalone
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.zero_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms zero_entry
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.zero_guarded_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_guarded_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.zero_copy_even_dirty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_copy_even_dirty
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.empty_standalone_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_standalone_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.partial_word_dirty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms partial_word_dirty
/-- info: '_private.Solidity.Backend.CalldataPackets.RawBool.Controls.0.Solidity.Backend.CalldataPackets.RawBool.Controls.oversized_head' does not depend on any axioms -/
#guard_msgs in
#print axioms oversized_head
/-- info: '_private.Solidity.Backend.CalldataPackets.RawBool.Controls.0.Solidity.Backend.CalldataPackets.RawBool.Controls.oversized_len' does not depend on any axioms -/
#guard_msgs in
#print axioms oversized_len
/-- info: '_private.Solidity.Backend.CalldataPackets.RawBool.Controls.0.Solidity.Backend.CalldataPackets.RawBool.Controls.oversized_bytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms oversized_bytes
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.oversized_entry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms oversized_entry
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.oversized_guarded_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms oversized_guarded_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.dirty_does_not_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dirty_does_not_panic
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.local_expression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms local_expression
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.local_dirty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms local_dirty
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.zero_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_horizon
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.one_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms one_horizon
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.wrong_order_rejected' does not depend on any axioms -/
#guard_msgs in
#print axioms wrong_order_rejected
/-- info: '_private.Solidity.Backend.CalldataPackets.RawBool.Controls.0.Solidity.Backend.CalldataPackets.RawBool.Controls.target_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms target_length
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.raw_transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms raw_transfer
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.dirty_transfer_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dirty_transfer_rejected
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.highbit_dirty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms highbit_dirty
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.wrong_table_offset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_table_offset
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.target_slice_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_slice_rejected
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.Controls.target_room_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_room_rejected

end Solidity.Backend.CalldataPackets.RawBool.Controls
