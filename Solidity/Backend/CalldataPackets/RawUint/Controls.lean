import Solidity.Backend.CalldataPackets.RawUint.Execution
import Solidity.Source.Semantics

/-! Concrete nonempty-prefix, unequal-word, entry-failure and padding controls.
These execute the Source operations; no desired successful run is assumed. -/
namespace Solidity.Backend.CalldataPackets.RawUint.Controls
open Solidity.Backend.MemoryOps

def E0 : Source.Env := ⟨[]⟩
def initial : Source.EMState E0 [] := (.nil,Source.St.init E0)
def old : Source.EMState E0 [] :=
  ((Source.allocRef (sourceUintMemory [wordValue 99])).run initial).2

def frame (bytes : List UInt8) : Source.Fr :=
  { this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨17,by decide⟩,
    static := false,contract := "RawUint",cd := bytes }

def raw : Source.Fr := frame ([171,205,239]++Source.natBytes 32 7++Source.natBytes 32 42)
def args : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++
  Source.natBytes 32 7++Source.natBytes 32 42
def selectorBytes : List UInt8 := [222,173,190,239]
def full : Source.Fr := frame (selectorBytes++args)
def truncated : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++Source.natBytes 32 7
def zeroArgs : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 0

private theorem args_head : Source.wordAt args 0=32 := by decide

private theorem args_len : Source.wordAt (args.drop 32) 0=2 := by decide

private theorem args_bytes : args.length=128 := by
  simp only [args,Source.natBytes,List.length_append,Source.beBytes_length]

private theorem truncated_head : Source.wordAt truncated 0=32 := by decide

private theorem truncated_len : Source.wordAt (truncated.drop 32) 0=2 := by decide

private theorem truncated_bytes : truncated.length=96 := by
  simp only [truncated,Source.natBytes,List.length_append,Source.beBytes_length]

private theorem zero_head : Source.wordAt zeroArgs 0=32 := by decide

private theorem zero_len : Source.wordAt (zeroArgs.drop 32) 0=0 := by decide

private theorem zero_bytes : zeroArgs.length=64 := by
  simp only [zeroArgs,Source.natBytes,List.length_append,Source.beBytes_length]

theorem old_nonempty : old.2.heap.next=1 ∧
    old.2.heap.get 0=some ⟨ArrayTy,sourceUintMemory [wordValue 99]⟩ := by
  constructor <;> rfl

theorem prefix_values : payload raw 3 2=[wordValue 7,wordValue 42] := by decide

theorem unequal : wordValue 7≠wordValue 42 := by decide

theorem prefix_copy : (Source.cdToMem raw ArrayTy 3 2).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc
        ⟨ArrayTy,sourceUintMemory [wordValue 7,wordValue 42]⟩).1})) := by
  rw [copy_run,prefix_values]

theorem prefix_keeps_old :
    ((Source.cdToMem raw ArrayTy 3 2).run old).2.2.heap.get 0=old.2.heap.get 0 :=
  (copy_observations raw 3 2 old).2.2.1 0 (by decide)

theorem entry_full : Source.cdTail args 0 32=.ok (68,2) := by
  unfold Source.cdTail
  rw [args_head,args_bytes]
  dsimp only
  rw [args_len]
  rfl

theorem entry_values : payload full 68 2=[wordValue 7,wordValue 42] := by decide

theorem entry_frame : full.cd=selectorBytes++args := rfl

theorem full_entry :
    ((Source.EM.lift (Source.cdTail args 0 32)) >>= fun p =>
      Source.cdToMem full ArrayTy p.1 p.2).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc
        ⟨ArrayTy,sourceUintMemory [wordValue 7,wordValue 42]⟩).1})) := by
  rw [guarded_run,entry_full]
  dsimp only
  rw [entry_values]

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

theorem missing_length_word : Source.cdTail [] 0 32=.error (.revert []) :=
  entry_short_head [] 0 (by decide)

theorem zero_entry : Source.cdTail zeroArgs 0 32=.ok (68,0) := by
  unfold Source.cdTail
  rw [zero_head,zero_bytes]
  dsimp only
  rw [zero_len]
  rfl

theorem zero_copy : (Source.cdToMem full ArrayTy 68 0).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc ⟨ArrayTy,sourceUintMemory []⟩).1})) := by
  rw [copy_run]
  rfl

theorem empty_values : payload (frame []) 123 2=[wordValue 0,wordValue 0] := by decide

theorem empty_standalone_copy : (Source.cdToMem (frame []) ArrayTy 123 2).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc
        ⟨ArrayTy,sourceUintMemory [wordValue 0,wordValue 0]⟩).1})) := by
  rw [copy_run,empty_values]

theorem partial_word_values : payload (frame (Source.natBytes 32 7++[18])) 0 2=
    [wordValue 7,wordValue (18*256^31)] := by decide

theorem short_standalone_copy :
    (Source.cdToMem (frame (Source.natBytes 32 7++[18])) ArrayTy 0 2).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc
        ⟨ArrayTy,sourceUintMemory [wordValue 7,wordValue (18*256^31)]⟩).1})) := by
  rw [copy_run,partial_word_values]

def localState : Source.EMState E0 [.array .calldata (.int .u256) none] :=
  (.cons (.cdRef rfl 68 2) .nil,old.2)

theorem local_expression (G : Source.Glob E0) (n : Nat) :
    (Source.evalE G full (n+2) (copyExpr (.here))).run localState=
    (.ok (.val (.memRef rfl localState.2.heap.next)),
      (localState.1,{localState.2 with heap := (localState.2.heap.alloc
        ⟨ArrayTy,sourceUintMemory [wordValue 7,wordValue 42]⟩).1})) := by
  rw [eval_copy G full n localState .here 68 2 rfl,entry_values]

theorem zero_horizon (G : Source.Glob E0) :
    (Source.evalE G full 0 (copyExpr (.here))).run localState=(.error .timeout,localState) := rfl

theorem one_horizon (G : Source.Glob E0) :
    (Source.evalE G full 1 (copyExpr (.here))).run localState=(.error .timeout,localState) := rfl

theorem wrong_order_rejected : payload raw 3 2≠[wordValue 42,wordValue 7] := by decide

def oversized : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 (2^64)

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

theorem entry_does_not_panic : Source.cdTail oversized 0 32≠
    .error (.revert (Source.panicData .alloc)) := by
  rw [oversized_entry]
  intro h
  cases h

theorem zero_guarded_copy :
    ((Source.EM.lift (Source.cdTail zeroArgs 0 32)) >>= fun p =>
      Source.cdToMem (frame (selectorBytes++zeroArgs)) ArrayTy p.1 p.2).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc ⟨ArrayTy,sourceUintMemory []⟩).1})) := by
  rw [guarded_run,zero_entry]
  rfl

private abbrev TargetTy : RefTy := .array (.prim .uint)
def targetRoot : HRef [TargetTy] TargetTy := ⟨0,rfl⟩
def targetHeap : Heap [TargetTy] :=
  (⟨[wordValue 99,wordValue 98,wordValue 97],by decide⟩,())

private theorem target_length : targetHeap.len targetRoot .dyn=3 := by
  simp only [Heap.len,Heap.get,Objs.get,targetRoot,targetHeap,MObj.elems_dyn]
  rfl

theorem raw_transfer :
    (checkedCalldataUints (table (D := E0.layout) raw 3 2) 3 targetHeap targetRoot
      .dyn 0 2 1).map (fun out => MObj.elems .dyn (out.get targetRoot))=
      some [wordValue 99,wordValue 7,wordValue 42] := by
  rw [transfer raw 3 2 targetHeap targetRoot .dyn 0 2 1 ⟨by decide,by decide⟩ (by rw [target_length];decide)]
  simp only [prefix_values,Option.map_some,overwriteSlice_elems]
  simp only [Heap.get,Objs.get,targetHeap,targetRoot,MObj.elems_dyn,replaceSlice]
  rfl

theorem full_width_values : payload (frame (List.replicate 32 255)) 0 1=
    [wordValue (2^256-1)] := by decide

theorem padding_is_right : payload (frame (Source.natBytes 32 7++[18])) 0 2≠
    [wordValue 7,wordValue 18] := by decide

/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.old_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms old_nonempty
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.prefix_values' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_values
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.unequal' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms unequal
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.prefix_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.prefix_keeps_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_keeps_old
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.entry_full' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms entry_full
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.entry_values' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms entry_values
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.entry_frame' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms entry_frame
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.full_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms full_entry
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.entry_truncated' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms entry_truncated
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.truncated_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms truncated_entry
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.missing_length_word' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms missing_length_word
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.zero_entry' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms zero_entry
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.zero_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.empty_values' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms empty_values
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.empty_standalone_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_standalone_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.partial_word_values' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms partial_word_values
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.short_standalone_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_standalone_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.local_expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_expression
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.zero_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_horizon
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.one_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms one_horizon
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.wrong_order_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_order_rejected
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.oversized_entry' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms oversized_entry
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.entry_does_not_panic' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms entry_does_not_panic
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.zero_guarded_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_guarded_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.raw_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_transfer
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.full_width_values' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms full_width_values
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.Controls.padding_is_right' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms padding_is_right
end Solidity.Backend.CalldataPackets.RawUint.Controls
