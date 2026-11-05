import Solidity.Backend.CalldataPackets.RawBytesN.Execution
import Solidity.Source.Semantics

/-! Raw, unequal bytes1 words and dirty-tail controls execute the actual copy. -/
namespace Solidity.Backend.CalldataPackets.RawBytesN.Controls
def E0 : Source.Env := ⟨[]⟩
def h1 : 1 ≤ 1 ∧ 1 ≤ 32 := by decide
def initial : Source.EMState E0 [] := (.nil,Source.St.init E0)
def value (b : Nat) : Source.Val E0.layout (.fixedBytes 1 h1) :=
  Source.mkBytes (Source.natBytes 32 (b*2^248))
def old : Source.EMState E0 [] :=
  ((Source.allocRef (memory [value 99])).run initial).2

def frame (bs : List UInt8) : Source.Fr :=
  { this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨17,by decide⟩,
    static := false,contract := "RawBytesN",cd := bs }
def clean : Source.Fr := frame ([171,205,239]++
  Source.natBytes 32 (7*2^248)++Source.natBytes 32 (42*2^248))
def dirty : Source.Fr := frame ([171,205,239]++
  Source.natBytes 32 (7*2^248)++Source.natBytes 32 (42*2^248+1))

theorem clean_decoded : decoded E0.layout 1 h1 clean 3 2=.ok [value 7,value 42] := by rfl

theorem dirty_decoded : decoded E0.layout 1 h1 dirty 3 2=.error (.revert []) := by rfl

theorem clean_copy : (Source.cdToMem clean (ArrayTy 1 h1) 3 2).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc
        ⟨ArrayTy 1 h1,memory [value 7,value 42]⟩).1})) := by
  rw [copy_run,clean_decoded]

/-- A later dirty element rolls back the entire copy, preserving the old heap. -/
theorem dirty_copy : (Source.cdToMem dirty (ArrayTy 1 h1) 3 2).run old=
    (.error (.revert []),old) := by rw [copy_run,dirty_decoded]

theorem prefix_nonempty : old.2.heap.next=1 := by rfl

theorem prefix_preserved :
    ((Source.cdToMem clean (ArrayTy 1 h1) 3 2).run old).2.2.heap.get 0=old.2.heap.get 0 := by
  rw [clean_copy]
  exact Source.Heap.alloc_other _ _ (by decide)

theorem zero_copy : (Source.cdToMem dirty (ArrayTy 1 h1) 3 0).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc
        ⟨ArrayTy 1 h1,memory ([] : List (Source.Val E0.layout (.fixedBytes 1 h1)))⟩).1})) := by
  rw [copy_run]
  rfl

/-- Beyond-EOF standalone reads pad to zero, independently of entry guards. -/
theorem padded_decode : decoded E0.layout 1 h1 (frame []) 100 1=.ok [value 0] := by rfl

theorem dirty_low_byte : Source.decodeWord E0.layout (42*2^248+1) (.fixedBytes 1 h1)=
    .error (.revert []) := by rfl

theorem wrong_order : [value 7,value 42]≠[value 42,value 7] := by
  intro same
  have first : value 7=value 42 := (List.cons.inj same).1
  have byte : (7 : UInt8)=42 := congrArg (fun v => match v with
    | .fixedBytes bs _ => bs.headD 0
    | _ => 0) first
  exact (by decide : (7 : UInt8)≠42) byte

/-- Even a clean standalone padded copy cannot bypass the entry head guard. -/
theorem short_entry :
    ((Source.EM.lift (Source.cdTail [] 0 32)) >>= fun p =>
      Source.cdToMem clean (ArrayTy 1 h1) p.1 p.2).run old=(.error (.revert []),old) := by
  have head : ([] : List UInt8).length < Source.wordAt [] 0+32 := by
    simp only [List.length_nil]
    omega
  have short : Source.cdTail [] 0 32=.error (.revert []) := by
    simp only [Source.cdTail,if_pos head]
  rw [guarded_run,short]

def selectorBytes : List UInt8 := [222,173,190,239]
def args : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++
  Source.natBytes 32 (7*2^248)++Source.natBytes 32 (42*2^248)
def full : Source.Fr := frame (selectorBytes++args)

private theorem args_head : Source.wordAt args 0=32 := by decide
private theorem args_len : Source.wordAt (args.drop 32) 0=2 := by decide
private theorem args_bytes : args.length=128 := by
  simp only [args,Source.natBytes,List.length_append,Source.beBytes_length]

theorem entry_full : Source.cdTail args 0 32=.ok (68,2) := by
  unfold Source.cdTail
  rw [args_head,args_bytes]
  dsimp only
  rw [args_len]
  rfl

theorem entry_values : decoded E0.layout 1 h1 full 68 2=.ok [value 7,value 42] := by rfl

theorem full_entry :
    ((Source.EM.lift (Source.cdTail args 0 32)) >>= fun p =>
      Source.cdToMem full (ArrayTy 1 h1) p.1 p.2).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc
        ⟨ArrayTy 1 h1,memory [value 7,value 42]⟩).1})) := by
  rw [guarded_run,entry_full]
  dsimp only
  rw [entry_values]

/-- Width32 has no low-byte padding to reject. -/
theorem width32_accepts_low_one :
    Source.decodeWord E0.layout 1 (.fixedBytes 32 (by decide))=
      .ok (Source.mkBytes (n := 32) (h := by decide) (Source.natBytes 32 1)) := by rfl

def dirtyArgs : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++
  Source.natBytes 32 (7*2^248)++Source.natBytes 32 (42*2^248+1)
def fullDirty : Source.Fr := frame (selectorBytes++dirtyArgs)

private theorem dirty_head : Source.wordAt dirtyArgs 0=32 := by decide
private theorem dirty_len : Source.wordAt (dirtyArgs.drop 32) 0=2 := by decide
private theorem dirty_bytes : dirtyArgs.length=128 := by
  simp only [dirtyArgs,Source.natBytes,List.length_append,Source.beBytes_length]

theorem entry_dirty_span_valid : Source.cdTail dirtyArgs 0 32=.ok (68,2) := by
  unfold Source.cdTail
  rw [dirty_head,dirty_bytes]
  dsimp only
  rw [dirty_len]
  rfl

theorem entry_dirty_values : decoded E0.layout 1 h1 fullDirty 68 2=.error (.revert []) := by rfl

theorem full_dirty_entry :
    ((Source.EM.lift (Source.cdTail dirtyArgs 0 32)) >>= fun p =>
      Source.cdToMem fullDirty (ArrayTy 1 h1) p.1 p.2).run old=(.error (.revert []),old) := by
  rw [guarded_run,entry_dirty_span_valid]
  dsimp only
  rw [entry_dirty_values]

/-- Width31 still validates its final low byte. -/
theorem width31_rejects_low_one :
    Source.decodeWord E0.layout 1 (.fixedBytes 31 (by decide))=.error (.revert []) := by rfl

def hugeArgs : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 (2^64)
def shortArgs : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 1
private theorem huge_head : Source.wordAt hugeArgs 0=32 := by decide
private theorem huge_len : Source.wordAt (hugeArgs.drop 32) 0=2^64 := by decide
private theorem huge_bytes : hugeArgs.length=64 := by
  simp only [hugeArgs,Source.natBytes,List.length_append,Source.beBytes_length]
private theorem short_head : Source.wordAt shortArgs 0=32 := by decide
private theorem short_len : Source.wordAt (shortArgs.drop 32) 0=1 := by decide
private theorem short_bytes : shortArgs.length=64 := by
  simp only [shortArgs,Source.natBytes,List.length_append,Source.beBytes_length]

theorem entry_huge : Source.cdTail hugeArgs 0 32=.error (.revert []) := by
  unfold Source.cdTail
  rw [huge_head,huge_bytes]
  dsimp only
  rw [huge_len]
  rfl

theorem entry_span : Source.cdTail shortArgs 0 32=.error (.revert []) := by
  unfold Source.cdTail
  rw [short_head,short_bytes]
  dsimp only
  rw [short_len]
  rfl

theorem huge_preserves_state :
    ((Source.EM.lift (Source.cdTail hugeArgs 0 32)) >>= fun p =>
      Source.cdToMem full (ArrayTy 1 h1) p.1 p.2).run old=(.error (.revert []),old) := by
  rw [guarded_run,entry_huge]

theorem span_preserves_state :
    ((Source.EM.lift (Source.cdTail shortArgs 0 32)) >>= fun p =>
      Source.cdToMem full (ArrayTy 1 h1) p.1 p.2).run old=(.error (.revert []),old) := by
  rw [guarded_run,entry_span]

#print axioms huge_preserves_state
#print axioms span_preserves_state
#print axioms clean_copy
#print axioms dirty_copy
#print axioms prefix_preserved
#print axioms zero_copy
#print axioms wrong_order
#print axioms full_entry
#print axioms full_dirty_entry
#print axioms width31_rejects_low_one
#print axioms width32_accepts_low_one
end Solidity.Backend.CalldataPackets.RawBytesN.Controls
