import Solidity.Backend.CalldataPackets.RawAddress.Execution

/-! Raw-byte positive and negative controls. No successful run, decoder result
or target representation is supplied as a hypothesis. -/
namespace Solidity.Backend.CalldataPackets.RawAddress.Controls

def E0 : Source.Env := ⟨[]⟩
def initial : Source.EMState E0 [] := (.nil,⟨⟨⟨fun _ => Source.Account.empty _⟩,Source.Transient.empty,[]⟩,
    Source.Heap.empty,[],[],⟨[],.nil⟩,Source.FailureExecution.Cursor.empty⟩)
def addr (n : Nat) : Source.Val E0.layout (.address false) :=
  .address ⟨n % 2^160,Nat.mod_lt _ (by decide)⟩
def old : Source.EMState E0 [] :=
  ((Source.allocRef (memory [addr 99])).run initial).2

def frame (bytes : List UInt8) : Source.Fr :=
  { this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨17,by decide⟩,
    static := false,contract := "RawAddress",cd := bytes }

def raw : Source.Fr := frame ([171,205,239]++Source.natBytes 32 7++Source.natBytes 32 42)
def dirty : Source.Fr := frame ([171,205,239]++Source.natBytes 32 7++Source.natBytes 32 (2^160))
def args : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++
  Source.natBytes 32 7++Source.natBytes 32 42
def selectorBytes : List UInt8 := [222,173,190,239]
def full : Source.Fr := frame (selectorBytes++args)
def dirtyArgs : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++
  Source.natBytes 32 7++Source.natBytes 32 (2^160)
def dirtyFull : Source.Fr := frame (selectorBytes++dirtyArgs)
def truncated : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++Source.natBytes 32 7
def oversized : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 (2^64)

theorem old_nonempty : old.2.heap.next=1 ∧
    old.2.heap.get 0=some ⟨ArrayTy false,memory [addr 99]⟩ := by
  constructor <;> rfl

theorem prefix_values : payload E0.layout false raw 3 2=.ok [addr 7,addr 42] := by rfl

theorem prefix_copy : (Source.cdToMem raw (ArrayTy false) 3 2).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc
        ⟨ArrayTy false,memory [addr 7,addr 42]⟩).1})) := by
  rw [copy_run,prefix_values]

theorem prefix_keeps_old :
    ((Source.cdToMem raw (ArrayTy false) 3 2).run old).2.2.heap.get 0=old.2.heap.get 0 :=
  (copy_observations false raw 3 2 old _ prefix_values).2.2.1 0 (by decide)

theorem wrong_order_rejected : payload E0.layout false raw 3 2≠.ok [addr 42,addr 7] := by
  rw [prefix_values]
  intro h
  have values : addr 7=addr 42 := (List.cons.inj (Except.ok.inj h)).1
  have observed := congrArg (fun v : Source.Val E0.layout (.address false) => v.word) values
  have different : (some (Source.toWord 7) : Option Solidity.Roadmap.Word)≠some (Source.toWord 42) := by decide
  exact different observed

theorem dirty_second_word : Source.cdWordAt dirty (3+32*1)=2^160 := by rfl

theorem dirty_after_valid_prefix : (Source.cdToMem dirty (ArrayTy false) 3 2).run old=
    (.error (.revert []),old) := by
  apply copy_dirty false dirty 3 2 old 1 (by decide)
  simpa only [dirty_second_word] using (Nat.le_refl (2^160))

theorem high_bits_are_not_masked : payload E0.layout false dirty 3 2≠.ok [addr 7,addr 0] := by
  have failed : payload E0.layout false dirty 3 2=.error (.revert []) := rfl
  rw [failed]
  intro h
  cases h

theorem boundary_clean : payload E0.layout false (frame (Source.natBytes 32 (2^160-1))) 0 1=
    .ok [addr (2^160-1)] := by rfl

theorem boundary_dirty : payload E0.layout false (frame (Source.natBytes 32 (2^160))) 0 1=
    .error (.revert []) := by rfl

theorem maximum_word_dirty : payload E0.layout false (frame (List.replicate 32 255)) 0 1=
    .error (.revert []) := by rfl

theorem payable_dirty : (Source.cdToMem dirty (ArrayTy true) 3 2).run old=
    (.error (.revert []),old) := by
  apply copy_dirty true dirty 3 2 old 1 (by decide)
  simpa only [dirty_second_word] using (Nat.le_refl (2^160))

theorem empty_padding : payload E0.layout false (frame []) 123 2=.ok [addr 0,addr 0] := by rfl

theorem right_padding_dirty : (Source.cdToMem (frame [18]) (ArrayTy false) 0 1).run old=
    (.error (.revert []),old) := by
  apply copy_dirty false (frame [18]) 0 1 old 0 (by decide)
  decide

theorem zero_ignores_dirty : (Source.cdToMem dirty (ArrayTy false) 3 0).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc ⟨ArrayTy false,memory []⟩).1})) :=
  copy_zero false dirty 3 old

private theorem entry_full : Source.cdTail args 0 32=.ok (68,2) := by
  unfold Source.cdTail
  rw [show Source.wordAt args 0=32 from by decide,show args.length=128 from by simp only [args,Source.natBytes,List.length_append,Source.beBytes_length]]
  dsimp only
  rw [show Source.wordAt (args.drop 32) 0=2 from by decide]
  rfl
private theorem entry_dirty : Source.cdTail dirtyArgs 0 32=.ok (68,2) := by
  unfold Source.cdTail
  rw [show Source.wordAt dirtyArgs 0=32 from by decide,show dirtyArgs.length=128 from by simp only [dirtyArgs,Source.natBytes,List.length_append,Source.beBytes_length]]
  dsimp only
  rw [show Source.wordAt (dirtyArgs.drop 32) 0=2 from by decide]
  rfl
private theorem dirty_values : payload E0.layout false dirtyFull 68 2=.error (.revert []) := by rfl
private theorem full_values : payload E0.layout false full 68 2=.ok [addr 7,addr 42] := by rfl

theorem full_entry :
    ((Source.EM.lift (Source.cdTail args 0 32)) >>= fun p =>
      Source.cdToMem full (ArrayTy false) p.1 p.2).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc
        ⟨ArrayTy false,memory [addr 7,addr 42]⟩).1})) := by
  rw [guarded_run,entry_full]
  dsimp only
  rw [full_values]

theorem full_dirty_entry :
    ((Source.EM.lift (Source.cdTail dirtyArgs 0 32)) >>= fun p =>
      Source.cdToMem dirtyFull (ArrayTy false) p.1 p.2).run old=(.error (.revert []),old) := by
  rw [guarded_run,entry_dirty]
  dsimp only
  rw [dirty_values]

theorem truncated_entry : Source.cdTail truncated 0 32=.error (.revert []) := by
  unfold Source.cdTail
  rw [show Source.wordAt truncated 0=32 from by decide,show truncated.length=96 from by simp only [truncated,Source.natBytes,List.length_append,Source.beBytes_length]]
  dsimp only
  rw [show Source.wordAt (truncated.drop 32) 0=2 from by decide]
  rfl

theorem oversized_entry : Source.cdTail oversized 0 32=.error (.revert []) := by
  unfold Source.cdTail
  rw [show Source.wordAt oversized 0=32 from by decide,show oversized.length=64 from by simp only [oversized,Source.natBytes,List.length_append,Source.beBytes_length]]
  dsimp only
  rw [show Source.wordAt (oversized.drop 32) 0=2^64 from by decide]
  rfl

theorem missing_head : Source.cdTail [] 0 32=.error (.revert []) := by
  unfold Source.cdTail
  rw [show Source.wordAt [] 0=0 from by decide]
  rfl

theorem dirty_is_not_allocation_panic :
    (Source.cdToMem dirty (ArrayTy false) 3 2).run old≠
      (.error (.revert (Source.panicData .alloc)),old) := by
  rw [dirty_after_valid_prefix]
  intro h
  cases h

theorem payable_positive : payload E0.layout true raw 3 2=
    .ok [.address ⟨7,by decide⟩,.address ⟨42,by decide⟩] := by rfl

theorem payable_copy : (Source.cdToMem raw (ArrayTy true) 3 2).run old=
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc
        ⟨ArrayTy true,memory [.address ⟨7,by decide⟩,.address ⟨42,by decide⟩]⟩).1})) := by
  rw [copy_run,payable_positive]

def localState : Source.EMState E0 [.array .calldata (.address false) none] :=
  (.cons (.cdRef rfl 68 2) .nil,old.2)

theorem local_expression (G : Source.Glob E0) (n : Nat) :
    (Source.evalE G full (n+2) (copyExpr false .here)).run localState=
    (.ok (.val (.memRef rfl localState.2.heap.next)),
      (localState.1,{localState.2 with heap := (localState.2.heap.alloc
        ⟨ArrayTy false,memory [addr 7,addr 42]⟩).1})) := by
  rw [eval_copy false G full n localState .here 68 2 rfl,copy_run,full_values]

theorem zero_horizon (G : Source.Glob E0) :
    (Source.evalE G full 0 (copyExpr false .here)).run localState=(.error .timeout,localState) := rfl

theorem one_horizon (G : Source.Glob E0) :
    (Source.evalE G full 1 (copyExpr false .here)).run localState=(.error .timeout,localState) := rfl

#print axioms payable_copy
#print axioms local_expression
#print axioms zero_horizon
#print axioms one_horizon
#print axioms prefix_copy
#print axioms prefix_keeps_old
#print axioms dirty_after_valid_prefix
#print axioms payable_dirty
#print axioms full_entry
#print axioms full_dirty_entry
#print axioms dirty_is_not_allocation_panic
end Solidity.Backend.CalldataPackets.RawAddress.Controls
