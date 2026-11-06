import Solidity.Evm.MemoryStorageCopyLoop

/-!
# Runtime-length array copy code

The source header is read from memory, the old destination header from storage.
One loop copies the payload, a second clears the old live suffix, and the
length is replaced last. Caller stack, all memory, balances and environment
are preserved. The store equation records cleanup even beyond the new length.
-/
namespace Solidity.Evm.Memory

private def dropRange : List Instr := [.pop, .pop, .pop, .pop]
private def enterCopy : List Instr :=
  [.dup 1, .keccakArr, .dup 3, .dup 1, .mloadAt, .swap 1,
   .push w[1], .add, .swap 1, .push w[0]]
private def enterClear : List Instr :=
  [.dup 1, .keccakArr, .dup 3, .dup 3, .sload, .dup 2, .mloadAt]
private def replaceLength : List Instr := [.dup 2, .mloadAt, .swap 1, .sstore, .pop]

/-- Input: destination slot above the source array header pointer. -/
def memoryArrayCopyCode : List Instr :=
  enterCopy ++ [.loop copyRangeCond copyRangeBody] ++ dropRange ++
  enterClear ++ [.loop copyRangeCond clearRangeBody] ++ dropRange ++ replaceLength

/-- Exact destination contents, including the discarded old live suffix. -/
def arrayCopyStore (st : WordStore) (dst : Slot) (n : Nat) (words : Nat → Fin W) : WordStore :=
  let copied := rangeStore (fun i st => WordStore.write st ((Slot.data dst 0).add i) (words i).val) 0 n st
  let cleared := rangeStore (fun i st => WordStore.write st ((Slot.data dst 0).add i) 0) n (st dst - n) copied
  WordStore.write cleared dst n

private theorem enterCopy_run (m : Machine) (base : Fin W) (dst : Slot) (n : Nat)
    (hn : n < W) (hm : m.mem base.val = .val (wmod n)) :
    run enterCopy ((m.push (.val base)).push (.slot dst)) =
      .ok (rangeMachine ((m.push (.val base)).push (.slot dst)) 0 n
        (wmod (base.val + 1)) (.data dst 0)) 0 := by
  simp only [enterCopy, run, rangeMachine, Machine.push, exec_cons_zero, Instr.step,
    Machine.next, Out.ok_bind, exec_nil, List.cons_append, List.nil_append,
    Nat.reduceSub, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.set_cons_zero, hm, wmod_def, Nat.mod_eq_of_lt hn,
    Nat.add_comm, Nat.zero_mod]

private theorem dropRange_run (m : Machine) (i n : Nat) (base : Fin W) (dst : Slot) :
    run dropRange (rangeMachine m i n base dst) = .ok m 0 := rfl

private theorem enterClear_run (m : Machine) (base : Fin W) (dst : Slot) (n : Nat)
    (hm : m.mem base.val = .val (wmod n)) :
    run enterClear ((m.push (.val base)).push (.slot dst)) =
      .ok (rangeMachine ((m.push (.val base)).push (.slot dst)) n (m.store dst)
        base (.data dst 0)) 0 := by
  have hs : m.store.cells dst = wmod (m.store dst) :=
    Fin.ext (Nat.mod_eq_of_lt (WordStore.read_lt m.store dst)).symm
  simp only [enterClear, run, rangeMachine, Machine.push, exec_cons_zero, Instr.step,
    Machine.next, Out.ok_bind, exec_nil, List.cons_append, List.nil_append,
    Nat.reduceSub, List.getElem?_cons_zero, List.getElem?_cons_succ, hm, hs]

private theorem replaceLength_run (m : Machine) (base : Fin W) (dst : Slot) (n : Nat)
    (hn : n < W) (hm : m.mem base.val = .val (wmod n)) :
    run replaceLength ((m.push (.val base)).push (.slot dst)) =
      .ok {m with store := WordStore.write m.store dst n} 0 := by
  simp only [replaceLength, run, Machine.push, exec_cons_zero, Instr.step,
    Machine.next, Out.ok_bind, exec_nil, Nat.reduceSub,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.set_cons_zero, hm, wmod_def, Nat.mod_eq_of_lt hn]

attribute [local irreducible] run exec Instr.step loopRun

/-- Both runtime loops terminate and implement the exact copy/cleanup algorithm. -/
theorem memoryArrayCopy_run (m : Machine) (base : Fin W) (dst : Slot) (n : Nat)
    (words : Nat → Fin W) (hn : n < W) (hs : base.val + 1 + n ≤ W)
    (hheader : m.mem base.val = .val (wmod n))
    (hwords : ∀ i, i < n → m.mem (base.val + 1 + i) = .val (words i)) :
    run memoryArrayCopyCode ((m.push (.val base)).push (.slot dst)) =
      .ok {m with store := arrayCopyStore m.store dst n words} 0 := by
  let payload := wmod (base.val + 1)
  have hp : payload.val + n ≤ W := by
    by_cases h : base.val + 1 < W
    · simpa only [payload, wmod_def, Nat.mod_eq_of_lt h] using hs
    · have hn0 : n = 0 := by omega
      rw [hn0, Nat.add_zero]
      exact Nat.le_of_lt payload.isLt
  have hw : ∀ i, i < n → m.mem (payload.val + i) = .val (words i) := by
    intro i hi
    have h : base.val + 1 < W := by omega
    simpa only [payload, wmod_def, Nat.mod_eq_of_lt h] using hwords i hi
  let copied := rangeStore (fun i st => WordStore.write st ((Slot.data dst 0).add i) (words i).val) 0 n m.store
  have hd : copied dst = m.store dst :=
    rangeStore_other (.data dst 0) words dst n 0 m.store (by
      intro i _ _; simpa only [Slot.add, Nat.zero_add] using Slot.ne_data dst i)
  let cm : Machine := {m with store := copied}
  let cleared := rangeStore (fun i st => WordStore.write st ((Slot.data dst 0).add i) 0) n (m.store dst - n) copied
  rw [memoryArrayCopyCode, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc, List.append_assoc, run_append_ok (enterCopy_run m base dst n hn hheader)]
  rw [run_append_ok (copyRange_run ((m.push (.val base)).push (.slot dst)) n payload
    (.data dst 0) words hn hp hw)]
  change run (dropRange ++ _) (rangeMachine ((cm.push (.val base)).push (.slot dst)) n n payload (.data dst 0)) = _
  rw [run_append_ok (dropRange_run ((cm.push (.val base)).push (.slot dst)) n n payload (.data dst 0))]
  rw [run_append_ok (enterClear_run cm base dst n hheader)]
  rw [run_append_ok (clearRange_from ((cm.push (.val base)).push (.slot dst)) n (cm.store dst)
    base (.data dst 0) hn (WordStore.read_lt cm.store dst))]
  simp only [show cm.store dst = m.store dst from hd]
  let dm : Machine := {m with store := cleared}
  have hd0 := dropRange_run ((dm.push (.val base)).push (.slot dst))
    (max n (m.store dst)) (m.store dst) base (.data dst 0)
  change run (dropRange ++ replaceLength) (rangeMachine
    ((dm.push (.val base)).push (.slot dst))
    (max n (m.store dst)) (m.store dst) base (.data dst 0)) = _
  rw [run_append_ok hd0]
  exact replaceLength_run dm base dst n hn hheader

end Solidity.Evm.Memory
