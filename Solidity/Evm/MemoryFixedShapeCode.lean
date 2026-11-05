import Solidity.Evm.MemoryFixedStorageCopy

/-! Fixed-source array shape conversion uses actual copy and cleanup loops.
The source payload has no header; dynamic destination headers are replaced last. -/
namespace Solidity.Evm.Memory

private def keepCopy : List Instr := [.dup 2, .dup 2]
private def popRange : List Instr := [.pop, .pop, .pop, .pop]
private def fixedClear (n k : Nat) : List Instr :=
  [.swap 1, .push (.val (wmod k)), .push (.val (wmod n))]
private def dynamicClear (n : Nat) : List Instr :=
  [.dup 1, .keccakArr, .dup 3, .dup 3, .sload, .push (.val (wmod n))]
private def dynamicLength (n : Nat) : List Instr :=
  [.push (.val (wmod n)), .swap 1, .sstore, .pop]

def memoryFixedPadCode (n k : Nat) : List Instr :=
  keepCopy ++ memoryFixedCopyCode n ++ fixedClear n k ++
  [.loop copyRangeCond clearRangeBody] ++ popRange

def fixedPadStore (st : WordStore) (dst : Slot) (n k : Nat) (words : Nat → Fin W) : WordStore :=
  rangeStore (fun i st => WordStore.write st (dst.add i) 0) n (k - n)
    (fixedCopyStore st dst n words)

def memoryFixedDynamicCode (n : Nat) : List Instr :=
  keepCopy ++ [.keccakArr] ++ memoryFixedCopyCode n ++ dynamicClear n ++
  [.loop copyRangeCond clearRangeBody] ++ popRange ++ dynamicLength n

private theorem keepCopy_run (m : Machine) (base : Fin W) (dst : Slot) :
    run keepCopy ((m.push (.val base)).push (.slot dst)) =
      .ok ((((m.push (.val base)).push (.slot dst)).push (.val base)).push (.slot dst)) 0 := rfl
private theorem fixedClear_run (m : Machine) (base : Fin W) (dst : Slot) (n k : Nat) :
    run (fixedClear n k) ((m.push (.val base)).push (.slot dst)) =
      .ok (rangeMachine m n k base dst) 0 := rfl
private theorem popRange_run (m : Machine) (base : Fin W) (dst : Slot) (i n : Nat) :
    run popRange (rangeMachine m i n base dst) = .ok m 0 := rfl
private theorem dynamicClear_run (m : Machine) (base : Fin W) (dst : Slot) (n : Nat) :
    run (dynamicClear n) ((m.push (.val base)).push (.slot dst)) =
      .ok (rangeMachine ((m.push (.val base)).push (.slot dst)) n (m.store dst) base (.data dst 0)) 0 := by
  have hs : m.store.cells dst = wmod (m.store dst) :=
    Fin.ext (Nat.mod_eq_of_lt (WordStore.read_lt m.store dst)).symm
  simp only [dynamicClear, run, rangeMachine, Machine.push, exec_cons_zero, Instr.step,
    Machine.next, Out.ok_bind, exec_nil, List.cons_append, List.nil_append,
    Nat.reduceSub, List.getElem?_cons_zero, List.getElem?_cons_succ, hs]
private theorem dynamicLength_run (m : Machine) (base : Fin W) (dst : Slot) (n : Nat) (hn : n < W) :
    run (dynamicLength n) ((m.push (.val base)).push (.slot dst)) =
      .ok {m with store := WordStore.write m.store dst n} 0 := by
  simp only [dynamicLength, run, Machine.push, exec_cons_zero, Instr.step,
    Machine.next, Out.ok_bind, exec_nil, List.getElem?_cons_zero, List.set_cons_zero,
    wmod_def, Nat.mod_eq_of_lt hn]

attribute [local irreducible] run exec Instr.step loopRun

theorem memoryFixedPad_run (m : Machine) (base : Fin W) (dst : Slot) (n k : Nat)
    (words : Nat → Fin W) (hn : n < W) (hk : k < W) (hs : base.val + n ≤ W)
    (hw : ∀ i, i < n → m.mem (base.val + i) = .val (words i)) :
    run (memoryFixedPadCode n k) ((m.push (.val base)).push (.slot dst)) =
      .ok {m with store := fixedPadStore m.store dst n k words} 0 := by
  let copied := fixedCopyStore m.store dst n words
  let cm : Machine := {m with store := copied}
  rw [memoryFixedPadCode, List.append_assoc, List.append_assoc, List.append_assoc,
    run_append_ok (keepCopy_run m base dst),
    run_append_ok (memoryFixedCopy_run ((m.push (.val base)).push (.slot dst)) base dst n words hn hs hw)]
  change run (fixedClear n k ++ _) ((cm.push (.val base)).push (.slot dst)) = _
  rw [run_append_ok (fixedClear_run cm base dst n k),
    run_append_ok (clearRange_from cm n k base dst hn hk)]
  exact popRange_run _ _ _ _ _

theorem memoryFixedDynamic_run (m : Machine) (base : Fin W) (dst : Slot) (n : Nat)
    (words : Nat → Fin W) (hn : n < W) (hs : base.val + n ≤ W)
    (hw : ∀ i, i < n → m.mem (base.val + i) = .val (words i)) :
    run (memoryFixedDynamicCode n) ((m.push (.val base)).push (.slot dst)) =
      .ok {m with store := arrayCopyStore m.store dst n words} 0 := by
  let copied := fixedCopyStore m.store (.data dst 0) n words
  let cm : Machine := {m with store := copied}
  have hd : copied dst = m.store dst :=
    rangeStore_other (.data dst 0) words dst n 0 m.store (by
      intro i _ _; simpa only [Slot.add, Nat.zero_add] using Slot.ne_data dst i)
  rw [memoryFixedDynamicCode, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc, List.append_assoc, run_append_ok (keepCopy_run m base dst)]
  have hhash : run [.keccakArr] ((((m.push (.val base)).push (.slot dst)).push (.val base)).push (.slot dst)) =
      .ok ((((m.push (.val base)).push (.slot dst)).push (.val base)).push (.slot (.data dst 0))) 0 := by
    simp only [run, exec_cons_zero, Instr.step, Machine.next, Out.ok_bind, exec_nil, Machine.push]
  rw [run_append_ok hhash, run_append_ok
    (memoryFixedCopy_run ((m.push (.val base)).push (.slot dst)) base (.data dst 0) n words hn hs hw)]
  change run (dynamicClear n ++ _) ((cm.push (.val base)).push (.slot dst)) = _
  rw [run_append_ok (dynamicClear_run cm base dst n),
    run_append_ok (clearRange_from ((cm.push (.val base)).push (.slot dst)) n (cm.store dst)
      base (.data dst 0) hn (WordStore.read_lt cm.store dst))]
  let cleared := rangeStore (fun i st => WordStore.write st ((Slot.data dst 0).add i) 0)
    n (m.store dst - n) copied
  let dm : Machine := {m with store := cleared}
  simp only [show cm.store dst = m.store dst from hd]
  change run (popRange ++ dynamicLength n) (rangeMachine
    ((dm.push (.val base)).push (.slot dst)) (max n (m.store dst)) (m.store dst) base (.data dst 0)) = _
  rw [run_append_ok (popRange_run _ _ _ _ _), dynamicLength_run _ _ _ _ hn]
  rfl

end Solidity.Evm.Memory
