import Solidity.Evm.Memory

/-!
# Iterative memory-to-storage word copies

The counter, runtime length, payload pointer and destination slot stay on the
stack. No scratch memory is used. The loop reads one payload word and stores
it at the corresponding symbolic storage slot, then increments the counter.
-/
namespace Solidity.Evm.Memory

/-- Stack: counter, limit, payload address, destination slot, caller stack. -/
def copyRangeCond : List Instr := [.dup 2, .dup 2, .lt]

def copyRangeBody : List Instr :=
  [.dup 3, .dup 2, .add, .mloadAt,
   .dup 5, .dup 3, .add, .sstore, .push w[1], .add]

/-- The same traversal writes zero to the discarded destination suffix. -/
def clearRangeBody : List Instr :=
  [.push w[0], .dup 5, .dup 3, .add, .sstore, .push w[1], .add]

def rangeMachine (m : Machine) (i n : Nat) (base : Fin W) (dst : Slot) : Machine :=
  {m with stack := [.val (wmod i), .val (wmod n), .val base, .slot dst] ++ m.stack}

theorem copyRangeCond_run (m : Machine) (i n : Nat) (base : Fin W) (dst : Slot)
    (hi : i < W) (hn : n < W) :
    run copyRangeCond (rangeMachine m i n base dst) =
      .ok ((rangeMachine m i n base dst).push (.val (bword (decide (i < n))))) 0 := by
  simp only [copyRangeCond, rangeMachine, run, exec_cons_zero, List.cons_append, List.nil_append, Nat.reduceSub,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Instr.step,
    Machine.next, Machine.push, Out.ok_bind, exec_nil, wmod_def,
    Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hn]

/-- One copy turn writes the actual memory word and preserves all other state. -/
theorem copyRangeBody_run (m : Machine) (i n : Nat) (base : Fin W) (dst : Slot)
    (hi : i + 1 < W) (hn : n < W) (ha : base.val + i < W)
    (v : Fin W) (hv : m.mem (base.val + i) = .val v) :
    run copyRangeBody (rangeMachine m i n base dst) =
      .ok (rangeMachine {m with store := WordStore.write m.store (dst.add i) v.val}
        (i + 1) n base dst) 0 := by
  have hi' : i < W := by omega
  have hv' : m.mem ((i + base.val) % W) = .val v := by
    rw [Nat.add_comm i base.val, Nat.mod_eq_of_lt ha, hv]
  simp only [copyRangeBody, rangeMachine, run, exec_cons_zero, List.cons_append, List.nil_append, Nat.reduceSub,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Instr.step,
    Machine.next, Out.ok_bind, exec_nil, wmod_def, Nat.mod_eq_of_lt hi',
    Nat.mod_eq_of_lt hn, hv', Nat.mod_eq_of_lt hi, Nat.add_comm]

/-- One cleanup turn explicitly clears the recycled/tail slot. -/
theorem clearRangeBody_run (m : Machine) (i n : Nat) (base : Fin W) (dst : Slot)
    (hi : i + 1 < W) (hn : n < W) :
    run clearRangeBody (rangeMachine m i n base dst) =
      .ok (rangeMachine {m with store := WordStore.write m.store (dst.add i) 0}
        (i + 1) n base dst) 0 := by
  have hi' : i < W := by omega
  simp only [clearRangeBody, rangeMachine, run, exec_cons_zero, List.cons_append, List.nil_append, Nat.reduceSub,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Instr.step,
    Machine.next, Out.ok_bind, exec_nil, wmod_def, Nat.mod_eq_of_lt hi',
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hi, Nat.add_comm]

/-- Exact storage effect of a finite sequence of loop turns. -/
def rangeStore (step : Nat → WordStore → WordStore) (i : Nat) : Nat → WordStore → WordStore
  | 0, st => st
  | k + 1, st => rangeStore step (i + 1) k (step i st)

/-- A finite increasing counter loop terminates at its runtime bound.
The body equation is discharged against the actual instructions below. -/
theorem rangeLoop_iter (m : Machine) (n : Nat) (base : Fin W) (dst : Slot)
    (body : List Instr) (step : Nat → WordStore → WordStore) (hn : n < W)
    (hb : ∀ i, i < n → ∀ st,
      run body (rangeMachine {m with store := st} i n base dst) =
        .ok (rangeMachine {m with store := step i st} (i + 1) n base dst) 0) :
    ∀ k i st, i + k = n →
      loopIterN (run copyRangeCond) (run body) (k + 1)
        (rangeMachine {m with store := st} i n base dst) =
      .inr (.ok (rangeMachine {m with store := rangeStore step i k st} n n base dst) 0) := by
  intro k
  induction k with
  | zero =>
    intro i st he
    have he' : i = n := by omega
    subst i
    have hc := copyRangeCond_run {m with store := st} n n base dst hn hn
    simp only [Nat.lt_irrefl, decide_false] at hc
    rw [loopIterN, loopTurn, hc]
    rfl
  | succ k ih =>
    intro i st he
    have hi : i < n := by omega
    have hiW : i < W := Nat.lt_trans hi hn
    have hc := copyRangeCond_run {m with store := st} i n base dst hiW hn
    simp only [hi, decide_true] at hc
    have ht : loopTurn (run copyRangeCond) (run body)
        (rangeMachine {m with store := st} i n base dst) =
        .inl (rangeMachine {m with store := step i st} (i + 1) n base dst) := by
      rw [loopTurn, hc]
      change (if (bword true).val = 0 then _ else _) = _
      rw [if_neg (by decide)]
      simp only [Machine.push]
      rw [hb i hi st]
    rw [loopIterN, ht]
    exact ih (i + 1) (step i st) (by omega)

/-- Arbitrary runtime-length copies execute the actual structured machine loop. -/
theorem copyRange_run (m : Machine) (n : Nat) (base : Fin W) (dst : Slot)
    (words : Nat → Fin W) (hn : n < W) (hs : base.val + n ≤ W)
    (hm : ∀ i, i < n → m.mem (base.val + i) = .val (words i)) :
    run [.loop copyRangeCond copyRangeBody] (rangeMachine m 0 n base dst) =
      .ok (rangeMachine {m with store := rangeStore (fun i st => WordStore.write st (dst.add i) (words i).val) 0 n m.store}
        n n base dst) 0 := by
  have hb : ∀ i, i < n → ∀ st,
      run copyRangeBody (rangeMachine {m with store := st} i n base dst) =
      .ok (rangeMachine {m with store := WordStore.write st (dst.add i) (words i).val}
        (i + 1) n base dst) 0 := by
    intro i hi st
    exact copyRangeBody_run {m with store := st} i n base dst (by omega) hn (by omega)
      (words i) (hm i hi)
  have hr := rangeLoop_iter m n base dst copyRangeBody _ hn hb n 0 m.store (Nat.zero_add n)
  have hloop := loopRun_of_iterN hr
  change (loopRun (run copyRangeCond) (run copyRangeBody) _).bind _ = _
  rw [hloop]
  rfl

/-- Cleanup also executes as a structured loop, with a runtime start and end. -/
theorem clearRange_run (m : Machine) (i n : Nat) (base : Fin W) (dst : Slot)
    (hi : i ≤ n) (hn : n < W) :
    run [.loop copyRangeCond clearRangeBody] (rangeMachine m i n base dst) =
      .ok (rangeMachine {m with store := rangeStore (fun j st => WordStore.write st (dst.add j) 0) i (n - i) m.store} n n base dst) 0 := by
  have hb : ∀ j, j < n → ∀ st,
      run clearRangeBody (rangeMachine {m with store := st} j n base dst) =
      .ok (rangeMachine {m with store := WordStore.write st (dst.add j) 0}
        (j + 1) n base dst) 0 := by
    intro j hj st
    exact clearRangeBody_run {m with store := st} j n base dst (by omega) hn
  have hr := rangeLoop_iter m n base dst clearRangeBody _ hn hb (n - i) i m.store (by omega)
  have hloop := loopRun_of_iterN hr
  change (loopRun (run copyRangeCond) (run clearRangeBody) _).bind _ = _
  rw [hloop]
  rfl

/-- Starting past the old bound clears nothing; otherwise exactly the suffix. -/
theorem clearRange_from (m : Machine) (i n : Nat) (base : Fin W) (dst : Slot)
    (hi : i < W) (hn : n < W) :
    run [.loop copyRangeCond clearRangeBody] (rangeMachine m i n base dst) =
      .ok (rangeMachine {m with store := rangeStore (fun j st => WordStore.write st (dst.add j) 0) i (n - i) m.store}
        (max i n) n base dst) 0 := by
  by_cases h : i ≤ n
  · rw [Nat.max_eq_right h]
    exact clearRange_run m i n base dst h hn
  · have hni : n ≤ i := by omega
    rw [Nat.max_eq_left hni, Nat.sub_eq_zero_of_le hni, rangeStore]
    have hc := copyRangeCond_run m i n base dst hi hn
    have hnot : ¬ i < n := by omega
    simp only [hnot, decide_false] at hc
    have ht : loopIterN (run copyRangeCond) (run clearRangeBody) 1
        (rangeMachine m i n base dst) = .inr (.ok (rangeMachine m i n base dst) 0) := by
      rw [loopIterN, loopTurn, hc]
      rfl
    have hr := loopRun_of_iterN ht
    change (loopRun (run copyRangeCond) (run clearRangeBody) _).bind _ = _
    rw [hr]
    rfl

/-- Slots outside the written interval retain their original contents. -/
theorem rangeStore_other (dst : Slot) (words : Nat → Fin W) (x : Slot) :
    ∀ k i st, (∀ j, i ≤ j → j < i + k → x ≠ dst.add j) →
      rangeStore (fun j st => WordStore.write st (dst.add j) (words j).val) i k st x = st x := by
  intro k
  induction k with
  | zero => intro i st _; rfl
  | succ k ih =>
    intro i st hx
    rw [rangeStore, ih (i + 1) _ (by intro j hj hk; exact hx j (by omega) (by omega))]
    exact WordStore.write_other _ _ (hx i (by omega) (by omega))

/-- Every copied slot contains its own source word, including recycled slots. -/
theorem rangeStore_written (dst : Slot) (words : Nat → Fin W) :
    ∀ k i st j, i ≤ j → j < i + k →
      rangeStore (fun j st => WordStore.write st (dst.add j) (words j).val) i k st (dst.add j) =
        (words j).val := by
  intro k
  induction k with
  | zero => intro i st j hj hk; omega
  | succ k ih =>
    intro i st j hj hk
    rw [rangeStore]
    by_cases he : j = i
    · subst j
      rw [rangeStore_other dst words (dst.add i) k (i + 1) _ (by
        intro j hj hk he
        have hij : i = j := Slot.add_inj he
        omega)]
      exact WordStore.write_same_of_lt _ _ _ (words i).isLt
    · exact ih (i + 1) _ j (by omega) (by omega)

attribute [irreducible] rangeStore

end Solidity.Evm.Memory
