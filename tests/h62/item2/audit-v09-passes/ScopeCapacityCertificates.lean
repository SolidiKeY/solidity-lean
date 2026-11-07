import Solidity.Yul.Compilation.ClzBounds

/-! Guard accepting a scope from its unchanged final height while missing entry
or writeback peaks, or unnecessarily refusing an empty full-capacity scope.
Reuse the existing finite locals, write sequence and scope execution contracts.
This is typed numeric preparation, not a V12 call convention or Source/native
simulation; the 1024 limit, index bounds and full-width words stay unchanged. -/
namespace Solidity.Yul.Compilation
open Backend Scalar

theorem stackBound_suffix (p q : Program) (height : Int)
    (bounded : stackBound (p ++ q) height = true) :
    stackBound q (height + (p.map stackDelta).sum) = true := by
  induction p generalizing height with
  | nil => simpa only [List.map_nil, List.sum_nil, Int.add_zero] using bounded
  | cons i p ih =>
    change (safeHeight height && stackBound (p ++ q) (height + stackDelta i)) = true at bounded
    rw [Bool.and_eq_true] at bounded
    have rest := ih (height + stackDelta i) bounded.2
    simpa only [List.map_cons, List.sum_cons, Int.add_assoc] using rest

/-- Splitting a capacity check retains the exact accumulated height, rather
than rechecking the suffix at the caller's original height. -/
theorem stackBound_append_iff (p q : Program) (height : Int) :
    stackBound (p ++ q) height = true ↔
    stackBound p height = true ∧
      stackBound q (height + (p.map stackDelta).sum) = true :=
  ⟨fun bound => ⟨stackBound_prefix p q height bound,
    stackBound_suffix p q height bound⟩,
    fun bounds => stackBound_comp bounds.1 bounds.2⟩

/-- Actual slice execution fixes the intermediate arity in both directions of
the composed capacity check; no model-tail or final-height shortcut is used. -/
theorem Slice.comp_bound_iff {a b c : Nat} (f : Slice a b) (g : Slice b c)
    (xs : Vector Word a) (tail : Stack) :
    stackBound (f.comp g).code ((a + tail.length : Nat) : Int) = true ↔
    stackBound f.code ((a + tail.length : Nat) : Int) = true ∧
    stackBound g.code ((b + tail.length : Nat) : Int) = true := by
  obtain ⟨middle, executed⟩ := f.correct xs tail
  have shifted : ((a + tail.length : Nat) : Int) + (f.code.map stackDelta).sum =
      ((b + tail.length : Nat) : Int) := by
    simpa only [List.length_append, Vector.length_toList] using (run_height executed).symm
  change stackBound (f.code ++ g.code) _ = true ↔ _
  rw [stackBound_append_iff, shifted]

theorem pushPrefix_delta (xs : Stack) :
    ((pushPrefix xs).map stackDelta).sum = (xs.length : Int) := by
  have sizes := run_height (pushPrefix_run xs [])
  simpa only [List.append_nil, List.length_nil, Int.natCast_zero, Int.zero_add] using sizes.symm

theorem popPrefix_delta (n : Nat) :
    ((popPrefix n).map stackDelta).sum = -(n : Int) := by
  have sizes := run_height (popPrefix_run (List.replicate n (0 : Word)) [])
  simp only [List.length_replicate, List.append_nil, List.length_nil,
    Int.natCast_zero] at sizes
  omega

theorem pushPrefix_bound (xs : Stack) (height : Int)
    (low : 0 ≤ height) (high : height + (xs.length : Int) ≤ 1024) :
    stackBound (pushPrefix xs) height = true := by
  induction xs generalizing height with
  | nil =>
    change (safeHeight height && true) = true
    rw [Bool.and_true]
    exact decide_eq_true ⟨low, by simpa only [List.length_nil, Int.natCast_zero, Int.add_zero] using high⟩
  | cons x xs ih =>
    rw [pushPrefix]
    apply stackBound_comp (ih height low (by simp only [List.length_cons] at high; omega))
    rw [pushPrefix_delta]
    change (safeHeight (height + (xs.length : Int)) &&
      (safeHeight (height + (xs.length : Int) + 1) && true)) = true
    simp only [Bool.and_true, Bool.and_eq_true, safeHeight, decide_eq_true_eq]
    simp only [List.length_cons] at high
    omega

theorem popPrefix_bound (n : Nat) (height : Int)
    (enough : (n : Int) ≤ height) (high : height ≤ 1024) :
    stackBound (popPrefix n) height = true := by
  induction n generalizing height with
  | zero =>
    change (safeHeight height && true) = true
    rw [Bool.and_true]
    exact decide_eq_true ⟨enough, high⟩
  | succ n ih =>
    change (safeHeight height && stackBound (popPrefix n) (height + -1)) = true
    rw [Bool.and_eq_true]
    refine ⟨?_, ih (height + -1) (by omega) (by omega)⟩
    exact decide_eq_true ⟨by omega, high⟩

theorem writeSequence_delta {n : Nat} (locals : Vector Word n) (writes : LocalWrites n) :
    ((writeSequence writes).map stackDelta).sum = 0 := by
  have sizes := run_height (writeSequence_run writes locals [])
  simp only [List.length_append, Vector.length_toList, List.length_nil, Nat.add_zero] at sizes
  omega

/-- Entry/write/exit actually preserves the caller and checks all heights.
Empty writes need no spare transient word; nonempty writes need exactly one. -/
theorem scope_updates_safe {n : Nat} (locals : Vector Word n)
    (writes : LocalWrites n) (tail : Stack)
    (room : n + tail.length + (if writes.isEmpty then 0 else 1) ≤ 1024) :
    run (pushPrefix locals.toList ++ writeSequence writes ++ popPrefix n) tail = some tail ∧
    stackBound (pushPrefix locals.toList ++ writeSequence writes ++ popPrefix n)
      (tail.length : Int) = true := by
  have fits : n + tail.length ≤ 1024 := by
    cases writes with
    | nil => change n + tail.length ≤ 1024 at room; exact room
    | cons first rest => change n + tail.length + 1 ≤ 1024 at room; omega
  have entry : stackBound (pushPrefix locals.toList) (tail.length : Int) = true := by
    apply pushPrefix_bound _ _ (by omega)
    simp only [Vector.length_toList]
    omega
  have body : stackBound (writeSequence writes) ((n + tail.length : Nat) : Int) = true := by
    cases writes with
    | nil =>
      change (safeHeight ((n + tail.length : Nat) : Int) && true) = true
      rw [Bool.and_true]
      exact decide_eq_true ⟨by omega, by omega⟩
    | cons first rest =>
      change n + tail.length + 1 ≤ 1024 at room
      exact writeSequence_bound_sufficient _ _ (by omega) (by omega)
  have exit : stackBound (popPrefix n) ((n + tail.length : Nat) : Int) = true :=
    popPrefix_bound n _ (by omega) (by omega)
  have rest : stackBound (writeSequence writes ++ popPrefix n)
      ((n + tail.length : Nat) : Int) = true := by
    apply stackBound_comp body
    rw [writeSequence_delta locals writes, Int.add_zero]
    exact exit
  have shifted : (tail.length : Int) + ((pushPrefix locals.toList).map stackDelta).sum =
      ((n + tail.length : Nat) : Int) := by
    rw [pushPrefix_delta, Vector.length_toList]
    omega
  refine ⟨scope_updates_exit locals writes tail, ?_⟩
  rw [List.append_assoc]
  apply stackBound_comp entry
  rw [shifted]
  exact rest

/-- Exact scope capacity includes entry and every transient write peak;
caller-preserving exit alone is insufficient. -/
theorem scope_bound_iff {n : Nat} (locals : Vector Word n)
    (writes : LocalWrites n) (tail : Stack) :
    stackBound (pushPrefix locals.toList ++ writeSequence writes ++ popPrefix n)
      (tail.length : Int) = true ↔
    n + tail.length + (if writes.isEmpty then 0 else 1) ≤ 1024 := by
  constructor
  · intro bounded
    cases writes with
    | nil =>
      have entry := prefix_capacity (pushPrefix locals.toList)
        (writeSequence ([] : LocalWrites n) ++ popPrefix n)
        (pushPrefix_run locals.toList tail)
        (by simpa only [List.append_assoc] using bounded)
      simpa only [List.length_append, Vector.length_toList, List.isEmpty_nil,
        Bool.true_eq, if_true, Nat.add_zero] using entry
    | cons first rest =>
      have afterEntry := stackBound_suffix (pushPrefix locals.toList)
        (writeSequence (first :: rest) ++ popPrefix n) (tail.length : Int)
        (by simpa only [List.append_assoc] using bounded)
      rw [pushPrefix_delta, Vector.length_toList] at afterEntry
      have shifted : (tail.length : Int) + (n : Int) = ((n + tail.length : Nat) : Int) := by omega
      rw [shifted] at afterEntry
      have body := stackBound_prefix (writeSequence (first :: rest)) (popPrefix n)
        ((n + tail.length : Nat) : Int) afterEntry
      exact writeSequence_bound_necessary first rest (n + tail.length) body
  · intro room
    exact (scope_updates_safe locals writes tail room).2

/-- Successful mathematical scope exit does not excuse an overflowing writeback. -/
theorem scope_write_overflow {n : Nat} (locals : Vector Word n)
    (first : {i : Fin n // i.val < 16} × Word) (rest : LocalWrites n) (tail : Stack)
    (full : n + tail.length = 1024) :
    run (pushPrefix locals.toList ++ writeSequence (first :: rest) ++ popPrefix n) tail = some tail ∧
    stackBound (pushPrefix locals.toList ++ writeSequence (first :: rest) ++ popPrefix n)
      (tail.length : Int) = false := by
  refine ⟨scope_updates_exit locals (first :: rest) tail, ?_⟩
  cases bounded : stackBound (pushPrefix locals.toList ++ writeSequence (first :: rest) ++ popPrefix n)
      (tail.length : Int) with
  | false => rfl
  | true =>
    have afterEntry := stackBound_suffix (pushPrefix locals.toList)
      (writeSequence (first :: rest) ++ popPrefix n) (tail.length : Int)
      (by simpa only [List.append_assoc] using bounded)
    rw [pushPrefix_delta, Vector.length_toList] at afterEntry
    have shifted : (tail.length : Int) + (n : Int) = ((n + tail.length : Nat) : Int) := by omega
    rw [shifted] at afterEntry
    have body := stackBound_prefix (writeSequence (first :: rest)) (popPrefix n)
      ((n + tail.length : Nat) : Int) afterEntry
    have necessary := writeSequence_bound_necessary first rest (n + tail.length) body
    omega

/-- Repeated updates obey last-write-wins inside a capacity-safe scope and
still preserve every arbitrary caller word on exit. -/
theorem scope_capacity_witness (tail : Stack) (room : tail.length + 3 ≤ 1024) :
    let locals : Vector Word 2 := #v[7,9]
    let slot : {i : Fin 2 // i.val < 16} := ⟨0, by decide⟩
    let writes : LocalWrites 2 := [(slot,42),(slot,99)]
    run (pushPrefix locals.toList ++ writeSequence writes ++ popPrefix 2) tail = some tail ∧
    stackBound (pushPrefix locals.toList ++ writeSequence writes ++ popPrefix 2)
      (tail.length : Int) = true ∧
    run (writeSequence writes) (locals.toList ++ tail) = some (99 :: 9 :: tail) := by
  have safe := scope_updates_safe (#v[7,9] : Vector Word 2)
    [(⟨0, by decide⟩,42),(⟨0, by decide⟩,99)] tail (by change 2 + tail.length + 1 ≤ 1024; omega)
  refine ⟨safe.1, safe.2, ?_⟩
  exact writeSequence_same (#v[7,9] : Vector Word 2) ⟨0, by decide⟩ 42 99 tail

/-- With no locals or writes, a full caller stack is safe: no hidden extra word. -/
theorem empty_scope_full (tail : Stack) (full : tail.length = 1024) :
    run ([] : Program) tail = some tail ∧ stackBound [] (tail.length : Int) = true :=
  scope_updates_safe (#v[] : Vector Word 0) [] tail (by change 0 + tail.length ≤ 1024; omega)

/-- info: 'Solidity.Yul.Compilation.stackBound_suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stackBound_suffix
/-- info: 'Solidity.Yul.Compilation.pushPrefix_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pushPrefix_delta
/-- info: 'Solidity.Yul.Compilation.popPrefix_delta' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms popPrefix_delta
/-- info: 'Solidity.Yul.Compilation.pushPrefix_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pushPrefix_bound
/-- info: 'Solidity.Yul.Compilation.popPrefix_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms popPrefix_bound
/-- info: 'Solidity.Yul.Compilation.writeSequence_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms writeSequence_delta
/-- info: 'Solidity.Yul.Compilation.scope_updates_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scope_updates_safe
/-- info: 'Solidity.Yul.Compilation.scope_write_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scope_write_overflow
/-- info: 'Solidity.Yul.Compilation.scope_capacity_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scope_capacity_witness
/-- info: 'Solidity.Yul.Compilation.empty_scope_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms empty_scope_full
/-- info: 'Solidity.Yul.Compilation.scope_bound_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scope_bound_iff
/-- info: 'Solidity.Yul.Compilation.stackBound_append_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stackBound_append_iff
/-- info: 'Solidity.Yul.Compilation.Slice.comp_bound_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Slice.comp_bound_iff
end Solidity.Yul.Compilation
