import Solidity.Backend.Failure.Emit
import Solidity.Backend.Failure.Slice

/-! The link from emitted real instructions to independent byte semantics.
Fits is the architectural address/length boundary; the checked corollary also proves stack-height safety. There is no fixed
small payload limit. No source semantics depends on this module. -/
namespace Solidity.Backend.Failure

open Slice

theorem pushed_digits (n : Nat) (h : n < wordLimit) :
    pushed (digits 32 n) = (⟨n, h⟩ : Roadmap.Word) := by
  apply Fin.ext
  change readImmediate (digits 32 n) % (2 ^ 256) = n
  rw [read_digits 32 n h]
  exact Nat.mod_eq_of_lt h

theorem byte_lt_word (b : UInt8) : b.toNat < wordLimit :=
  Nat.lt_trans b.toNat_lt_size (by decide)

theorem pushed_byte (b : UInt8) :
    pushed [b] = (⟨b.toNat, byte_lt_word b⟩ : Roadmap.Word) := by
  apply Fin.ext
  simp only [pushed, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add]
  exact Nat.mod_eq_of_lt (byte_lt_word b)

theorem run_pushNat (n : Nat) (h : n < wordLimit) (p : Program) (s : Machine) :
    run (pushNat n :: p) s = run p { s with stack := ⟨n, h⟩ :: s.stack } := by
  simp only [run, step, pushNat, Vector.toList, pushed_digits n h]
  rfl

theorem run_pushByte (b : UInt8) (p : Program) (s : Machine) :
    run (pushByte b :: p) s =
      run p { s with stack := ⟨b.toNat, byte_lt_word b⟩ :: s.stack } := by
  simp only [run, step, pushByte]
  change run p { s with stack := pushed [b] :: s.stack } = _
  rw [pushed_byte]

/-- Any continuation, initial memory and intrinsic stack tail are allowed. -/
theorem run_writes (a : Nat) (bs : List UInt8) (p : Program) (s : Machine)
    (h : a + bs.length ≤ wordLimit) :
    run (writes a bs ++ p) s =
      run p { s with memory := putBytes s.memory a bs } := by
  induction bs generalizing a s with
  | nil => rfl
  | cons b bs ih =>
    have ha : a < wordLimit := by simp only [List.length_cons] at h; omega
    have ht : a + 1 + bs.length ≤ wordLimit := by simp only [List.length_cons] at h; omega
    simp only [writes, List.cons_append, List.nil_append]
    rw [run_pushByte, run_pushNat a ha]
    simp only [run, step, UInt8.ofNat_toNat]
    exact ih (a + 1) ⟨s.stack, putByte s.memory a b⟩ ht

/-- Exact terminal result even with arbitrary instructions concatenated after
it. Those instructions are never reached. Both the stack and memory frame
are stated in the result, rather than hidden behind an observation quotient. -/
theorem run_emit_suffix (a : Nat) (i : Input) (p : Program) (s : Machine)
    (h : Fits a i.bytes) :
    run (emit a i ++ p) s =
      some ({ s with memory := putBytes s.memory a i.bytes }, some i.observation) := by
  rcases h with ⟨ha, hn, hend⟩
  simp only [emit, List.append_assoc]
  rw [run_writes a i.bytes _ s hend]
  simp only [List.cons_append, List.nil_append]
  rw [run_pushNat i.bytes.length hn, run_pushNat a ha]
  cases i <;> simp only [Input.terminal, Input.observation, run, step,
    getBytes_putBytes, Input.bytes] <;> rfl

theorem run_emit (a : Nat) (i : Input) (s : Machine) (h : Fits a i.bytes) :
    run (emit a i) s =
      some ({ s with memory := putBytes s.memory a i.bytes }, some i.observation) := by
  simpa only [List.append_nil] using run_emit_suffix a i [] s h

theorem stackSafe_pushNat (n : Nat) (h : n < wordLimit) (p : Program) (s : Machine) :
    stackSafe (pushNat n :: p) s =
      (decide (s.stack.length ≤ 1024) && stackSafe p { s with stack := ⟨n, h⟩ :: s.stack }) := by
  simp only [stackSafe, step, pushNat, Vector.toList, pushed_digits n h]

theorem stackSafe_pushByte (b : UInt8) (p : Program) (s : Machine) :
    stackSafe (pushByte b :: p) s =
      (decide (s.stack.length ≤ 1024) &&
        stackSafe p { s with stack := ⟨b.toNat, byte_lt_word b⟩ :: s.stack }) := by
  simp only [stackSafe, step, pushByte]
  change (decide (s.stack.length ≤ 1024) && stackSafe p { s with stack := pushed [b] :: s.stack }) = _
  rw [pushed_byte]

theorem stackSafe_writes (a : Nat) (bs : List UInt8) (p : Program) (s : Machine)
    (h : a + bs.length ≤ wordLimit) (hs : s.stack.length + 2 ≤ 1024)
    (hp : stackSafe p { s with memory := putBytes s.memory a bs } = true) :
    stackSafe (writes a bs ++ p) s = true := by
  induction bs generalizing a s with
  | nil => exact hp
  | cons b bs ih =>
    have ha : a < wordLimit := by simp only [List.length_cons] at h; omega
    have ht : a + 1 + bs.length ≤ wordLimit := by simp only [List.length_cons] at h; omega
    simp only [writes, List.cons_append, List.nil_append]
    rw [stackSafe_pushByte, stackSafe_pushNat a ha]
    simp only [stackSafe, step, List.length_cons, UInt8.ofNat_toNat,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, by omega, by omega,
      ih (a + 1) ⟨s.stack, putByte s.memory a b⟩ ht hs hp⟩

theorem stackSafe_emit_suffix (a : Nat) (i : Input) (p : Program) (s : Machine)
    (h : Fits a i.bytes) (hs : s.stack.length + 2 ≤ 1024) :
    stackSafe (emit a i ++ p) s = true := by
  rcases h with ⟨ha, hn, hend⟩
  simp only [emit, List.append_assoc]
  apply stackSafe_writes a i.bytes _ s hend hs
  simp only [List.cons_append, List.nil_append]
  rw [stackSafe_pushNat i.bytes.length hn, stackSafe_pushNat a ha]
  cases i <;> simp only [Input.terminal, stackSafe, step, List.length_cons,
    Bool.and_eq_true, decide_eq_true_eq] <;> omega

theorem empty_stack_boundary (a : Nat) (ha : a < wordLimit) (s : Machine) :
    stackSafe (emit a .empty) s = true ↔ s.stack.length + 2 ≤ 1024 := by
  simp only [emit, Input.bytes, writes, List.nil_append, Input.terminal, List.length_nil]
  rw [stackSafe_pushNat 0 (by decide), stackSafe_pushNat a ha]
  simp only [stackSafe, step, List.length_cons, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem checkedRun_emit_suffix (a : Nat) (i : Input) (p : Program) (s : Machine)
    (h : Fits a i.bytes) (hs : s.stack.length + 2 ≤ 1024) :
    checkedRun (emit a i ++ p) s =
      some ({ s with memory := putBytes s.memory a i.bytes }, some i.observation) := by
  rw [checkedRun, stackSafe_emit_suffix a i p s h hs]
  exact run_emit_suffix a i p s h

theorem emitted_memory_frame (a x : Nat) (i : Input) (s : Machine)
    (hx : x < a ∨ a + i.bytes.length ≤ x) :
    putBytes s.memory a i.bytes x = s.memory x :=
  putBytes_frame s.memory a x i.bytes hx

theorem address_in_bounds (a : Nat) (bs : List UInt8) (h : Fits a bs)
    (k : Nat) (hk : k < bs.length) : a + k < wordLimit := by
  rcases h with ⟨_, _, hend⟩
  omega

/-- The bytes after the exact payload, including a partial final word, keep
all their original values. There is no implicit zero-fill claim. -/
theorem tail_untouched (a k : Nat) (bs : List UInt8) (m : Memory) :
    putBytes m a bs (a + bs.length + k) = m (a + bs.length + k) := by
  apply putBytes_frame
  omega

/-- Chunk sizes and count are unrestricted; the address advances by the
actual byte count of each chunk. Empty chunks are allowed. -/
def chunkWrites : Nat → List (List UInt8) → Program
  | _, [] => []
  | a, bs :: chunks => writes a bs ++ chunkWrites (a + bs.length) chunks

theorem chunkWrites_eq (a : Nat) (chunks : List (List UInt8)) :
    chunkWrites a chunks = writes a chunks.flatten := by
  induction chunks generalizing a with
  | nil => rfl
  | cons bs chunks ih =>
    simp only [chunkWrites, List.flatten_cons, writes_append, ih]

theorem run_chunkWrites (a : Nat) (chunks : List (List UInt8)) (p : Program)
    (s : Machine) (h : a + chunks.flatten.length ≤ wordLimit) :
    run (chunkWrites a chunks ++ p) s =
      run p { s with memory := putBytes s.memory a chunks.flatten } := by
  rw [chunkWrites_eq, run_writes a chunks.flatten p s h]

end Solidity.Backend.Failure
