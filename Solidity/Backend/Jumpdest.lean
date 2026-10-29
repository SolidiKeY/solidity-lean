import Solidity.Backend.Opcode

/-!
# Jump-destination analysis (G45.05)

The EVM accepts a jump to offset `i` iff the byte there is `JUMPDEST`
(`0x5b`) and `i` is an instruction boundary: the scan that starts at 0 and
steps over each `PUSHn`'s `n` immediate bytes reaches it. Any byte list is
code here, including one that `decode` refuses (an undefined opcode is
one byte; a `PUSHn` near the end simply runs out of bytes).

* `starts c` — the boundaries, in order, by that scan;
* `jumpdests c` — the boundaries holding `JUMPDEST`; `validJumpdest c i`;
* `InPushData c i` — `i` lies in the immediate of a `PUSH` at a boundary.

Proved:

* `mem_starts` — `i` is a boundary iff `i < c.length` and `i` is not push data;
* `validJumpdest_iff` — a byte is a valid jump destination iff it is
  `JUMPDEST` and not inside push data;
* `starts_encode_append` — on encoded code the boundaries are exactly the
  instruction offsets, whatever bytes follow;
* `validJumpdest_encode_iff` — in `encode p`, offset `i` is valid iff an
  instruction of `p` at offset `i` is `JUMPDEST`.
-/

namespace Solidity.Backend

/-- The number of immediate bytes after an opcode byte: `n` for `PUSHn`, else 0. -/
def immWidth (b : UInt8) : Nat :=
  match pushWidth b with
  | some n => n.val
  | none => 0

/-- Instruction boundaries of a byte list, by the scan from offset 0. -/
def starts : List UInt8 → List Nat
  | [] => []
  | b :: bs => 0 :: (starts (bs.drop (immWidth b))).map (· + (immWidth b + 1))
termination_by c => c.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- `i` lies in the immediate data of a `PUSH` that starts at a boundary. -/
def InPushData (c : List UInt8) (i : Nat) : Prop :=
  ∃ j ∈ starts c, ∃ b, c[j]? = some b ∧ j < i ∧ i ≤ j + immWidth b

/-- The valid jump destinations: boundaries holding `JUMPDEST`. -/
def jumpdests (c : List UInt8) : List Nat :=
  (starts c).filter fun i => c[i]? == some Op.JUMPDEST.code

/-- Whether a jump to offset `i` of code `c` is allowed. -/
def validJumpdest (c : List UInt8) (i : Nat) : Bool := (jumpdests c).contains i

theorem starts_cons (b : UInt8) (bs : List UInt8) :
    starts (b :: bs) = 0 :: (starts (bs.drop (immWidth b))).map (· + (immWidth b + 1)) := by
  rw [starts]

theorem inPushData_cons (b : UInt8) (bs : List UInt8) (i : Nat) :
    InPushData (b :: bs) i ↔
      (0 < i ∧ i ≤ immWidth b) ∨
        ∃ k, i = k + (immWidth b + 1) ∧ InPushData (bs.drop (immWidth b)) k := by
  have hget : ∀ k, (b :: bs)[k + (immWidth b + 1)]? = (bs.drop (immWidth b))[k]? := by
    intro k
    rw [List.getElem?_drop, show k + (immWidth b + 1) = (immWidth b + k) + 1 by omega,
      List.getElem?_cons_succ]
  simp only [InPushData, starts_cons, List.mem_cons, List.mem_map]
  constructor
  · rintro ⟨j, hj, b', hb', hji, hij⟩
    rcases hj with rfl | ⟨k, hk, rfl⟩
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hb'
      subst hb'
      exact Or.inl ⟨hji, by omega⟩
    · refine Or.inr ⟨i - (immWidth b + 1), by omega, k, hk, b', ?_, by omega, by omega⟩
      rw [← hget, hb']
  · rintro (⟨h0, hw⟩ | ⟨k, rfl, j, hj, b', hb', hjk, hkj⟩)
    · exact ⟨0, Or.inl rfl, b, rfl, h0, by omega⟩
    · refine ⟨j + (immWidth b + 1), Or.inr ⟨j, hj, rfl⟩, b', ?_, by omega, by omega⟩
      rw [hget, hb']

theorem mem_starts (c : List UInt8) (i : Nat) :
    i ∈ starts c ↔ i < c.length ∧ ¬ InPushData c i := by
  fun_induction starts c generalizing i with
  | case1 => simp only [List.not_mem_nil, List.length_nil, Nat.not_lt_zero, false_and]
  | case2 b bs ih =>
    rw [inPushData_cons]
    simp only [List.mem_cons, List.mem_map, List.length_cons]
    have hlen : (bs.drop (immWidth b)).length = bs.length - immWidth b := List.length_drop
    by_cases h0 : i = 0
    · subst h0
      refine ⟨fun _ => ⟨by omega, ?_⟩, fun _ => Or.inl rfl⟩
      rintro (⟨h, _⟩ | ⟨k, hk, _⟩) <;> omega
    by_cases hw : i ≤ immWidth b
    · constructor
      · rintro (h | ⟨k, _, hk⟩) <;> omega
      · rintro ⟨_, h⟩
        exact absurd (Or.inl ⟨by omega, hw⟩) h
    · have hk : i = (i - (immWidth b + 1)) + (immWidth b + 1) := by omega
      have hiff := ih (i - (immWidth b + 1))
      constructor
      · rintro (h | ⟨k, hks, hki⟩)
        · omega
        · have hk' : k = i - (immWidth b + 1) := by omega
          subst hk'
          obtain ⟨hlt, hnd⟩ := hiff.mp hks
          refine ⟨by omega, ?_⟩
          rintro (⟨_, h⟩ | ⟨k', hk'', hd⟩)
          · omega
          · have : k' = i - (immWidth b + 1) := by omega
            subst this
            exact hnd hd
      · rintro ⟨hlt, hnd⟩
        refine Or.inr ⟨i - (immWidth b + 1), hiff.mpr ⟨by omega, fun hd => hnd (Or.inr ⟨_, hk, hd⟩)⟩, by omega⟩

/-- Instruction boundaries as the yellow paper's recurrence `N(i, w)`: offset
0 of non-empty code, and the offset after each boundary's opcode and its
immediate, while it is inside the code. Independent of `starts`. -/
inductive Boundary (c : List UInt8) : Nat → Prop where
  | zero : 0 < c.length → Boundary c 0
  | next {j : Nat} {b : UInt8} : Boundary c j → c[j]? = some b →
      j + immWidth b + 1 < c.length → Boundary c (j + immWidth b + 1)

theorem Boundary.cons {b : UInt8} {bs : List UInt8} {k : Nat}
    (h : Boundary (bs.drop (immWidth b)) k) : Boundary (b :: bs) (k + (immWidth b + 1)) := by
  have hlen : (bs.drop (immWidth b)).length = bs.length - immWidth b := List.length_drop
  induction h with
  | zero h0 =>
    have := Boundary.next (c := b :: bs) (j := 0) (b := b)
      (Boundary.zero (by simp only [List.length_cons]; omega)) rfl
      (by simp only [List.length_cons]; omega)
    rwa [show 0 + immWidth b + 1 = 0 + (immWidth b + 1) by omega] at this
  | @next j b' _ hb' hlt ih =>
    have hget : (b :: bs)[j + (immWidth b + 1)]? = some b' := by
      rw [show j + (immWidth b + 1) = (immWidth b + j) + 1 by omega, List.getElem?_cons_succ,
        ← List.getElem?_drop, hb']
    have := Boundary.next ih hget (by simp only [List.length_cons]; omega)
    rwa [show j + (immWidth b + 1) + immWidth b' + 1 = j + immWidth b' + 1 + (immWidth b + 1) by
      omega] at this

/-- `starts` computes exactly the boundaries of the recurrence. -/
theorem mem_starts_iff_boundary (c : List UInt8) (i : Nat) : i ∈ starts c ↔ Boundary c i := by
  constructor
  · intro h
    fun_induction starts c generalizing i with
    | case1 => exact absurd h List.not_mem_nil
    | case2 b bs ih =>
      simp only [List.mem_cons, List.mem_map] at h
      rcases h with rfl | ⟨k, hk, rfl⟩
      · exact Boundary.zero (by simp only [List.length_cons]; omega)
      · exact Boundary.cons (ih k hk)
  · intro h
    induction h with
    | zero h0 =>
      cases c with
      | nil => simp only [List.length_nil, Nat.lt_irrefl] at h0
      | cons b bs => rw [starts_cons]; exact List.mem_cons_self
    | @next j b _ hb hlt ih =>
      rw [mem_starts] at ih ⊢
      refine ⟨hlt, ?_⟩
      rintro ⟨j', hj', b', hb', hlo, hhi⟩
      have hj's := (mem_starts c j').mp hj'
      rcases Nat.lt_trichotomy j' j with hlt' | rfl | hgt
      · exact ih.2 ⟨j', hj', b', hb', hlt', by omega⟩
      · rw [hb] at hb'
        cases hb'
        omega
      · exact hj's.2 ⟨j, (mem_starts c j).mpr ih, b, hb, hgt, by omega⟩

theorem validJumpdest_iff (c : List UInt8) (i : Nat) :
    validJumpdest c i = true ↔ c[i]? = some Op.JUMPDEST.code ∧ ¬ InPushData c i := by
  simp only [validJumpdest, jumpdests, List.contains_iff_mem, List.mem_filter, mem_starts,
    beq_iff_eq]
  constructor
  · rintro ⟨⟨_, h⟩, hb⟩
    exact ⟨hb, h⟩
  · rintro ⟨hb, h⟩
    refine ⟨⟨?_, h⟩, hb⟩
    exact (List.getElem?_eq_some_iff.mp hb).1

/-! ## Encoded programs -/

theorem Instr.opcode_eq_jumpdest {i : Instr} (h : i.opcode = Op.JUMPDEST.code) :
    i = .op .JUMPDEST := by
  cases i with
  | op o => rw [Op.code_injective h]
  | push n imm =>
    have hw : pushWidth (pushCode n) = pushWidth Op.JUMPDEST.code := by
      simp only [opcode] at h; rw [h]
    rw [pushWidth_pushCode, Op.pushWidth_code] at hw
    cases hw

theorem immWidth_opcode (i : Instr) : immWidth i.opcode + 1 = i.size := by
  cases i with
  | op o => simp only [Instr.opcode, immWidth, Op.pushWidth_code, Instr.size]
  | push n imm => simp only [Instr.opcode, immWidth, pushWidth_pushCode, Instr.size]

theorem Instr.encode_eq (i : Instr) : ∃ imm : List UInt8,
    i.encode = i.opcode :: imm ∧ imm.length = immWidth i.opcode := by
  cases i with
  | op o => exact ⟨[], rfl, by simp only [List.length_nil, opcode, immWidth, Op.pushWidth_code]⟩
  | push n imm =>
    exact ⟨imm.toList, rfl, by simp only [Vector.length_toList, opcode, immWidth, pushWidth_pushCode]⟩

theorem starts_instr_append (i : Instr) (Y : List UInt8) :
    starts (i.encode ++ Y) = 0 :: (starts Y).map (· + i.size) := by
  obtain ⟨imm, he, hl⟩ := i.encode_eq
  rw [he, List.cons_append, starts_cons, ← hl, List.drop_left, hl, immWidth_opcode]

/-- The byte offset of a program's `k`-th instruction. -/
def offset (p : Program) (k : Nat) : Nat := size (p.take k)

theorem offset_cons_succ (i : Instr) (p : Program) (k : Nat) :
    offset (i :: p) (k + 1) = offset p k + i.size := by
  simp only [offset, List.take_succ_cons, size, List.map_cons, List.sum_cons]
  omega

theorem offset_append (q p : Program) (k : Nat) :
    offset (q ++ p) (q.length + k) = size q + offset p k := by
  simp only [offset, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, size, List.map_append, List.sum_append_nat]

/-- On encoded code the boundaries are the instruction offsets, followed by
the boundaries of whatever bytes come after, shifted. -/
theorem starts_encode_append (p : Program) (X : List UInt8) :
    starts (encode p ++ X) =
      (List.range p.length).map (offset p) ++ (starts X).map (· + size p) := by
  induction p with
  | nil => simp only [encode_nil, List.nil_append, List.length_nil, List.range_zero, List.map_nil,
      size, List.sum_nil, Nat.add_zero, List.map_id_fun', id_eq]
  | cons i p ih =>
    rw [encode_cons, List.append_assoc, starts_instr_append, ih, List.length_cons,
      List.range_succ_eq_map, List.map_cons, List.map_append, List.map_map, List.map_map,
      List.map_map]
    simp only [List.cons_append, List.cons.injEq]
    refine ⟨rfl, ?_⟩
    congr 1
    · apply List.map_congr_left
      intro k _
      simp only [Function.comp, offset_cons_succ]
    · apply List.map_congr_left
      intro m _
      simp only [Function.comp, size, List.map_cons, List.sum_cons]
      omega

theorem getElem?_encode_append_offset (p : Program) (X : List UInt8) {k : Nat} {i : Instr}
    (h : p[k]? = some i) : (encode p ++ X)[offset p k]? = some i.opcode := by
  induction p generalizing k with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at h
  | cons j p ih =>
    obtain ⟨imm, he, hl⟩ := j.encode_eq
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [offset, List.take_zero, size, List.map_nil, List.sum_nil, encode_cons, he,
        List.cons_append, List.getElem?_cons_zero]
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      rw [offset_cons_succ, encode_cons, he, List.cons_append, List.cons_append, List.append_assoc,
        show offset p k + j.size = (imm.length + offset p k) + 1 by
          rw [hl, ← immWidth_opcode]; omega,
        List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left, ih h]

/-- A `JUMPDEST` of an encoded program is a valid destination in any code
that starts with it. -/
theorem validJumpdest_encode_append (p : Program) (X : List UInt8) {k : Nat}
    (h : p[k]? = some (.op .JUMPDEST)) : validJumpdest (encode p ++ X) (offset p k) = true := by
  have hk : k < p.length := (List.getElem?_eq_some_iff.mp h).1
  simp only [validJumpdest, jumpdests, List.contains_iff_mem, List.mem_filter,
    starts_encode_append, List.mem_append, List.mem_map, List.mem_range, beq_iff_eq,
    getElem?_encode_append_offset p X h, Instr.opcode]
  exact ⟨Or.inl ⟨k, hk, rfl⟩, trivial⟩

/-- In an encoded program, a jump to byte `n` is valid iff some instruction
at offset `n` is `JUMPDEST`. -/
theorem validJumpdest_encode_iff (p : Program) (n : Nat) :
    validJumpdest (encode p) n = true ↔ ∃ k, p[k]? = some (.op .JUMPDEST) ∧ offset p k = n := by
  constructor
  · intro hv
    have hv' := hv
    simp only [validJumpdest, jumpdests, List.contains_iff_mem, List.mem_filter, beq_iff_eq] at hv'
    obtain ⟨hs, hb⟩ := hv'
    have hs' := hs
    rw [← List.append_nil (encode p), starts_encode_append] at hs'
    simp only [starts, List.map_nil, List.append_nil, List.mem_map, List.mem_range] at hs'
    obtain ⟨k, hk, rfl⟩ := hs'
    have hpk : p[k]? = some p[k] := List.getElem?_eq_getElem hk
    have hb' := getElem?_encode_append_offset p [] hpk
    rw [List.append_nil, hb, Option.some.injEq] at hb'
    exact ⟨k, by rw [hpk, Instr.opcode_eq_jumpdest hb'.symm], rfl⟩
  · rintro ⟨k, hk, rfl⟩
    have := validJumpdest_encode_append p [] hk
    rwa [List.append_nil] at this

theorem offset_lt_size {p : Program} {k : Nat} (hk : k < p.length) : offset p k < size p := by
  have hsplit : size p = offset p k + size (p.drop k) := by
    conv => lhs; rw [← List.take_append_drop k p]
    simp only [size, offset, List.map_append, List.sum_append_nat]
  obtain ⟨i, q, hq⟩ : ∃ i q, p.drop k = i :: q := by
    cases h : p.drop k with
    | nil => simp only [List.drop_eq_nil_iff] at h; omega
    | cons i q => exact ⟨i, q, rfl⟩
  have hi : 0 < i.size := by cases i <;> simp only [Instr.size] <;> omega
  rw [hsplit, hq]
  simp only [size, List.map_cons, List.sum_cons]
  omega

/-- Before the end of `encode p`, trailing bytes change no jump destination:
offset `n` is valid iff an instruction of `p` at `n` is `JUMPDEST`. -/
theorem validJumpdest_encode_append_iff (p : Program) (X : List UInt8) {n : Nat}
    (hn : n < size p) :
    validJumpdest (encode p ++ X) n = true ↔
      ∃ k, p[k]? = some (.op .JUMPDEST) ∧ offset p k = n := by
  constructor
  · intro hv
    simp only [validJumpdest, jumpdests, List.contains_iff_mem, List.mem_filter, beq_iff_eq,
      starts_encode_append, List.mem_append, List.mem_map, List.mem_range] at hv
    obtain ⟨hs, hb⟩ := hv
    rcases hs with ⟨k, hk, rfl⟩ | ⟨m, _, rfl⟩
    · have hpk : p[k]? = some p[k] := List.getElem?_eq_getElem hk
      have hb' := getElem?_encode_append_offset p X hpk
      rw [hb, Option.some.injEq] at hb'
      exact ⟨k, by rw [hpk, Instr.opcode_eq_jumpdest hb'.symm], rfl⟩
    · omega
  · rintro ⟨k, hk, rfl⟩
    exact validJumpdest_encode_append p X hk

/-- Relocation: behind an encoded prefix of size `size q`, every jump
destination of `Y` moves by exactly `size q`. -/
theorem validJumpdest_encode_prefix (q : Program) (Y : List UInt8) (n : Nat) :
    validJumpdest (encode q ++ Y) (size q + n) = validJumpdest Y n := by
  have hbyte : (encode q ++ Y)[size q + n]? = Y[n]? := by
    rw [List.getElem?_append_right (by rw [length_encode]; omega), length_encode,
      Nat.add_sub_cancel_left]
  have hmem : size q + n ∈ starts (encode q ++ Y) ↔ n ∈ starts Y := by
    rw [starts_encode_append]
    simp only [List.mem_append, List.mem_map, List.mem_range]
    constructor
    · rintro (⟨k, hk, hkn⟩ | ⟨m, hm, hmn⟩)
      · have := offset_lt_size hk
        omega
      · rwa [show n = m by omega]
    · intro h
      exact Or.inr ⟨n, h, by omega⟩
  apply Bool.eq_iff_iff.mpr
  simp only [validJumpdest, jumpdests, List.contains_iff_mem, List.mem_filter, beq_iff_eq,
    hbyte, hmem]

end Solidity.Backend
