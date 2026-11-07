import Solidity.Evm.MachineV2

/-! Input bytes placed in word-addressed memory for `CALLIN`.

`wordBytes_bytesWord`: a 32-byte chunk survives `bytesWord` then
`wordBytes` (the MSTORE/byte-window round trip). `chunks` pads the input to
whole cells, `stores` emits one `PUSH`/`MSTORE` pair per cell, and
`readBytes_stores` reads exactly the input back from the window. -/
namespace Solidity.Backend.Passes.SourceCallBytes
open Solidity.Evm

/-! ## Big-endian digits -/

def value (l : List UInt8) : Nat := l.foldl byteStep 0

theorem fold_shift (l : List UInt8) (acc : Nat) :
    l.foldl byteStep acc = acc * 256 ^ l.length + l.foldl byteStep 0 := by
  induction l generalizing acc with
  | nil => simp only [List.foldl_nil, List.length_nil, Nat.pow_zero, Nat.mul_one, Nat.add_zero]
  | cons b l ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (byteStep 0 b)]
    simp only [byteStep, Nat.zero_mul, Nat.zero_add, Nat.pow_succ]
    rw [Nat.add_mul, ← Nat.add_assoc, Nat.mul_assoc acc 256, Nat.mul_comm 256]

theorem value_cons (b : UInt8) (l : List UInt8) :
    value (b :: l) = b.toNat * 256 ^ l.length + value l := by
  unfold value
  rw [List.foldl_cons, fold_shift]
  simp only [byteStep, Nat.zero_mul, Nat.zero_add]

theorem value_lt (l : List UInt8) : value l < 256 ^ l.length := by
  have h := bytesNat_fold_lt l 0
  rw [Nat.zero_add, Nat.one_mul] at h
  exact h

/-- Digit `i` of a big-endian list is its `i`-th byte. -/
theorem digit (l : List UInt8) (i : Nat) (h : i < l.length) :
    value l / 256 ^ (l.length - 1 - i) % 256 = l[i].toNat := by
  induction l generalizing i with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons b rest ih =>
    rw [value_cons]
    have hv := value_lt rest
    have hpos : 0 < 256 ^ rest.length := Nat.pow_pos (by decide)
    cases i with
    | zero =>
      have e : (b :: rest).length - 1 - 0 = rest.length := by
        simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero]
      rw [e, Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hv, Nat.zero_add,
        Nat.mod_eq_of_lt b.toNat_lt]
      rfl
    | succ j =>
      have hj : j < rest.length := by simp only [List.length_cons] at h; omega
      have e : (b :: rest).length - 1 - (j + 1) = rest.length - 1 - j := by
        simp only [List.length_cons]; omega
      have split : 256 ^ rest.length = 256 ^ (j + 1) * 256 ^ (rest.length - 1 - j) := by
        rw [← Nat.pow_add]; congr 1; omega
      have epos : 0 < 256 ^ (rest.length - 1 - j) := Nat.pow_pos (by decide)
      rw [e, split, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ epos,
        Nat.pow_succ, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
      rw [ih j hj]
      rfl

/-- **Round trip**: a 32-byte chunk is the bytes of its word. -/
theorem wordBytes_bytesWord (bs : List UInt8) (h : bs.length = 32) :
    wordBytes (bytesWord bs) = bs := by
  have take : (bs ++ List.replicate 32 0).take 32 = bs := by
    rw [List.take_append_of_le_length (by omega)]
    exact List.take_of_length_le (by omega)
  have hb : (bytesWord bs).1 = value bs := by
    simp only [bytesWord, bytesNat, take, value]
  apply List.ext_getElem
  · simp only [wordBytes, List.length_map, List.length_range, h]
  · intro i h1 h2
    simp only [wordBytes, List.getElem_map, List.getElem_range, hb]
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat']
    have d := digit bs i h2
    rw [h] at d
    exact d

/-! ## Chunks and stores -/

/-- The input in 32-byte cells, the last padded with zeroes. -/
def chunks : List UInt8 → List (List UInt8)
  | [] => []
  | b :: bs => ((b :: bs) ++ List.replicate 32 0).take 32 :: chunks ((b :: bs).drop 32)
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

theorem chunk_length (l : List UInt8) : ∀ c ∈ chunks l, c.length = 32 := by
  induction l using chunks.induct with
  | case1 => intro c m; simp only [chunks, List.not_mem_nil] at m
  | case2 b bs ih =>
    intro c m
    rw [chunks, List.mem_cons] at m
    rcases m with rfl | m
    · simp only [List.length_take, List.length_append, List.length_replicate]; omega
    · exact ih c m

theorem chunks_length (l : List UInt8) : (chunks l).length = cellsOf l.length := by
  induction l using chunks.induct with
  | case1 => rw [chunks]; rfl
  | case2 b bs ih =>
    rw [chunks, List.length_cons, ih]
    simp only [cellsOf, List.length_drop, List.length_cons]
    omega

theorem flatten_take (l : List UInt8) : (chunks l).flatten.take l.length = l := by
  induction l using chunks.induct with
  | case1 => rw [chunks]; rfl
  | case2 b bs ih =>
    rw [chunks, List.flatten_cons]
    have headLen : (((b :: bs) ++ List.replicate 32 0).take 32).length = 32 := by
      simp only [List.length_take, List.length_append, List.length_replicate]; omega
    by_cases short : (b :: bs).length ≤ 32
    · rw [List.take_append_of_le_length (by omega), List.take_take,
        Nat.min_eq_left short, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
    · have long : 32 ≤ (b :: bs).length := by omega
      have head : ((b :: bs) ++ List.replicate 32 0).take 32 = (b :: bs).take 32 := by
        rw [List.take_append_of_le_length long]
      have len : (b :: bs).length = 32 + ((b :: bs).drop 32).length := by
        rw [List.length_drop]; omega
      rw [head, len, List.take_append, List.take_of_length_le (by simp only [List.length_take]; omega),
        List.length_take, Nat.min_eq_left long, Nat.add_sub_cancel_left, ih, List.take_append_drop]

/-- One `PUSH word; MSTORE cell` pair per chunk, from cell `o` on. -/
def stores (o : Nat) : List (List UInt8) → List Instr
  | [] => []
  | c :: cs => .push (.val (bytesWord c)) :: .mstore o :: stores (o + 1) cs

def storeMem (mem : Nat → Word) (o : Nat) : List (List UInt8) → Nat → Word
  | [] => mem
  | c :: cs => storeMem (upd mem o (.val (bytesWord c))) (o + 1) cs

theorem run_stores (o : Nat) (cs : List (List UInt8)) (m : Machine) :
    run (stores o cs) m = .ok {m with mem := storeMem m.mem o cs} 0 := by
  induction cs generalizing o m with
  | nil => rfl
  | cons c cs ih =>
    have pair : run [.push (.val (bytesWord c)), .mstore o] m =
        .ok {m with mem := upd m.mem o (.val (bytesWord c))} 0 := rfl
    have split : stores o (c :: cs) = [.push (.val (bytesWord c)), .mstore o] ++ stores (o + 1) cs := rfl
    rw [split, run_append_ok pair, ih]
    rfl

theorem storeMem_below (mem : Nat → Word) (o : Nat) (cs : List (List UInt8)) (x : Nat)
    (h : x < o) : storeMem mem o cs x = mem x := by
  induction cs generalizing mem o with
  | nil => rfl
  | cons c cs ih =>
    rw [storeMem, ih _ _ (by omega), upd_other _ _ (by omega)]

theorem readCells_storeMem (mem : Nat → Word) (o : Nat) (cs : List (List UInt8))
    (h : ∀ c ∈ cs, c.length = 32) :
    readCells (storeMem mem o cs) o cs.length = some cs.flatten := by
  induction cs generalizing mem o with
  | nil => rfl
  | cons c cs ih =>
    have hc : c.length = 32 := h c (List.mem_cons_self ..)
    have rest := ih (upd mem o (.val (bytesWord c))) (o + 1)
      (fun d m => h d (List.mem_cons_of_mem _ m))
    have at_o : storeMem mem o (c :: cs) o = .val (bytesWord c) := by
      rw [storeMem, storeMem_below _ _ _ _ (Nat.lt_succ_self o), upd_same]
    rw [List.length_cons, readCells, at_o]
    simp only [storeMem] at rest ⊢
    rw [rest, wordBytes_bytesWord c hc, List.flatten_cons]
    rfl

/-- **Transport**: the stored window holds exactly the input. -/
theorem readBytes_stores (mem : Nat → Word) (o : Nat) (input : List UInt8) :
    readBytes (storeMem mem o (chunks input)) o input.length = some input := by
  unfold readBytes
  rw [← chunks_length, readCells_storeMem _ _ _ (chunk_length input)]
  simp only [Option.map_some, flatten_take]

end Solidity.Backend.Passes.SourceCallBytes

/-- info: 'Solidity.Backend.Passes.SourceCallBytes.fold_shift' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallBytes.fold_shift
/-- info: 'Solidity.Backend.Passes.SourceCallBytes.value_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallBytes.value_cons
/-- info: 'Solidity.Backend.Passes.SourceCallBytes.value_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallBytes.value_lt
/-- info: 'Solidity.Backend.Passes.SourceCallBytes.digit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallBytes.digit
/-- info: 'Solidity.Backend.Passes.SourceCallBytes.wordBytes_bytesWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallBytes.wordBytes_bytesWord
/-- info: 'Solidity.Backend.Passes.SourceCallBytes.chunk_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallBytes.chunk_length
/-- info: 'Solidity.Backend.Passes.SourceCallBytes.chunks_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallBytes.chunks_length
/-- info: 'Solidity.Backend.Passes.SourceCallBytes.flatten_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallBytes.flatten_take
/-- info: 'Solidity.Backend.Passes.SourceCallBytes.run_stores' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallBytes.run_stores
/-- info: 'Solidity.Backend.Passes.SourceCallBytes.storeMem_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallBytes.storeMem_below
/-- info: 'Solidity.Backend.Passes.SourceCallBytes.readCells_storeMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallBytes.readCells_storeMem
/-- info: 'Solidity.Backend.Passes.SourceCallBytes.readBytes_stores' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallBytes.readBytes_stores
