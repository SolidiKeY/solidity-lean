import Solidity.Source.Eval
import Solidity.Backend.AbiWorld.ErrorEmission

/-! Measurements of the actual published ABI layout; no second byte encoder. -/
namespace Solidity.Backend.AbiWorld.PublishedLayout
open Roadmap

/-- Observed head size, allowing every part accepted by the published layout. -/
def headSize : List (Bool × Bytes) → Nat
  | [] => 0
  | (dynamic, bs) :: ps => (if dynamic then 32 else bs.length) + headSize ps

/-- Observed tail size. These are natural measurements, never replacement bytes. -/
def tailSize : List (Bool × Bytes) → Nat
  | [] => 0
  | (dynamic, bs) :: ps =>
    (if dynamic then 32 + (Source.pad32 bs).length else 0) + tailSize ps

/-- Actual head and tail lengths for arbitrary part lists and starting offsets. -/
theorem layout_go_lengths (parts : List (Bool × Bytes)) (off : Nat) :
    (Source.abiLayout.go parts off).1.length = headSize parts ∧
      (Source.abiLayout.go parts off).2.length = tailSize parts := by
  induction parts generalizing off with
  | nil => exact ⟨rfl, rfl⟩
  | cons p ps ih =>
    rcases p with ⟨dynamic, bs⟩
    cases dynamic with
    | false =>
      simp only [Source.abiLayout.go, headSize, tailSize, Bool.false_eq_true, ite_false,
        List.length_append, (ih off).1, (ih off).2, Nat.zero_add]
      trivial
    | true =>
      simp only [Source.abiLayout.go, headSize, tailSize, ite_true,
        List.length_append, Source.wordBytes_length, (ih _).1, (ih _).2]
      trivial

/-- The actual layout has exactly the measured head and tail bytes. -/
theorem layout_length (parts : List (Bool × Bytes)) :
    (Source.abiLayout parts).length = headSize parts + tailSize parts := by
  change ((Source.abiLayout.go parts (32 * parts.length)).1 ++
    (Source.abiLayout.go parts (32 * parts.length)).2).length = _
  rw [List.length_append, (layout_go_lengths _ _).1, (layout_go_lengths _ _).2]

/-- Canonical static parts give exactly the head region the existing encoder reserves.
The static-width premise is explicit; arbitrary raw static fragments need not satisfy it. -/
theorem canonical_head_size (parts : List (Bool × Bytes))
    (hs : ∀ p ∈ parts, p.1 = false → p.2.length = 32) :
    headSize parts = 32 * parts.length := by
  induction parts with
  | nil => rfl
  | cons p ps ih =>
    have ht : ∀ p ∈ ps, p.1 = false → p.2.length = 32 :=
      fun p hp => hs p (List.mem_cons_of_mem _ hp)
    have hh : p.1 = false → p.2.length = 32 := hs p List.mem_cons_self
    rcases p with ⟨dynamic, bs⟩
    cases dynamic with
    | false =>
      simp only [headSize, Bool.false_eq_true, ite_false, hh rfl, ih ht, List.length_cons,
        Nat.mul_add, Nat.mul_one]
      omega
    | true =>
      simp only [headSize, ite_true, ih ht, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- Every dynamic head records the actual cursor modulo the ABI word limit. -/
theorem dynamic_head (bs : Bytes) (parts : List (Bool × Bytes)) (off : Nat) :
    (Source.abiLayout.go ((true, bs) :: parts) off).1.take 32 =
      Source.wordBytes (Source.toWord off) := by
  change (Source.wordBytes (Source.toWord off) ++ _).take 32 = _
  exact List.take_left' (Source.wordBytes_length _)

/-- Numerical offset observation includes the existing word wrap exactly. -/
theorem dynamic_offset (bs : Bytes) (parts : List (Bool × Bytes)) (off : Nat) :
    Source.beValue ((Source.abiLayout.go ((true, bs) :: parts) off).1.take 32) =
      off % 2 ^ 256 := by
  rw [dynamic_head, Source.wordBytes_value]
  rfl

/-- Numerical length-word observation preserves exact modulo behavior for all lists. -/
theorem dynamic_length (bs : Bytes) (parts : List (Bool × Bytes)) (off : Nat) :
    Source.beValue ((Source.abiLayout.go ((true, bs) :: parts) off).2.take 32) =
      bs.length % 2 ^ 256 := by
  change Source.beValue (((Source.wordBytes (Source.toWord bs.length) ++ Source.pad32 bs) ++ _).take 32) = _
  rw [List.append_assoc, List.take_left' (Source.wordBytes_length _), Source.wordBytes_value]
  rfl

/-- Every dynamic tail retains every payload byte, including empty and boundary tails. -/
theorem dynamic_payload (bs : Bytes) (parts : List (Bool × Bytes)) (off : Nat) :
    ((Source.abiLayout.go ((true, bs) :: parts) off).2.drop 32).take bs.length = bs := by
  change (((Source.wordBytes (Source.toWord bs.length) ++ Source.pad32 bs) ++ _).drop 32).take bs.length = _
  rw [List.append_assoc, List.drop_left' (Source.wordBytes_length _)]
  change ((bs ++ List.replicate ((32 - bs.length % 32) % 32) 0) ++ _).take bs.length = _
  rw [List.append_assoc]
  exact List.take_left

/-- An arbitrary number of dynamic tails occupies an aligned length. -/
theorem tail_alignment (parts : List (Bool × Bytes)) : tailSize parts % 32 = 0 := by
  induction parts with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨dynamic, bs⟩
    cases dynamic with
    | false => simpa only [tailSize, Bool.false_eq_true, ite_false, Nat.zero_add] using ih
    | true =>
      have hp : (Source.pad32 bs).length % 32 = 0 := padded_alignment bs
      simp only [tailSize, ite_true]
      omega

/-- Canonical static widths and the measured tails give complete layout alignment. -/
theorem canonical_layout_alignment (parts : List (Bool × Bytes))
    (hs : ∀ p ∈ parts, p.1 = false → p.2.length = 32) :
    (Source.abiLayout parts).length % 32 = 0 := by
  rw [layout_length, canonical_head_size parts hs]
  have ht : tailSize parts % 32 = 0 := tail_alignment parts
  omega

/-- Layout concatenation uses the actual prefix tail size as its next cursor.
This is a theorem about the existing encoder, not a compositional redefinition. -/
theorem go_append (xs ys : List (Bool × Bytes)) (off : Nat) :
    Source.abiLayout.go (xs ++ ys) off =
      ((Source.abiLayout.go xs off).1 ++ (Source.abiLayout.go ys (off + tailSize xs)).1,
       (Source.abiLayout.go xs off).2 ++ (Source.abiLayout.go ys (off + tailSize xs)).2) := by
  induction xs generalizing off with
  | nil => simp only [List.nil_append, Source.abiLayout.go, tailSize, Nat.add_zero]
  | cons p ps ih =>
    rcases p with ⟨dynamic, bs⟩
    cases dynamic with
    | false =>
      simp only [List.cons_append, Source.abiLayout.go, tailSize, Bool.false_eq_true,
        ite_false, Nat.zero_add, ih, List.append_assoc]
    | true =>
      simp only [List.cons_append, Source.abiLayout.go, tailSize, ite_true,
        List.length_append, Source.wordBytes_length, ih, Nat.add_assoc, List.append_assoc]

/-- Later encoded parts cannot change any of the prefix's tail bytes. -/
theorem tail_noninterference (xs ys : List (Bool × Bytes)) (off : Nat) :
    (Source.abiLayout.go (xs ++ ys) off).2.take (tailSize xs) =
      (Source.abiLayout.go xs off).2 := by
  rw [go_append]
  exact List.take_left' (layout_go_lengths xs off).2

/-- The later head starts after exactly the measured prefix head bytes. -/
theorem later_head (xs ys : List (Bool × Bytes)) (off : Nat) :
    (Source.abiLayout.go (xs ++ ys) off).1.drop (headSize xs) =
      (Source.abiLayout.go ys (off + tailSize xs)).1 := by
  rw [go_append]
  exact List.drop_left' (layout_go_lengths xs off).1

/-- Equality of the two already-published numeral encodings, at every width. -/
theorem source_digits (k n : Nat) : Source.beBytes k n = Failure.digits k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [Source.beBytes, Failure.digits, ih]

/-- Source and intrinsic ABI words agree for every natural-number input, including overflow. -/
theorem source_word_bytes (n : Nat) :
    Source.wordBytes (Source.toWord n) = Semantics.wordBytes n := by
  rw [word_eq_numeral]
  change Source.beBytes 32 (n % 2 ^ 256) = Failure.digits 32 n
  rw [source_digits]
  have hlimit : 2 ^ 256 = 256 ^ 32 := by decide +kernel
  rw [hlimit, numeral_mod]

/-- Exact error-byte agreement consumes the independent source encoder unchanged. -/
theorem source_error_bytes (bs : Bytes) : Source.errorData bs = Semantics.encodeError bs := by
  unfold Source.errorData Semantics.encodeError
  rw [source_word_bytes, source_word_bytes]
  rfl

/-- Every published source Panic code retains its exact selector and word bytes. -/
theorem source_panic_bytes (code : Source.PanicCode) :
    Source.panicData code = Semantics.encodePanic code.code := by
  unfold Source.panicData Semantics.encodePanic
  rw [source_word_bytes]
  rfl

/-- A typed adapter into the existing real-instruction Panic emitter. -/
def sourcePanicInput (code : Source.PanicCode) : Failure.Input :=
  .panic ⟨code.code, by cases code <;> decide +kernel⟩

/-- Packet-specialized execution observes the actual independent source error bytes.
This does not compile a dynamic source body or discharge whole-call simulation. -/
theorem execute_source_error (a : Nat) (bs : Bytes) (suffix : Program)
    (s : Failure.Slice.Machine) (hf : Failure.Fits a (Source.errorData bs))
    (hs : s.stack.length + 2 ≤ 1024) :
    Failure.Slice.checkedRun (emitError a bs ++ suffix) s =
      some ({ s with memory := Failure.Slice.putBytes s.memory a (Source.errorData bs) },
        some (.revert (Source.errorData bs))) := by
  rw [source_error_bytes] at hf ⊢
  exact execute_error a bs suffix s hf hs

/-- All source Panic constructors select actual bytes of the published emitter. -/
theorem execute_source_panic (a : Nat) (code : Source.PanicCode) (suffix : Program)
    (s : Failure.Slice.Machine) (hf : Failure.Fits a (Source.panicData code))
    (hs : s.stack.length + 2 ≤ 1024) :
    Failure.Slice.checkedRun (Failure.emit a (sourcePanicInput code) ++ suffix) s =
      some ({ s with memory := Failure.Slice.putBytes s.memory a (Source.panicData code) },
        some (.revert (Source.panicData code))) := by
  rw [source_panic_bytes] at hf ⊢
  exact Failure.checkedRun_emit_suffix a (sourcePanicInput code) suffix s hf hs

/-- info: 'Solidity.Backend.AbiWorld.PublishedLayout.dynamic_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_length
/-- info: 'Solidity.Backend.AbiWorld.PublishedLayout.source_word_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_word_bytes
/-- info: 'Solidity.Backend.AbiWorld.PublishedLayout.execute_source_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms execute_source_error
/-- info: 'Solidity.Backend.AbiWorld.PublishedLayout.execute_source_panic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms execute_source_panic

/-- info: 'Solidity.Backend.AbiWorld.PublishedLayout.layout_go_lengths' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms layout_go_lengths
/-- info: 'Solidity.Backend.AbiWorld.PublishedLayout.dynamic_offset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_offset
/-- info: 'Solidity.Backend.AbiWorld.PublishedLayout.go_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms go_append
/-- info: 'Solidity.Backend.AbiWorld.PublishedLayout.tail_noninterference' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms tail_noninterference
end Solidity.Backend.AbiWorld.PublishedLayout
