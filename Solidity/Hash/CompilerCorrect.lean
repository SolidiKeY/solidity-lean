import Solidity.Goals.Hash

/-! Operational producers and encoding facts for the frozen E4A contract. -/
namespace Solidity.Hash.CompilerCorrect

open Solidity.Evm Solidity.Goals.HashContract

/-- Iterate the specified transition without filtering any execution prefix. -/
noncomputable def iteratePrefix (atom : Instr → S → Result S)
    (test : S → Option (Bool × S)) : Nat → Cursor S → Cursor S
  | 0, c => c
  | n + 1, c => tick atom test (iteratePrefix atom test n c)

/-- One producer for both machines, including terminal stuttering. -/
noncomputable def producer : Producer where
  ideal n c m := iteratePrefix (fun i s => idealResult (i.step s)) idealTest n (.running c 0 [] m)
  numeric F n c m := iteratePrefix (numericAtom F) numericTest n (.running c 0 [] m)

theorem producer_produces : Produces producer where
  ideal_zero _ _ := rfl
  numeric_zero _ _ _ := rfl
  ideal_succ _ _ _ := rfl
  numeric_succ _ _ _ _ := rfl

/-- The contract equations determine every ideal prefix uniquely. -/
theorem ideal_unique (E : Producer) (h : Produces E) (n : Nat)
    (c : List Instr) (m : Machine) : E.ideal n c m = producer.ideal n c m := by
  induction n with
  | zero => exact h.ideal_zero c m
  | succ n ih => rw [h.ideal_succ, producer_produces.ideal_succ, ih]

/-- Numeric traces are likewise fixed, even after a revert or fault. -/
theorem numeric_unique (E : Producer) (h : Produces E) (F : Roadmap.Fixed)
    (n : Nat) (c : List Instr) (m : Numeric) :
    E.numeric F n c m = producer.numeric F n c m := by
  induction n with
  | zero => exact h.numeric_zero F c m
  | succ n ih => rw [h.numeric_succ, producer_produces.numeric_succ, ih]

theorem prefix_halted (atom : Instr → S → Result S)
    (test : S → Option (Bool × S)) (n : Nat) (r : Result S) :
    iteratePrefix atom test n (.halted r) = .halted r := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iteratePrefix, ih, tick]

/-- Split an actual prefix at any instruction boundary. -/
theorem prefix_add (atom : Instr → S → Result S)
    (test : S → Option (Bool × S)) (n k : Nat) (c : Cursor S) :
    iteratePrefix atom test (n + k) c = iteratePrefix atom test k (iteratePrefix atom test n c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change tick atom test (iteratePrefix atom test (n + k) c) =
      tick atom test (iteratePrefix atom test k (iteratePrefix atom test n c))
    rw [ih]

/-- Once halted, every later prefix has exactly the same outcome. -/
theorem prefix_done_le (atom : Instr → S → Result S)
    (test : S → Option (Bool × S)) {n k : Nat} {c : Cursor S} {r : Result S}
    (hnk : n ≤ k) (hn : iteratePrefix atom test n c = .halted r) :
    iteratePrefix atom test k c = .halted r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnk
  rw [prefix_add, hn, prefix_halted]

/-- The limit convention always has an outcome, with fault for no terminal prefix. -/
theorem prefix_limit_exists (atom : Instr → S → Result S)
    (test : S → Option (Bool × S)) (c : Cursor S) :
    ∃ r, Limit (fun n => iteratePrefix atom test n c) r := by
  classical
  by_cases h : ∃ n r, iteratePrefix atom test n c = .halted r
  · obtain ⟨n, r, hn⟩ := h
    exact ⟨r, Or.inl ⟨n, hn⟩⟩
  · exact ⟨.fault, Or.inr ⟨rfl, fun n r hn => h ⟨n, r, hn⟩⟩⟩

/-- Fault-as-divergence cannot introduce a second limit outcome. -/
theorem prefix_limit_unique (atom : Instr → S → Result S)
    (test : S → Option (Bool × S)) (c : Cursor S) {r t : Result S}
    (hr : Limit (fun n => iteratePrefix atom test n c) r)
    (ht : Limit (fun n => iteratePrefix atom test n c) t) : r = t := by
  rcases hr with ⟨n, hn⟩ | ⟨rfl, hn⟩
  · rcases ht with ⟨k, hk⟩ | ⟨rfl, hk⟩
    · have h₁ := prefix_done_le atom test (Nat.le_max_left n k) hn
      have h₂ := prefix_done_le atom test (Nat.le_max_right n k) hk
      exact Cursor.halted.inj (h₁.symm.trans h₂)
    · exact False.elim (hk n r hn)
  · rcases ht with ⟨k, hk⟩ | ⟨rfl, _⟩
    · exact False.elim (hn k t hk)
    · rfl

/-- Each natural byte emitted by the ABI encoder fits in UInt8. -/
theorem bytesBE_lt (n v : Nat) : ∀ b ∈ Storage.bytesBE n v, b < 256 := by
  induction n generalizing v with
  | zero => simp [Storage.bytesBE]
  | succ n ih =>
    intro b hb
    simp only [Storage.bytesBE, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact ih _ _ hb
    · exact Nat.mod_lt _ (by decide)

theorem encode_lt (p : Storage.Pre) : ∀ b ∈ Storage.encode p, b < 256 := by
  cases p with
  | entry k w =>
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact bytesBE_lt 32 k b hb
    · exact bytesBE_lt 32 w b hb
  | data w => exact bytesBE_lt 32 w

/-- Decoding runtime bytes recovers the complete natural-byte preimage. -/
theorem encoded_toNat (p : Storage.Pre) :
    (encoded p).map UInt8.toNat = Storage.encode p := by
  simp only [encoded, List.map_map]
  calc
    _ = (Storage.encode p).map id := by
      apply List.map_congr_left
      intro b hb
      exact UInt8.toNat_ofNat_of_lt' (encode_lt p b hb)
    _ = Storage.encode p := List.map_id _

theorem encoded_eq_iff (p q : Storage.Pre) :
    encoded p = encoded q ↔ Storage.encode p = Storage.encode q := by
  constructor
  · intro h
    have h' := congrArg (List.map UInt8.toNat) h
    simpa only [encoded_toNat] using h'
  · intro h
    exact congrArg (List.map UInt8.ofNat) h

/-- Runtime encoding is injective on the same word domain as the natural encoder. -/
theorem encoded_inj {p q : Storage.Pre} (hp : p.Words) (hq : q.Words)
    (h : encoded p = encoded q) : p = q :=
  Storage.encode_inj hp hq ((encoded_eq_iff p q).mp h)

end Solidity.Hash.CompilerCorrect

/-- info: 'Solidity.Hash.CompilerCorrect.producer_produces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.producer_produces
/-- info: 'Solidity.Hash.CompilerCorrect.prefix_limit_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.prefix_limit_unique
/-- info: 'Solidity.Hash.CompilerCorrect.encoded_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.encoded_inj
