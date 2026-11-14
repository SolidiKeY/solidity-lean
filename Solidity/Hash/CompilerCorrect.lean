import Solidity.Goals.Hash
import Solidity.Storage.Representation.Transport

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

/-- Symbolic slot interpretation is already reduced to a word. -/
theorem slot_word_lt (F : Roadmap.Fixed) (s : Slot) :
    (Storage.ofSlot s).word W (hashPre F) < W := by
  cases s <;> exact Nat.mod_lt _ W_pos

theorem address_val (F : Roadmap.Fixed) (s : Slot) :
    (address F s).val = (Storage.ofSlot s).word W (hashPre F) :=
  Nat.mod_eq_of_lt (slot_word_lt F s)

/-- Every recursively accessed representation preimage has word-sized fields. -/
theorem slot_pres_words (F : Roadmap.Fixed) (s : Slot) :
    ∀ p ∈ (Storage.ofSlot s).pres W (hashPre F), p.Words := by
  induction s with
  | root o => intro p hp; cases hp
  | hash k s o ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ih p hp
    · have he := List.mem_singleton.mp hp
      subst p
      exact ⟨k.isLt, slot_word_lt F s⟩
  | data s o ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ih p hp
    · have he := List.mem_singleton.mp hp
      subst p
      exact slot_word_lt F s

/-- Move the exact byte-level region obligation to its natural preimages. -/
theorem representation_regions (F : Roadmap.Fixed) (slots : List Slot)
    (hr : RegionsDisjoint W F.regionLen (fun b => (F.hash b).val)
      (List.range F.rootSlots) (preimages F slots)) :
    RegionsDisjoint W F.regionLen (hashPre F) (List.range F.rootSlots)
      (slots.flatMap (fun s => (Storage.ofSlot s).pres W (hashPre F))) := by
  have hw : ∀ p ∈ slots.flatMap (fun s => (Storage.ofSlot s).pres W (hashPre F)),
      p.Words := by
    intro p hp
    obtain ⟨s, _, hp⟩ := List.mem_flatMap.mp hp
    exact slot_pres_words F s p hp
  constructor
  · intro p hp q hq hne
    exact hr.1 (encoded p) (List.mem_map_of_mem hp)
      (encoded q) (List.mem_map_of_mem hq)
      (fun he => hne (encoded_inj (hw p hp) (hw q hq) he))
  · intro p hp r hroot
    exact hr.2 (encoded p) (List.mem_map_of_mem hp) r hroot

/-- E4A's explicit footprint supplies the existing finite transport conditions. -/
theorem representation_run (F : Roadmap.Fixed) (slots : List Slot)
    (hL : F.regionLen ≤ W) (hR : F.rootSlots ≤ W)
    (hb : ∀ s ∈ slots, (Storage.ofSlot s).Bounded F.regionLen F.rootSlots)
    (hr : RegionsDisjoint W F.regionLen (fun b => (F.hash b).val)
      (List.range F.rootSlots) (preimages F slots)) :
    Storage.Representation.FiniteRun W F.regionLen F.rootSlots (hashPre F)
      (slots.flatMap (fun s => (Storage.ofSlot s).pres W (hashPre F)))
      (slots.map Storage.ofSlot) where
  hash_bound p := (F.hash (encoded p)).isLt
  region_bound := hL
  root_bound := hR
  regions := representation_regions F slots hr
  bounded := by
    intro l hl
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hl
    exact hb s hs
  covered := by
    intro l hl p hp
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hl
    exact List.mem_flatMap.mpr ⟨s, hs, hp⟩

/-- On the explicit bounded footprint, numeric address equality reflects slot equality. -/
theorem address_injective_on (F : Roadmap.Fixed) (slots : List Slot)
    (hL : F.regionLen ≤ W) (hR : F.rootSlots ≤ W)
    (hb : ∀ s ∈ slots, (Storage.ofSlot s).Bounded F.regionLen F.rootSlots)
    (hr : RegionsDisjoint W F.regionLen (fun b => (F.hash b).val)
      (List.range F.rootSlots) (preimages F slots))
    {s t : Slot} (hs : s ∈ slots) (ht : t ∈ slots)
    (he : address F s = address F t) : s = t := by
  apply Storage.ofSlot_injective
  apply (representation_run F slots hL hR hb hr).word_inj
    (List.mem_map_of_mem hs) (List.mem_map_of_mem ht)
  have hv := congrArg Fin.val he
  simpa only [address_val] using hv

/-- A concrete numeric write preserves every covered symbolic observation. -/
theorem store_write_agrees (F : Roadmap.Fixed) (slots : List Slot)
    (hL : F.regionLen ≤ W) (hR : F.rootSlots ≤ W)
    (hb : ∀ s ∈ slots, (Storage.ofSlot s).Bounded F.regionLen F.rootSlots)
    (hr : RegionsDisjoint W F.regionLen (fun b => (F.hash b).val)
      (List.range F.rootSlots) (preimages F slots))
    (st : WordStore) (ns : Fin W → Fin W)
    (same : ∀ s ∈ slots, ns (address F s) = st.cells s)
    (s : Slot) (hs : s ∈ slots) (a : Fin W) :
    ∀ t ∈ slots, (if address F t = address F s then a else ns (address F t)) =
      (WordStore.write st s a.val).cells t := by
  intro t ht
  by_cases he : t = s
  · subst t
    rw [if_pos rfl, WordStore.write_cells_same]
  · rw [if_neg (fun eq => he (address_injective_on F slots hL hR hb hr ht hs eq))]
    apply (same t ht).trans
    apply Fin.ext
    exact (WordStore.write_other st a.val he).symm

/-- SLOAD preserves the full machine relation on the covered footprint. -/
theorem sload_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (s : Slot) (tail : List Word) (shape : m.stack = .slot s :: tail)
    (hs : s ∈ slots) :
    ResultRelated F slots (idealResult (Instr.sload.step m)) (numericAtom F .sload v) := by
  obtain ⟨stack, mem, store, env⟩ := rep
  have stack' : v.stack = address F s :: tail.map (word F) := by
    rw [stack, shape]
    rfl
  simp only [Instr.step, shape, numericAtom, stack', idealResult, ResultRelated]
  refine ⟨rfl, ?_, mem, store, env⟩
  simp only [List.map_cons, word, store s hs]

/-- SSTORE derives the numeric storage update; no step simulation is assumed. -/
theorem sstore_related (F : Roadmap.Fixed) (slots : List Slot)
    (hL : F.regionLen ≤ W) (hR : F.rootSlots ≤ W)
    (hb : ∀ s ∈ slots, (Storage.ofSlot s).Bounded F.regionLen F.rootSlots)
    (hr : RegionsDisjoint W F.regionLen (fun b => (F.hash b).val)
      (List.range F.rootSlots) (preimages F slots))
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (s : Slot) (a : Fin W) (tail : List Word)
    (shape : m.stack = .slot s :: .val a :: tail) (hs : s ∈ slots) :
    ResultRelated F slots (idealResult (Instr.sstore.step m)) (numericAtom F .sstore v) := by
  obtain ⟨stack, mem, store, env⟩ := rep
  have stack' : v.stack = address F s :: a :: tail.map (word F) := by
    rw [stack, shape]
    rfl
  simp only [Instr.step, shape, numericAtom, stack', idealResult, ResultRelated]
  exact ⟨True.intro, rfl, mem, store_write_agrees F slots hL hR hb hr m.store v.store store s hs a, env⟩

/-- Mapping KECCAK consumes exactly the numeric key and recursively interpreted parent. -/
theorem address_hash (F : Roadmap.Fixed) (k : Fin W) (s : Slot) :
    address F (.hash k s 0) = F.hash (encoded (.entry k.val (address F s).val)) := by
  apply Fin.ext
  simp only [address_val, Storage.ofSlot, Storage.Loc.word, hashPre, Nat.add_zero]
  exact Nat.mod_eq_of_lt (F.hash _).isLt

/-- Array KECCAK uses the same parent preimage as the symbolic location. -/
theorem address_data (F : Roadmap.Fixed) (s : Slot) :
    address F (.data s 0) = F.hash (encoded (.data (address F s).val)) := by
  apply Fin.ext
  simp only [address_val, Storage.ofSlot, Storage.Loc.word, hashPre, Nat.add_zero]
  exact Nat.mod_eq_of_lt (F.hash _).isLt

/-- Mapping hash execution commutes with the full machine representation. -/
theorem keccakMap_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (k : Fin W) (s : Slot) (tail : List Word)
    (shape : m.stack = .val k :: .slot s :: tail) :
    ResultRelated F slots (idealResult (Instr.keccakMap.step m))
      (numericAtom F .keccakMap v) := by
  obtain ⟨stack, mem, store, env⟩ := rep
  have stack' : v.stack = k :: address F s :: tail.map (word F) := by
    rw [stack, shape]
    rfl
  simp only [Instr.step, shape, numericAtom, stack', idealResult, ResultRelated]
  refine ⟨rfl, ?_, mem, store, env⟩
  simp only [List.map_cons, word, address_hash]

/-- Array hash execution commutes with the full machine representation. -/
theorem keccakArr_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (s : Slot) (tail : List Word) (shape : m.stack = .slot s :: tail) :
    ResultRelated F slots (idealResult (Instr.keccakArr.step m))
      (numericAtom F .keccakArr v) := by
  obtain ⟨stack, mem, store, env⟩ := rep
  have stack' : v.stack = address F s :: tail.map (word F) := by
    rw [stack, shape]
    rfl
  simp only [Instr.step, shape, numericAtom, stack', idealResult, ResultRelated]
  refine ⟨rfl, ?_, mem, store, env⟩
  simp only [List.map_cons, word, address_data]

/-- Symbolic offset addition is the same modular numeric address addition. -/
theorem address_add (F : Roadmap.Fixed) (s : Slot) (i : Nat) :
    address F (s.add i) = wmod ((address F s).val + i) := by
  apply Fin.ext
  cases s <;>
    simp only [address, Storage.ofSlot, Slot.add, Storage.Loc.word, wmod,
      Nat.mod_mod, Nat.mod_add_mod, Nat.add_assoc]

/-- Either legal symbolic-slot ADD order agrees with ordinary numeric ADD. -/
theorem add_slot_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (s : Slot) (i : Fin W) (tail : List Word)
    (shape : m.stack = .val i :: .slot s :: tail ∨
      m.stack = .slot s :: .val i :: tail) :
    ResultRelated F slots (idealResult (Instr.add.step m)) (numericAtom F .add v) := by
  obtain ⟨stack, mem, store, env⟩ := rep
  rcases shape with shape | shape <;>
    simp only [numericAtom, embed, stack, shape, List.map_cons, word, Instr.step,
      Machine.next, idealResult, resultMap, project, ResultRelated, Represents,
      List.map_map, Function.comp_def, List.map_id_fun', address_add, Nat.add_comm,
      true_and] <;>
    exact ⟨rfl, mem, store, env⟩

/-- A reached symbolic SLOAD emits exactly the numeric read event. -/
theorem sload_access_agrees (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (s : Slot) (tail : List Word) (shape : m.stack = .slot s :: tail)
    (rest : List Instr) (fs : List Frame) :
    (idealAccessAt (.running (.sload :: rest) 0 fs m)).map (mapAccess (address F)) =
      numericAccessAt (.running (.sload :: rest) 0 fs v) := by
  simp only [idealAccessAt, numericAccessAt, rep.1, shape, List.map_cons, word,
    List.map_nil, mapAccess]

/-- A reached symbolic SSTORE retains both the numeric address and written value. -/
theorem sstore_access_agrees (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (s : Slot) (a : Fin W) (tail : List Word)
    (shape : m.stack = .slot s :: .val a :: tail) (rest : List Instr) (fs : List Frame) :
    (idealAccessAt (.running (.sstore :: rest) 0 fs m)).map (mapAccess (address F)) =
      numericAccessAt (.running (.sstore :: rest) 0 fs v) := by
  simp only [idealAccessAt, numericAccessAt, rep.1, shape, List.map_cons, word,
    List.map_nil, mapAccess]

/-- Empty-stack storage/hash/ADD faults are retained by the numeric atom. -/
theorem empty_stack_fault_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v) (shape : m.stack = [])
    (i : Instr) (hi : i ∈ [.sload, .sstore, .keccakMap, .keccakArr, .add]) :
    ResultRelated F slots (idealResult (i.step m)) (numericAtom F i v) := by
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Instr.step, shape, numericAtom, rep.1, List.map_nil, embed,
      idealResult, resultMap, ResultRelated]

end Solidity.Hash.CompilerCorrect

/-- info: 'Solidity.Hash.CompilerCorrect.producer_produces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.producer_produces
/-- info: 'Solidity.Hash.CompilerCorrect.prefix_limit_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.prefix_limit_unique
/-- info: 'Solidity.Hash.CompilerCorrect.encoded_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.encoded_inj

/-- info: 'Solidity.Hash.CompilerCorrect.address_injective_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.address_injective_on

/-- info: 'Solidity.Hash.CompilerCorrect.sload_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.sload_related
/-- info: 'Solidity.Hash.CompilerCorrect.sstore_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.sstore_related
/-- info: 'Solidity.Hash.CompilerCorrect.keccakMap_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.keccakMap_related
/-- info: 'Solidity.Hash.CompilerCorrect.keccakArr_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.keccakArr_related
/-- info: 'Solidity.Hash.CompilerCorrect.add_slot_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.add_slot_related
/-- info: 'Solidity.Hash.CompilerCorrect.sload_access_agrees' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.sload_access_agrees
/-- info: 'Solidity.Hash.CompilerCorrect.sstore_access_agrees' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.sstore_access_agrees
/-- info: 'Solidity.Hash.CompilerCorrect.empty_stack_fault_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.empty_stack_fault_related
