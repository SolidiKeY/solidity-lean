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
      List.map_map, Function.comp_def, address_add, Nat.add_comm,
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
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Instr.step, shape, numericAtom, rep.1, List.map_nil, embed,
      idealResult, resultMap, ResultRelated]

/-- One semantic loop turn unfolds even when its remaining execution diverges. -/
theorem loop_run_unfold (rc rb : Machine → Evm.Out) (m : Machine) :
    loopRun rc rb m =
      match loopTurn rc rb m with
      | .inl next => loopRun rc rb next
      | .inr out => out := by
  cases ht : loopTurn rc rb m with
  | inr r =>
    exact loopRun_of_iterN (n := 1) (by simp only [loopIterN, ht])
  | inl next =>
    by_cases h : ∃ r n, loopIterN rc rb n next = .inr r
    · obtain ⟨r, n, hn⟩ := h
      simp only [loopRun_of_iterN hn]
      exact loopRun_of_iterN (n := n + 1) (by simp only [loopIterN, ht, hn])
    · have hm : ¬ ∃ r n, loopIterN rc rb n m = .inr r := by
        rintro ⟨r, n, hn⟩
        cases n with
        | zero => cases hn
        | succ n => exact h ⟨r, n, by simpa only [loopIterN, ht] using hn⟩
      simp only [loopRun, h, hm, dif_neg, not_false_eq_true]

/-- Reinterpret the contract result in the existing EVM outcome type. -/
def outOfResult : Result Machine → Evm.Out
  | .ok m k => .ok m k
  | .revert => .revert
  | .fault => .fault

/-- Remaining loop execution, followed by the code after the loop. -/
noncomputable def continueLoop (c b rest : List Instr) (m : Machine) : Evm.Out :=
  (loopRun (Evm.run c) (Evm.run b) m).bind (fun m k => Evm.exec rest k m)

noncomputable def bodyResult (c b rest : List Instr) : Evm.Out → Evm.Out
  | .ok m 0 => continueLoop c b rest m
  | .ok _ (_ + 1) => .fault
  | .revert => .revert
  | .fault => .fault

noncomputable def testResult (c b rest : List Instr) : Evm.Out → Evm.Out
  | .ok m 0 =>
    match m.stack with
    | .val w :: tail =>
      if w.val = 0 then Evm.run rest {m with stack := tail}
      else bodyResult c b rest (Evm.run b {m with stack := tail})
    | _ => .fault
  | .ok _ (_ + 1) => .fault
  | .revert => .revert
  | .fault => .fault

noncomputable def frameResult : Frame → Evm.Out → Evm.Out
  | .test c b rest => testResult c b rest
  | .body c b rest => bodyResult c b rest

noncomputable def finishFrames : List Frame → Evm.Out → Evm.Out
  | [], r => r
  | f :: fs, r => finishFrames fs (frameResult f r)

/-- Denotation includes all pending frames, including divergent continuations. -/
noncomputable def denoteCursor : Cursor Machine → Evm.Out
  | .running c k fs m => finishFrames fs (Evm.exec c k m)
  | .halted r => outOfResult r

theorem finishFrames_fault (fs : List Frame) : finishFrames fs .fault = .fault := by
  induction fs with
  | nil => rfl
  | cons f fs ih => cases f <;> exact ih

theorem finishFrames_revert (fs : List Frame) : finishFrames fs .revert = .revert := by
  induction fs with
  | nil => rfl
  | cons f fs ih => cases f <;> exact ih

theorem continueLoop_test (c b rest : List Instr) (m : Machine) :
    continueLoop c b rest m = testResult c b rest (Evm.run c m) := by
  unfold continueLoop
  rw [loop_run_unfold]
  cases hc : Evm.run c m with
  | fault => simp [loopTurn, hc, testResult, Evm.Out.bind]
  | revert => simp [loopTurn, hc, testResult, Evm.Out.bind]
  | ok s k =>
    cases k with
    | succ k => simp [loopTurn, hc, testResult, Evm.Out.bind]
    | zero =>
      cases hs : s.stack with
      | nil => simp [loopTurn, hc, hs, testResult, Evm.Out.bind]
      | cons x tail =>
        cases x with
        | slot a => simp [loopTurn, hc, hs, testResult, Evm.Out.bind]
        | val w =>
          by_cases hz : w.val = 0
          · simp only [loopTurn, hc, hs, hz, if_pos, testResult, Evm.Out.bind]; rfl
          · cases hb : Evm.run b {s with stack := tail} with
            | fault => simp [loopTurn, hc, hs, hz, hb, testResult, bodyResult, Evm.Out.bind]
            | revert => simp [loopTurn, hc, hs, hz, hb, testResult, bodyResult, Evm.Out.bind]
            | ok t j =>
              cases j <;> simp [loopTurn, hc, hs, hz, hb, testResult, bodyResult,
                continueLoop, Evm.Out.bind]

/-- An atomic transition preserves the denotation of its entire continuation. -/
theorem denote_atom (out : Evm.Out) (rest : List Instr) (fs : List Frame) :
    denoteCursor (match idealResult out with
      | .ok m k => .running rest k fs m
      | .revert => .halted .revert
      | .fault => .halted .fault) =
    finishFrames fs (out.bind (fun m k => Evm.exec rest k m)) := by
  cases out with
  | ok m k => rfl
  | revert => exact (finishFrames_revert fs).symm
  | fault => exact (finishFrames_fault fs).symm

/-- Every specified ideal tick preserves the complete EVM denotation. -/
theorem denote_tick (cur : Cursor Machine) :
    denoteCursor (tick (fun i s => idealResult (i.step s)) idealTest cur) =
      denoteCursor cur := by
  cases cur with
  | halted r => rfl
  | running code k fs m =>
    cases code with
    | nil =>
      cases fs with
      | nil => cases k <;> rfl
      | cons f fs =>
        cases k with
        | succ k =>
          cases f <;>
            simp [tick, denoteCursor, Evm.exec, finishFrames, frameResult,
              testResult, bodyResult, outOfResult, finishFrames_fault]
        | zero =>
          cases f with
          | body c b rest =>
            exact congrArg (finishFrames fs) (continueLoop_test c b rest m).symm
          | test c b rest =>
            cases hs : m.stack with
            | nil =>
              simp [tick, idealTest, hs, denoteCursor, Evm.exec, finishFrames,
                frameResult, testResult, outOfResult, finishFrames_fault]
            | cons x tail =>
              cases x with
              | slot a =>
                simp [tick, idealTest, hs, denoteCursor, Evm.exec, finishFrames,
                  frameResult, testResult, outOfResult, finishFrames_fault]
              | val w =>
                by_cases hz : w.val = 0
                · simp [tick, idealTest, hs, hz, denoteCursor, Evm.exec, finishFrames,
                    frameResult, testResult, Evm.run]
                · have flag : (w.val == 0) = false :=
                    Bool.eq_false_iff.mpr (fun h => hz (beq_iff_eq.mp h))
                  simp [tick, idealTest, hs, hz, flag, bne, denoteCursor, Evm.exec,
                    finishFrames, frameResult, testResult, Evm.run]
    | cons i rest =>
      cases k with
      | succ k => simp only [tick, denoteCursor, Evm.exec]
      | zero =>
        have ha := denote_atom (i.step m) rest fs
        generalize ho : i.step m = out at ha
        cases i <;> try
          simp only [tick, denoteCursor, exec_cons_zero, ho]
          cases out <;> simpa only [idealResult, denoteCursor, Evm.Out.bind] using ha
        case loop c b =>
          exact congrArg (finishFrames fs) (continueLoop_test c b rest m).symm

theorem denote_prefix (n : Nat) (cur : Cursor Machine) :
    denoteCursor (iteratePrefix (fun i s => idealResult (i.step s)) idealTest n cur) =
      denoteCursor cur := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iteratePrefix, denote_tick, ih]

/-- Any actual finite terminal prefix agrees with the original EVM semantics. -/
theorem ideal_finite_sound (n : Nat) (c : List Instr) (m : Machine) (r : Result Machine)
    (h : producer.ideal n c m = .halted r) : idealResult (Evm.run c m) = r := by
  have hd := denote_prefix n (.running c 0 [] m)
  change denoteCursor (producer.ideal n c m) = Evm.run c m at hd
  rw [h] at hd
  have hr : idealResult (outOfResult r) = r := by cases r <;> rfl
  exact (congrArg idealResult hd).symm.trans hr

/-- Reachability uses precisely the already fixed ideal tick sequence. -/
def IdealReaches (a b : Cursor Machine) : Prop :=
  ∃ n, iteratePrefix (fun i s => idealResult (i.step s)) idealTest n a = b

theorem reaches_refl (a : Cursor Machine) : IdealReaches a a := ⟨0, rfl⟩

theorem reaches_tick (a : Cursor Machine) :
    IdealReaches a (tick (fun i s => idealResult (i.step s)) idealTest a) := ⟨1, rfl⟩

theorem reaches_trans {a b c : Cursor Machine} (hab : IdealReaches a b)
    (hbc : IdealReaches b c) : IdealReaches a c := by
  obtain ⟨n, hn⟩ := hab
  obtain ⟨k, hk⟩ := hbc
  exact ⟨n + k, by rw [prefix_add, hn, hk]⟩

/-- Non-fault loop outcomes have a finite witness, even with unbounded loops. -/
theorem loop_nonfault_witness (rc rb : Machine → Evm.Out) (m : Machine)
    (h : loopRun rc rb m ≠ .fault) :
    ∃ n, loopIterN rc rb n m = .inr (loopRun rc rb m) := by
  by_cases hex : ∃ r n, loopIterN rc rb n m = .inr r
  · obtain ⟨r, n, hn⟩ := hex
    exact ⟨n, by rw [loopRun_of_iterN hn]; exact hn⟩
  · exact False.elim (h (by simp only [loopRun, hex, dif_neg, not_false_eq_true]))

/-- A completed subcode leaves successful results at its frame boundary. -/
def afterCode (fs : List Frame) : Evm.Out → Cursor Machine
  | .ok m k => .running [] k fs m
  | .revert => .halted .revert
  | .fault => .halted .fault

/-- Internal induction property; no completeness premise is added to the goal. -/
def CodeComplete (c : List Instr) : Prop :=
  ∀ k fs m, Evm.exec c k m ≠ .fault →
    IdealReaches (.running c k fs m) (afterCode fs (Evm.exec c k m))

theorem complete_run {c : List Instr} (hc : CodeComplete c) (fs : List Frame)
    (m : Machine) (r : Evm.Out) (hr : Evm.run c m = r) (hne : r ≠ .fault) :
    IdealReaches (.running c 0 fs m) (afterCode fs r) := by
  have h := hc 0 fs m
  change Evm.run c m ≠ .fault →
    IdealReaches (.running c 0 fs m) (afterCode fs (Evm.run c m)) at h
  rw [hr] at h
  exact h hne

theorem complete_nil : CodeComplete [] := by
  intro k fs m _
  exact reaches_refl _

/-- Pending jumps consume instructions without invoking their semantics. -/
theorem complete_skip {rest : List Instr} (hr : CodeComplete rest)
    (i : Instr) (k : Nat) (fs : List Frame) (m : Machine)
    (hne : Evm.exec (i :: rest) (k + 1) m ≠ .fault) :
    IdealReaches (.running (i :: rest) (k + 1) fs m)
      (afterCode fs (Evm.exec (i :: rest) (k + 1) m)) := by
  rw [exec_cons_succ] at hne ⊢
  have ht := reaches_tick (.running (i :: rest) (k + 1) fs m)
  simp only [tick] at ht
  exact reaches_trans ht (hr k fs m hne)

def afterAtom (rest : List Instr) (fs : List Frame) : Evm.Out → Cursor Machine
  | .ok m k => .running rest k fs m
  | .revert => .halted .revert
  | .fault => .halted .fault

/-- Realize finitely many semantic loop turns using the actual ideal ticks. -/
theorem loop_turns_complete (c b : List Instr) (hc : CodeComplete c)
    (hb : CodeComplete b) (rest : List Instr) (fs : List Frame)
    (n : Nat) (m : Machine) (r : Evm.Out)
    (hn : loopIterN (Evm.run c) (Evm.run b) n m = .inr r) (hne : r ≠ .fault) :
    IdealReaches (.running c 0 (.test c b rest :: fs) m) (afterAtom rest fs r) := by
  induction n generalizing m with
  | zero => cases hn
  | succ n ih =>
    cases hcond : Evm.run c m with
    | fault => simp [loopIterN, loopTurn, hcond] at hn; exact False.elim (hne hn.symm)
    | revert =>
      simp only [loopIterN, loopTurn, hcond, Sum.inr.injEq] at hn
      subst r
      exact complete_run hc _ m .revert hcond (by intro h; cases h)
    | ok s k =>
      cases k with
      | succ k => simp [loopIterN, loopTurn, hcond] at hn; exact False.elim (hne hn.symm)
      | zero =>
        have hcr := complete_run hc (.test c b rest :: fs) m (.ok s 0) hcond
          (by intro h; cases h)
        cases hs : s.stack with
        | nil => simp [loopIterN, loopTurn, hcond, hs] at hn; exact False.elim (hne hn.symm)
        | cons x tail =>
          cases x with
          | slot a => simp [loopIterN, loopTurn, hcond, hs] at hn; exact False.elim (hne hn.symm)
          | val w =>
            have ht := reaches_tick (.running [] 0 (.test c b rest :: fs) s)
            by_cases hz : w.val = 0
            · simp only [loopIterN, loopTurn, hcond, hs, hz, if_pos, Sum.inr.injEq] at hn
              subst r
              simp [tick, idealTest, hs, hz] at ht
              exact reaches_trans hcr ht
            · have flag : (w.val == 0) = false :=
                Bool.eq_false_iff.mpr (fun h => hz (beq_iff_eq.mp h))
              simp [tick, idealTest, hs, flag, bne] at ht
              cases hbody : Evm.run b {s with stack := tail} with
              | fault =>
                simp [loopIterN, loopTurn, hcond, hs, hz, hbody] at hn
                exact False.elim (hne hn.symm)
              | revert =>
                simp only [loopIterN, loopTurn, hcond, hs, hz, if_false, hbody,
                  Sum.inr.injEq] at hn
                subst r
                exact reaches_trans (reaches_trans hcr ht)
                  (complete_run hb _ _ .revert hbody (by intro h; cases h))
              | ok t j =>
                cases j with
                | succ j =>
                  simp [loopIterN, loopTurn, hcond, hs, hz, hbody] at hn
                  exact False.elim (hne hn.symm)
                | zero =>
                  simp only [loopIterN, loopTurn, hcond, hs, hz, if_false, hbody] at hn
                  have hbr := complete_run hb (.body c b rest :: fs) _ (.ok t 0) hbody
                    (by intro h; cases h)
                  have hbt := reaches_tick (.running [] 0 (.body c b rest :: fs) t)
                  exact reaches_trans (reaches_trans (reaches_trans (reaches_trans hcr ht)
                    hbr) hbt) (ih t hn)

mutual
/-- Every non-fault instruction outcome has its actual finite execution. -/
theorem instr_complete (i : Instr) (m : Machine) (rest : List Instr) (fs : List Frame)
    (hne : i.step m ≠ .fault) :
    IdealReaches (.running (i :: rest) 0 fs m) (afterAtom rest fs (i.step m)) := by
  have ht := reaches_tick (.running (i :: rest) 0 fs m)
  generalize ho : i.step m = out at *
  cases shape : i <;> simp only [shape] at ho ht <;> try
    cases out <;> simpa only [tick, ho, idealResult, afterAtom] using ht
  case loop c b =>
    have hloop : loopRun (Evm.run c) (Evm.run b) m ≠ .fault := by
      change (Instr.loop c b).step m ≠ .fault
      rwa [ho]
    obtain ⟨n, hn⟩ := loop_nonfault_witness (Evm.run c) (Evm.run b) m hloop
    have hr := loop_turns_complete c b (code_complete c) (code_complete b)
      rest fs n m _ hn hloop
    change IdealReaches _ (afterAtom rest fs ((Instr.loop c b).step m)) at hr
    rw [ho] at hr
    exact reaches_trans ht hr
termination_by sizeOf i
decreasing_by all_goals simp_all only; all_goals simp_wf; all_goals omega

/-- Structural completeness includes nested loops and arbitrary pending frames. -/
theorem code_complete (c : List Instr) : CodeComplete c := by
  intro k fs m hne
  cases shape : c with
  | nil => exact complete_nil k fs m (by simpa only [shape] using hne)
  | cons i rest =>
    rw [shape] at hne
    cases k with
    | succ k => exact complete_skip (code_complete rest) i k fs m hne
    | zero =>
      rw [exec_cons_zero] at hne ⊢
      cases hi : i.step m with
      | fault => simp only [hi, Evm.Out.bind, ne_eq, not_true_eq_false] at hne
      | revert =>
        have h := instr_complete i m rest fs (by rw [hi]; intro h; cases h)
        simpa only [hi, Evm.Out.bind, afterCode, afterAtom] using h
      | ok t j =>
        have h := instr_complete i m rest fs (by rw [hi]; intro h; cases h)
        simp only [hi, Evm.Out.bind] at hne ⊢
        rw [hi] at h
        exact reaches_trans h (code_complete rest j fs t hne)
termination_by sizeOf c
decreasing_by all_goals simp_all only; all_goals simp_wf; all_goals omega
end

theorem ideal_nonfault_complete (c : List Instr) (m : Machine)
    (hne : Evm.run c m ≠ .fault) :
    ∃ n, producer.ideal n c m = .halted (idealResult (Evm.run c m)) := by
  have hc := complete_run (code_complete c) [] m (Evm.run c m) rfl hne
  cases hr : Evm.run c m with
  | fault => exact False.elim (hne hr)
  | revert => simpa only [hr, afterCode, idealResult, IdealReaches, producer] using hc
  | ok t k =>
    rw [hr] at hc
    have ht : IdealReaches (.running [] k [] t) (.halted (.ok t k)) :=
      ⟨1, by cases k <;> rfl⟩
    exact reaches_trans hc ht

/-- Limit soundness uses non-fault completeness in the no-terminal-prefix case. -/
theorem ideal_limit_sound (c : List Instr) (m : Machine) (out : Result Machine)
    (h : Limit (fun n => producer.ideal n c m) out) :
    out = idealResult (Evm.run c m) := by
  rcases h with ⟨n, hn⟩ | ⟨rfl, hn⟩
  · exact (ideal_finite_sound n c m out hn).symm
  · by_cases hf : Evm.run c m = .fault
    · rw [hf]; rfl
    · obtain ⟨n, he⟩ := ideal_nonfault_complete c m hf
      exact False.elim (hn n _ he)

/-- Adequacy for all ideal code, including nested loops and divergence. -/
theorem producer_idealAdequacy : IdealAdequacy producer := by
  intro c m out
  constructor
  · exact ideal_limit_sound c m out
  · intro h
    obtain ⟨r, hr⟩ := prefix_limit_exists (fun i s => idealResult (i.step s)) idealTest
      (.running c 0 [] m)
    have he := ideal_limit_sound c m r hr
    rw [← h] at he
    cases he
    exact hr

/-- Once the compiler simulation is proved, its actual prefix failures are
bounded by the existing adaptive theorem on one shared transcript. -/
theorem adaptive_of_compilerBridge (E : Producer) (bridge : CompilerBridge E) :
    AdaptiveBridge E := by
  classical
  intro C Γ Δ b frag P r compiled F s dom q n L frame base σ m v observed
    hs hroots hinput hready hqueries
  let ys := fun g => preimages (CollisionBridge.oracleFixed F dom g)
    (locations E n r.code (m g) observed)
  let xs := fun g => queries E (CollisionBridge.oracleFixed F dom g) n r.code (v g) ++ ys g
  have hbound := CollisionBridge.run_premise_le F hs hroots q xs ys hqueries
    (fun g hg x hx => hqueries g hg x (List.mem_append_right _ hx))
  apply CollisionBridge.scale_count_le (b :=
    (tuples W dom.length).countP (CollisionBridge.runPremiseFails F dom xs ys)) _ hbound
  apply countP_le_of_imp
  intro g hg hbad
  simp only [Solidity.Goals.HashContract.failure, decide_eq_true_eq] at hbad
  apply decide_eq_true
  intro hp
  have hb := bridge b frag P r compiled L frame (base g) (σ g) (m g) (hinput g hg)
  exact hbad ((hb.2 (CollisionBridge.oracleFixed F dom g) (v g) observed).1 n
    (hready g hg) hp)

/-- Pointwise correspondence preserves both terminal and divergent limits. -/
theorem limits_related (F : Roadmap.Fixed) (c : List Instr) (m : Machine) (v : Numeric)
    (observed : List Slot) (ir : Result Machine) (nr : Result Numeric)
    (hi : Limit (fun n => producer.ideal n c m) ir)
    (hn : Limit (fun n => producer.numeric F n c v) nr)
    (hrel : ∀ n, Related F observed (producer.ideal n c m) (producer.numeric F n c v)) :
    ResultRelated F observed ir nr := by
  rcases hi with ⟨i, hi⟩ | ⟨rfl, hi⟩
  · rcases hn with ⟨j, hn⟩ | ⟨rfl, hn⟩
    · have hi' : producer.ideal (max i j) c m = .halted ir :=
        prefix_done_le _ _ (Nat.le_max_left i j) hi
      have hn' : producer.numeric F (max i j) c v = .halted nr :=
        prefix_done_le _ _ (Nat.le_max_right i j) hn
      have h := hrel (max i j)
      rw [hi', hn'] at h
      exact h
    · have h := hrel i
      change producer.ideal i c m = .halted ir at hi
      rw [hi] at h
      cases he : producer.numeric F i c v with
      | running code k fs s => simp only [he, Related] at h
      | halted r => exact False.elim (hn i r he)
  · rcases hn with ⟨j, hn⟩ | ⟨rfl, hn⟩
    · have h := hrel j
      change producer.numeric F j c v = .halted nr at hn
      rw [hn] at h
      cases he : producer.ideal j c m with
      | running code k fs s => simp only [he, Related] at h
      | halted r => exact False.elim (hi j r he)
    · trivial

/-- The compiler's limit clause follows once every actual prefix is related. -/
theorem numeric_limits (F : Roadmap.Fixed) (c : List Instr) (m : Machine) (v : Numeric)
    (observed : List Slot)
    (hrel : ∀ n, Related F observed (producer.ideal n c m) (producer.numeric F n c v)) :
    (∃ out, Limit (fun n => producer.numeric F n c v) out ∧
      ResultRelated F observed (idealResult (Evm.run c m)) out) ∧
    (∀ out, Limit (fun n => producer.numeric F n c v) out →
      ResultRelated F observed (idealResult (Evm.run c m)) out) := by
  have hi := (producer_idealAdequacy c m (idealResult (Evm.run c m))).mpr rfl
  have hall := fun out hn => limits_related F c m v observed _ out hi hn hrel
  obtain ⟨out, hn⟩ := prefix_limit_exists (numericAtom F) numericTest (.running c 0 [] v)
  exact ⟨⟨out, hn, hall out hn⟩, hall⟩

/-- A non-fault execution cannot reach an atom whose ideal step faults.
Compiler certificates, rather than a new caller premise, must supply this fact. -/
theorem reached_step_nonfault (c : List Instr) (m : Machine) (n : Nat)
    (i : Instr) (rest : List Instr) (fs : List Frame) (s : Machine)
    (hr : producer.ideal n c m = .running (i :: rest) 0 fs s)
    (hne : Evm.run c m ≠ .fault) : i.step s ≠ .fault := by
  intro hf
  have hd := denote_prefix n (.running c 0 [] m)
  change denoteCursor (producer.ideal n c m) = Evm.run c m at hd
  rw [hr] at hd
  simp only [denoteCursor, exec_cons_zero, hf, Evm.Out.bind, finishFrames_fault] at hd
  exact hne hd.symm

/-- Value-headed loop tests agree and preserve every represented field. -/
theorem test_step_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (w : Fin W) (tail : List Word) (shape : m.stack = .val w :: tail) :
    ∃ m' v', idealTest m = some (w.val != 0, m') ∧
      numericTest v = some (w.val != 0, v') ∧ Represents F slots m' v' := by
  refine ⟨{m with stack := tail}, {v with stack := tail.map (word F)}, ?_, ?_, ?_⟩
  · simp only [idealTest, shape]
  · simp only [numericTest, rep.1, shape, List.map_cons, word]
  · exact ⟨rfl, rep.2⟩

/-- PUSH translates the actual symbolic operand without a synthetic runtime hash. -/
theorem push_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v) (w : Word) :
    ResultRelated F slots (idealResult ((Instr.push w).step m)) (numericAtom F (.push w) v) := by
  simp only [Instr.step, Machine.next, idealResult, numericAtom, ResultRelated]
  exact ⟨True.intro, by simpa only [List.map_cons] using congrArg (List.cons (word F w)) rep.1,
    rep.2⟩

/-- POP preserves the representation even when the discarded word is a slot. -/
theorem pop_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (w : Word) (tail : List Word) (shape : m.stack = w :: tail) :
    ResultRelated F slots (idealResult (Instr.pop.step m)) (numericAtom F .pop v) := by
  obtain ⟨stack, mem, store, env⟩ := rep
  simp only [numericAtom, embed, stack, shape, List.map_cons, Instr.step, Machine.next,
    idealResult, resultMap, project, ResultRelated, Represents, List.map_map,
    Function.comp_def, word, true_and]
  exact ⟨rfl, mem, store, env⟩

/-- Ordinary binary arithmetic acts identically on represented value operands. -/
theorem binary_values_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (a b : Fin W) (tail : List Word) (shape : m.stack = .val a :: .val b :: tail)
    (i : Instr) (hi : i ∈ [.add, .sub, .mul, .div, .mod, .lt, .gt, .eq, .or, .and,
      .slt, .sgt, .sdiv, .smod, .xor, .shl, .shr, .exp, .sar]) :
    ResultRelated F slots (idealResult (i.step m)) (numericAtom F i v) := by
  obtain ⟨stack, mem, store, env⟩ := rep
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [numericAtom, embed, stack, shape, List.map_cons, word, Instr.step,
      Machine.next, idealResult, resultMap, project, ResultRelated, Represents,
      List.map_map, Function.comp_def, true_and] <;>
    exact ⟨rfl, mem, store, env⟩

theorem unary_values_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (a : Fin W) (tail : List Word) (shape : m.stack = .val a :: tail)
    (i : Instr) (hi : i = .iszero ∨ i = .not) :
    ResultRelated F slots (idealResult (i.step m)) (numericAtom F i v) := by
  obtain ⟨stack, mem, store, env⟩ := rep
  rcases hi with rfl | rfl <;>
    simp only [numericAtom, embed, stack, shape, List.map_cons, word, Instr.step,
      Machine.next, idealResult, resultMap, project, ResultRelated, Represents,
      List.map_map, Function.comp_def, true_and] <;>
    exact ⟨rfl, mem, store, env⟩

/-- Loading a symbolic memory word returns its represented numeric value. -/
theorem mload_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v) (x : Nat) :
    ResultRelated F slots (idealResult ((Instr.mload x).step m)) (numericAtom F (.mload x) v) := by
  obtain ⟨stack, mem, store, env⟩ := rep
  simp only [numericAtom, embed, stack, Instr.step, Machine.next, idealResult,
    resultMap, project, ResultRelated, Represents, List.map_cons, List.map_map,
    Function.comp_def, word, true_and]
  exact ⟨by rw [mem x]; rfl, mem, store, env⟩

/-- Memory stores commute on every cell, including symbolic pointer values. -/
theorem mstore_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (x : Nat) (w : Word) (tail : List Word) (shape : m.stack = w :: tail) :
    ResultRelated F slots (idealResult ((Instr.mstore x).step m))
      (numericAtom F (.mstore x) v) := by
  obtain ⟨stack, mem, store, env⟩ := rep
  simp only [numericAtom, embed, stack, shape, Instr.step, idealResult, resultMap,
    project, ResultRelated, Represents, List.map_cons, List.map_map,
    Function.comp_def, word, true_and]
  refine ⟨rfl, ?_, store, env⟩
  intro y
  by_cases h : y = x <;> simp [Evm.upd, h, word, mem]

theorem mloadAt_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (x : Fin W) (tail : List Word) (shape : m.stack = .val x :: tail) :
    ResultRelated F slots (idealResult (Instr.mloadAt.step m)) (numericAtom F .mloadAt v) := by
  obtain ⟨stack, mem, store, env⟩ := rep
  simp only [numericAtom, embed, stack, shape, Instr.step, Machine.next, idealResult,
    resultMap, project, ResultRelated, Represents, List.map_cons, List.map_map,
    Function.comp_def, word, true_and]
  exact ⟨by rw [mem x.val]; rfl, mem, store, env⟩

theorem mstoreAt_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (x : Fin W) (w : Word) (tail : List Word) (shape : m.stack = .val x :: w :: tail) :
    ResultRelated F slots (idealResult (Instr.mstoreAt.step m))
      (numericAtom F .mstoreAt v) := by
  obtain ⟨stack, mem, store, env⟩ := rep
  simp only [numericAtom, embed, stack, shape, Instr.step, idealResult, resultMap,
    project, ResultRelated, Represents, List.map_cons, List.map_map,
    Function.comp_def, word, true_and]
  refine ⟨rfl, ?_, store, env⟩
  intro y
  by_cases h : y = x.val <;> simp [Evm.upd, h, word, mem]

/-- Unconditional jumps preserve the exact pending skip count. -/
theorem jump_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v) (n : Nat) :
    ResultRelated F slots (idealResult ((Instr.jump n).step m)) (numericAtom F (.jump n) v) := by
  obtain ⟨stack, mem, store, env⟩ := rep
  simp only [numericAtom, embed, stack, Instr.step, idealResult, resultMap, project,
    ResultRelated, Represents, List.map_map, Function.comp_def, word, true_and]
  exact ⟨rfl, mem, store, env⟩

theorem jumpi_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (n : Nat) (x : Fin W) (tail : List Word) (shape : m.stack = .val x :: tail) :
    ResultRelated F slots (idealResult ((Instr.jumpi n).step m))
      (numericAtom F (.jumpi n) v) := by
  obtain ⟨stack, mem, store, env⟩ := rep
  simp only [numericAtom, embed, stack, shape, Instr.step, idealResult, resultMap, project,
    ResultRelated, Represents, List.map_cons, List.map_map, Function.comp_def, word, true_and]
  exact ⟨rfl, mem, store, env⟩

/-- Environment reads retain the unchanged world components of Represents. -/
theorem environment_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (i : Instr) (hi : i ∈ [.caller, .callvalue, .timestamp, .selfbalance, .address]) :
    ResultRelated F slots (idealResult (i.step m)) (numericAtom F i v) := by
  obtain ⟨stack, mem, store, bal, bal₀, self, accepts, caller, value, time⟩ := rep
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    simp only [numericAtom, embed, stack, Instr.step, Machine.next, idealResult,
      resultMap, project, ResultRelated, Represents, List.map_cons, List.map_map,
      Function.comp_def, word, bal, bal₀, self, accepts, caller, value, time, true_and, and_true]
    <;> exact ⟨rfl, mem, store⟩

/-- CALL uses the same balance and payment oracle, including refusal and self-call. -/
theorem call_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (amount dest : Fin W) (tail : List Word)
    (shape : m.stack = .val amount :: .val dest :: tail) :
    ResultRelated F slots (idealResult (Instr.call.step m)) (numericAtom F .call v) := by
  obtain ⟨stack, mem, store, bal, bal₀, self, accepts, caller, value, time⟩ := rep
  by_cases refused : m.bal m.self < amount.val ∨ m.accepts dest amount = false
  · simp only [numericAtom, embed, stack, shape, Instr.step, Machine.next, idealResult,
      resultMap, project, ResultRelated, Represents, List.map_cons, List.map_map,
      Function.comp_def, word, bal, bal₀, self, accepts, caller, value, time,
      refused, if_true, true_and, and_true]
    exact ⟨rfl, mem, store⟩
  · by_cases same : dest = m.self <;>
      simp_all only [numericAtom, embed, Instr.step, Machine.next, idealResult,
        resultMap, project, ResultRelated, Represents, List.map_cons, List.map_map,
        Function.comp_def, word, if_true, if_false, true_and, and_true] <;>
      exact ⟨rfl, fun _ => True.intro, fun _ _ => True.intro⟩

/-- DUP copies the represented word at the exact checked stack position. -/
theorem dup_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (n : Nat) (w : Word) (found : m.stack[n]? = some w) :
    ResultRelated F slots (idealResult ((Instr.dup (n + 1)).step m))
      (numericAtom F (.dup (n + 1)) v) := by
  obtain ⟨stack, mem, store, env⟩ := rep
  simp only [numericAtom, embed, stack, Instr.step, Nat.add_sub_cancel,
    List.getElem?_map, found, Option.map_some, Machine.next, idealResult,
    resultMap, project, ResultRelated, Represents, List.map_cons, List.map_map,
    Function.comp_def, word, true_and]
  exact ⟨rfl, mem, store, env⟩

/-- SWAP preserves symbolic words at both positions and throughout the tail. -/
theorem swap_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (n : Nat) (a b : Word) (tail : List Word)
    (shape : m.stack = a :: tail) (found : tail[n]? = some b) :
    ResultRelated F slots (idealResult ((Instr.swap (n + 1)).step m))
      (numericAtom F (.swap (n + 1)) v) := by
  obtain ⟨stack, mem, store, env⟩ := rep
  simp only [numericAtom, embed, stack, shape, Instr.step, List.map_cons,
    List.getElem?_map, found, Option.map_some, Machine.next, idealResult,
    resultMap, project, ResultRelated, Represents, List.map_set, List.map_map,
    Function.comp_def, word, true_and]
  exact ⟨rfl, mem, store, env⟩

theorem revert_related (F : Roadmap.Fixed) (slots : List Slot) (m : Machine) (v : Numeric) :
    ResultRelated F slots (idealResult (Instr.revert.step m)) (numericAtom F .revert v) := by
  trivial

/-- Invert an actual non-fault unary value operation. -/
theorem nonfault_one_value {st : List Word} {f : Fin W → List Word → Evm.Out}
    (h : (match st with | .val a :: tail => f a tail | _ => .fault) ≠ .fault) :
    ∃ a tail, st = .val a :: tail := by
  cases st with
  | nil => exact False.elim (h rfl)
  | cons w tail =>
    cases w with
    | slot s => exact False.elim (h rfl)
    | val a => exact ⟨a, tail, rfl⟩

/-- Invert an actual non-fault binary value operation. -/
theorem nonfault_two_values {st : List Word}
    {f : Fin W → Fin W → List Word → Evm.Out}
    (h : (match st with | .val a :: .val b :: tail => f a b tail | _ => .fault) ≠ .fault) :
    ∃ a b tail, st = .val a :: .val b :: tail := by
  cases st with
  | nil => exact False.elim (h rfl)
  | cons w tail =>
    cases w with
    | slot s => exact False.elim (h rfl)
    | val a =>
      cases tail with
      | nil => exact False.elim (h rfl)
      | cons w tail =>
        cases w with
        | slot s => exact False.elim (h rfl)
        | val b => exact ⟨a, b, tail, rfl⟩

/-- Value-only binary opcodes cannot silently accept symbolic slot operands. -/
theorem binary_nonfault_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (i : Instr) (hi : i ∈ [.sub, .mul, .div, .mod, .lt, .gt, .eq, .or, .and,
      .slt, .sgt, .sdiv, .smod, .xor, .shl, .shr, .exp, .sar])
    (safe : i.step m ≠ .fault) :
    ResultRelated F slots (idealResult (i.step m)) (numericAtom F i v) := by
  have shape : ∃ a b tail, m.stack = .val a :: .val b :: tail := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact nonfault_two_values safe
  obtain ⟨a, b, tail, shape⟩ := shape
  exact binary_values_related F slots m v rep a b tail shape i (List.mem_cons_of_mem _ hi)

theorem nonfault_one_slot {st : List Word} {f : Slot → List Word → Evm.Out}
    (h : (match st with | .slot s :: tail => f s tail | _ => .fault) ≠ .fault) :
    ∃ s tail, st = .slot s :: tail := by
  cases st with
  | nil => exact False.elim (h rfl)
  | cons w tail =>
    cases w with
    | val a => exact False.elim (h rfl)
    | slot s => exact ⟨s, tail, rfl⟩

theorem nonfault_value_slot {st : List Word}
    {f : Fin W → Slot → List Word → Evm.Out}
    (h : (match st with | .val a :: .slot s :: tail => f a s tail | _ => .fault) ≠ .fault) :
    ∃ a s tail, st = .val a :: .slot s :: tail := by
  cases st with
  | nil => exact False.elim (h rfl)
  | cons w tail =>
    cases w with
    | slot s => exact False.elim (h rfl)
    | val a =>
      cases tail with
      | nil => exact False.elim (h rfl)
      | cons w tail =>
        cases w with
        | val b => exact False.elim (h rfl)
        | slot s => exact ⟨a, s, tail, rfl⟩

theorem nonfault_slot_value {st : List Word}
    {f : Slot → Fin W → List Word → Evm.Out}
    (h : (match st with | .slot s :: .val a :: tail => f s a tail | _ => .fault) ≠ .fault) :
    ∃ s a tail, st = .slot s :: .val a :: tail := by
  cases st with
  | nil => exact False.elim (h rfl)
  | cons w tail =>
    cases w with
    | val a => exact False.elim (h rfl)
    | slot s =>
      cases tail with
      | nil => exact False.elim (h rfl)
      | cons w tail =>
        cases w with
        | slot t => exact False.elim (h rfl)
        | val a => exact ⟨s, a, tail, rfl⟩


/-- ADD's non-fault shapes include both symbolic offset orders. -/
theorem add_nonfault_related (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (safe : Instr.add.step m ≠ .fault) :
    ResultRelated F slots (idealResult (Instr.add.step m)) (numericAtom F .add v) := by
  cases shape : m.stack with
  | nil => exact False.elim (safe (by simp [Instr.step, shape]))
  | cons a tail =>
    cases tail with
    | nil => cases a <;> exact False.elim (safe (by simp [Instr.step, shape]))
    | cons b tail =>
      cases a with
      | val a =>
        cases b with
        | val b => exact binary_values_related F slots m v rep a b tail shape .add (by simp)
        | slot b => exact add_slot_related F slots m v rep b a tail (Or.inl shape)
      | slot a =>
        cases b with
        | val b => exact add_slot_related F slots m v rep a b tail (Or.inr shape)
        | slot b => exact False.elim (safe (by simp [Instr.step, shape]))

/-- Every non-fault atomic step preserves the concrete representation. Storage
writes use the explicit bounded regions; no storage simulation is a premise. -/
theorem nonfault_atom_related (F : Roadmap.Fixed) (slots : List Slot)
    (hL : F.regionLen ≤ W) (hR : F.rootSlots ≤ W)
    (hb : ∀ s ∈ slots, (Storage.ofSlot s).Bounded F.regionLen F.rootSlots)
    (hr : RegionsDisjoint W F.regionLen (fun b => (F.hash b).val)
      (List.range F.rootSlots) (preimages F slots))
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (i : Instr) (nonloop : ∀ c b, i ≠ .loop c b)
    (safe : i.step m ≠ .fault)
    (covered : ∀ s ∈ stackSlots m, s ∈ slots) :
    ResultRelated F slots (idealResult (i.step m)) (numericAtom F i v) := by
  cases i
  case sub | mul | div | mod | lt | gt | eq | or | and | slt | sgt | sdiv |
      smod | xor | shl | shr | exp | sar =>
    exact binary_nonfault_related F slots m v rep _ (by simp) safe
  case caller | callvalue | timestamp | selfbalance | address =>
    exact environment_related F slots m v rep _ (by simp)
  case push w => exact push_related F slots m v rep w
  case pop =>
    cases shape : m.stack with
    | nil => exact False.elim (safe (by simp [Instr.step, shape]))
    | cons w tail => exact pop_related F slots m v rep w tail shape
  case dup n =>
    cases n with
    | zero => exact False.elim (safe (by simp [Instr.step]))
    | succ n =>
      cases found : m.stack[n]? with
      | none => exact False.elim (safe (by simp [Instr.step, found]))
      | some w => exact dup_related F slots m v rep n w found
  case swap n =>
    cases n with
    | zero => exact False.elim (safe (by simp [Instr.step]))
    | succ n =>
      cases shape : m.stack with
      | nil => exact False.elim (safe (by simp [Instr.step, shape]))
      | cons a tail =>
        cases found : tail[n]? with
        | none => exact False.elim (safe (by simp [Instr.step, shape, found]))
        | some b => exact swap_related F slots m v rep n a b tail shape found
  case add => exact add_nonfault_related F slots m v rep safe
  case iszero =>
    obtain ⟨a, tail, shape⟩ := nonfault_one_value safe
    exact unary_values_related F slots m v rep a tail shape _ (Or.inl rfl)
  case not =>
    obtain ⟨a, tail, shape⟩ := nonfault_one_value safe
    exact unary_values_related F slots m v rep a tail shape _ (Or.inr rfl)
  case keccakMap =>
    obtain ⟨a, s, tail, shape⟩ := nonfault_value_slot safe
    exact keccakMap_related F slots m v rep a s tail shape
  case keccakArr =>
    obtain ⟨s, tail, shape⟩ := nonfault_one_slot safe
    exact keccakArr_related F slots m v rep s tail shape
  case sload =>
    obtain ⟨s, tail, shape⟩ := nonfault_one_slot safe
    exact sload_related F slots m v rep s tail shape (covered s (by simp [stackSlots, shape]))
  case sstore =>
    obtain ⟨s, a, tail, shape⟩ := nonfault_slot_value safe
    exact sstore_related F slots hL hR hb hr m v rep s a tail shape
      (covered s (by simp [stackSlots, shape]))
  case mload x => exact mload_related F slots m v rep x
  case mstore x =>
    cases shape : m.stack with
    | nil => exact False.elim (safe (by simp [Instr.step, shape]))
    | cons w tail => exact mstore_related F slots m v rep x w tail shape
  case mloadAt =>
    obtain ⟨x, tail, shape⟩ := nonfault_one_value safe
    exact mloadAt_related F slots m v rep x tail shape
  case mstoreAt =>
    cases shape : m.stack with
    | nil => exact False.elim (safe (by simp [Instr.step, shape]))
    | cons w tail =>
      cases w with
      | slot s => exact False.elim (safe (by simp [Instr.step, shape]))
      | val x =>
        cases tail with
        | nil => exact False.elim (safe (by simp [Instr.step, shape]))
        | cons w tail => exact mstoreAt_related F slots m v rep x w tail shape
  case jump n => exact jump_related F slots m v rep n
  case jumpi n =>
    obtain ⟨x, tail, shape⟩ := nonfault_one_value safe
    exact jumpi_related F slots m v rep n x tail shape
  case call =>
    obtain ⟨a, b, tail, shape⟩ := nonfault_two_values safe
    exact call_related F slots m v rep a b tail shape
  case revert => exact revert_related F slots m v
  case loop c b => exact False.elim (nonloop c b rfl)


/-- Access correspondence keeps each actual storage read and write, including
steps before reversion; it does not substitute representation coverage for events. -/
theorem nonfault_access_agrees (F : Roadmap.Fixed) (slots : List Slot)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (i : Instr) (safe : i.step m ≠ .fault)
    (rest : List Instr) (fs : List Frame) :
    (idealAccessAt (.running (i :: rest) 0 fs m)).map (mapAccess (address F)) =
      numericAccessAt (.running (i :: rest) 0 fs v) := by
  cases i <;> try rfl
  case sload =>
    obtain ⟨s, tail, shape⟩ := nonfault_one_slot safe
    exact sload_access_agrees F slots m v rep s tail shape rest fs
  case sstore =>
    obtain ⟨s, a, tail, shape⟩ := nonfault_slot_value safe
    exact sstore_access_agrees F slots m v rep s a tail shape rest fs


theorem tick_atom_eq (atom : Instr → S → Result S) (test : S → Option (Bool × S))
    (i : Instr) (rest : List Instr) (fs : List Frame) (m : S)
    (nonloop : ∀ a b, i ≠ .loop a b) :
    tick atom test (.running (i :: rest) 0 fs m) =
      match atom i m with
      | .ok s k => .running rest k fs s
      | .revert => .halted .revert
      | .fault => .halted .fault := by
  cases i <;> try rfl
  case loop a b => exact False.elim (nonloop a b rfl)

/-- The exact protocol preserves representation once the reached atom and
condition obligations have been established; loop entry never executes an atom. -/
theorem running_tick_related (F : Roadmap.Fixed) (slots : List Slot)
    (c : List Instr) (k : Nat) (fs : List Frame)
    (m : Machine) (v : Numeric) (rep : Represents F slots m v)
    (atom : ∀ i rest, c = i :: rest → k = 0 → (∀ a b, i ≠ .loop a b) →
      ResultRelated F slots (idealResult (i.step m)) (numericAtom F i v))
    (test : ∀ a b rest gs, c = [] → k = 0 → fs = .test a b rest :: gs →
      ∃ w tail, m.stack = .val w :: tail) :
    Related F slots
      (tick (fun i s => idealResult (i.step s)) idealTest (.running c k fs m))
      (tick (numericAtom F) numericTest (.running c k fs v)) := by
  cases c with
  | nil =>
    cases fs with
    | nil =>
      simp only [tick, Related, ResultRelated, true_and]
      exact rep
    | cons f fs =>
      cases k with
      | succ k => trivial
      | zero =>
        cases f with
        | body a b rest => exact ⟨rfl, rfl, rfl, rep⟩
        | test a b rest =>
          obtain ⟨w, tail, shape⟩ := test a b rest fs rfl rfl rfl
          obtain ⟨m', v', hm, hv, hrep⟩ := test_step_related F slots m v rep w tail shape
          simp only [tick, hm, hv]
          cases h : (w.val != 0) <;> exact ⟨rfl, rfl, rfl, hrep⟩
  | cons i rest =>
    cases k with
    | succ k =>
      simp only [tick, Related, true_and]
      exact rep
    | zero =>
      by_cases loop : ∃ a b, i = .loop a b
      · obtain ⟨a, b, rfl⟩ := loop
        exact ⟨rfl, rfl, rfl, rep⟩
      · have nonloop : ∀ a b, i ≠ .loop a b := by
          intro a b h
          exact loop ⟨a, b, h⟩
        rw [tick_atom_eq _ _ _ _ _ _ nonloop, tick_atom_eq _ _ _ _ _ _ nonloop]
        have h := atom i rest rfl rfl nonloop
        cases ha : idealResult (i.step m) <;> cases hv : numericAtom F i v <;>
          simp only [ha, hv, ResultRelated, Related, true_and] at h ⊢ <;> exact h

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

/-- info: 'Solidity.Hash.CompilerCorrect.ideal_finite_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.ideal_finite_sound

/-- info: 'Solidity.Hash.CompilerCorrect.producer_idealAdequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.producer_idealAdequacy

/-- info: 'Solidity.Hash.CompilerCorrect.adaptive_of_compilerBridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.adaptive_of_compilerBridge

/-- info: 'Solidity.Hash.CompilerCorrect.numeric_limits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.numeric_limits

/-- info: 'Solidity.Hash.CompilerCorrect.nonfault_atom_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.nonfault_atom_related
/-- info: 'Solidity.Hash.CompilerCorrect.nonfault_access_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.nonfault_access_agrees

/-- info: 'Solidity.Hash.CompilerCorrect.running_tick_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.running_tick_related
