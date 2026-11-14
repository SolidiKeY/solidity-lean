import Solidity.Hash.CompilerCorrect

/-! Finite-prefix transport and divergence-safe composition for the frozen E4A contract. -/
namespace Solidity.Hash.CompilerCorrect

open Solidity.Evm Solidity.Goals.HashContract

/-- Local safety obligations at an actual instruction or loop-test boundary. -/
def CursorSafe : Cursor Machine → Prop
  | .running (i :: _) 0 _ m => (∀ c b, i ≠ .loop c b) → i.step m ≠ .fault
  | .running [] 0 (.test _ _ _ :: _) m => ∃ w tail, m.stack = .val w :: tail
  | _ => True

/-- An internal compiler proof obligation, never a public caller premise. -/
def CodeSafe (c : List Instr) (m : Machine) : Prop :=
  ∀ n, CursorSafe (producer.ideal n c m)

theorem represents_subset (F : Roadmap.Fixed) (xs ys : List Slot)
    (sub : ∀ s ∈ ys, s ∈ xs) (m : Machine) (v : Numeric)
    (h : Represents F xs m v) : Represents F ys m v :=
  ⟨h.1, h.2.1, fun s hs => h.2.2.1 s (sub s hs), h.2.2.2⟩

theorem related_subset (F : Roadmap.Fixed) (xs ys : List Slot)
    (sub : ∀ s ∈ ys, s ∈ xs) (a : Cursor Machine) (b : Cursor Numeric)
    (h : Related F xs a b) : Related F ys a b := by
  cases a with
  | running c k fs m =>
    cases b with
    | halted r => exact False.elim h
    | running d j gs v =>
      exact ⟨h.1, h.2.1, h.2.2.1, represents_subset F xs ys sub m v h.2.2.2⟩
  | halted r =>
    cases b with
    | running d j gs v => exact False.elim h
    | halted s =>
      cases r <;> cases s <;> try exact h
      exact ⟨h.1, represents_subset F xs ys sub _ _ h.2⟩

theorem locations_stack (n k : Nat) (c : List Instr) (m : Machine)
    (observed : List Slot) (hk : k ≤ n) (rest : List Instr) (skip : Nat)
    (fs : List Frame) (s : Machine)
    (hrch : producer.ideal k c m = .running rest skip fs s) :
    ∀ x ∈ stackSlots s, x ∈ locations producer n c m observed := by
  intro x hx
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨k, List.mem_range.mpr (by omega), by simpa only [hrch, slotsAt] using hx⟩

/-- A non-fault complete execution also has valid reached loop-test operands. -/
theorem reached_test_value (c : List Instr) (m : Machine) (n : Nat)
    (a b rest : List Instr) (fs : List Frame) (s : Machine)
    (hrch : producer.ideal n c m = .running [] 0 (.test a b rest :: fs) s)
    (safe : Evm.run c m ≠ .fault) : ∃ w tail, s.stack = .val w :: tail := by
  have hd := denote_prefix n (.running c 0 [] m)
  change denoteCursor (producer.ideal n c m) = Evm.run c m at hd
  rw [hrch] at hd
  cases shape : s.stack with
  | nil =>
    exact False.elim (safe (by
      simpa only [denoteCursor, Evm.exec, finishFrames, frameResult,
        testResult, shape, finishFrames_fault] using hd.symm))
  | cons w tail =>
    cases w with
    | slot x =>
      exact False.elim (safe (by
        simpa only [denoteCursor, Evm.exec, finishFrames, frameResult,
          testResult, shape, finishFrames_fault] using hd.symm))
    | val w => exact ⟨w, tail, rfl⟩

theorem codeSafe_of_nonfault (c : List Instr) (m : Machine)
    (safe : Evm.run c m ≠ .fault) : CodeSafe c m := by
  intro n
  cases hrch : producer.ideal n c m with
  | halted r => trivial
  | running rest k fs s =>
    cases rest with
    | cons i rest =>
      cases k with
      | succ k => trivial
      | zero => exact fun _ => reached_step_nonfault c m n i rest fs s hrch safe
    | nil =>
      cases k with
      | succ k => trivial
      | zero =>
        cases fs with
        | nil => trivial
        | cons f fs =>
          cases f with
          | body a b rest => trivial
          | test a b rest => exact reached_test_value c m n a b rest fs s hrch safe


/-- One tick on a safe actual cursor retains the complete finite footprint. -/
theorem safe_tick_related (F : Roadmap.Fixed) (slots : List Slot)
    (hL : F.regionLen ≤ W) (hR : F.rootSlots ≤ W)
    (hb : ∀ s ∈ slots, (Storage.ofSlot s).Bounded F.regionLen F.rootSlots)
    (hr : RegionsDisjoint W F.regionLen (fun b => (F.hash b).val)
      (List.range F.rootSlots) (preimages F slots))
    (a : Cursor Machine) (b : Cursor Numeric)
    (rel : Related F slots a b) (safe : CursorSafe a)
    (covered : ∀ code skip fs s, a = .running code skip fs s →
      ∀ x ∈ stackSlots s, x ∈ slots) :
    Related F slots
      (tick (fun i s => idealResult (i.step s)) idealTest a)
      (tick (numericAtom F) numericTest b) := by
  cases a with
  | halted r =>
    cases b with
    | running code skip fs s => exact False.elim rel
    | halted t => exact rel
  | running code skip fs m =>
    cases b with
    | halted t => exact False.elim rel
    | running other j gs v =>
      obtain ⟨rfl, rfl, rfl, rep⟩ := rel
      apply running_tick_related F slots code skip fs m v rep
      · intro i rest hc hk nonloop
        subst code
        subst skip
        exact nonfault_atom_related F slots hL hR hb hr m v rep i nonloop
          (safe nonloop) (covered _ _ _ _ rfl)
      · intro c body rest frames hc hk hf
        subst code
        subst skip
        subst fs
        exact safe

/-- Prefix induction uses the full reached footprint, then permits observation
restriction separately. Safety will be discharged by the checked compiler. -/
theorem finite_related_of_safe (F : Roadmap.Fixed) (n : Nat)
    (c : List Instr) (m : Machine) (v : Numeric) (observed : List Slot)
    (safe : CodeSafe c m)
    (ready : Ready producer F n c m v observed)
    (premise : Solidity.Goals.HashContract.Premise producer F n c m v observed) :
    ∀ k, k ≤ n → Related F (locations producer n c m observed)
      (producer.ideal k c m) (producer.numeric F k c v) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨rfl, rfl, rfl, ready.2.2.2⟩
  | succ k ih =>
    intro hk
    rw [producer_produces.ideal_succ, producer_produces.numeric_succ]
    apply safe_tick_related F _ ready.1 ready.2.1 ready.2.2.1 premise.2
      _ _ (ih (by omega)) (safe k)
    intro code skip fs s hrch
    exact locations_stack n k c m observed (by omega) code skip fs s hrch


theorem safe_access_related (F : Roadmap.Fixed) (slots : List Slot)
    (a : Cursor Machine) (b : Cursor Numeric)
    (rel : Related F slots a b) (safe : CursorSafe a) :
    (idealAccessAt a).map (mapAccess (address F)) = numericAccessAt b := by
  cases a with
  | halted r =>
    cases b with
    | running code skip fs s => exact False.elim rel
    | halted t => rfl
  | running code skip fs m =>
    cases b with
    | halted t => exact False.elim rel
    | running other j gs v =>
      obtain ⟨rfl, rfl, rfl, rep⟩ := rel
      cases code with
      | nil => rfl
      | cons i rest =>
        cases skip with
        | succ j => simp only [idealAccessAt, numericAccessAt, List.map_nil]
        | zero =>
          by_cases loop : ∃ c b, i = .loop c b
          · obtain ⟨c, b, rfl⟩ := loop
            rfl
          · have nonloop : ∀ c b, i ≠ .loop c b := by
              intro c b h
              exact loop ⟨c, b, h⟩
            exact nonfault_access_agrees F slots m v rep i (safe nonloop) rest fs

/-- Full finite-prefix observations and exact access events, conditional only
on the internal safety obligation that the compiler proof must discharge. -/
theorem prefix_related_of_safe (F : Roadmap.Fixed) (n : Nat)
    (c : List Instr) (m : Machine) (v : Numeric) (observed : List Slot)
    (safe : CodeSafe c m)
    (ready : Ready producer F n c m v observed)
    (premise : Solidity.Goals.HashContract.Premise producer F n c m v observed) :
    PrefixRelated producer F n c m v observed := by
  have full := finite_related_of_safe F n c m v observed safe ready premise
  refine ⟨?_, ?_⟩
  · intro k hk
    exact related_subset F _ observed
      (fun s hs => List.mem_append_left _ hs) _ _ (full k hk)
  · unfold AccessesAgree
    rw [List.map_flatMap, List.flatMap_def, List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro k hk
    exact safe_access_related F _ _ _ (full k (by
      have := List.mem_range.mp hk
      omega)) (safe k)


/-- Extend only the enclosing continuation, never a loop condition or body. -/
def appendFrameSuffix (suffix : List Instr) : Frame → Frame
  | .test c b rest => .test c b (rest ++ suffix)
  | .body c b rest => .body c b (rest ++ suffix)

def attachFrames (suffix : List Instr) (outer : List Frame) : List Frame → List Frame
  | [] => outer
  | [f] => appendFrameSuffix suffix f :: outer
  | f :: g :: fs => f :: attachFrames suffix outer (g :: fs)

/-- Embed a segment's exact cursor in its code and frame continuation. -/
def attachCursor (suffix : List Instr) (outer : List Frame) : Cursor S → Cursor S
  | .running c k [] m => .running (c ++ suffix) k outer m
  | .running c k (f :: fs) m => .running c k (attachFrames suffix outer (f :: fs)) m
  | .halted r => .halted r

/-- The segment boundary precedes its standalone terminal tick. -/
def AtBoundary : Cursor S → Prop
  | .running [] _ [] _ => True
  | _ => False

theorem attach_tick (atom : Instr → S → Result S) (test : S → Option (Bool × S))
    (suffix : List Instr) (outer : List Frame) (cur : Cursor S)
    (inside : ¬ AtBoundary cur) :
    attachCursor suffix outer (tick atom test cur) =
      tick atom test (attachCursor suffix outer cur) := by
  cases cur with
  | halted r => rfl
  | running code k fs m =>
    cases code with
    | nil =>
      cases fs with
      | nil => exact False.elim (inside True.intro)
      | cons f fs =>
        cases k with
        | succ k => cases f <;> cases fs <;> rfl
        | zero =>
          cases f with
          | body c b rest => cases fs <;> rfl
          | test c b rest =>
            cases ht : test m with
            | none => cases fs <;>
                simp only [tick, ht, attachCursor, attachFrames, appendFrameSuffix]
            | some pair =>
              obtain ⟨flag, m'⟩ := pair
              cases flag <;> cases fs <;>
                simp only [tick, ht, attachCursor, attachFrames, appendFrameSuffix]
    | cons i rest =>
      cases k with
      | succ k => cases fs <;> simp only [tick, attachCursor, List.cons_append]
      | zero =>
        by_cases loop : ∃ c b, i = .loop c b
        · obtain ⟨c, b, rfl⟩ := loop
          cases fs <;> rfl
        · have nonloop : ∀ c b, i ≠ .loop c b := by
            intro c b h
            exact loop ⟨c, b, h⟩
          cases fs <;>
            simp only [attachCursor, List.cons_append, tick_atom_eq atom test i _ _ _ nonloop]
          all_goals
            cases atom i m <;> rfl


/-- Safety from a concrete cursor, including an exact pending skip count. -/
def SafeFrom (cur : Cursor Machine) : Prop :=
  ∀ n, CursorSafe (iteratePrefix (fun i s => idealResult (i.step s)) idealTest n cur)

theorem boundary_result (c : List Instr) (m : Machine) (n k : Nat) (s : Machine)
    (hrch : producer.ideal n c m = .running [] k [] s) :
    Evm.run c m = .ok s k := by
  have hd := denote_prefix n (.running c 0 [] m)
  change denoteCursor (producer.ideal n c m) = Evm.run c m at hd
  rw [hrch] at hd
  exact hd.symm

/-- Away from completion, attaching a continuation changes no executed operand
or loop-test value obligation. -/
theorem attach_safe (suffix : List Instr) (outer : List Frame) (cur : Cursor Machine)
    (inside : ¬ AtBoundary cur) (safe : CursorSafe cur) :
    CursorSafe (attachCursor suffix outer cur) := by
  cases cur with
  | halted r => trivial
  | running code k fs m =>
    cases code with
    | nil =>
      cases fs with
      | nil => exact False.elim (inside True.intro)
      | cons f fs =>
        cases k with
        | succ k => cases fs <;> trivial
        | zero =>
          cases f <;> cases fs <;> exact safe
    | cons i rest => cases k <;> cases fs <;> exact safe


theorem boundary_shape (cur : Cursor S) (h : AtBoundary cur) :
    ∃ k m, cur = .running [] k [] m := by
  cases cur with
  | halted r => exact False.elim h
  | running code k fs m =>
    cases code with
    | cons i rest => exact False.elim h
    | nil =>
      cases fs with
      | cons f fs => exact False.elim h
      | nil => exact ⟨k, m, rfl⟩

/-- Every appended-code prefix is either still inside the first segment or is
an actual suffix prefix after a concrete successful segment boundary. -/
theorem append_prefix_phase (a b : List Instr) (m : Machine) (n : Nat) :
    (¬ AtBoundary (producer.ideal n a m) ∧
      producer.ideal n (a ++ b) m = attachCursor b [] (producer.ideal n a m)) ∨
    (∃ s k j, Evm.run a m = .ok s k ∧
      producer.ideal n (a ++ b) m =
        iteratePrefix (fun i s => idealResult (i.step s)) idealTest j (.running b k [] s)) := by
  induction n with
  | zero =>
    cases a with
    | nil => exact Or.inr ⟨m, 0, 0, rfl, rfl⟩
    | cons i rest => exact Or.inl ⟨by intro h; exact h, rfl⟩
  | succ n ih =>
    rcases ih with ⟨inside, heq⟩ | ⟨s, k, j, hr, heq⟩
    · have next :
          producer.ideal (n + 1) (a ++ b) m =
            attachCursor b [] (producer.ideal (n + 1) a m) := by
        rw [producer_produces.ideal_succ, heq, ← attach_tick _ _ b [] _ inside,
          ← producer_produces.ideal_succ]
      by_cases boundary : AtBoundary (producer.ideal (n + 1) a m)
      · obtain ⟨k, s, hs⟩ := boundary_shape _ boundary
        refine Or.inr ⟨s, k, 0, boundary_result a m (n + 1) k s hs, ?_⟩
        rw [next, hs]
        rfl
      · exact Or.inl ⟨boundary, next⟩
    · refine Or.inr ⟨s, k, j + 1, hr, ?_⟩
      rw [producer_produces.ideal_succ, heq]
      rfl

/-- Append composition retains the exact pending jump returned by the segment.
Compiler certificates, not a new public premise, supply the continuation proof. -/
theorem safe_append (a b : List Instr) (m : Machine) (ha : CodeSafe a m)
    (hb : ∀ s k, Evm.run a m = .ok s k → SafeFrom (.running b k [] s)) :
    CodeSafe (a ++ b) m := by
  intro n
  rcases append_prefix_phase a b m n with ⟨inside, heq⟩ | ⟨s, k, j, hr, heq⟩
  · rw [heq]
    exact attach_safe b [] _ inside (ha n)
  · rw [heq]
    exact hb s k hr j


/-- Proof phases of the existing loop producer, not an alternative execution. -/
inductive LoopPhase (I J : Machine → Prop) (c b : List Instr) : Cursor Machine → Prop
  | entry {s} : I s → LoopPhase I J c b (.running [.loop c b] 0 [] s)
  | condition {s n} : I s →
      LoopPhase I J c b (attachCursor [] [.test c b []] (producer.ideal n c s))
  | body {s n} : J s →
      LoopPhase I J c b (attachCursor [] [.body c b []] (producer.ideal n b s))
  | done {s} : LoopPhase I J c b (.running [] 0 [] s)
  | halted {r} : LoopPhase I J c b (.halted r)

theorem loopPhase_safe (I J : Machine → Prop) (c b : List Instr)
    (hc : ∀ s, I s → CodeSafe c s)
    (hcDone : ∀ s t k, I s → Evm.run c s = .ok t k →
      k = 0 ∧ ∃ w tail, t.stack = .val w :: tail ∧
        (w.val ≠ 0 → J {t with stack := tail}))
    (hb : ∀ s, J s → CodeSafe b s)
    {cur : Cursor Machine} (phase : LoopPhase I J c b cur) : CursorSafe cur := by
  cases phase with
  | entry hi => exact fun nonloop => False.elim (nonloop c b rfl)
  | @condition s n hi =>
    by_cases boundary : AtBoundary (producer.ideal n c s)
    · obtain ⟨k, t, hx⟩ := boundary_shape _ boundary
      obtain ⟨rfl, w, tail, hst, _⟩ := hcDone s t k hi (boundary_result c s n k t hx)
      rw [hx]
      exact ⟨w, tail, hst⟩
    · exact attach_safe [] [.test c b []] _ boundary (hc s hi n)
  | @body s n hj =>
    by_cases boundary : AtBoundary (producer.ideal n b s)
    · obtain ⟨k, t, hx⟩ := boundary_shape _ boundary
      rw [hx]
      cases k <;> trivial
    · exact attach_safe [] [.body c b []] _ boundary (hb s hj n)
  | done => trivial
  | halted => trivial

theorem loopPhase_tick (I J : Machine → Prop) (c b : List Instr)
    (hcDone : ∀ s t k, I s → Evm.run c s = .ok t k →
      k = 0 ∧ ∃ w tail, t.stack = .val w :: tail ∧
        (w.val ≠ 0 → J {t with stack := tail}))
    (hbDone : ∀ s t k, J s → Evm.run b s = .ok t k → k = 0 ∧ I t)
    {cur : Cursor Machine} (phase : LoopPhase I J c b cur) :
    LoopPhase I J c b (tick (fun i s => idealResult (i.step s)) idealTest cur) := by
  cases phase with
  | entry hi =>
    simpa only [producer, iteratePrefix, attachCursor, List.append_nil, tick] using
      (LoopPhase.condition (I := I) (J := J) (c := c) (b := b) (n := 0) hi)
  | @condition s n hi =>
    by_cases boundary : AtBoundary (producer.ideal n c s)
    · obtain ⟨k, t, hx⟩ := boundary_shape _ boundary
      obtain ⟨rfl, w, tail, hst, hj⟩ := hcDone s t k hi (boundary_result c s n k t hx)
      simp only [hx, attachCursor, List.nil_append, tick, idealTest, hst]
      by_cases hz : w.val = 0
      · have flag : (w.val != 0) = false := by simp [hz]
        rw [flag]
        exact .done
      · have flag : (w.val != 0) = true := by simp [hz]
        rw [flag]
        simpa only [producer, iteratePrefix, attachCursor, List.append_nil] using
          (LoopPhase.body (I := I) (J := J) (c := c) (b := b) (n := 0) (hj hz))
    · have next := LoopPhase.condition (I := I) (J := J) (c := c) (b := b) (n := n + 1) hi
      simpa only [producer_produces.ideal_succ, attach_tick _ _ [] [.test c b []] _ boundary] using next
  | @body s n hj =>
    by_cases boundary : AtBoundary (producer.ideal n b s)
    · obtain ⟨k, t, hx⟩ := boundary_shape _ boundary
      obtain ⟨rfl, hi⟩ := hbDone s t k hj (boundary_result b s n k t hx)
      simp only [hx, attachCursor, List.nil_append, tick]
      simpa only [producer, iteratePrefix, attachCursor, List.append_nil] using
        (LoopPhase.condition (I := I) (J := J) (c := c) (b := b) (n := 0) hi)
    · have next := LoopPhase.body (I := I) (J := J) (c := c) (b := b) (n := n + 1) hj
      simpa only [producer_produces.ideal_succ, attach_tick _ _ [] [.body c b []] _ boundary] using next
  | done => exact .halted
  | halted => exact .halted

/-- Loop safety follows from condition/body safety and actual successful-boundary
invariants, including when a condition or nested body never terminates. -/
theorem safe_loop (I J : Machine → Prop) (c b : List Instr) (m : Machine)
    (initial : I m)
    (hc : ∀ s, I s → CodeSafe c s)
    (hcDone : ∀ s t k, I s → Evm.run c s = .ok t k →
      k = 0 ∧ ∃ w tail, t.stack = .val w :: tail ∧
        (w.val ≠ 0 → J {t with stack := tail}))
    (hb : ∀ s, J s → CodeSafe b s)
    (hbDone : ∀ s t k, J s → Evm.run b s = .ok t k → k = 0 ∧ I t) :
    CodeSafe [.loop c b] m := by
  have phases : ∀ n, LoopPhase I J c b (producer.ideal n [.loop c b] m) := by
    intro n
    induction n with
    | zero => exact .entry initial
    | succ n ih =>
      rw [producer_produces.ideal_succ]
      exact loopPhase_tick I J c b hcDone hbDone ih
  intro n
  exact loopPhase_safe I J c b hc hcDone hb (phases n)


/-- info: 'Solidity.Hash.CompilerCorrect.codeSafe_of_nonfault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.codeSafe_of_nonfault

/-- info: 'Solidity.Hash.CompilerCorrect.prefix_related_of_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.prefix_related_of_safe

/-- info: 'Solidity.Hash.CompilerCorrect.safe_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.safe_append

/-- info: 'Solidity.Hash.CompilerCorrect.safe_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.safe_loop
end Solidity.Hash.CompilerCorrect
