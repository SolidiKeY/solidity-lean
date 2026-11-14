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
/-- Internal finite-run helper; divergence must be handled separately by
compiler invariants, never excluded from the public theorem. -/
theorem compilation_safe_of_nondiv {C : Contract} {b L frame : Nat}
    {Γ Δ : Ctx} {frag : Frag Γ} {P : Prog C Γ Δ}
    (r : Evm.Compiler.Compilation b frag P) {base : Nat → Fin W}
    {σ : State C Γ} {m : Machine} (input : r.Input L frame base σ m)
    (finite : P.run σ ≠ .error .diverge) : CodeSafe r.code m := by
  apply codeSafe_of_nonfault
  rcases r.correct_exact input with ⟨o, s, ho, hc, rest⟩ | ⟨ho, hc⟩ | ⟨ho, hc⟩
  · rw [hc]
    intro impossible
    cases impossible
  · rw [hc]
    intro impossible
    cases impossible
  · exact False.elim (finite ho)

/-- Internal assembly only: the compiler proof must supply safety for every
successful branch without adding it to the frozen caller interface. -/
theorem compilerBridge_of_safe
    (safe : ∀ {C : Contract} {Γ Δ : Ctx} (b : Nat) (frag : Frag Γ)
      (P : Prog C Γ Δ) (r : Evm.Compiler.Compilation b frag P),
      Evm.Compiler.compile b frag P = some r →
      ∀ (L frame : Nat) (base : Nat → Fin W) (σ : State C Γ) (m : Machine),
      r.Input L frame base σ m → CodeSafe r.code m) : CompilerBridge producer := by
  intro C Γ Δ b frag P r accepted L frame base σ m input
  refine ⟨r.correct_exact input, ?_⟩
  intro F v observed
  have hsafe := safe b frag P r accepted L frame base σ m input
  refine ⟨fun n ready premise => prefix_related_of_safe F n r.code m v observed hsafe ready premise, ?_⟩
  intro all
  apply numeric_limits
  intro n
  exact (prefix_related_of_safe F n r.code m v observed hsafe (all n).1 (all n).2).1 n (Nat.le_refl n)

/-- Safety follows from this branch's actual finite-result certificate. -/
theorem memory_safe {C : Contract} {b L frame : Nat}
    {Γ Δ : Ctx} {frag : Frag Γ} {P : Prog C Γ Δ}
    (out : Memory.CompiledProg b frag P) {base : Nat → Fin W}
    {σ : State C Γ} {m : Machine}
    (input : (Evm.Compiler.Compilation.memory out).Input L frame base σ m) :
    CodeSafe out.code m := by
  apply codeSafe_of_nonfault
  rcases out.cert.correct input.1 input.2.1 input.2.2 with ⟨o, s, base2, ho, hc, rest⟩ | ⟨ho, hc⟩
  all_goals
    intro bad
    rw [hc] at bad
    cases bad

/-- Safety follows from this branch's actual finite-result certificate. -/
theorem referenceArrays_safe {C : Contract} {b L frame : Nat}
    {Γ Δ : Ctx} {frag : Frag Γ} {P : Prog C Γ Δ}
    (out : Memory.ReferenceArrays.CompiledProg b frag P) {base : Nat → Fin W}
    {σ : State C Γ} {m : Machine}
    (input : (Evm.Compiler.Compilation.referenceArrays out).Input L frame base σ m) :
    CodeSafe out.code m := by
  apply codeSafe_of_nonfault
  rcases out.cert.correct input with ⟨o, s, ho, hc, rest⟩ | ⟨ho, hc⟩
  all_goals
    intro bad
    rw [hc] at bad
    cases bad

/-- Safety follows from this branch's actual finite-result certificate. -/
theorem objects_safe {C : Contract} {b L frame : Nat}
    {Γ Δ : Ctx} {frag : Frag Γ} {P : Prog C Γ Δ}
    (out : Memory.Objects.CompiledProg b frag P) {base : Nat → Fin W}
    {σ : State C Γ} {m : Machine}
    (input : (Evm.Compiler.Compilation.objects out).Input L frame base σ m) :
    CodeSafe out.code m := by
  apply codeSafe_of_nonfault
  rcases out.cert.correct input.1 input.2 with ⟨o, s, ho, hc, rest⟩ | ⟨ho, hc⟩
  all_goals
    intro bad
    rw [hc] at bad
    cases bad

/-- Safety follows from this branch's actual finite-result certificate. -/
theorem construction_safe {C : Contract} {b L frame : Nat}
    {Γ Δ : Ctx} {frag : Frag Γ} {P : Prog C Γ Δ}
    (out : Memory.Construction.CompiledProg b frag P) {base : Nat → Fin W}
    {σ : State C Γ} {m : Machine}
    (input : (Evm.Compiler.Compilation.construction out).Input L frame base σ m) :
    CodeSafe out.code m := by
  apply codeSafe_of_nonfault
  rcases out.cert.correct input.1 input.2.1 input.2.2 with ⟨o, s, base2, ho, hc, rest⟩ | ⟨ho, hc⟩
  all_goals
    intro bad
    rw [hc] at bad
    cases bad

/-- Safety follows from this branch's actual finite-result certificate. -/
theorem memoryCalls_safe {C : Contract} {b L frame : Nat}
    {Γ Δ : Ctx} {frag : Frag Γ} {P : Prog C Γ Δ}
    (out : Memory.Calls.Program b frag P) (hz : Evm.Prog.pushes P = 0) {base : Nat → Fin W}
    {σ : State C Γ} {m : Machine}
    (input : (Evm.Compiler.Compilation.memoryCalls out hz).Input L frame base σ m) :
    CodeSafe out.code m := by
  apply codeSafe_of_nonfault
  rcases out.sound input.1 input.2.1 input.2.2 with ⟨o, s, base2, ho, hc, rest⟩ | ⟨ho, hc⟩
  all_goals
    intro bad
    rw [hc] at bad
    cases bad

/-- Safety follows from this branch's actual finite-result certificate. -/
theorem memoryCopy_safe {C : Contract} {b L frame : Nat}
    {Γ Δ : Ctx} {frag : Frag Γ} {P : Prog C Γ Δ}
    (out : Memory.StorageCopy.CompiledProg b frag P) {base : Nat → Fin W}
    {σ : State C Γ} {m : Machine}
    (input : (Evm.Compiler.Compilation.memoryCopy out).Input L frame base σ m) :
    CodeSafe out.code m := by
  apply codeSafe_of_nonfault
  rcases out.cert.correct input.1 input.2.1 input.2.2.1 input.2.2.2 with ⟨o, s, base2, ho, hc, rest⟩ | ⟨ho, hc⟩
  all_goals
    intro bad
    rw [hc] at bad
    cases bad

/-- Safety follows from this branch's actual finite-result certificate. -/
theorem fixedMemory_safe {C : Contract} {b L frame : Nat}
    {Γ Δ : Ctx} {frag : Frag Γ} {P : Prog C Γ Δ}
    (out : Memory.Fixed.CompiledProg b frag P) {base : Nat → Fin W}
    {σ : State C Γ} {m : Machine}
    (input : (Evm.Compiler.Compilation.fixedMemory out).Input L frame base σ m) :
    CodeSafe out.code m := by
  apply codeSafe_of_nonfault
  rcases out.cert.correct input.1 input.2 with ⟨o, s, ho, hc, rest⟩ | ⟨ho, hc⟩
  all_goals
    intro bad
    rw [hc] at bad
    cases bad

/-- Safety follows from this branch's actual finite-result certificate. -/
theorem copyConstruction_safe {C : Contract} {b L frame : Nat}
    {Γ Δ : Ctx} {frag : Frag Γ} {P : Prog C Γ Δ}
    (out : Memory.CopyConstruction.CompiledProg b frag P) {base : Nat → Fin W}
    {σ : State C Γ} {m : Machine}
    (input : (Evm.Compiler.Compilation.copyConstruction out).Input L frame base σ m) :
    CodeSafe out.code m := by
  apply codeSafe_of_nonfault
  rcases out.cert.correct input.1 input.2.1 input.2.2.1 input.2.2.2 with ⟨o, s, base2, ho, hc, rest⟩ | ⟨ho, hc⟩
  all_goals
    intro bad
    rw [hc] at bad
    cases bad

/-- A successful segment retains its exact zero skip and post-state simulation. -/
theorem stmtOut_success {C : Contract} {L b : Nat} {Γ : Ctx}
    {frag : Frag Γ} {sh pays asserts : Bool} {H : HTy}
    {res : TRes (Solidity.Out C H Γ)} {out : Evm.Out} {m t : Machine} {k : Nat}
    (h : StmtOut C L b frag sh pays asserts res out m)
    (done : out = .ok t k) :
    ∃ o, res = .ok o ∧ k = 0 ∧ t.stack = m.stack ∧
      Keeps C b sh m t ∧ Sim C L b frag o.st t := by
  cases h with
  | inl h =>
    obtain ⟨o, s, ho, hc, hs, hk, hm⟩ := h
    rw [hc] at done
    cases done
    exact ⟨o, ho, rfl, hs, hk, hm⟩
  | inr h => rw [h.2] at done; cases done
  | panic _ h => rw [h.2] at done; cases done
  | refused _ h => rw [h.1] at done; cases done
  | diverge h =>
    rcases h.2 with bad | ⟨_, bad⟩ <;> rw [bad] at done <;> cases done

/-- Loop safety follows from a state invariant and safety of every reached body,
including bodies whose denotational execution diverges. -/
theorem core_loop_safe {C : Contract} {Γ Δ : Ctx} {L b : Nat}
    {frag : Frag Γ} {post : Frag Δ} (c : Solidity.Val C Γ .bool)
    (body : Prog C Γ Δ) (condition : valIn frag c = true)
    (bodyFrag : inFragP frag body = some post) (pushes : Evm.Prog.pushes body = 0)
    (restrict : post.restrict Γ = frag) (bound : L ≤ Lmax)
    (bodySafe : ∀ (σ : State C Γ) (m : Machine),
      Sim C L b frag σ m → CodeSafe (compileProg b body) m)
    {σ : State C Γ} {m : Machine} (input : Sim C L b frag σ m) :
    CodeSafe [.loop (compileVal b c) (compileProg b body)] m := by
  let I : Machine → Prop := fun s => ∃ τ : State C Γ, Sim C L b frag τ s
  apply safe_loop I I (compileVal b c) (compileProg b body) m ⟨σ, input⟩
  · intro s hs
    obtain ⟨τ, hm⟩ := hs
    apply codeSafe_of_nonfault
    rcases Evm.val_sim c hm condition with ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
    all_goals intro bad; rw [hc] at bad; cases bad
  · intro s t k hs done
    obtain ⟨τ, hm⟩ := hs
    rcases Evm.val_sim c hm condition with ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
    · obtain rfl := hw.bool_inv
      rw [hc] at done
      cases done
      refine ⟨rfl, bword v, s.stack, rfl, ?_⟩
      intro _
      exact ⟨τ, by simpa [Machine.push] using hm⟩
    · rw [hc] at done
      cases done
  · intro s hs
    obtain ⟨τ, hm⟩ := hs
    exact bodySafe τ s hm
  · intro s t k hs done
    obtain ⟨τ, hm⟩ := hs
    have hb := Evm.prog_sim body hm bodyFrag (by simpa [pushes] using bound)
    obtain ⟨o, ho, hk, hstack, hkeep, hsim⟩ := stmtOut_success hb done
    refine ⟨hk, o.st.drop body.ext, ?_⟩
    have dropped := Sim.dropState body.ext hsim
    simpa [pushes, restrict] using dropped

/-- Advance the actual cursor by one safe transition. -/
theorem safeFrom_tick (cur : Cursor Machine) (now : CursorSafe cur)
    (next : SafeFrom (tick (fun i s => idealResult (i.step s)) idealTest cur)) :
    SafeFrom cur := by
  intro n
  cases n with
  | zero => exact now
  | succ n =>
    change CursorSafe (iteratePrefix _ _ (n + 1) cur)
    rw [Nat.add_comm n 1, prefix_add]
    exact next n

/-- Skipped instructions impose no operand condition and retain the exact tail. -/
theorem safeFrom_skip (skipCode suffix : List Instr) (m : Machine)
    (safe : CodeSafe suffix m) :
    SafeFrom (.running (skipCode ++ suffix) skipCode.length [] m) := by
  induction skipCode with
  | nil => exact safe
  | cons i rest ih =>
    apply safeFrom_tick
    · trivial
    · simpa only [List.cons_append, List.length_cons, tick] using ih

/-- Sequence safety uses the successful first segment's actual post-state. -/
theorem core_seq_safe {C : Contract} {Γ Δ Ξ : Ctx} {L b : Nat}
    {frag : Frag Γ} {mid : Frag Δ} (s : Solidity.Stmt C Γ Δ) (tail : Prog C Δ Ξ)
    {σ : State C Γ} {m : Machine} (input : Sim C L b frag σ m)
    (cert : inFrag frag s = some mid) (bound : L + Evm.Stmt.pushes s ≤ Lmax)
    (first : CodeSafe (compileStmt b s) m)
    (rest : ∀ (τ : State C Δ) (t : Machine),
      Sim C (L + Evm.Stmt.pushes s) b mid τ t → CodeSafe (compileProg b tail) t) :
    CodeSafe (compileProg b (.cons s tail)) m := by
  apply safe_append (compileStmt b s) (compileProg b tail) m first
  intro t k done
  obtain ⟨o, ho, hk, hstack, hkeep, hsim⟩ :=
    stmtOut_success (Evm.stmt_sim s input cert bound) done
  subst k
  exact rest o.st t hsim

/-- Both conditional arms use the actual skip counts, including the unselected arm. -/
theorem branch_safe (yes no : List Instr) (m : Machine) (v : Bool)
    (hy : CodeSafe yes m) (hn : CodeSafe no m)
    (hyDone : ∀ s k, Evm.run yes m = .ok s k → k = 0) :
    CodeSafe ([.iszero, .jumpi (yes.length + 1)] ++ yes ++
      [.jump no.length] ++ no) (m.push (.val (bword v))) := by
  have header : Evm.run [.iszero, .jumpi (yes.length + 1)] (m.push (.val (bword v))) =
      .ok m (if v then 0 else yes.length + 1) := by cases v <;> rfl
  rw [List.append_assoc, List.append_assoc]
  apply safe_append
  · apply codeSafe_of_nonfault
    intro bad
    rw [header] at bad
    cases bad
  · intro s k done
    rw [header] at done
    cases done
    cases v with
    | false =>
      have skip := safeFrom_skip (yes ++ [.jump no.length]) no m hn
      simpa only [List.append_assoc, List.length_append, List.length_singleton] using skip
    | true =>
      change CodeSafe (yes ++ ([.jump no.length] ++ no)) m
      refine safe_append yes ([Instr.jump no.length] ++ no) m hy ?_
      intro s k done
      have hk := hyDone s k done
      subst k
      apply codeSafe_of_nonfault
      have jump : Evm.run ([.jump no.length] ++ no) s = .ok s 0 := by
        change exec no no.length s = .ok s 0
        exact exec_length no s
      intro bad
      rw [jump] at bad
      cases bad

/-- A compiled conditional is safe even when its selected branch diverges. -/
theorem core_ite_safe {C : Contract} {Γ Δ Ξ : Ctx} {L b : Nat}
    {frag : Frag Γ} {yesFrag : Frag Δ}
    (c : Solidity.Val C Γ .bool) (yes : Prog C Γ Δ) (no : Prog C Γ Ξ)
    {σ : State C Γ} {m : Machine} (input : Sim C L b frag σ m)
    (condition : valIn frag c = true)
    (yesCert : inFragP frag yes = some yesFrag)
    (yesBound : L + Evm.Prog.pushes yes ≤ Lmax)
    (hy : CodeSafe (compileProg b yes) m) (hn : CodeSafe (compileProg b no) m) :
    CodeSafe (compileStmt b (.ite c yes no)) m := by
  simp only [compileStmt, List.append_assoc]
  apply safe_append
  · apply codeSafe_of_nonfault
    rcases Evm.val_sim c input condition with ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
    all_goals intro bad; rw [hc] at bad; cases bad
  · intro s k done
    rcases Evm.val_sim c input condition with ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
    · obtain rfl := hw.bool_inv
      rw [hc] at done
      cases done
      have branch := branch_safe (compileProg b yes) (compileProg b no) m v hy hn
        (fun s k done => (stmtOut_success (Evm.prog_sim yes input yesCert yesBound) done).choose_spec.2.1)
      simpa only [List.append_assoc] using branch
    · rw [hc] at done
      cases done

/-- Calls enter the actual argument frame, preserve divergent body prefixes,
and leave through the compiler's finite return code. -/
theorem core_call_safe {C : Contract} {Γ Γ' ps rs Γf : Ctx} {L b : Nat}
    {frag : Frag Γ} {post : Frag Γ'} (f : Name) (args : Solidity.Args C Γ ps)
    (ret : Solidity.CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf)
    {σ : State C Γ} {m : Machine} (input : Sim C L b frag σ m)
    (cert : inFrag frag (.call f args ret body) = some post)
    (bound : L + Evm.Prog.pushes body ≤ Lmax)
    (bodySafe : ∀ {G : Frag Γf} {τ : State C (rs ++ ps)} {s : Machine},
      inFragP (Frag.init (rs ++ ps)) body = some G →
      Sim C L (b + Γ.length) (Frag.init (rs ++ ps)) τ s →
      CodeSafe (compileProg (b + Γ.length) body) s) :
    CodeSafe (compileStmt b (.call f args ret body)) m := by
  obtain ⟨hwa, ⟨G, hb⟩, hret⟩ := Evm.call_frag cert
  cases ret with
  | none =>
    simp only [compileStmt, retEnterCode, retLeaveCode, List.append_nil]
    apply safe_append
    · apply codeSafe_of_nonfault
      rcases Evm.args_sim input args hwa with ⟨a, mem1, ha, hc, hmem, hv⟩ | ⟨ha, hc⟩
      all_goals intro bad; rw [hc] at bad; cases bad
    · intro s k done
      rcases Evm.args_sim input args hwa with ⟨a, mem1, ha, hc, hmem, hv⟩ | ⟨ha, hc⟩
      · rw [hc] at done
        cases done
        have entered := (input.congrMem (mem := mem1) fun l _ hl => hmem l hl).enter
          (b + Γ.length) (Look.ofTEnv a) hv (Args.noAlias args hwa)
        exact bodySafe hb (τ := σ.withEnv a) entered
      · rw [hc] at done
        cases done
  | val p r res =>
    simp only [compileStmt, List.append_assoc]
    apply safe_append
    · apply codeSafe_of_nonfault
      rcases Evm.args_sim input args hwa with ⟨a, mem1, ha, hc, hmem, hv⟩ | ⟨ha, hc⟩
      all_goals intro bad; rw [hc] at bad; cases bad
    · intro s k done
      rcases Evm.args_sim input args hwa with ⟨a, mem1, ha, hc, hmem, hv⟩ | ⟨ha, hc⟩
      · rw [hc] at done
        cases done
        have entered := ((input.congrMem (mem := mem1) fun l _ hl => hmem l hl).enter
          (b + Γ.length) (Look.ofTEnv a) hv (Args.noAlias args hwa)).consVal
          (v := PrimTy.dflt p) (ReprV.dflt_zero p)
        have simulated : Sim C L (b + Γ.length) (Frag.init ([.val p] ++ ps))
            ((σ.withEnv a).push (t := .val p) (PrimTy.dflt p))
            {m with mem := Evm.upd mem1 (cell (b + Γ.length + ps.length)) w[0]} :=
          entered.congrLook fun j => Look.ofTEnv_cons (u := .val p) (PrimTy.dflt p) a j
        have enterRun : Evm.run (retEnterCode b ps (.val p r res)) {m with mem := mem1} =
            .ok {m with mem := Evm.upd mem1 (cell (b + Γ.length + ps.length)) w[0]} 0 := rfl
        change CodeSafe _ _
        apply safe_append
        · apply codeSafe_of_nonfault
          intro bad
          rw [enterRun] at bad
          cases bad
        · intro s k done
          rw [enterRun] at done
          cases done
          refine safe_append (compileProg (b + Γ.length) body)
            (retLeaveCode b ps (.val p r res)) _ (bodySafe hb simulated) ?_
          intro t k done
          have hk := (stmtOut_success (Evm.prog_sim body simulated hb bound) done).choose_spec.2.1
          subst k
          apply codeSafe_of_nonfault
          cases res <;> intro bad <;> cases bad
      · rw [hc] at done
        cases done
  | rets _ => cases hret
  | mem _ _ _ _ => cases hret
  | storage _ _ => cases hret

/-- info: 'Solidity.Hash.CompilerCorrect.compilation_safe_of_nondiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.compilation_safe_of_nondiv

/-- info: 'Solidity.Hash.CompilerCorrect.compilerBridge_of_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.compilerBridge_of_safe

/-- info: 'Solidity.Hash.CompilerCorrect.memory_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.memory_safe

/-- info: 'Solidity.Hash.CompilerCorrect.referenceArrays_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.referenceArrays_safe

/-- info: 'Solidity.Hash.CompilerCorrect.objects_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.objects_safe

/-- info: 'Solidity.Hash.CompilerCorrect.construction_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.construction_safe

/-- info: 'Solidity.Hash.CompilerCorrect.memoryCalls_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.memoryCalls_safe

/-- info: 'Solidity.Hash.CompilerCorrect.memoryCopy_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.memoryCopy_safe

/-- info: 'Solidity.Hash.CompilerCorrect.fixedMemory_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.fixedMemory_safe

/-- info: 'Solidity.Hash.CompilerCorrect.copyConstruction_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.copyConstruction_safe

/-- info: 'Solidity.Hash.CompilerCorrect.core_loop_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.core_loop_safe

/-- info: 'Solidity.Hash.CompilerCorrect.core_seq_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.core_seq_safe

/-- info: 'Solidity.Hash.CompilerCorrect.core_ite_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.core_ite_safe

/-- info: 'Solidity.Hash.CompilerCorrect.core_call_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CompilerCorrect.core_call_safe

end Solidity.Hash.CompilerCorrect
