import Solidity.Hash.CompilerCorrect

namespace Solidity.Hash.CompilerCorrect

open Solidity.Evm Solidity.Goals.HashContract

def CursorSafe : Cursor Machine → Prop
  | .running (i :: _) 0 _ m => (∀ c b, i ≠ .loop c b) → i.step m ≠ .fault
  | .running [] 0 (.test _ _ _ :: _) m => ∃ w tail, m.stack = .val w :: tail
  | _ => True

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

def appendFrameSuffix (suffix : List Instr) : Frame → Frame
  | .test c b rest => .test c b (rest ++ suffix)
  | .body c b rest => .body c b (rest ++ suffix)

def attachFrames (suffix : List Instr) (outer : List Frame) : List Frame → List Frame
  | [] => outer
  | [f] => appendFrameSuffix suffix f :: outer
  | f :: g :: fs => f :: attachFrames suffix outer (g :: fs)

def attachCursor (suffix : List Instr) (outer : List Frame) : Cursor S → Cursor S
  | .running c k [] m => .running (c ++ suffix) k outer m
  | .running c k (f :: fs) m => .running c k (attachFrames suffix outer (f :: fs)) m
  | .halted r => .halted r

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

def SafeFrom (cur : Cursor Machine) : Prop :=
  ∀ n, CursorSafe (iteratePrefix (fun i s => idealResult (i.step s)) idealTest n cur)

theorem boundary_result (c : List Instr) (m : Machine) (n k : Nat) (s : Machine)
    (hrch : producer.ideal n c m = .running [] k [] s) :
    Evm.run c m = .ok s k := by
  have hd := denote_prefix n (.running c 0 [] m)
  change denoteCursor (producer.ideal n c m) = Evm.run c m at hd
  rw [hrch] at hd
  exact hd.symm

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

theorem safe_append (a b : List Instr) (m : Machine) (ha : CodeSafe a m)
    (hb : ∀ s k, Evm.run a m = .ok s k → SafeFrom (.running b k [] s)) :
    CodeSafe (a ++ b) m := by
  intro n
  rcases append_prefix_phase a b m n with ⟨inside, heq⟩ | ⟨s, k, j, hr, heq⟩
  · rw [heq]
    exact attach_safe b [] _ inside (ha n)
  · rw [heq]
    exact hb s k hr j

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

theorem safeFrom_skip (skipCode suffix : List Instr) (m : Machine)
    (safe : CodeSafe suffix m) :
    SafeFrom (.running (skipCode ++ suffix) skipCode.length [] m) := by
  induction skipCode with
  | nil => exact safe
  | cons i rest ih =>
    apply safeFrom_tick
    · trivial
    · simpa only [List.cons_append, List.length_cons, tick] using ih

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

theorem branch_safe (yes no : List Instr) (m : Machine) (v : Bool)
    (hy : v = true → CodeSafe yes m) (hn : v = false → CodeSafe no m)
    (hyDone : v = true → ∀ s k, Evm.run yes m = .ok s k → k = 0) :
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
      have skip := safeFrom_skip (yes ++ [.jump no.length]) no m (hn rfl)
      simpa only [List.append_assoc, List.length_append, List.length_singleton] using skip
    | true =>
      change CodeSafe (yes ++ ([.jump no.length] ++ no)) m
      refine safe_append yes ([Instr.jump no.length] ++ no) m (hy rfl) ?_
      intro s k done
      have hk := hyDone rfl s k done
      subst k
      apply codeSafe_of_nonfault
      have jump : Evm.run ([.jump no.length] ++ no) s = .ok s 0 := by
        change exec no no.length s = .ok s 0
        exact exec_length no s
      intro bad
      rw [jump] at bad
      cases bad

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
      have branch := branch_safe (compileProg b yes) (compileProg b no) m v (fun _ => hy) (fun _ => hn)
        (fun _ s k done => (stmtOut_success (Evm.prog_sim yes input yesCert yesBound) done).choose_spec.2.1)
      simpa only [List.append_assoc] using branch
    · rw [hc] at done
      cases done

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

namespace Solidity.Hash.CompilerCorrect
open Solidity.Evm Solidity.Goals.HashContract

theorem alias_noDiv {C : Contract} {Γ : Ctx} (σ : State C Γ) {R : RefTy} :
    (r : ARhs C Γ R) → (r.evalT σ).NoDiv
  | .path p => TRes.NoDiv.bind (p.resolveT_ends σ).1 fun _ => TRes.NoDiv.ok _
  | .push b _ => TRes.NoDiv.bind (b.resolveT_ends σ).1 fun r => by
    show (if σ.storage.full r then .error .exhausted else do
      let (st, n) ← TRes.ofOpt (σ.storage.pushPlace r)
      pure (st, r.index (.arr .dyn) n) : TRes _).NoDiv
    split
    · exact fun h => nomatch h
    · exact (TRes.NoDiv.ofOpt _).bind fun _ => TRes.NoDiv.ok _

theorem push_noDiv {C : Contract} {Γ : Ctx} (σ : State C Γ) {E : Ty}
    (b : SPath C Γ (.array E)) (v : Option (Src C Γ E)) :
    (TRun.push b v σ).NoDiv := by
  unfold TRun.push
  refine TRes.NoDiv.bind (b.resolveT_ends σ).1 fun ref => ?_
  cases v with
  | none =>
    dsimp only
    split
    · exact fun h => nomatch h
    · exact (TRes.NoDiv.ofOpt _).bind fun _ => TRes.NoDiv.ok _
  | some r =>
    refine TRes.NoDiv.bind (r.valueT_ends σ).1 fun _ => ?_
    dsimp only
    split
    · exact fun h => nomatch h
    · exact (TRes.NoDiv.ofOpt _).bind fun _ => TRes.NoDiv.ok _

def CoreLeaf {C : Contract} {Γ Δ : Ctx} : Solidity.Stmt C Γ Δ → Prop
  | .assign .. | .rebind .. | .assignLocal .. | .declLocal .. | .declStorage ..
  | .opAssign .. | .incDec .. | .assignIncDec .. | .push .. | .pop ..
  | .transfer .. | .delete .. | .require .. | .assert .. | .revert => True
  | _ => False

theorem core_leaf_noDiv {C : Contract} {Γ Δ : Ctx} (s : Solidity.Stmt C Γ Δ)
    (leaf : CoreLeaf s) (σ : State C Γ) : (s.run σ).NoDiv := by
  cases s <;> simp only [CoreLeaf] at leaf
  case assign l r =>
    exact TRes.NoDiv.bind (r.valueT_ends σ).1 fun _ => TRes.NoDiv.bind (l.resolveT_ends σ).1
      fun _ => (TRes.NoDiv.ofOpt _).bind fun _ => TRes.NoDiv.ok _
  case rebind i r => exact (alias_noDiv σ r).bind fun _ => TRes.NoDiv.ok _
  case assignLocal i r => exact TRes.NoDiv.bind (r.evalT_ends σ).1 fun _ => TRes.NoDiv.ok _
  case declLocal p x init =>
    cases init with
    | none => exact TRes.NoDiv.ok _
    | some e => exact TRes.NoDiv.bind (e.evalT_ends σ).1 fun _ => TRes.NoDiv.ok _
  case declStorage R x init =>
    cases init with
    | none => exact TRes.NoDiv.ok _
    | some r => exact (alias_noDiv σ r).bind fun _ => TRes.NoDiv.ok _
  case opAssign op hop hp l r =>
    exact TRes.NoDiv.bind (r.evalT_ends σ).1 fun _ => (OpLoc.storeT_ends σ op l _).1
  case incDec op hp l => exact TRes.NoDiv.bind (OpLoc.bumpT_ends σ op l).1 fun _ => TRes.NoDiv.ok _
  case assignIncDec op hp i l hs =>
    exact TRes.NoDiv.bind (OpLoc.bumpT_ends σ op l).1 fun _ => TRes.NoDiv.ok _
  case push b v hd => exact push_noDiv σ b v
  case pop b => exact TRes.NoDiv.bind (b.resolveT_ends σ).1 fun _ =>
    (TRes.NoDiv.ofOpt _).bind fun _ => TRes.NoDiv.ok _
  case transfer r a =>
    apply TRes.NoDiv.bind (r.evalT_ends σ).1
    intro _
    apply TRes.NoDiv.bind (a.evalT_ends σ).1
    intro _
    split
    · exact TRes.NoDiv.ok _
    · exact fun h => nomatch h
  case delete l => exact TRes.NoDiv.bind (l.resolveT_ends σ).1 fun _ =>
    (TRes.NoDiv.ofOpt _).bind fun _ => TRes.NoDiv.ok _
  case require c =>
    apply TRes.NoDiv.bind (c.evalT_ends σ).1
    intro _
    split
    · exact TRes.NoDiv.ok _
    · exact fun h => nomatch h
  case assert c =>
    apply TRes.NoDiv.bind (c.evalT_ends σ).1
    intro _
    split
    · exact TRes.NoDiv.ok _
    · exact fun h => nomatch h
  case revert => exact fun h => nomatch h

theorem stmtOut_nonfault {C : Contract} {L b : Nat} {Γ : Ctx} {frag : Frag Γ}
    {sh pays asserts : Bool} {H : HTy} {res : TRes (Solidity.Out C H Γ)}
    {out : Evm.Out} {m : Machine} (h : StmtOut C L b frag sh pays asserts res out m)
    (finite : res.NoDiv) : out ≠ .fault := by
  intro bad
  cases h with
  | inl h => obtain ⟨o, s, ho, hc, rest⟩ := h; rw [hc] at bad; cases bad
  | inr h => rw [h.2] at bad; cases bad
  | panic _ h => rw [h.2] at bad; cases bad
  | refused _ h => rw [h.1] at bad; cases bad
  | diverge h => exact finite h.1

theorem core_leaf_safe {C : Contract} {Γ Δ : Ctx} {L b : Nat}
    {frag : Frag Γ} {post : Frag Δ} (s : Solidity.Stmt C Γ Δ) (leaf : CoreLeaf s)
    {σ : State C Γ} {m : Machine} (input : Sim C L b frag σ m)
    (cert : inFrag frag s = some post) (bound : L + Evm.Stmt.pushes s ≤ Lmax) :
    CodeSafe (compileStmt b s) m :=
  codeSafe_of_nonfault _ _ (stmtOut_nonfault (Evm.stmt_sim s input cert bound)
    (core_leaf_noDiv s leaf σ))

theorem core_outside_safe {C : Contract} {Γ Δ : Ctx} (s : Solidity.Stmt C Γ Δ)
    (outside : Evm.Stmt.evmOutside s = true) {L b : Nat}
    {frag : Frag Γ} {post : Frag Δ} {σ : State C Γ} {m : Machine} :
    Sim C L b frag σ m → inFrag frag s = some post → L + Evm.Stmt.pushes s ≤ Lmax →
      CodeSafe (compileStmt b s) m :=
  fun _ cert _ => Option.noConfusion ((Evm.inFrag_outside _ _ outside).symm.trans cert)

mutual

theorem core_stmt_safe : ∀ {C : Contract} {Γ Δ : Ctx} (s : Solidity.Stmt C Γ Δ)
    {L b : Nat} {frag : Frag Γ} {post : Frag Δ} {σ : State C Γ} {m : Machine},
    Sim C L b frag σ m → inFrag frag s = some post → L + Evm.Stmt.pushes s ≤ Lmax →
      CodeSafe (compileStmt b s) m
  | _, _, _, .assign l r => fun hm hw hL => core_leaf_safe (.assign l r) (by trivial) hm hw hL
  | _, _, _, .rebind i r => fun hm hw hL => core_leaf_safe (.rebind i r) (by trivial) hm hw hL
  | _, _, _, .assignLocal i r => fun hm hw hL => core_leaf_safe (.assignLocal i r) (by trivial) hm hw hL
  | _, _, _, .declLocal p x init => fun hm hw hL => core_leaf_safe (.declLocal p x init) (by trivial) hm hw hL
  | _, _, _, .declStorage R x init => fun hm hw hL => core_leaf_safe (.declStorage R x init) (by trivial) hm hw hL
  | _, _, _, .opAssign op hop hp l r => fun hm hw hL => core_leaf_safe (.opAssign op hop hp l r) (by trivial) hm hw hL
  | _, _, _, .incDec op hp l => fun hm hw hL => core_leaf_safe (.incDec op hp l) (by trivial) hm hw hL
  | _, _, _, .assignIncDec i op hp l hs => fun hm hw hL => core_leaf_safe (.assignIncDec i op hp l hs) (by trivial) hm hw hL
  | _, _, _, .push q v hd => fun hm hw hL => core_leaf_safe (.push q v hd) (by trivial) hm hw hL
  | _, _, _, .pop q => fun hm hw hL => core_leaf_safe (.pop q) (by trivial) hm hw hL
  | _, _, _, .transfer r a => fun hm hw hL => core_leaf_safe (.transfer r a) (by trivial) hm hw hL
  | _, _, _, .delete l => fun hm hw hL => core_leaf_safe (.delete l) (by trivial) hm hw hL
  | _, _, _, .require c => fun hm hw hL => core_leaf_safe (.require c) (by trivial) hm hw hL
  | _, _, _, .assert c => fun hm hw hL => core_leaf_safe (.assert c) (by trivial) hm hw hL
  | _, _, _, .revert => fun hm hw hL => core_leaf_safe (.revert) (by trivial) hm hw hL
  | _, _, _, .assumeFalse => fun _ hw _ => nomatch hw
  | _, _, _, .ite c t e => fun hm hw hL => by
    obtain ⟨hwc, F₁, F₂, ht, he, rfl⟩ := Evm.ite_frag hw
    have bound : _ + (Evm.Prog.pushes t + Evm.Prog.pushes e) ≤ Lmax := hL
    exact core_ite_safe c t e hm hwc ht (by omega)
      (core_prog_safe t hm ht (by omega)) (core_prog_safe e hm he (by omega))
  | _, _, _, .block body => fun hm hw hL => by
    obtain ⟨G, hb, rfl⟩ := Evm.block_frag hw
    exact core_prog_safe body hm hb hL
  | _, _, _, .call f args ret body => fun hm hw hL =>
    core_call_safe f args ret body hm hw hL fun hb hm₂ => core_prog_safe body hm₂ hb hL
  | _, _, _, .loop a c body => fun hm hw hL => by
    obtain ⟨hwc, hpush, hpay, hshr, G, hb, hG, rfl⟩ := Evm.loop_frag hw
    exact core_loop_safe c body hwc hb hpush hG hL
      (fun τ m hm' => core_prog_safe body hm' hb (by simpa [hpush] using hL)) hm
  | _, _, _, .tryCall .. => fun _ hw _ => by rw [Evm.inFrag_tryCall] at hw; cases hw
  | _, _, _, .send a0 a1 a2 a3 => core_outside_safe (.send a0 a1 a2 a3) rfl
  | _, _, _, .declMem a0 a1 a2 a3 a4 => core_outside_safe (.declMem a0 a1 a2 a3 a4) rfl
  | _, _, _, .rebindMem a0 a1 => core_outside_safe (.rebindMem a0 a1) rfl
  | _, _, _, .assignFromMem a0 a1 => core_outside_safe (.assignFromMem a0 a1) rfl
  | _, _, _, .assignMem a0 a1 => core_outside_safe (.assignMem a0 a1) rfl
  | _, _, _, .deleteMem a0 a1 => core_outside_safe (.deleteMem a0 a1) rfl
  | _, _, _, .assignNew a0 a1 a2 => core_outside_safe (.assignNew a0 a1 a2) rfl
  | _, _, _, .assignLocalPush a0 a1 => core_outside_safe (.assignLocalPush a0 a1) rfl
  | _, _, _, .pushOpAssign a0 a1 a2 a3 a4 => core_outside_safe (.pushOpAssign a0 a1 a2 a3 a4) rfl
  | _, _, _, .pushIncDec a0 a1 a2 => core_outside_safe (.pushIncDec a0 a1 a2) rfl
  | _, _, _, .callReceiver a0 a1 a2 a3 a4 => core_outside_safe (.callReceiver a0 a1 a2 a3 a4) rfl
  | _, _, _, .callReceiverPush a0 a1 a2 a3 a4 a5 => core_outside_safe (.callReceiverPush a0 a1 a2 a3 a4 a5) rfl
  | _, _, _, .callRec a0 a1 a2 a3 a4 => core_outside_safe (.callRec a0 a1 a2 a3 a4) rfl
  | _, _, _, .revertData a0 => core_outside_safe (.revertData a0) rfl
  | _, _, _, .catchData c rets sargs sbody self kind x body => core_outside_safe (.catchData c rets sargs sbody self kind x body) rfl

theorem core_prog_safe : ∀ {C : Contract} {Γ Δ : Ctx} (P : Prog C Γ Δ)
    {L b : Nat} {frag : Frag Γ} {post : Frag Δ} {σ : State C Γ} {m : Machine},
    Sim C L b frag σ m → inFragP frag P = some post → L + Evm.Prog.pushes P ≤ Lmax →
      CodeSafe (compileProg b P) m
  | _, _, _, .nil => fun _ _ _ => codeSafe_of_nonfault _ _ (by intro bad; cases bad)
  | _, _, _, .cons s P => fun hm hw hL => by
    simp only [inFragP] at hw
    split at hw
    · rename_i F₁ hs
      have bound : _ + (Evm.Stmt.pushes s + Evm.Prog.pushes P) ≤ Lmax := hL
      exact core_seq_safe s P hm hs (by omega) (core_stmt_safe s hm hs (by omega))
        fun τ m hm' => core_prog_safe P hm' hw (by omega)
    · cases hw

end

theorem memory_loop_safe {C : Contract} {Γ Δ : Ctx} {L b frame : Nat}
    {frag : Frag Γ} {c : Solidity.Val C Γ .bool} {body : Prog C Γ Δ}
    {cond code : List Instr} (cert : Memory.LoopCert b frag c body cond code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : Memory.StateRepr L b frame frag σ base m)
    (cap : b + Memory.frameNeedProg body ≤ frame)
    (room : Memory.LoopRoom b frame c body σ base m) :
    CodeSafe [.loop cond code] m := by
  let I : Machine → Prop := fun s =>
    ∃ (o : Solidity.Out C σ.H Γ) (bases : Nat → Fin W) (cost : Nat),
      Memory.LoopPrefix c body σ o cost ∧ Memory.StateRepr L b frame frag o.st bases s ∧
      Memory.GrowsAllocator b frame cost σ base m o.st bases s
  let J : Machine → Prop := fun s =>
    ∃ (o : Solidity.Out C σ.H Γ) (bases : Nat → Fin W) (cost : Nat),
      Memory.LoopPrefix c body σ o cost ∧ Memory.StateRepr L b frame frag o.st bases s ∧
      Memory.GrowsAllocator b frame cost σ base m o.st bases s ∧ c.evalT o.st = .ok true
  apply safe_loop I J cond code m
  · exact ⟨⟨σ, List.prefix_refl _⟩, base, 0, .start, repr, fun _ _ ha _ => ha⟩
  · intro s hs
    obtain ⟨o, bases, cost, hp, hr, hg⟩ := hs
    apply codeSafe_of_nonfault
    rcases cert.condition.correct hr with ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
    all_goals intro bad; rw [hc] at bad; cases bad
  · intro s t k hs done
    obtain ⟨o, bases, cost, hp, hr, hg⟩ := hs
    rcases cert.condition.correct hr with ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
    · obtain rfl := hw.bool_inv
      rw [hc] at done
      cases done
      refine ⟨rfl, bword v, s.stack, rfl, ?_⟩
      intro nonzero
      cases v with
      | false => exact False.elim (nonzero rfl)
      | true =>
        exact ⟨o, bases, cost, hp, by simpa [Machine.push] using hr,
          by simpa [Machine.push] using hg, hv⟩
    · rw [hc] at done
      cases done
  · intro s hs
    obtain ⟨o, bases, cost, hp, hr, hg, hv⟩ := hs
    have capacity := hg.nextInput (room o cost hp hv)
    apply codeSafe_of_nonfault
    rcases cert.bodyCert.correct hr cap capacity with
      ⟨o', t, bases', ho, hc, hr', hstack, hbase, hg'⟩ | ⟨ho, hc⟩
    all_goals intro bad; rw [hc] at bad; cases bad
  · intro s t k hs done
    obtain ⟨o, bases, cost, hp, hr, hg, hv⟩ := hs
    have capacity := hg.nextInput (room o cost hp hv)
    rcases cert.bodyCert.correct hr cap capacity with
      ⟨o', t', bases', ho, hc, hr', hstack, hbase, hg'⟩ | ⟨ho, hc⟩
    · rw [hc] at done
      cases done
      refine ⟨rfl, ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩, bases',
        cost + Memory.allocationCostProg body o.st, .next hp hv ho, ?_, hg.comp hg'⟩
      rw [← cert.stable]
      exact hr'.drop body.ext
    · rw [hc] at done
      cases done

theorem loops_stmt_safe {C : Contract} {b L frame Γ Δ F G stmt code}
    (hs : Memory.Loops.StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G stmt code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : Memory.StateRepr L b frame F σ base m) (cap : b + hs.need ≤ frame)
    (room : ∀ amount, hs.Demand σ amount → Memory.AllocationInput b frame amount σ base m) :
    CodeSafe code m := by
  cases hs with
  | finite cert =>
    apply codeSafe_of_nonfault
    rcases cert.correct repr cap (room _ rfl) with
      ⟨o, t, bases, ho, hc, rest⟩ | ⟨ho, hc⟩
    all_goals intro bad; rw [hc] at bad; cases bad
  | loop a c body cond code G hc hb stable =>
    apply memory_loop_safe ⟨hc, G, hb, stable⟩ repr
    · change b + max Γ.length (Memory.frameNeedProg body) ≤ frame at cap
      omega
    · exact fun o cost hp hv => room _ (.inr ⟨o, cost, hp, hv, rfl⟩)

theorem loops_stmt_success {C : Contract} {b L frame Γ Δ F G stmt code}
    (hs : Memory.Loops.StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G stmt code)
    {σ : State C Γ} {base : Nat → Fin W} {m t : Machine} {k : Nat}
    (repr : Memory.StateRepr L b frame F σ base m) (cap : b + hs.need ≤ frame)
    (room : ∀ amount, hs.Demand σ amount → Memory.AllocationInput b frame amount σ base m)
    (done : Evm.run code m = .ok t k) :
    ∃ (o : Solidity.Out C σ.H Δ) (bases : Nat → Fin W) (cost : Nat),
      stmt.run σ = .ok o ∧ k = 0 ∧ hs.Cost σ o cost ∧
      Memory.StateRepr L b frame G o.st bases t ∧
      Memory.GrowsAllocator b frame cost σ base m o.st bases t := by
  cases hs with
  | finite cert =>
    rcases cert.correct repr cap (room _ rfl) with
      ⟨o, t', bases, ho, hc, hr, hstack, hbase, hg⟩ | ⟨ho, hc⟩
    · rw [hc] at done
      cases done
      exact ⟨o, bases, _, ho, rfl, rfl, hr, hg⟩
    · rw [hc] at done
      cases done
  | loop a c body cond code G hc hb stable =>
    have cap' : b + Memory.frameNeedProg body ≤ frame := by
      change b + max Γ.length (Memory.frameNeedProg body) ≤ frame at cap
      omega
    have room' : Memory.LoopRoom b frame c body σ base m :=
      fun o cost hp hv => room _ (.inr ⟨o, cost, hp, hv, rfl⟩)
    rcases Memory.LoopCert.correct ⟨hc, G, hb, stable⟩ a repr cap' room' with
      ⟨o, t', bases, cost, ho, hout, hp, hr, hstack, hbase, hg⟩ | ⟨ho, hout⟩ | ⟨ho, hout⟩
    · rw [hout] at done
      cases done
      exact ⟨o, bases, cost, ho, rfl, hp, hr, hg⟩
    · rw [hout] at done
      cases done
    · rw [hout] at done
      cases done

theorem loops_prog_safe {C : Contract} {b L frame Γ Δ F G P code}
    (hp : Memory.Loops.ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : Memory.StateRepr L b frame F σ base m) (cap : b + hp.need ≤ frame)
    (room : Memory.Loops.Room hp frame σ base m) : CodeSafe code m := by
  induction hp generalizing base m with
  | nil F => exact codeSafe_of_nonfault _ _ (by intro bad; cases bad)
  | @cons Γ Δ Ξ F G K stmt P head tail hs hp ih =>
    have caps : b + hs.need ≤ frame := by change b + max hs.need hp.need ≤ frame at cap; omega
    have capp : b + hp.need ≤ frame := by change b + max hs.need hp.need ≤ frame at cap; omega
    have roomHead := fun amount h => room amount (Memory.Loops.Demand.head h)
    apply safe_append head tail m (loops_stmt_safe hs repr caps roomHead)
    intro t k done
    obtain ⟨o, bases, cost, ho, hk, hc, hr, hg⟩ := loops_stmt_success hs repr caps roomHead done
    subst k
    exact ih hr capp (fun amount hd => hg.nextInput (room _ (.tail ho hc hd)))

def ScopeStmtSafe {C : Contract} {b Γ Δ F G stmt code}
    (hs : Memory.LoopScopes.StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G stmt code)
    (L frame : Nat) : Prop :=
  ∀ (σ : State C Γ) (base : Nat → Fin W) (m : Machine),
    Memory.StateRepr L b frame F σ base m → b + hs.need ≤ frame →
    (∀ amount, Memory.LoopScopes.StmtDemand hs σ amount →
      Memory.AllocationInput b frame amount σ base m) → CodeSafe code m

def ScopeProgSafe {C : Contract} {b Γ Δ F G P code}
    (hp : Memory.LoopScopes.ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    (L frame : Nat) : Prop :=
  ∀ (σ : State C Γ) (base : Nat → Fin W) (m : Machine),
    Memory.StateRepr L b frame F σ base m → b + hp.need ≤ frame →
    Memory.LoopScopes.Room hp frame σ base m → CodeSafe code m

theorem scopes_prog_safe {C : Contract} {b L frame Γ Δ F G P code}
    (hp : Memory.LoopScopes.ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code) :
    ScopeProgSafe hp L frame := by
  induction hp using Memory.LoopScopes.ProgCert.rec
    (motive_1 := fun F G stmt code hs => ScopeStmtSafe hs L frame) with
  | base hs =>
    intro σ base m hr cap room
    have safe := loops_prog_safe (Memory.LoopScopes.singleton hs) hr cap
      (fun amount hd => room amount (.base hd))
    simpa only [List.append_nil] using safe
  | @block Γ Δ F G body code hp ih =>
    intro σ base m hr cap room
    have cap' : b + hp.need ≤ frame := by
      change b + max Γ.length hp.need ≤ frame at cap
      omega
    exact ih σ base m hr cap' (fun amount hd => room amount (.block hd))
  | @ite Γ Δ Ξ F G K c thn els cond left right hc ht he iht ihe =>
    intro σ base m hr cap room
    have capt : b + ht.need ≤ frame := by
      change b + max Γ.length (max ht.need he.need) ≤ frame at cap
      omega
    have cape : b + he.need ≤ frame := by
      change b + max Γ.length (max ht.need he.need) ≤ frame at cap
      omega
    simp only [Memory.conditionalCode, List.append_assoc]
    apply safe_append
    · apply codeSafe_of_nonfault
      rcases hc.correct hr with ⟨v, w, hv, hw, hout⟩ | ⟨hv, hout⟩
      all_goals intro bad; rw [hout] at bad; cases bad
    · intro s k done
      rcases hc.correct hr with ⟨v, w, hv, hw, hout⟩ | ⟨hv, hout⟩
      · obtain rfl := hw.bool_inv
        rw [hout] at done
        cases done
        have selected : CodeSafe ([.iszero, .jumpi (left.length + 1)] ++ left ++
            [.jump right.length] ++ right) (m.push (.val (bword v))) := by
          apply branch_safe
          · intro choice
            subst v
            exact iht σ base m hr capt (fun amount hd => room amount (.iteTrue hv hd))
          · intro choice
            subst v
            exact ihe σ base m hr cape (fun amount hd => room amount (.iteFalse hv hd))
          · intro choice t k done
            subst v
            rcases ht.correct σ base m hr capt (fun amount hd => room amount (.iteTrue hv hd)) with
              ⟨o, t', bases, amount, ho, hout, rest⟩ | ⟨ho, hout⟩ | ⟨ho, hout⟩
            · rw [hout] at done
              cases done
              rfl
            · rw [hout] at done
              cases done
            · rw [hout] at done
              cases done
        simpa only [List.append_assoc] using selected
      · rw [hout] at done
        cases done
  | nil F => intro σ base m hr cap room; exact codeSafe_of_nonfault _ _ (by intro bad; cases bad)
  | @cons Γ Δ Ξ F G K stmt P head tail hs hp ihs ihp =>
    intro σ base m hr cap room
    have caps : b + hs.need ≤ frame := by change b + max hs.need hp.need ≤ frame at cap; omega
    have capp : b + hp.need ≤ frame := by change b + max hs.need hp.need ≤ frame at cap; omega
    have headRoom := fun amount hd => room amount (Memory.LoopScopes.Demand.head hd)
    apply safe_append head tail m (ihs σ base m hr caps headRoom)
    intro t k done
    rcases hs.correct σ base m hr caps headRoom with
      ⟨o, t', bases, amount, ho, hout, hc, hr', hstack, hbase, hg⟩ | ⟨ho, hout⟩ | ⟨ho, hout⟩
    · rw [hout] at done
      cases done
      exact ihp o.st bases _ hr' capp (fun n hd => hg.nextInput (room _ (.tail ho hc hd)))
    · rw [hout] at done
      cases done
    · rw [hout] at done
      cases done

theorem compilation_safe {C : Contract} {Γ Δ : Ctx} {b L frame : Nat}
    {frag : Frag Γ} {P : Prog C Γ Δ} (r : Evm.Compiler.Compilation b frag P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (input : r.Input L frame base σ m) : CodeSafe r.code m := by
  cases r with
  | core post cert => exact core_prog_safe P input.1 cert input.2
  | memory out => exact memory_safe out input
  | referenceArrays out => exact referenceArrays_safe out input
  | objects out => exact objects_safe out input
  | construction out => exact construction_safe out input
  | memoryLoops out => exact loops_prog_safe out.cert input.1 input.2.1 input.2.2
  | memoryLoopScopes out => exact scopes_prog_safe out.cert σ base m input.1 input.2.1 input.2.2
  | memoryCalls out hz => exact memoryCalls_safe out hz input
  | memoryCopy out => exact memoryCopy_safe out input
  | fixedMemory out => exact fixedMemory_safe out input
  | copyConstruction out => exact copyConstruction_safe out input

theorem compiler_bridge : CompilerBridge producer :=
  compilerBridge_of_safe fun _ _ _ r _ _ _ _ _ _ input => compilation_safe r input

end Solidity.Hash.CompilerCorrect

namespace Solidity.Hash

theorem compiler_correct_collisionFree : Solidity.Goals.compilerCorrectCollisionFree :=
  ⟨Backend.compiler_endpoint_correct, CompilerCorrect.producer,
    CompilerCorrect.producer_produces, CompilerCorrect.producer_idealAdequacy,
    CompilerCorrect.compiler_bridge,
    CompilerCorrect.adaptive_of_compilerBridge _ CompilerCorrect.compiler_bridge⟩
end Solidity.Hash

/-- info: 'Solidity.Hash.compiler_correct_collisionFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.compiler_correct_collisionFree
