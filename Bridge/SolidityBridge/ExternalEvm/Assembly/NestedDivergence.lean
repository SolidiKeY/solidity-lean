import SolidityBridge.ExternalEvm.Assembly.Structured

namespace Solidity.Evm.External.Assembly

/-- Arbitrarily long prefixes in the actual upstream fetched-step relation.
This is not a finite-resource X divergence or fault-equivalence assertion. -/
def UnboundedPrefixes (s : EvmYul.EVM.State) : Prop :=
  ∀ n, ∃ k t, n ≤ k ∧ fetchedSteps k s = .ok t

theorem UnboundedPrefixes.prepend {s t : EvmYul.EVM.State} {count : Nat}
    (prefixRun : fetchedSteps count s = .ok t) (infinite : UnboundedPrefixes t) : UnboundedPrefixes s := by
  intro n
  obtain ⟨k, out, hk, ht⟩ := infinite n
  refine ⟨count + k, out, by omega, ?_⟩
  rw [fetchedSteps_add, prefixRun]
  exact ht

/-- Execute an arbitrary source segment within its ambient typed image,
retaining pending skips and the following code. -/
theorem segment_simulation {code : List Instr} {base : Nat}
    (image : Image code base) (frame : EvmYul.EVM.State)
    (macros : MacroRefinement image frame) (pre segment post : List Instr)
    (shape : code = pre ++ segment ++ post) (skip finalSkip : Nat)
    (m m' : Machine) (s : EvmYul.EVM.State)
    (entry : Boundary image frame (pre.length + skip) m s)
    (source : exec segment skip m = .ok m' finalSkip) :
    ∃ n t, fetchedSteps n s = .ok t ∧
      Boundary image frame (pre.length + segment.length + finalSkip) m' t := by
  induction segment generalizing pre skip m s with
  | nil =>
    simp only [exec_nil, Out.ok.injEq] at source
    obtain ⟨rfl, rfl⟩ := source
    exact ⟨0, s, rfl, by simpa only [List.length_nil, Nat.add_zero] using entry⟩
  | cons i rest ih =>
    have shape' : code = (pre ++ [i]) ++ rest ++ post := by
      simpa only [List.append_assoc, List.singleton_append] using shape
    cases skip with
    | succ skip =>
      have ent : Boundary image frame ((pre ++ [i]).length + skip) m s := by
        simpa only [List.length_append, List.length_singleton, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using entry
      obtain ⟨n, t, trace, boundary⟩ := ih (pre ++ [i]) shape' skip m s ent source
      refine ⟨n, t, trace, ?_⟩
      simpa only [List.length_append, List.length_singleton, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using boundary
    | zero =>
      simp only [exec_cons_zero] at source
      cases hs : i.step m with
      | fault => simp only [hs, Out.fault_bind] at source; cases source
      | revert => simp only [hs, Out.revert_bind] at source; cases source
      | ok next k =>
        obtain ⟨n, t, trace, boundary⟩ := macros pre i (rest ++ post)
          (by simpa only [List.append_assoc, List.cons_append] using shape)
          m next k s hs (by simpa only [Nat.add_zero] using entry)
        have ent : Boundary image frame ((pre ++ [i]).length + k) next t := by
          simpa only [List.length_append, List.length_singleton, Nat.add_assoc] using boundary
        obtain ⟨n', out, restRun, related⟩ := ih (pre ++ [i]) shape' k next t ent
          (by simpa only [hs, Out.ok_bind] using source)
        refine ⟨n + n', out, ?_, ?_⟩
        · rw [fetchedSteps_add, trace]
          exact restRun
        · simpa only [List.length_append, List.length_singleton, List.length_cons,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using related

/-- Divergence may occur after a successful source prefix, including branches
inside that prefix. No successful execution of the divergent suffix is assumed. -/
theorem sequence_divergence {code : List Instr} {base : Nat}
    (image : Image code base) (frame : EvmYul.EVM.State)
    (macros : MacroRefinement image frame) (pre post : List Instr) (shape : code = pre ++ post)
    (m mid : Machine) (s : EvmYul.EVM.State) (skip : Nat)
    (entry : Boundary image frame 0 m s) (source : run pre m = .ok mid skip)
    (divergent : ∀ t, Boundary image frame (pre.length + skip) mid t → UnboundedPrefixes t) :
    UnboundedPrefixes s := by
  obtain ⟨n, t, trace, boundary⟩ := segment_simulation image frame macros [] pre post
    (by simpa only [List.nil_append] using shape) 0 skip m mid s entry source
  exact (divergent t (by simpa only [List.length_nil, Nat.zero_add] using boundary)).prepend trace

/-- An infinite nested condition is entered after the outer header JD. -/
theorem loop_condition_divergence {whole c b : List Instr} {base cb bb origin : Nat}
    (image : Image whole base) (ci : Image c cb) (bi : Image b bb)
    (frame : EvmYul.EVM.State) (header exit : Fin W)
    (layout : LoopLayout (origin := origin) image ci bi frame header exit)
    (m : Machine) (s : EvmYul.EVM.State) (entry : Boundary image frame origin m s)
    (divergent : ∀ t, Boundary ci frame 0 m t → UnboundedPrefixes t) : UnboundedPrefixes s := by
  obtain ⟨hd, ha⟩ := layout.enter m s entry
  have ent : Boundary ci frame 0 m (destState s) :=
    ⟨Nat.zero_lt_succ _, ha, entry.stack, entry.state, entry.memory⟩
  apply (divergent _ ent).prepend (count := 1)
  simp only [fetchedSteps, fetched_dest s hd, bind, Except.bind]

/-- A divergent nested body is entered after a successful condition and its
nonzero guard. It need not finish even one outer loop turn. -/
theorem loop_body_divergence {whole c b : List Instr} {base cb bb origin : Nat}
    (image : Image whole base) (ci : Image c cb) (bi : Image b bb)
    (frame : EvmYul.EVM.State) (header exit : Fin W)
    (layout : LoopLayout (origin := origin) image ci bi frame header exit)
    (cond : MacroRefinement ci frame) (m mc : Machine) (w : Fin W) (tail : List Word)
    (source : run c m = .ok mc 0) (stack : mc.stack = .val w :: tail) (nonzero : w.val ≠ 0)
    (s : EvmYul.EVM.State) (entry : Boundary image frame origin m s)
    (divergent : ∀ t, Boundary bi frame 0 {mc with stack := tail} t → UnboundedPrefixes t) :
    UnboundedPrefixes s := by
  obtain ⟨hd, ha⟩ := layout.enter m s entry
  have ent : Boundary ci frame 0 m (destState s) :=
    ⟨Nat.zero_lt_succ _, ha, entry.stack, entry.state, entry.memory⟩
  obtain ⟨n, t, trace, boundary⟩ := run_simulation ci frame cond m mc (destState s) ent source
  obtain ⟨rest, hrest, hwords⟩ := words_cons_inverse t.stack w tail (boundary.stack.symm.trans stack)
  obtain ⟨hh, hi, hp, hj⟩ := layout.guard mc t w tail rest boundary stack hrest
  have guard := guard_trace t (.ofNat w.val) rest exit hrest hh hi hp hj
  have entered : Boundary bi frame 0 {mc with stack := tail} (guardState t (.ofNat w.val) rest exit) :=
    ⟨Nat.zero_lt_succ _, layout.nonzeroAddress mc t w tail rest boundary stack hrest nonzero,
      hwords.symm, boundary.state, boundary.memory⟩
  have nested := (divergent _ entered).prepend guard
  have afterCond := nested.prepend trace
  apply afterCond.prepend (count := 1)
  simp only [fetchedSteps, fetched_dest s hd, bind, Except.bind]

private theorem loopIterN_add (rc rb : Machine → Out) (n k : Nat) (m : Machine) :
    loopIterN rc rb (n + k) m = match loopIterN rc rb n m with
      | .inl mid => loopIterN rc rb k mid
      | .inr result => .inr result := by
  induction n generalizing m with
  | zero => simp only [Nat.zero_add, loopIterN]
  | succ n ih =>
    simp only [Nat.succ_add, loopIterN]
    cases loopTurn rc rb m with
    | inl mid => exact ih mid
    | inr result => rfl

private theorem loopRun_fault_after (rc rb : Machine → Out) (n : Nat) (m mid : Machine)
    (prefixRun : loopIterN rc rb n m = .inl mid) (later : loopRun rc rb mid = .fault) :
    loopRun rc rb m = .fault := by
  classical
  by_cases ended : ∃ result k, loopIterN rc rb k m = .inr result
  · obtain ⟨result, k, hk⟩ := ended
    have shifted := loopIterN_done_le (Nat.le_add_left k n) hk
    rw [loopIterN_add, prefixRun] at shifted
    have resultFault : result = .fault := (loopRun_of_iterN shifted).symm.trans later
    exact (loopRun_of_iterN hk).trans resultFault
  · apply loopRun_of_forall
    intro k
    cases hk : loopIterN rc rb k m with
    | inl mid => exact ⟨mid, rfl⟩
    | inr result => exact False.elim (ended ⟨result, k, hk⟩)

/-! Semantic divergence witnesses over the existing typed instructions.
They distinguish actual infinite loop paths from other source faults. This
is a proof relation, not an alternative source syntax or evaluator. -/
mutual
  inductive BlockDiverges : List Instr → Machine → Prop where
    | afterPrefix (pre c b post : List Instr) {m mid : Machine}
        (prefixRun : run pre m = .ok mid 0) (nested : LoopDiverges c b mid) :
        BlockDiverges (pre ++ .loop c b :: post) m
  inductive LoopDiverges : List Instr → List Instr → Machine → Prop where
    | forever {c b : List Instr} {m : Machine}
        (turns : ∀ n, ∃ next, loopIterN (run c) (run b) n m = .inl next) : LoopDiverges c b m
    | afterTurns {c b : List Instr} {m mid : Machine} (n : Nat)
        (prefixRun : loopIterN (run c) (run b) n m = .inl mid)
        (later : LoopDiverges c b mid) : LoopDiverges c b m
    | condition {c b : List Instr} {m : Machine} (nested : BlockDiverges c m) : LoopDiverges c b m
    | body {c b : List Instr} {m mc : Machine} (w : Fin W) (tail : List Word)
        (conditionRun : run c m = .ok mc 0) (stack : mc.stack = .val w :: tail)
        (nonzero : w.val ≠ 0) (nested : BlockDiverges b {mc with stack := tail}) : LoopDiverges c b m
end

/-- Nested divergence retains the core's existing fault classification. -/
theorem BlockDiverges.source_fault {code : List Instr} {m : Machine} (h : BlockDiverges code m) :
    run code m = .fault := by
  induction h using BlockDiverges.rec
    (motive_2 := fun c b m _ => (Instr.loop c b).step m = .fault) with
  | afterPrefix pre c b post prefixRun _ ih =>
    rw [run_append_ok prefixRun]
    change ((Instr.loop c b).step _).bind _ = _
    rw [ih]
    rfl
  | forever turns => exact loopRun_of_forall turns
  | afterTurns n prefixRun _ ih => exact loopRun_fault_after _ _ n _ _ prefixRun ih
  | condition _ ih =>
    apply loopRun_of_iterN (n := 1)
    change (match loopTurn (run _) (run _) _ with
      | .inl next => (Sum.inl next : Machine ⊕ Out)
      | .inr result => Sum.inr result) = _
    simp only [loopTurn, ih]
  | body w tail conditionRun stack nonzero _ ih =>
    apply loopRun_of_iterN (n := 1)
    change (match loopTurn (run _) (run _) _ with
      | .inl next => (Sum.inl next : Machine ⊕ Out)
      | .inr result => Sum.inr result) = _
    simp only [loopTurn, conditionRun, stack, if_neg nonzero, ih]

/-- General sequence/condition/body divergence compilation from recursive
certificates, including inner loops that never finish an outer turn. -/
theorem BlockDiverges.compiled {code : List Instr} {m : Machine} (h : BlockDiverges code m) :
    ∀ {base} (image : Image code base) (frame : EvmYul.EVM.State),
      DecodedCode frame image → ∀ s, Boundary image frame 0 m s → UnboundedPrefixes s := by
  induction h using BlockDiverges.rec
    (motive_2 := fun c b m _ => ∀ {whole base origin} (image : Image whole base)
      (frame : EvmYul.EVM.State), DecodedSite frame image origin (.loop c b) →
      ∀ s, Boundary image frame origin m s → UnboundedPrefixes s) with
  | afterPrefix pre c b post prefixRun _ ih =>
    intro base image frame certificate s entry
    have site : DecodedSite frame image pre.length (.loop c b) := by
      cases certificate with
      | intro _ sites => exact sites pre (.loop c b) post rfl
    apply sequence_divergence image frame certificate.refinement pre (.loop c b :: post) rfl
      _ _ s 0 entry prefixRun
    intro t related
    exact ih image frame site t (by simpa only [Nat.add_zero] using related)
  | forever turns =>
    rename_i whole base origin image frame certificate s entry
    cases certificate with
    | primitive image i facts => exact False.elim (facts _ _ entry).2
    | loop image ci bi header exit layout cond body =>
      obtain ⟨_, prefixes⟩ := decoded_loop_divergence_prefixes image ci bi frame header exit
        layout cond.refinement body.refinement _ s entry turns
      intro n
      obtain ⟨k, t, _, bound, trace, _⟩ := prefixes n
      exact ⟨k, t, bound, trace⟩
  | afterTurns n prefixRun _ ih =>
    rename_i whole base origin image frame certificate s entry
    cases certificate with
    | primitive image i facts => exact False.elim (facts _ _ entry).2
    | loop image ci bi header exit layout cond body =>
      obtain ⟨k, t, _, trace, boundary⟩ := decoded_loop_prefixes image ci bi frame header exit
        layout cond.refinement body.refinement n _ _ s entry prefixRun
      exact (ih image frame (.loop image ci bi header exit layout cond body) t boundary).prepend trace
  | condition _ ih =>
    rename_i whole base origin image frame certificate s entry
    cases certificate with
    | primitive image i facts => exact False.elim (facts _ _ entry).2
    | loop image ci bi header exit layout cond body =>
      apply loop_condition_divergence image ci bi frame header exit layout _ s entry
      intro t related
      exact ih ci frame cond t related
  | body w tail conditionRun stack nonzero _ ih =>
    rename_i whole base origin image frame certificate s entry
    cases certificate with
    | primitive image i facts => exact False.elim (facts _ _ entry).2
    | loop image ci bi header exit layout cond body =>
      apply loop_body_divergence image ci bi frame header exit layout cond.refinement
        _ _ w tail conditionRun stack nonzero s entry
      intro t related
      exact ih bi frame body t related


end Solidity.Evm.External.Assembly
