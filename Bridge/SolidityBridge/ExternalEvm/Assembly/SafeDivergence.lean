import SolidityBridge.ExternalEvm.Assembly.NestedDivergence
import SolidityBridge.ExternalEvm.Assembly.SafeStructured

namespace Solidity.Evm.External.Assembly

def SafeUnboundedPrefixes (destinations : List EvmYul.UInt256) (s : EvmYul.EVM.State) : Prop :=
  ∀ n, ∃ k t, n ≤ k ∧ SafeTrace destinations k s t

theorem SafeUnboundedPrefixes.prepend {destinations : List EvmYul.UInt256} {s t : EvmYul.EVM.State} {count : Nat}
    (prefixRun : SafeTrace destinations count s t) (infinite : SafeUnboundedPrefixes destinations t) : SafeUnboundedPrefixes destinations s := by
  intro n
  obtain ⟨k, out, hk, ht⟩ := infinite n
  refine ⟨count + k, out, by omega, ?_⟩
  exact prefixRun.trans ht

/-- Execute an arbitrary source segment within its ambient typed image,
retaining pending skips and the following code. -/
theorem safe_segment_simulation {destinations : List EvmYul.UInt256} {code : List Instr} {base : Nat}
    (image : Image code base) (frame : EvmYul.EVM.State)
    (macros : SafeMacroRefinement destinations image frame) (pre segment post : List Instr)
    (shape : code = pre ++ segment ++ post) (skip finalSkip : Nat)
    (m m' : Machine) (s : EvmYul.EVM.State)
    (entry : Boundary image frame (pre.length + skip) m s)
    (source : exec segment skip m = .ok m' finalSkip) :
    ∃ n t, SafeTrace destinations n s t ∧
      Boundary image frame (pre.length + segment.length + finalSkip) m' t := by
  induction segment generalizing pre skip m s with
  | nil =>
    simp only [exec_nil, Out.ok.injEq] at source
    obtain ⟨rfl, rfl⟩ := source
    exact ⟨0, s, .nil _, by simpa only [List.length_nil, Nat.add_zero] using entry⟩
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
        · exact trace.trans restRun
        · simpa only [List.length_append, List.length_singleton, List.length_cons,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using related

/-- Divergence may occur after a successful source prefix, including branches
inside that prefix. No successful execution of the divergent suffix is assumed. -/
theorem safe_sequence_divergence {destinations : List EvmYul.UInt256} {code : List Instr} {base : Nat}
    (image : Image code base) (frame : EvmYul.EVM.State)
    (macros : SafeMacroRefinement destinations image frame) (pre post : List Instr) (shape : code = pre ++ post)
    (m mid : Machine) (s : EvmYul.EVM.State) (skip : Nat)
    (entry : Boundary image frame 0 m s) (source : run pre m = .ok mid skip)
    (divergent : ∀ t, Boundary image frame (pre.length + skip) mid t → SafeUnboundedPrefixes destinations t) :
    SafeUnboundedPrefixes destinations s := by
  obtain ⟨n, t, trace, boundary⟩ := safe_segment_simulation image frame macros [] pre post
    (by simpa only [List.nil_append] using shape) 0 skip m mid s entry source
  exact (divergent t (by simpa only [List.length_nil, Nat.zero_add] using boundary)).prepend trace

/-- An infinite nested condition is entered after the outer header JD. -/
theorem safe_loop_condition_divergence {destinations : List EvmYul.UInt256} {whole c b : List Instr} {base cb bb origin : Nat}
    (image : Image whole base) (ci : Image c cb) (bi : Image b bb)
    (frame : EvmYul.EVM.State) (header exit : Fin W)
    (layout : LoopLayout (origin := origin) image ci bi frame header exit)
    (m : Machine) (s : EvmYul.EVM.State) (entry : Boundary image frame origin m s)
    (divergent : ∀ t, Boundary ci frame 0 m t → SafeUnboundedPrefixes destinations t) : SafeUnboundedPrefixes destinations s := by
  obtain ⟨hd, ha⟩ := layout.enter m s entry
  have ent : Boundary ci frame 0 m (destState s) :=
    ⟨Nat.zero_lt_succ _, ha, entry.stack, entry.state, entry.memory⟩
  exact (divergent _ ent).prepend (SafeTrace.dest s hd)

/-- A divergent nested body is entered after a successful condition and its
nonzero guard. It need not finish even one outer loop turn. -/
theorem safe_loop_body_divergence {destinations : List EvmYul.UInt256} {whole c b : List Instr} {base cb bb origin : Nat}
    (image : Image whole base) (ci : Image c cb) (bi : Image b bb)
    (frame : EvmYul.EVM.State) (header exit : Fin W)
    (layout : LoopLayout (origin := origin) image ci bi frame header exit)
    (exitMember : EvmYul.UInt256.ofNat exit.val ∈ destinations)
    (cond : SafeMacroRefinement destinations ci frame) (m mc : Machine) (w : Fin W) (tail : List Word)
    (source : run c m = .ok mc 0) (stack : mc.stack = .val w :: tail) (nonzero : w.val ≠ 0)
    (s : EvmYul.EVM.State) (entry : Boundary image frame origin m s)
    (divergent : ∀ t, Boundary bi frame 0 {mc with stack := tail} t → SafeUnboundedPrefixes destinations t) :
    SafeUnboundedPrefixes destinations s := by
  obtain ⟨hd, ha⟩ := layout.enter m s entry
  have ent : Boundary ci frame 0 m (destState s) :=
    ⟨Nat.zero_lt_succ _, ha, entry.stack, entry.state, entry.memory⟩
  obtain ⟨n, t, trace, boundary⟩ := safe_run_simulation ci frame cond m mc (destState s) ent source
  obtain ⟨rest, hrest, hwords⟩ := words_cons_inverse t.stack w tail (boundary.stack.symm.trans stack)
  obtain ⟨hh, hi, hp, hj⟩ := layout.guard mc t w tail rest boundary stack hrest
  have guard := safe_guard_trace t (.ofNat w.val) rest exit hrest exitMember hh hi hp hj
  have entered : Boundary bi frame 0 {mc with stack := tail} (guardState t (.ofNat w.val) rest exit) :=
    ⟨Nat.zero_lt_succ _, layout.nonzeroAddress mc t w tail rest boundary stack hrest nonzero,
      hwords.symm, boundary.state, boundary.memory⟩
  have nested := (divergent _ entered).prepend guard
  have afterCond := nested.prepend trace
  exact afterCond.prepend (SafeTrace.dest s hd)


/-- Every semantic nested-divergence witness compiles into arbitrarily long
actual fetched traces whose branch checks are scanner justified. -/
theorem BlockDiverges.safe_compiled {code : List Instr} {m : Machine} (h : BlockDiverges code m) :
    ∀ {base} (image : Image code base) (frame : EvmYul.EVM.State) (destinations : List EvmYul.UInt256),
      ScannedCode frame destinations image → ∀ s, Boundary image frame 0 m s → SafeUnboundedPrefixes destinations s := by
  induction h using BlockDiverges.rec
    (motive_2 := fun c b m _ => ∀ {whole base origin} (image : Image whole base)
      (frame : EvmYul.EVM.State) (destinations : List EvmYul.UInt256),
      ScannedSite frame destinations image origin (.loop c b) →
      ∀ s, Boundary image frame origin m s → SafeUnboundedPrefixes destinations s) with
  | afterPrefix pre c b post prefixRun _ ih =>
    intro base image frame destinations certificate s entry
    have site : ScannedSite frame destinations image pre.length (.loop c b) := by
      cases certificate with
      | intro _ labels sites => exact sites pre (.loop c b) post rfl
    apply safe_sequence_divergence image frame certificate.safe_refinement pre (.loop c b :: post) rfl
      _ _ s 0 entry prefixRun
    intro t related
    exact ih image frame destinations site t (by simpa only [Nat.add_zero] using related)
  | forever turns =>
    rename_i whole base origin image frame destinations certificate s entry
    cases certificate with
    | atom image site safe => cases site
    | loop image ci bi site header exit cond body =>
      let turn := safe_decoded_loop_turn image ci bi frame site.here
        ⟨site.here.val + ci.size + bi.size + 72, site.fits⟩ site.layout header exit
        cond.safe_refinement body.safe_refinement
      intro n
      obtain ⟨mid, hm⟩ := turns n
      obtain ⟨k, t, bound, trace, related⟩ := safe_loop_prefix_simulation turn n _ mid s entry hm
      exact ⟨k, t, bound, trace⟩
  | afterTurns n prefixRun _ ih =>
    rename_i whole base origin image frame destinations certificate s entry
    cases certificate with
    | atom image site safe => cases site
    | loop image ci bi site header exit cond body =>
      let turn := safe_decoded_loop_turn image ci bi frame site.here
        ⟨site.here.val + ci.size + bi.size + 72, site.fits⟩ site.layout header exit
        cond.safe_refinement body.safe_refinement
      obtain ⟨k, t, _, trace, related⟩ := safe_loop_prefix_simulation turn n _ _ s entry prefixRun
      exact (ih image frame destinations (.loop image ci bi site header exit cond body) t related).prepend trace
  | condition _ ih =>
    rename_i whole base origin image frame destinations certificate s entry
    cases certificate with
    | atom image site safe => cases site
    | loop image ci bi site header exit cond body =>
      apply safe_loop_condition_divergence image ci bi frame site.here
        ⟨site.here.val + ci.size + bi.size + 72, site.fits⟩ site.layout _ s entry
      intro t related
      exact ih ci frame destinations cond t related
  | body w tail conditionRun stack nonzero _ ih =>
    rename_i whole base origin image frame destinations certificate s entry
    cases certificate with
    | atom image site safe => cases site
    | loop image ci bi site header exit cond body =>
      apply safe_loop_body_divergence image ci bi frame site.here
        ⟨site.here.val + ci.size + bi.size + 72, site.fits⟩ site.layout exit cond.safe_refinement
        _ _ w tail conditionRun stack nonzero s entry
      intro t related
      exact ih bi frame destinations body t related

theorem SafeUnboundedPrefixes.forget {destinations : List EvmYul.UInt256} {s : EvmYul.EVM.State}
    (safe : SafeUnboundedPrefixes destinations s) : UnboundedPrefixes s := by
  intro n
  obtain ⟨k, t, bound, trace⟩ := safe n
  exact ⟨k, t, bound, trace.forget⟩

end Solidity.Evm.External.Assembly

/-- info: 'Solidity.Evm.External.Assembly.BlockDiverges.safe_compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.BlockDiverges.safe_compiled
