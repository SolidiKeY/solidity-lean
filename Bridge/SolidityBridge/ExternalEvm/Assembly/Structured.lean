import SolidityBridge.ExternalEvm.Assembly.Composition

/-! General loop macro refinement. The explicit layout assumptions below are
only packet decodings and absolute address equations. Condition/body execution
is obtained from their own macro refinements; no loop target trace is assumed.
The boundary relation intentionally keeps the finite positive-fuel fetched-step
semantics separate from gas/halting/validJumps checks in the X driver. -/
namespace Solidity.Evm.External.Assembly

/-- Relocated nested slices and the emitted loop's four-instruction guard
and three-instruction backedge. Every decoding is against actual ambient code. -/
structure LoopLayout {whole c b : List Instr} {base cb bb origin : Nat}
    (image : Image whole base) (ci : Image c cb) (bi : Image b bb)
    (frame : EvmYul.EVM.State) (entryWord exitWord : Fin W) : Prop where
  shape : whole[origin]? = some (.loop c b)
  headerBound : origin < whole.length + 1
  exitBound : origin + 1 < whole.length + 1
  headerAddress : address whole base ⟨origin, headerBound⟩ = some entryWord.val
  enter : ∀ m s, Boundary image frame origin m s →
    Fetches s (.JUMPDEST, none) ∧
    address c cb ⟨0, Nat.zero_lt_succ _⟩ = some (destState s).pc.toNat
  guard : ∀ mc s w tail rest, Boundary ci frame c.length mc s →
    mc.stack = .val w :: tail → s.stack = .ofNat w.val :: rest →
    Fetches s (.JUMPDEST, none) ∧
    Fetches (destState s) (.ISZERO, none) ∧
    Fetches (iszeroState s (.ofNat w.val) rest)
      (.Push .PUSH32, some (.ofNat exitWord.val, 32)) ∧
    Fetches (pushState (iszeroState s (.ofNat w.val) rest) (.ofNat exitWord.val))
      (.JUMPI, none)
  zeroAddress : ∀ mc s w tail rest, Boundary ci frame c.length mc s →
    mc.stack = .val w :: tail → s.stack = .ofNat w.val :: rest → w.val = 0 →
    address whole base ⟨origin + 1, exitBound⟩ =
      some (guardState s (.ofNat w.val) rest exitWord).pc.toNat
  nonzeroAddress : ∀ mc s w tail rest, Boundary ci frame c.length mc s →
    mc.stack = .val w :: tail → s.stack = .ofNat w.val :: rest → w.val ≠ 0 →
    address b bb ⟨0, Nat.zero_lt_succ _⟩ =
      some (guardState s (.ofNat w.val) rest exitWord).pc.toNat
  back : ∀ m s, Boundary bi frame b.length m s →
    Fetches s (.JUMPDEST, none) ∧
    Fetches (destState s) (.Push .PUSH32, some (.ofNat entryWord.val, 32)) ∧
    Fetches (pushState (destState s) (.ofNat entryWord.val)) (.JUMP, none)

/-- General emitted structured-loop turn, composed from recursively verified
condition/body blocks and explicit layout/decoder facts. -/
theorem decoded_loop_turn {whole c b : List Instr} {base cb bb origin : Nat}
    (image : Image whole base) (ci : Image c cb) (bi : Image b bb)
    (frame : EvmYul.EVM.State) (entryWord exitWord : Fin W)
    (layout : LoopLayout (origin := origin) image ci bi frame entryWord exitWord)
    (cond : MacroRefinement ci frame) (body : MacroRefinement bi frame) :
    TurnRefinement (run c) (run b) (Boundary image frame origin)
      (Boundary image frame (origin + 1)) := by
  apply turn_of_parts (condition := Boundary ci frame c.length)
    (bodyEntry := Boundary bi frame 0) (bodyExit := Boundary bi frame b.length)
  · intro m s he mc hc
    obtain ⟨hd, ha⟩ := layout.enter m s he
    have entry : Boundary ci frame 0 m (destState s) :=
      ⟨Nat.zero_lt_succ _, ha, he.stack, he.state, he.memory⟩
    obtain ⟨n, t, ht, hb⟩ := run_simulation ci frame cond m mc (destState s) entry hc
    refine ⟨1 + n, t, ?_, hb⟩
    rw [fetchedSteps_add]
    have h : fetchedSteps 1 s = .ok (destState s) := by
      simp only [fetchedSteps, fetched_dest s hd, bind, Except.bind]
    rw [h]
    exact ht
  · intro mc s w tail he hs hz
    obtain ⟨rest, hrest, hwords⟩ := words_cons_inverse s.stack w tail (he.stack.symm.trans hs)
    obtain ⟨hd, hi, hp, hj⟩ := layout.guard mc s w tail rest he hs hrest
    refine ⟨4, guardState s (.ofNat w.val) rest exitWord, by decide,
      guard_trace s _ rest exitWord hrest hd hi hp hj, ?_⟩
    exact ⟨layout.exitBound, layout.zeroAddress mc s w tail rest he hs hrest hz,
      hwords.symm, he.state, he.memory⟩
  · intro mc s w tail he hs hn
    obtain ⟨rest, hrest, hwords⟩ := words_cons_inverse s.stack w tail (he.stack.symm.trans hs)
    obtain ⟨hd, hi, hp, hj⟩ := layout.guard mc s w tail rest he hs hrest
    refine ⟨4, guardState s (.ofNat w.val) rest exitWord, by decide,
      guard_trace s _ rest exitWord hrest hd hi hp hj, ?_⟩
    exact ⟨Nat.zero_lt_succ _, layout.nonzeroAddress mc s w tail rest he hs hrest hn,
      hwords.symm, he.state, he.memory⟩
  · intro m s he next hb
    exact run_simulation bi frame body m next s he hb
  · intro m s he
    obtain ⟨hd, hp, hj⟩ := layout.back m s he
    obtain ⟨n, hn⟩ := (FetchedTrace.cons (fetched_dest s hd)
      (fetched_jump_trace 0 (.ofNat entryWord.val) (destState s) hp hj)).count
    refine ⟨n, _, hn, ⟨layout.headerBound, ?_, he.stack, he.state, he.memory⟩⟩
    rw [jump_pc]
    exact layout.headerAddress

/-- A successful existing core structured loop has a fetched execution to
its outer continuation, for arbitrary verified condition and body blocks. -/
theorem decoded_loop_simulation {whole c b : List Instr} {base cb bb origin : Nat}
    (image : Image whole base) (ci : Image c cb) (bi : Image b bb)
    (frame : EvmYul.EVM.State) (entryWord exitWord : Fin W)
    (layout : LoopLayout (origin := origin) image ci bi frame entryWord exitWord)
    (cond : MacroRefinement ci frame) (body : MacroRefinement bi frame)
    (m m' : Machine) (s : EvmYul.EVM.State) (entry : Boundary image frame origin m s)
    (source : (Instr.loop c b).step m = .ok m' 0) :
    ∃ n t, 0 < n ∧ fetchedSteps n s = .ok t ∧ Boundary image frame (origin + 1) m' t :=
  structured_loop_simulation (decoded_loop_turn image ci bi frame entryWord exitWord layout cond body)
    m m' s entry source

/-- General still-running loop prefixes, with target progress, under the
same local decoder/layout assumptions. No driver-divergence claim is made. -/
theorem decoded_loop_prefixes {whole c b : List Instr} {base cb bb origin : Nat}
    (image : Image whole base) (ci : Image c cb) (bi : Image b bb)
    (frame : EvmYul.EVM.State) (entryWord exitWord : Fin W)
    (layout : LoopLayout (origin := origin) image ci bi frame entryWord exitWord)
    (cond : MacroRefinement ci frame) (body : MacroRefinement bi frame)
    (n : Nat) (m m' : Machine) (s : EvmYul.EVM.State)
    (entry : Boundary image frame origin m s)
    (source : loopIterN (run c) (run b) n m = .inl m') :
    ∃ k t, n ≤ k ∧ fetchedSteps k s = .ok t ∧ Boundary image frame origin m' t :=
  loop_prefix_simulation (decoded_loop_turn image ci bi frame entryWord exitWord layout cond body)
    n m m' s entry source

/-- Successful core loop turns never export a pending relative jump. -/
theorem loopTurn_success_skip {rc rb : Machine → Out} {m next : Machine} {k : Nat}
    (h : loopTurn rc rb m = .inr (.ok next k)) : k = 0 := by
  unfold loopTurn at h
  cases hc : rc m with
  | fault => simp only [hc] at h; cases h
  | revert => simp only [hc] at h; cases h
  | ok mc skip =>
    cases skip with
    | succ j => simp only [hc] at h; cases h
    | zero =>
      simp only [hc] at h
      cases hs : mc.stack with
      | nil => simp only [hs] at h; cases h
      | cons word tail =>
        cases word <;> try (simp only [hs] at h; cases h)
        case val w =>
          simp only [hs] at h
          split at h
          · exact ((Out.ok.inj (Sum.inr.inj h)).2).symm
          · cases hb : rb {mc with stack := tail} with
            | fault => simp only [hb] at h; cases h
            | revert => simp only [hb] at h; cases h
            | ok next' skip =>
              cases skip <;> simp only [hb] at h <;> cases h

theorem loopRun_success_skip {rc rb : Machine → Out} {m next : Machine} {k : Nat}
    (h : loopRun rc rb m = .ok next k) : k = 0 := by
  have witness : ∃ n, loopIterN rc rb n m = .inr (.ok next k) := by
    unfold loopRun at h
    split at h
    · rename_i hex
      obtain ⟨n, hn⟩ := Classical.choose_spec hex
      exact ⟨n, h ▸ hn⟩
    · cases h
  obtain ⟨n, hn⟩ := witness
  clear h
  induction n generalizing m with
  | zero => cases hn
  | succ n ih =>
    cases ht : loopTurn rc rb m with
    | inl m' => exact ih (by simpa only [loopIterN, ht] using hn)
    | inr out =>
      have he : out = .ok next k := by simpa only [loopIterN, ht, Sum.inr.injEq] using hn
      exact loopTurn_success_skip (he ▸ ht)

/-- Discharge the local loop instruction obligation, including the fact that
its successful source outcome has no pending skip. -/
theorem decoded_loop_macro {whole c b : List Instr} {base cb bb origin : Nat}
    (image : Image whole base) (ci : Image c cb) (bi : Image b bb)
    (frame : EvmYul.EVM.State) (entryWord exitWord : Fin W)
    (layout : LoopLayout (origin := origin) image ci bi frame entryWord exitWord)
    (cond : MacroRefinement ci frame) (body : MacroRefinement bi frame)
    (m m' : Machine) (skip : Nat) (s : EvmYul.EVM.State)
    (entry : Boundary image frame origin m s)
    (source : (Instr.loop c b).step m = .ok m' skip) :
    ∃ n t, fetchedSteps n s = .ok t ∧ Boundary image frame (origin + 1 + skip) m' t := by
  have hk : skip = 0 := loopRun_success_skip source
  subst skip
  obtain ⟨n, t, _, ht, he⟩ := decoded_loop_simulation image ci bi frame entryWord exitWord
    layout cond body m m' s entry source
  exact ⟨n, t, ht, he⟩

/-! Proof certificates follow the existing instruction syntax. They are
not an executable intermediate language: each leaf contains actual decoding
and address facts, and each loop contains recursively certified emitted slices. -/
mutual
  inductive DecodedCode (frame : EvmYul.EVM.State) :
      {code : List Instr} → {base : Nat} → Image code base → Prop where
    | intro {code base} (image : Image code base)
        (sites : ∀ pre i rest, code = pre ++ i :: rest →
          DecodedSite frame image pre.length i) : DecodedCode frame image
  inductive DecodedSite (frame : EvmYul.EVM.State) :
      {whole : List Instr} → {base : Nat} → Image whole base → Nat → Instr → Prop where
    | primitive {whole base origin} (image : Image whole base) (i : Instr)
        (facts : ∀ m s, Boundary image frame origin m s → PrimitiveLayout image origin i s) :
        DecodedSite frame image origin i
    | loop {whole c b base cb bb origin} (image : Image whole base)
        (ci : Image c cb) (bi : Image b bb) (entryWord exitWord : Fin W)
        (layout : LoopLayout (origin := origin) image ci bi frame entryWord exitWord)
        (cond : DecodedCode frame ci) (body : DecodedCode frame bi) :
        DecodedSite frame image origin (.loop c b)
end

/-- Recursive decoding/layout certificates imply local macro refinement,
including arbitrary nesting of structured loops. -/
theorem DecodedCode.refinement {frame : EvmYul.EVM.State} {code : List Instr} {base : Nat}
    {image : Image code base} (h : DecodedCode frame image) : MacroRefinement image frame := by
  induction h using DecodedCode.rec
    (motive_2 := fun {_ _} image origin i _ =>
      ∀ m m' skip s, i.step m = .ok m' skip → Boundary image frame origin m s →
        ∃ n t, fetchedSteps n s = .ok t ∧ Boundary image frame (origin + 1 + skip) m' t) with
  | intro image sites ih =>
    intro pre i rest hc m m' skip s hs he
    exact ih pre i rest hc m m' skip s hs he
  | primitive image i facts =>
    rename_i m m' skip s hs he
    exact primitive_refinement image frame i m m' skip s (facts m s he) he hs
  | loop image ci bi entryWord exitWord layout _ _ cond body =>
    rename_i m m' skip s hs he
    exact decoded_loop_macro image ci bi frame entryWord exitWord layout cond body m m' skip s he hs

/-- General control-flow assembly correctness under explicit recursively
inhabited decoder/layout certificates. This is an actual upstream fetched-run
simulation, not sampled agreement and not an X-driver halting assertion. -/
theorem certified_run_simulation {code : List Instr} {base : Nat}
    (image : Image code base) (frame : EvmYul.EVM.State)
    (certificate : DecodedCode frame image)
    (m m' : Machine) (s : EvmYul.EVM.State)
    (entry : Boundary image frame 0 m s) (source : run code m = .ok m' 0) :
    ∃ n t, fetchedSteps n s = .ok t ∧ Boundary image frame code.length m' t :=
  run_simulation image frame certificate.refinement m m' s entry source

/-- General divergence consequence justified by the upstream fetched-step
relation: unbounded positive-length prefixes, not finite-fuel driver divergence. -/
theorem decoded_loop_divergence_prefixes {whole c b : List Instr} {base cb bb origin : Nat}
    (image : Image whole base) (ci : Image c cb) (bi : Image b bb)
    (frame : EvmYul.EVM.State) (entryWord exitWord : Fin W)
    (layout : LoopLayout (origin := origin) image ci bi frame entryWord exitWord)
    (cond : MacroRefinement ci frame) (body : MacroRefinement bi frame)
    (m : Machine) (s : EvmYul.EVM.State) (entry : Boundary image frame origin m s)
    (source : ∀ n, ∃ m', loopIterN (run c) (run b) n m = .inl m') :
    (Instr.loop c b).step m = .fault ∧
      ∀ n, ∃ k t m', n ≤ k ∧ fetchedSteps k s = .ok t ∧ Boundary image frame origin m' t := by
  refine ⟨loopRun_of_forall source, ?_⟩
  intro n
  obtain ⟨m', hm⟩ := source n
  obtain ⟨k, t, hk, ht, he⟩ := decoded_loop_prefixes image ci bi frame entryWord exitWord
    layout cond body n m m' s entry hm
  exact ⟨k, t, m', hk, ht, he⟩

end Solidity.Evm.External.Assembly

/-- info: 'Solidity.Evm.External.Assembly.decoded_loop_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.decoded_loop_turn
/-- info: 'Solidity.Evm.External.Assembly.DecodedCode.refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.DecodedCode.refinement
/-- info: 'Solidity.Evm.External.Assembly.certified_run_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.certified_run_simulation
/-- info: 'Solidity.Evm.External.Assembly.decoded_loop_divergence_prefixes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.decoded_loop_divergence_prefixes
