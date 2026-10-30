import SolidityBridge.ExternalEvm.Assembly.SafeLocal

namespace Solidity.Evm.External.Assembly

theorem safe_decoded_loop_turn {destinations : List EvmYul.UInt256} {whole c b : List Instr} {base cb bb origin : Nat}
    (image : Image whole base) (ci : Image c cb) (bi : Image b bb)
    (frame : EvmYul.EVM.State) (entryWord exitWord : Fin W)
    (layout : LoopLayout (origin := origin) image ci bi frame entryWord exitWord)
    (headerMember : EvmYul.UInt256.ofNat entryWord.val ∈ destinations)
    (exitMember : EvmYul.UInt256.ofNat exitWord.val ∈ destinations)
    (cond : SafeMacroRefinement destinations ci frame) (body : SafeMacroRefinement destinations bi frame) :
    SafeTurnRefinement destinations (run c) (run b) (Boundary image frame origin)
      (Boundary image frame (origin + 1)) := by
  apply safe_turn_of_parts (condition := Boundary ci frame c.length)
    (bodyEntry := Boundary bi frame 0) (bodyExit := Boundary bi frame b.length)
  · intro m s he mc hc
    obtain ⟨hd, ha⟩ := layout.enter m s he
    have entry : Boundary ci frame 0 m (destState s) :=
      ⟨Nat.zero_lt_succ _, ha, he.stack, he.state, he.memory⟩
    obtain ⟨n, t, ht, hb⟩ := safe_run_simulation ci frame cond m mc (destState s) entry hc
    exact ⟨1 + n, t, (SafeTrace.dest s hd).trans ht, hb⟩
  · intro mc s w tail he hs hz
    obtain ⟨rest, hrest, hwords⟩ := words_cons_inverse s.stack w tail (he.stack.symm.trans hs)
    obtain ⟨hd, hi, hp, hj⟩ := layout.guard mc s w tail rest he hs hrest
    refine ⟨4, guardState s (.ofNat w.val) rest exitWord, by decide,
      safe_guard_trace s _ rest exitWord hrest exitMember hd hi hp hj, ?_⟩
    exact ⟨layout.exitBound, layout.zeroAddress mc s w tail rest he hs hrest hz,
      hwords.symm, he.state, he.memory⟩
  · intro mc s w tail he hs hn
    obtain ⟨rest, hrest, hwords⟩ := words_cons_inverse s.stack w tail (he.stack.symm.trans hs)
    obtain ⟨hd, hi, hp, hj⟩ := layout.guard mc s w tail rest he hs hrest
    refine ⟨4, guardState s (.ofNat w.val) rest exitWord, by decide,
      safe_guard_trace s _ rest exitWord hrest exitMember hd hi hp hj, ?_⟩
    exact ⟨Nat.zero_lt_succ _, layout.nonzeroAddress mc s w tail rest he hs hrest hn,
      hwords.symm, he.state, he.memory⟩
  · intro m s he next hb
    exact safe_run_simulation bi frame body m next s he hb
  · intro m s he
    obtain ⟨hd, hp, hj⟩ := layout.back m s he
    refine ⟨3, _, (SafeTrace.dest s hd).trans (SafeTrace.jump _ _ headerMember hp hj),
      ⟨layout.headerBound, ?_, he.stack, he.state, he.memory⟩⟩
    rw [jump_pc]
    exact layout.headerAddress


/-- The stored memberships on the exact loop routing certificate are used
on every guard/backedge, while recursive children supply their safe traces. -/
theorem safe_decoded_loop_macro {destinations : List EvmYul.UInt256}
    {whole c b : List Instr} {base cb bb origin : Nat}
    (image : Image whole base) (ci : Image c cb) (bi : Image b bb)
    (frame : EvmYul.EVM.State) (entryWord exitWord : Fin W)
    (layout : LoopLayout (origin := origin) image ci bi frame entryWord exitWord)
    (headerMember : EvmYul.UInt256.ofNat entryWord.val ∈ destinations)
    (exitMember : EvmYul.UInt256.ofNat exitWord.val ∈ destinations)
    (cond : SafeMacroRefinement destinations ci frame) (body : SafeMacroRefinement destinations bi frame)
    (m m' : Machine) (skip : Nat) (s : EvmYul.EVM.State)
    (entry : Boundary image frame origin m s) (source : (Instr.loop c b).step m = .ok m' skip) :
    ∃ n t, SafeTrace destinations n s t ∧ Boundary image frame (origin + 1 + skip) m' t := by
  have hk : skip = 0 := loopRun_success_skip source
  subst skip
  obtain ⟨n, t, _, trace, related⟩ := safe_structured_loop_simulation
    (safe_decoded_loop_turn image ci bi frame entryWord exitWord layout headerMember exitMember cond body)
    m m' s entry source
  exact ⟨n, t, trace, related⟩

/-- Scanner safety is consumed by execution refinement, not left beside an
unannotated simulation. Every returned microstep is fetched, pure and jump-safe. -/
theorem ScannedCode.safe_refinement {frame : EvmYul.EVM.State} {destinations : List EvmYul.UInt256}
    {code : List Instr} {base : Nat} {image : Image code base}
    (certificate : ScannedCode frame destinations image) : SafeMacroRefinement destinations image frame := by
  induction certificate using ScannedCode.rec
    (motive_2 := fun {_ _} image origin i _ => ∀ m m' skip s,
      i.step m = .ok m' skip → Boundary image frame origin m s →
      ∃ n t, SafeTrace destinations n s t ∧ Boundary image frame (origin + 1 + skip) m' t) with
  | intro image labels sites ih =>
    intro pre i rest shape m m' skip s source entry
    exact ih pre i rest shape m m' skip s source entry
  | atom image site safe =>
    rename_i m m' skip s source entry
    exact site.safe_refinement safe m m' skip s entry source
  | loop image ci bi site header exit _ _ cond body =>
    rename_i m m' skip s source entry
    exact safe_decoded_loop_macro image ci bi frame site.here
      ⟨site.here.val + ci.size + bi.size + 72, site.fits⟩ site.layout header exit cond body
      m m' skip s entry source

theorem LinkedProgram.safe_simulation {code : List Instr} (program : LinkedProgram code)
    (m m' : Machine) (s : EvmYul.EVM.State)
    (entry : Boundary program.checked.image program.frame 0 m s) (source : run code m = .ok m' 0) :
    ∃ n t, SafeTrace program.scanner.destinations n s t ∧
      Boundary program.checked.image program.frame code.length m' t :=
  safe_run_simulation program.checked.image program.frame program.scanned.safe_refinement m m' s entry source

end Solidity.Evm.External.Assembly
