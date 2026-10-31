import SolidityBridge.ExternalEvm.Assembly.Loop

/-!
Composition at typed source labels. The local obligation is deliberately
separate from the whole-program theorem: it must be discharged by opcode
macros (and recursively by loop condition/body simulations), not by sampled
runs. All executions below use the actual fetched upstream step relation.
-/
namespace Solidity.Evm.External.Assembly

/-- The ambient executable code contains this relocated image. This permits
an arbitrary prefix and suffix but does not equate raw bytes with scanner output. -/
def Placed {code : List Instr} {base : Nat} (image : Image code base)
    (s : EvmYul.EVM.State) : Prop :=
  (s.executionEnv.code.data.toList.drop base).take image.bytes.length = image.bytes

/-- A source boundary, exact absolute PC, numeric stack and unchanged
upstream account/environment/memory frame. No source storage refinement is
claimed by this instruction-only relation. -/
structure Boundary {code : List Instr} {base : Nat} (image : Image code base)
    (frame : EvmYul.EVM.State) (index : Nat) (m : Machine)
    (s : EvmYul.EVM.State) : Prop where
  inBounds : index < code.length + 1
  pc : address code base ⟨index, inBounds⟩ = some s.pc.toNat
  stack : m.stack = words s.stack
  state : s.toState = frame.toState
  memory : s.memory = frame.memory

/-- Local proof obligation at an actual source instruction. It retains the
source's pending skip, so taken jumps compose with skipped suffixes rather
than executing their bytes. This is an obligation, not an assembler theorem. -/
def MacroRefinement {code : List Instr} {base : Nat} (image : Image code base)
    (frame : EvmYul.EVM.State) : Prop :=
  ∀ (pre : List Instr) (i : Instr) (rest : List Instr),
    code = pre ++ i :: rest →
    ∀ (m m' : Machine) (skip : Nat) (s : EvmYul.EVM.State),
    i.step m = .ok m' skip → Boundary image frame pre.length m s →
    ∃ n t, fetchedSteps n s = .ok t ∧
      Boundary image frame (pre.length + 1 + skip) m' t

/-- General relocated suffix composition, by induction over the existing
core runner. No target evaluator expansion, fuel increase, or independent
whole-target-run premise is used here. -/
theorem exec_simulation {code : List Instr} {base : Nat}
    (image : Image code base) (frame : EvmYul.EVM.State)
    (macros : MacroRefinement image frame)
    (pre rest : List Instr) (hc : code = pre ++ rest)
    (skip : Nat) (m m' : Machine) (s : EvmYul.EVM.State)
    (entry : Boundary image frame (pre.length + skip) m s)
    (source : exec rest skip m = .ok m' 0) :
    ∃ n t, fetchedSteps n s = .ok t ∧
      Boundary image frame code.length m' t := by
  induction rest generalizing pre skip m s with
  | nil =>
    simp only [exec_nil, Out.ok.injEq] at source
    obtain ⟨rfl, rfl⟩ := source
    refine ⟨0, s, rfl, ?_⟩
    simpa only [hc, List.append_nil, Nat.add_zero] using entry
  | cons i rest ih =>
    cases skip with
    | succ skip =>
      apply ih (pre ++ [i]) (by simpa only [List.append_assoc, List.singleton_append] using hc) skip m s
      · simpa only [List.length_append, List.length_singleton, Nat.add_assoc, Nat.add_comm skip 1] using entry
      · exact source
    | zero =>
      simp only [exec_cons_zero] at source
      cases hs : i.step m with
      | fault => simp only [hs, Out.fault_bind] at source
                 cases source
      | revert => simp only [hs, Out.revert_bind] at source
                  cases source
      | ok next k =>
        obtain ⟨n, t, ht, hb⟩ := macros pre i rest hc m next k s hs
          (by simpa only [Nat.add_zero] using entry)
        obtain ⟨n', u, hu, he⟩ := ih (pre ++ [i])
          (by simpa only [List.append_assoc, List.singleton_append] using hc) k next t
          (by simpa only [List.length_append, List.length_singleton, Nat.add_assoc] using hb)
          (by simpa only [hs, Out.ok_bind] using source)
        refine ⟨n + n', u, ?_, he⟩
        rw [fetchedSteps_add, ht]
        exact hu

theorem run_simulation {code : List Instr} {base : Nat}
    (image : Image code base) (frame : EvmYul.EVM.State)
    (macros : MacroRefinement image frame) (m m' : Machine) (s : EvmYul.EVM.State)
    (entry : Boundary image frame 0 m s) (source : run code m = .ok m' 0) :
    ∃ n t, fetchedSteps n s = .ok t ∧ Boundary image frame code.length m' t :=
  exec_simulation image frame macros [] code rfl 0 m m' s entry source

/-- Convert an actual fetched trace to its exact finite dispatcher count. -/
theorem FetchedTrace.count {s t : EvmYul.EVM.State} (h : FetchedTrace 0 s t) :
    ∃ n, fetchedSteps n s = .ok t := by
  induction h with
  | nil => exact ⟨0, rfl⟩
  | cons head _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    simp only [fetchedSteps, head]
    exact hn

def destState (s : EvmYul.EVM.State) : EvmYul.EVM.State := (prepare s).incrPC

theorem fetched_dest (s : EvmYul.EVM.State) (h : Fetches s (.JUMPDEST, none)) :
    EvmYul.EVM.step 1 0 none s = .ok (destState s) := by
  rw [fetched_step 0 s _ h]
  rfl

/-- A local macro preserves the boundary relation when its computed PC is
exactly the selected source label. The address premise is arithmetic/layout,
not an execution premise. Account, environment, memory and stack are proved. -/
theorem jump_boundary {code : List Instr} {base origin offset : Nat}
    (image : Image code base) (frame : EvmYul.EVM.State)
    (m : Machine) (s : EvmYul.EVM.State)
    (entry : Boundary image frame origin m s)
    (target : Fin W) (bound : origin + 1 + offset < code.length + 1)
    (address_eq : address code base ⟨origin + 1 + offset, bound⟩ = some target.val)
    (hd : Fetches s (.JUMPDEST, none))
    (hp : Fetches (destState s) (.Push .PUSH32, some (.ofNat target.val, 32)))
    (hj : Fetches (pushState (destState s) (.ofNat target.val)) (.JUMP, none)) :
    ∃ n t, fetchedSteps n s = .ok t ∧
      Boundary image frame (origin + 1 + offset) m t := by
  let t := jumpState (destState s) (.ofNat target.val)
  have trace : FetchedTrace 0 s t :=
    .cons (fetched_dest s hd) (fetched_jump_trace 0 _ _ hp hj)
  obtain ⟨n, hn⟩ := trace.count
  refine ⟨n, t, hn, ⟨bound, ?_, entry.stack, ?_, ?_⟩⟩
  · rw [jump_pc]
    exact address_eq
  · exact entry.state
  · exact entry.memory

/-- Local conditional macro: the caller supplies the exact selected-label
address and decoded packets. This proves the fetched execution and all frames;
it never replaces decoder validity with raw byte equality. -/
theorem jumpi_boundary {code : List Instr} {base origin offset : Nat}
    (image : Image code base) (frame : EvmYul.EVM.State)
    (m : Machine) (s : EvmYul.EVM.State) (c : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) (hs : s.stack = c :: tail)
    (entry : Boundary image frame origin m s) (target : Fin W)
    (bound : origin + 1 + (if c.toNat = 0 then 0 else offset) < code.length + 1)
    (address_eq : address code base
      ⟨origin + 1 + (if c.toNat = 0 then 0 else offset), bound⟩ =
      some (jumpiState (destState s) (.ofNat target.val) c tail).pc.toNat)
    (hd : Fetches s (.JUMPDEST, none))
    (hp : Fetches (destState s) (.Push .PUSH32, some (.ofNat target.val, 32)))
    (hj : Fetches (pushState (destState s) (.ofNat target.val)) (.JUMPI, none)) :
    (Instr.jumpi offset).step m =
        .ok {m with stack := words tail} (if c.toNat = 0 then 0 else offset) ∧
    ∃ n t, fetchedSteps n s = .ok t ∧ Boundary image frame
      (origin + 1 + (if c.toNat = 0 then 0 else offset)) {m with stack := words tail} t := by
  have hstack : m.stack = words (c :: tail) := entry.stack.trans (congrArg words hs)
  have core := (relative_jumpi_macro offset 0 (.ofNat target.val) c tail m s).1
  have hm : {m with stack := words (c :: tail)} = m := by rw [← hstack]
  rw [hm] at core
  refine ⟨core, ?_⟩
  let t := jumpiState (destState s) (.ofNat target.val) c tail
  have he : {destState s with stack := c :: tail} = destState s := by
    change {destState s with stack := c :: tail} = destState s
    have h : (destState s).stack = c :: tail := hs
    rw [← h]
  have ht : FetchedTrace 0 (destState s) t := by
    have h := fetched_jumpi_trace 0 (.ofNat target.val) c tail (destState s)
    rw [he] at h
    exact h hp hj
  obtain ⟨n, hn⟩ := (FetchedTrace.cons (fetched_dest s hd) ht).count
  exact ⟨n, t, hn, ⟨bound, address_eq, rfl, entry.state, entry.memory⟩⟩

/-- A word encoded by PUSH32 recovers the intrinsic numeric source word. -/
theorem words_ofNat (w : Fin W) (tail : List EvmYul.UInt256) :
    words (.ofNat w.val :: tail) = .val w :: words tail := by
  unfold words
  simp only [List.map_cons]
  congr 2
  apply Fin.ext
  exact Nat.mod_eq_of_lt w.isLt

theorem push_boundary {code : List Instr} {base origin : Nat}
    (image : Image code base) (frame : EvmYul.EVM.State)
    (m : Machine) (s : EvmYul.EVM.State) (w : Fin W)
    (entry : Boundary image frame origin m s)
    (bound : origin + 1 < code.length + 1)
    (address_eq : address code base ⟨origin + 1, bound⟩ =
      some (pushState (destState s) (.ofNat w.val)).pc.toNat)
    (hd : Fetches s (.JUMPDEST, none))
    (hp : Fetches (destState s) (.Push .PUSH32, some (.ofNat w.val, 32))) :
    ∃ n t, fetchedSteps n s = .ok t ∧
      Boundary image frame (origin + 1) {m with stack := .val w :: m.stack} t := by
  have ht : FetchedTrace 0 s (pushState (destState s) (.ofNat w.val)) :=
    .cons (fetched_dest s hd) (.cons (by rw [fetched_step 0 _ _ hp]; rfl) (.nil _))
  obtain ⟨n, hn⟩ := ht.count
  refine ⟨n, _, hn, ⟨bound, address_eq, ?_, entry.state, entry.memory⟩⟩
  change .val w :: m.stack = words (.ofNat w.val :: s.stack)
  rw [words_ofNat, entry.stack]

/-- Pure stack pop following its emitted JUMPDEST. -/
def popState (s : EvmYul.EVM.State) (tail : List EvmYul.UInt256) : EvmYul.EVM.State :=
  (prepare (destState s)).replaceStackAndIncrPC tail

theorem pop_boundary {code : List Instr} {base origin : Nat}
    (image : Image code base) (frame : EvmYul.EVM.State)
    (m : Machine) (s : EvmYul.EVM.State) (c : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) (hs : s.stack = c :: tail)
    (entry : Boundary image frame origin m s)
    (bound : origin + 1 < code.length + 1)
    (address_eq : address code base ⟨origin + 1, bound⟩ = some (popState s tail).pc.toNat)
    (hd : Fetches s (.JUMPDEST, none)) (hp : Fetches (destState s) (.POP, none)) :
    ∃ n t, fetchedSteps n s = .ok t ∧
      Boundary image frame (origin + 1) {m with stack := words tail} t := by
  have step : EvmYul.EVM.step 1 0 none (destState s) = .ok (popState s tail) := by
    rw [fetched_step 0 _ _ hp]
    have h : {destState s with stack := c :: tail} = destState s := by
      have h : (destState s).stack = c :: tail := hs
      rw [← h]
    rw [← h]
    rfl
  obtain ⟨n, hn⟩ := (FetchedTrace.cons (fetched_dest s hd)
    (.cons step (.nil _))).count
  exact ⟨n, _, hn, ⟨bound, address_eq, rfl, entry.state, entry.memory⟩⟩

/-- Decoder and arithmetic assumptions for a single emitted non-loop
instruction. These contain no source or target execution-simulation premise. -/
def PrimitiveLayout {code : List Instr} {base : Nat} (_image : Image code base)
    (origin : Nat) (i : Instr) (s : EvmYul.EVM.State) : Prop :=
  Fetches s (.JUMPDEST, none) ∧ match i with
  | .push (.val w) => ∃ h : origin + 1 < code.length + 1,
      address code base ⟨origin + 1, h⟩ = some (pushState (destState s) (.ofNat w.val)).pc.toNat ∧
      Fetches (destState s) (.Push .PUSH32, some (.ofNat w.val, 32))
  | .pop => ∀ c tail, s.stack = c :: tail → ∃ h : origin + 1 < code.length + 1,
      address code base ⟨origin + 1, h⟩ = some (popState s tail).pc.toNat ∧
      Fetches (destState s) (.POP, none)
  | .jump offset => ∃ target : Fin W, ∃ h : origin + 1 + offset < code.length + 1,
      address code base ⟨origin + 1 + offset, h⟩ = some target.val ∧
      Fetches (destState s) (.Push .PUSH32, some (.ofNat target.val, 32)) ∧
      Fetches (pushState (destState s) (.ofNat target.val)) (.JUMP, none)
  | .jumpi offset => ∀ c tail, s.stack = c :: tail → ∃ target : Fin W,
      ∃ h : origin + 1 + (if c.toNat = 0 then 0 else offset) < code.length + 1,
      address code base ⟨origin + 1 + (if c.toNat = 0 then 0 else offset), h⟩ =
        some (jumpiState (destState s) (.ofNat target.val) c tail).pc.toNat ∧
      Fetches (destState s) (.Push .PUSH32, some (.ofNat target.val, 32)) ∧
      Fetches (pushState (destState s) (.ofNat target.val)) (.JUMPI, none)
  | _ => False

/-- Discharge a non-loop local refinement from actual decoding and exact
arithmetic addresses, rather than from a supplied target trace. -/
theorem primitive_refinement {code : List Instr} {base origin : Nat}
    (image : Image code base) (frame : EvmYul.EVM.State)
    (i : Instr) (m m' : Machine) (skip : Nat) (s : EvmYul.EVM.State)
    (layout : PrimitiveLayout image origin i s)
    (entry : Boundary image frame origin m s) (source : i.step m = .ok m' skip) :
    ∃ n t, fetchedSteps n s = .ok t ∧ Boundary image frame (origin + 1 + skip) m' t := by
  obtain ⟨hd, hl⟩ := layout
  cases i <;> try contradiction
  case push w =>
    cases w <;> try contradiction
    case val w =>
      obtain ⟨bound, address_eq, hp⟩ := hl
      cases source
      simpa only [Nat.add_zero] using push_boundary image frame m s w entry bound address_eq hd hp
  case pop =>
    cases hs : s.stack with
    | nil =>
      have hm : m.stack = [] := entry.stack.trans (congrArg words hs)
      simp only [Instr.step, hm] at source
      cases source
    | cons c tail =>
      obtain ⟨bound, address_eq, hp⟩ := hl c tail hs
      have hm : m.stack = words (c :: tail) := entry.stack.trans (congrArg words hs)
      simp only [Instr.step, hm, words, List.map_cons, Machine.next, Out.ok.injEq] at source
      obtain ⟨rfl, rfl⟩ := source
      simpa only [Nat.add_zero] using pop_boundary image frame m s c tail hs entry bound address_eq hd hp
  case jump offset =>
    obtain ⟨target, bound, address_eq, hp, hj⟩ := hl
    cases source
    exact jump_boundary image frame m s entry target bound address_eq hd hp hj
  case jumpi offset =>
    cases hs : s.stack with
    | nil =>
      have hm : m.stack = [] := entry.stack.trans (congrArg words hs)
      simp only [Instr.step, hm] at source
      cases source
    | cons c tail =>
      obtain ⟨target, bound, address_eq, hp, hj⟩ := hl c tail hs
      obtain ⟨hc, ht⟩ := jumpi_boundary image frame m s c tail hs entry target bound address_eq hd hp hj
      rw [hc] at source
      cases source
      exact ht

/-- A decoded image of numeric pushes, pops and forward branches refines
all successful core executions, including nontrivial branch compositions. -/
theorem decoded_run_simulation {code : List Instr} {base : Nat}
    (image : Image code base) (frame : EvmYul.EVM.State)
    (decode : ∀ pre i rest, code = pre ++ i :: rest → ∀ m s,
      Boundary image frame pre.length m s → PrimitiveLayout image pre.length i s)
    (m m' : Machine) (s : EvmYul.EVM.State)
    (entry : Boundary image frame 0 m s) (source : run code m = .ok m' 0) :
    ∃ n t, fetchedSteps n s = .ok t ∧ Boundary image frame code.length m' t := by
  apply run_simulation image frame ?_ m m' s entry source
  intro pre i rest hc m m' skip s hs he
  exact primitive_refinement image frame i m m' skip s (decode pre i rest hc m s he) he hs

theorem condition_beq (c : EvmYul.UInt256) :
    (c == ⟨0⟩) = decide (c.toNat = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [EvmYul.instBEqUInt256, EvmYul.instBEqUInt256.beq,
    beq_iff_eq, decide_eq_true_eq, Fin.ext_iff]
  rfl

/-- Success of the noncomputable core loop has a finite semantic witness.
This does not treat its divergent fault result as finite target failure. -/
theorem loopRun_ok_witness {rc rb : Machine → Out} {m m' : Machine}
    (h : loopRun rc rb m = .ok m' 0) :
    ∃ n, loopIterN rc rb n m = .inr (.ok m' 0) := by
  unfold loopRun at h
  split at h
  · rename_i hex
    obtain ⟨n, hn⟩ := Classical.choose_spec hex
    exact ⟨n, h ▸ hn⟩
  · cases h

/-- One-turn simulation is sufficient for arbitrary structured-loop
composition. It must be supplied from condition/body simulation and routing
macros; the premises use the *existing* core loopTurn, not an invented IR. -/
def TurnRefinement (rc rb : Machine → Out)
    (header exit : Machine → EvmYul.EVM.State → Prop) : Prop :=
  ∀ m s, header m s →
    (∀ m', loopTurn rc rb m = .inl m' →
      ∃ n t, 0 < n ∧ fetchedSteps n s = .ok t ∧ header m' t) ∧
    (∀ m', loopTurn rc rb m = .inr (.ok m' 0) →
      ∃ n t, 0 < n ∧ fetchedSteps n s = .ok t ∧ exit m' t)

/-- Finite semantic loop iterations compose actual fetched traces, with
positive progress for every completed turn. -/
theorem loopIterN_simulation {rc rb : Machine → Out}
    {header exit : Machine → EvmYul.EVM.State → Prop}
    (turn : TurnRefinement rc rb header exit)
    (n : Nat) (m m' : Machine) (s : EvmYul.EVM.State)
    (entry : header m s) (h : loopIterN rc rb n m = .inr (.ok m' 0)) :
    ∃ k t, 0 < k ∧ fetchedSteps k s = .ok t ∧ exit m' t := by
  induction n generalizing m s with
  | zero => cases h
  | succ n ih =>
    cases ht : loopTurn rc rb m with
    | inl next =>
      obtain ⟨k, t, hk, hs, he⟩ := (turn m s entry).1 next ht
      obtain ⟨k', u, hk', hu, hout⟩ := ih next t he
        (by simpa only [loopIterN, ht] using h)
      refine ⟨k + k', u, by omega, ?_, hout⟩
      rw [fetchedSteps_add, hs]
      exact hu
    | inr out =>
      have ho : out = .ok m' 0 := by simpa only [loopIterN, ht, Sum.inr.injEq] using h
      subst out
      exact (turn m s entry).2 m' ht

theorem structured_loop_simulation {rc rb : Machine → Out}
    {header exit : Machine → EvmYul.EVM.State → Prop}
    (turn : TurnRefinement rc rb header exit)
    (m m' : Machine) (s : EvmYul.EVM.State) (entry : header m s)
    (source : loopRun rc rb m = .ok m' 0) :
    ∃ k t, 0 < k ∧ fetchedSteps k s = .ok t ∧ exit m' t := by
  obtain ⟨n, hn⟩ := loopRun_ok_witness source
  exact loopIterN_simulation turn n m m' s entry hn

/-- Every still-running semantic prefix has an actual target prefix with
at least as many steps. There is no finite-fuel X divergence conclusion. -/
theorem loop_prefix_simulation {rc rb : Machine → Out}
    {header exit : Machine → EvmYul.EVM.State → Prop}
    (turn : TurnRefinement rc rb header exit)
    (n : Nat) (m m' : Machine) (s : EvmYul.EVM.State)
    (entry : header m s) (h : loopIterN rc rb n m = .inl m') :
    ∃ k t, n ≤ k ∧ fetchedSteps k s = .ok t ∧ header m' t := by
  induction n generalizing m s with
  | zero =>
    have hm : m = m' := Sum.inl.inj h
    subst m'
    exact ⟨0, s, Nat.le_refl _, rfl, entry⟩
  | succ n ih =>
    cases ht : loopTurn rc rb m with
    | inl next =>
      obtain ⟨k, t, hk, hs, he⟩ := (turn m s entry).1 next ht
      obtain ⟨k', u, hk', hu, hout⟩ := ih next t he
        (by simpa only [loopIterN, ht] using h)
      refine ⟨k + k', u, by omega, ?_, hout⟩
      rw [fetchedSteps_add, hs]
      exact hu
    | inr out =>
      simp only [loopIterN, ht] at h
      cases h

/-- Invert the numeric stack interpretation at a semantic loop guard. -/
theorem words_cons_inverse (stack : List EvmYul.UInt256) (w : Fin W) (tail : List Word)
    (h : words stack = .val w :: tail) :
    ∃ rest, stack = .ofNat w.val :: rest ∧ words rest = tail := by
  cases stack with
  | nil => cases h
  | cons c rest =>
    have hp : (.val ⟨c.toNat, c.val.isLt⟩ : Word) = .val w ∧ words rest = tail :=
      List.cons.inj h
    have hn : c.toNat = w.val := congrArg Fin.val (Word.val.inj hp.1)
    have hc : c = .ofNat w.val := by
      apply congrArg EvmYul.UInt256.mk
      apply Fin.ext
      change c.toNat = w.val % W
      rw [hn, Nat.mod_eq_of_lt w.isLt]
    exact ⟨rest, by rw [hc], hp.2⟩

/-- The emitted loop guard consumes the condition's continuation JUMPDEST,
ISZERO, PUSH32 exit and JUMPI. -/
def iszeroState (s : EvmYul.EVM.State) (c : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) : EvmYul.EVM.State :=
  (prepare (destState s)).replaceStackAndIncrPC (EvmYul.UInt256.isZero c :: tail)

def guardState (s : EvmYul.EVM.State) (c : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) (exit : Fin W) : EvmYul.EVM.State :=
  jumpiState (iszeroState s c tail) (.ofNat exit.val) (EvmYul.UInt256.isZero c) tail

theorem guard_trace (s : EvmYul.EVM.State) (c : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) (exit : Fin W) (hs : s.stack = c :: tail)
    (hd : Fetches s (.JUMPDEST, none))
    (hz : Fetches (destState s) (.ISZERO, none))
    (hp : Fetches (iszeroState s c tail) (.Push .PUSH32, some (.ofNat exit.val, 32)))
    (hj : Fetches (pushState (iszeroState s c tail) (.ofNat exit.val)) (.JUMPI, none)) :
    fetchedSteps 4 s = .ok (guardState s c tail exit) := by
  have zeroStep : EvmYul.EVM.step 1 0 none (destState s) = .ok (iszeroState s c tail) := by
    rw [fetched_step 0 _ _ hz]
    have h : {destState s with stack := c :: tail} = destState s := by
      have h : (destState s).stack = c :: tail := hs
      rw [← h]
    rw [← h]
    rfl
  have pushStep : EvmYul.EVM.step 1 0 none (iszeroState s c tail) =
      .ok (pushState (iszeroState s c tail) (.ofNat exit.val)) := by
    rw [fetched_step 0 _ _ hp]
    rfl
  have jumpStep : EvmYul.EVM.step 1 0 none
      (pushState (iszeroState s c tail) (.ofNat exit.val)) = .ok (guardState s c tail exit) := by
    rw [fetched_step 0 _ _ hj]
    rfl
  simp only [fetchedSteps, fetched_dest s hd, bind, Except.bind, zeroStep, pushStep, jumpStep]

/-- Structural decomposition of a still-running source turn. -/
theorem loopTurn_continue {rc rb : Machine → Out} {m next : Machine}
    (h : loopTurn rc rb m = .inl next) :
    ∃ mc w tail, rc m = .ok mc 0 ∧ mc.stack = .val w :: tail ∧
      w.val ≠ 0 ∧ rb {mc with stack := tail} = .ok next 0 := by
  unfold loopTurn at h
  cases hc : rc m with
  | fault => simp only [hc] at h; cases h
  | revert => simp only [hc] at h; cases h
  | ok mc skip =>
    cases skip with
    | succ k => simp only [hc] at h; cases h
    | zero =>
      simp only [hc] at h
      cases hs : mc.stack with
      | nil => simp only [hs] at h; cases h
      | cons word tail =>
        cases word <;> try (simp only [hs] at h; cases h)
        case val w =>
          simp only [hs] at h
          split at h
          · cases h
          · rename_i hn
            cases hb : rb {mc with stack := tail} with
            | fault => simp only [hb] at h; cases h
            | revert => simp only [hb] at h; cases h
            | ok next' skip =>
              cases skip with
              | succ k => simp only [hb] at h; cases h
              | zero =>
                have he : next' = next := by simpa only [hb, Sum.inl.injEq] using h
                subst next'
                exact ⟨mc, w, tail, rfl, hs, hn, hb⟩

/-- Structural decomposition of a successfully exiting source turn. -/
theorem loopTurn_exit {rc rb : Machine → Out} {m next : Machine}
    (h : loopTurn rc rb m = .inr (.ok next 0)) :
    ∃ mc w tail, rc m = .ok mc 0 ∧ mc.stack = .val w :: tail ∧
      w.val = 0 ∧ next = {mc with stack := tail} := by
  unfold loopTurn at h
  cases hc : rc m with
  | fault => simp only [hc] at h; cases h
  | revert => simp only [hc] at h; cases h
  | ok mc skip =>
    cases skip with
    | succ k => simp only [hc] at h; cases h
    | zero =>
      simp only [hc] at h
      cases hs : mc.stack with
      | nil => simp only [hs] at h; cases h
      | cons word tail =>
        cases word <;> try (simp only [hs] at h; cases h)
        case val w =>
          simp only [hs] at h
          split at h
          · rename_i hz
            have he : {mc with stack := tail} = next := by
              simpa only [Sum.inr.injEq, Out.ok.injEq, and_true] using h
            exact ⟨mc, w, tail, rfl, hs, hz, he.symm⟩
          · cases hb : rb {mc with stack := tail} with
            | fault => simp only [hb] at h; cases h
            | revert => simp only [hb] at h; cases h
            | ok next' skip =>
              cases skip <;> simp only [hb] at h <;> cases h

/-- Compose verified condition/body executions with the local guard and
backedge executions. Relations may be distinct relocated code slices. The
routing premises are local macros, never whole-loop target simulations. -/
theorem turn_of_parts {rc rb : Machine → Out}
    {header condition bodyEntry bodyExit exit : Machine → EvmYul.EVM.State → Prop}
    (cond : ∀ m s, header m s → ∀ mc, rc m = .ok mc 0 →
      ∃ n t, fetchedSteps n s = .ok t ∧ condition mc t)
    (zero : ∀ mc s w tail, condition mc s → mc.stack = .val w :: tail → w.val = 0 →
      ∃ n t, 0 < n ∧ fetchedSteps n s = .ok t ∧ exit {mc with stack := tail} t)
    (nonzero : ∀ mc s w tail, condition mc s → mc.stack = .val w :: tail → w.val ≠ 0 →
      ∃ n t, 0 < n ∧ fetchedSteps n s = .ok t ∧ bodyEntry {mc with stack := tail} t)
    (body : ∀ m s, bodyEntry m s → ∀ next, rb m = .ok next 0 →
      ∃ n t, fetchedSteps n s = .ok t ∧ bodyExit next t)
    (back : ∀ m s, bodyExit m s → ∃ n t,
      fetchedSteps n s = .ok t ∧ header m t) :
    TurnRefinement rc rb header exit := by
  intro m s he
  constructor
  · intro next ht
    obtain ⟨mc, w, tail, hc, hs, hn, hb⟩ := loopTurn_continue ht
    obtain ⟨a, t, hat, hct⟩ := cond m s he mc hc
    obtain ⟨b, u, hpos, hbu, hbe⟩ := nonzero mc t w tail hct hs hn
    obtain ⟨c, v, hcv, hce⟩ := body _ u hbe next hb
    obtain ⟨d, z, hdz, hze⟩ := back next v hce
    refine ⟨a + (b + (c + d)), z, by omega, ?_, hze⟩
    rw [fetchedSteps_add, hat]
    change fetchedSteps (b + (c + d)) t = _
    rw [fetchedSteps_add, hbu]
    change fetchedSteps (c + d) u = _
    rw [fetchedSteps_add, hcv]
    exact hdz
  · intro next ht
    obtain ⟨mc, w, tail, hc, hs, hz, rfl⟩ := loopTurn_exit ht
    obtain ⟨a, t, hat, hct⟩ := cond m s he mc hc
    obtain ⟨b, u, hpos, hbu, hbe⟩ := zero mc t w tail hct hs hz
    refine ⟨a + b, u, by omega, ?_, hbe⟩
    rw [fetchedSteps_add, hat]
    exact hbu

end Solidity.Evm.External.Assembly

/-- info: 'Solidity.Evm.External.Assembly.exec_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.exec_simulation
/-- info: 'Solidity.Evm.External.Assembly.decoded_run_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.decoded_run_simulation
/-- info: 'Solidity.Evm.External.Assembly.loopIterN_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.loopIterN_simulation
/-- info: 'Solidity.Evm.External.Assembly.loop_prefix_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.loop_prefix_simulation
/-- info: 'Solidity.Evm.External.Assembly.guard_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.guard_trace
