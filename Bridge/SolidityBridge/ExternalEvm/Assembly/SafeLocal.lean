import SolidityBridge.ExternalEvm.Assembly.SafeComposition

namespace Solidity.Evm.External.Assembly
open EvmYul EvmYul.EVM

private theorem safe_pop {destinations : List UInt256} (s : EVM.State) (c : UInt256)
    (tail : List UInt256) (stack : s.stack = c :: tail)
    (fetch : Fetches (destState s) (.POP, none)) :
    SafeTrace destinations 1 (destState s) (popState s tail) := by
  refine .cons (.POP, none) fetch .pop trivial ?_ (.nil _)
  rw [fetched_step 0 _ _ fetch]
  have he : {destState s with stack := c :: tail} = destState s := by
    have hs : (destState s).stack = c :: tail := stack
    rw [← hs]
  rw [← he]
  rfl

private theorem safe_zero {destinations : List UInt256} (s : EVM.State) (c : UInt256)
    (tail : List UInt256) (stack : s.stack = c :: tail)
    (fetch : Fetches (destState s) (.ISZERO, none)) :
    SafeTrace destinations 1 (destState s) (iszeroState s c tail) := by
  refine .cons (.ISZERO, none) fetch .zero trivial ?_ (.nil _)
  rw [fetched_step 0 _ _ fetch]
  have he : {destState s with stack := c :: tail} = destState s := by
    have hs : (destState s).stack = c :: tail := stack
    rw [← hs]
  rw [← he]
  rfl

theorem safe_guard_trace {destinations : List UInt256} (s : EVM.State) (c : UInt256)
    (tail : List UInt256) (exit : Fin W) (stack : s.stack = c :: tail)
    (member : UInt256.ofNat exit.val ∈ destinations)
    (hd : Fetches s (.JUMPDEST, none)) (hz : Fetches (destState s) (.ISZERO, none))
    (hp : Fetches (iszeroState s c tail) (.Push .PUSH32, some (.ofNat exit.val, 32)))
    (hj : Fetches (pushState (iszeroState s c tail) (.ofNat exit.val)) (.JUMPI, none)) :
    SafeTrace destinations 4 s (guardState s c tail exit) :=
  (SafeTrace.dest s hd).trans ((safe_zero s c tail stack hz).trans
    (SafeTrace.jumpi (iszeroState s c tail) (.ofNat exit.val) (UInt256.isZero c) tail rfl member hp hj))

private theorem safe_push_boundary {destinations : List UInt256} {code : List Instr} {base origin : Nat}
    (image : Image code base) (frame : EVM.State) (m : Machine) (s : EVM.State) (w : Fin W)
    (entry : Boundary image frame origin m s) (bound : origin + 1 < code.length + 1)
    (address_eq : address code base ⟨origin + 1, bound⟩ = some (pushState (destState s) (.ofNat w.val)).pc.toNat)
    (hd : Fetches s (.JUMPDEST, none))
    (hp : Fetches (destState s) (.Push .PUSH32, some (.ofNat w.val, 32))) :
    ∃ n t, SafeTrace destinations n s t ∧
      Boundary image frame (origin + 1) {m with stack := .val w :: m.stack} t := by
  refine ⟨2, _, (SafeTrace.dest s hd).trans (SafeTrace.push _ _ hp),
    ⟨bound, address_eq, ?_, entry.state, entry.memory⟩⟩
  change .val w :: m.stack = words (.ofNat w.val :: s.stack)
  rw [words_ofNat, entry.stack]

private theorem safe_pop_boundary {destinations : List UInt256} {code : List Instr} {base origin : Nat}
    (image : Image code base) (frame : EVM.State) (m : Machine) (s : EVM.State)
    (c : UInt256) (tail : List UInt256) (stack : s.stack = c :: tail)
    (entry : Boundary image frame origin m s) (bound : origin + 1 < code.length + 1)
    (address_eq : address code base ⟨origin + 1, bound⟩ = some (popState s tail).pc.toNat)
    (hd : Fetches s (.JUMPDEST, none)) (hp : Fetches (destState s) (.POP, none)) :
    ∃ n t, SafeTrace destinations n s t ∧ Boundary image frame (origin + 1) {m with stack := words tail} t :=
  ⟨2, _, (SafeTrace.dest s hd).trans (safe_pop s c tail stack hp),
    ⟨bound, address_eq, rfl, entry.state, entry.memory⟩⟩

private theorem safe_jump_boundary {destinations : List UInt256} {code : List Instr} {base origin offset : Nat}
    (image : Image code base) (frame : EVM.State) (m : Machine) (s : EVM.State)
    (entry : Boundary image frame origin m s) (target : Fin W)
    (member : UInt256.ofNat target.val ∈ destinations)
    (bound : origin + 1 + offset < code.length + 1)
    (address_eq : address code base ⟨origin + 1 + offset, bound⟩ = some target.val)
    (hd : Fetches s (.JUMPDEST, none))
    (hp : Fetches (destState s) (.Push .PUSH32, some (.ofNat target.val, 32)))
    (hj : Fetches (pushState (destState s) (.ofNat target.val)) (.JUMP, none)) :
    ∃ n t, SafeTrace destinations n s t ∧ Boundary image frame (origin + 1 + offset) m t := by
  refine ⟨3, _, (SafeTrace.dest s hd).trans (SafeTrace.jump _ _ member hp hj),
    ⟨bound, ?_, entry.stack, entry.state, entry.memory⟩⟩
  rw [jump_pc]
  exact address_eq

private theorem safe_jumpi_boundary {destinations : List UInt256} {code : List Instr} {base origin offset : Nat}
    (image : Image code base) (frame : EVM.State) (m : Machine) (s : EVM.State)
    (c : UInt256) (tail : List UInt256) (stack : s.stack = c :: tail)
    (entry : Boundary image frame origin m s) (target : Fin W)
    (member : UInt256.ofNat target.val ∈ destinations)
    (bound : origin + 1 + (if c.toNat = 0 then 0 else offset) < code.length + 1)
    (address_eq : address code base ⟨origin + 1 + (if c.toNat = 0 then 0 else offset), bound⟩ =
      some (jumpiState (destState s) (.ofNat target.val) c tail).pc.toNat)
    (hd : Fetches s (.JUMPDEST, none))
    (hp : Fetches (destState s) (.Push .PUSH32, some (.ofNat target.val, 32)))
    (hj : Fetches (pushState (destState s) (.ofNat target.val)) (.JUMPI, none)) :
    (Instr.jumpi offset).step m = .ok {m with stack := words tail} (if c.toNat = 0 then 0 else offset) ∧
      ∃ n t, SafeTrace destinations n s t ∧ Boundary image frame
        (origin + 1 + (if c.toNat = 0 then 0 else offset)) {m with stack := words tail} t := by
  have hstack : m.stack = words (c :: tail) := entry.stack.trans (congrArg words stack)
  have core := (relative_jumpi_macro offset 0 (.ofNat target.val) c tail m s).1
  have hm : {m with stack := words (c :: tail)} = m := by rw [← hstack]
  rw [hm] at core
  exact ⟨core, 3, _, (SafeTrace.dest s hd).trans (SafeTrace.jumpi _ _ c tail stack member hp hj),
    ⟨bound, address_eq, rfl, entry.state, entry.memory⟩⟩

/-- An atomic certificate and its stored relocation safety produce the same
source macro refinement with safe evidence on every fetched instruction. -/
theorem AtomicSite.safe_refinement {destinations : List UInt256} {code : List Instr} {base origin : Nat}
    {image : Image code base} {frame : EVM.State} {i : Instr}
    (site : AtomicSite image frame origin i) (safe : TargetsSafe code base origin destinations i)
    (m m' : Machine) (skip : Nat) (s : EVM.State)
    (entry : Boundary image frame origin m s) (source : i.step m = .ok m' skip) :
    ∃ n t, SafeTrace destinations n s t ∧ Boundary image frame (origin + 1 + skip) m' t := by
  have facts := site.layout m s entry
  cases site with
  | push w here hb ha hn fit next head op =>
    obtain ⟨hd, bound, address_eq, hp⟩ := facts
    cases source
    simpa only [Nat.add_zero] using safe_push_boundary image frame m s w entry bound address_eq hd hp
  | pop here hb ha hn fit next head op =>
    obtain ⟨hd, layout⟩ := facts
    cases hs : s.stack with
    | nil =>
      have hm : m.stack = [] := entry.stack.trans (congrArg words hs)
      simp only [Instr.step, hm] at source
      cases source
    | cons c tail =>
      obtain ⟨bound, address_eq, hp⟩ := layout c tail hs
      have hm : m.stack = words (c :: tail) := entry.stack.trans (congrArg words hs)
      simp only [Instr.step, hm, words, List.map_cons, Machine.next, Out.ok.injEq] at source
      obtain ⟨rfl, rfl⟩ := source
      simpa only [Nat.add_zero] using safe_pop_boundary image frame m s c tail hs entry bound address_eq hd hp
  | jump offset here hb ha fit original head push op =>
    obtain ⟨hd, target, bound, address_eq, hp, hj⟩ := facts
    have member : UInt256.ofNat target.val ∈ destinations := safe ⟨⟨origin + 1 + offset, bound⟩, rfl, target, address_eq⟩
    cases source
    exact safe_jump_boundary image frame m s entry target member bound address_eq hd hp hj
  | jumpi offset here hb ha hn fit next original head push op =>
    obtain ⟨hd, layout⟩ := facts
    cases hs : s.stack with
    | nil =>
      have hm : m.stack = [] := entry.stack.trans (congrArg words hs)
      simp only [Instr.step, hm] at source
      cases source
    | cons c tail =>
      obtain ⟨target, bound, address_eq, hp, hj⟩ := layout c tail hs
      have hp0 : Fetches (destState s) (.Push .PUSH32, some (.ofNat original.pc.val, 32)) := by
        apply decode_fetch frame (destState s) _ _ entry.state _ push
        change s.pc + .ofNat 1 = .ofNat (here.val + 1)
        rw [boundary_pc entry here ha, word_add]
      have packetEq := Except.ok.inj (hp.symm.trans hp0)
      have wordEq : UInt256.ofNat target.val = .ofNat original.pc.val :=
        congrArg Prod.fst (Option.some.inj (congrArg Prod.snd packetEq))
      have member : UInt256.ofNat target.val ∈ destinations := by rw [wordEq]; exact safe original
      obtain ⟨hc, ht⟩ := safe_jumpi_boundary image frame m s c tail hs entry target member bound address_eq hd hp hj
      rw [hc] at source
      cases source
      exact ht

end Solidity.Evm.External.Assembly
