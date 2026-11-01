import SolidityBridge.ExternalEvm.Assembly.Structured

namespace Solidity.Evm.External.Assembly.StackLoop

/-- This loop consumes input conditions; it is not a constant guard loop. -/
def code : List Instr := [.loop [] []]
def bytes : List UInt8 := [0x5b, 0x5b, 0x15] ++ push32 ⟨72, by decide⟩ ++
  [0x57, 0x5b] ++ push32 ⟨0, by decide⟩ ++ [0x56, 0x5b]
def image : Image code 0 where
  bytes := bytes
  size := 72
  span_eq := rfl
  emitted := by simp only [code, emit.eq_def, emitInstr.eq_def, span, width]; rfl
  length_eq := by decide +kernel
  fits := by decide
  destinations := by
    intro l
    have hl : l.val = 0 ∨ l.val = 1 := by have h := l.isLt; change l.val < 2 at h; omega
    rcases hl with h | h
    · refine ⟨0, ?_, rfl⟩
      simp only [address, h]
      rfl
    · refine ⟨72, ?_, rfl⟩
      simp only [address, h]
      rfl
  refs := [0, 72]
  targets_eq := by simp only [code, targets.eq_def, instrTargets.eq_def, span, width]; rfl
  validRefs := by decide +kernel

def emptyImage (base : Fin W) : Image [] base.val where
  bytes := [0x5b]
  size := 0
  span_eq := rfl
  emitted := by rw [emit.eq_def]
  length_eq := rfl
  fits := base.isLt
  destinations := by
    intro l
    have h : l.val = 0 := by have hl := l.isLt; change l.val < 1 at hl; omega
    refine ⟨base.val, ?_, ?_⟩
    · simp only [address, h, List.take_zero, span, Option.map_some, Nat.add_zero]
    · simp only [Nat.sub_self, List.getElem?_cons_zero]
  refs := []
  targets_eq := by rw [targets.eq_def]
  validRefs := by intro n hn; cases hn

def ambient : ByteArray := ⟨(bytes ++ [0x00]).toArray⟩
def initial (stack : List EvmYul.UInt256) : EvmYul.EVM.State :=
  {(default : EvmYul.EVM.State) with
    pc := .ofNat 0
    stack := stack
    executionEnv := {(default : EvmYul.ExecutionEnv .EVM) with code := ambient}}

local instance : DecidableEq EvmYul.UInt256
  | ⟨a⟩, ⟨b⟩ => if h : a = b then .isTrue (congrArg EvmYul.UInt256.mk h)
    else .isFalse (fun he => h (congrArg EvmYul.UInt256.val he))

private theorem d0 : EvmYul.EVM.decode ambient (.ofNat 0) = some (.JUMPDEST, none) := by decide +kernel
private theorem d1 : EvmYul.EVM.decode ambient (.ofNat 1) = some (.JUMPDEST, none) := by decide +kernel
private theorem d2 : EvmYul.EVM.decode ambient (.ofNat 2) = some (.ISZERO, none) := by decide +kernel
private theorem d3 : EvmYul.EVM.decode ambient (.ofNat 3) =
    some (.Push .PUSH32, some (.ofNat 72, 32)) := by decide +kernel
private theorem d36 : EvmYul.EVM.decode ambient (.ofNat 36) = some (.JUMPI, none) := by decide +kernel
private theorem d37 : EvmYul.EVM.decode ambient (.ofNat 37) = some (.JUMPDEST, none) := by decide +kernel
private theorem d38 : EvmYul.EVM.decode ambient (.ofNat 38) =
    some (.Push .PUSH32, some (.ofNat 0, 32)) := by decide +kernel
private theorem d71 : EvmYul.EVM.decode ambient (.ofNat 71) = some (.JUMP, none) := by decide +kernel

private theorem fetch (s : EvmYul.EVM.State) (n : Nat) (packet : Packet)
    (hc : s.executionEnv.code = ambient) (hp : s.pc = .ofNat n)
    (hd : EvmYul.EVM.decode ambient (.ofNat n) = some packet) : Fetches s packet := by
  unfold Fetches EvmYul.EVM.fetchInstr
  rw [hc, hp, hd]
  rfl
private theorem pc_eq (s : EvmYul.EVM.State) (n : Fin W) (h : s.pc.toNat = n.val) :
    s.pc = .ofNat n.val := by
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  change s.pc.toNat = n.val % W
  rw [h, Nat.mod_eq_of_lt n.isLt]
private theorem env_eq {frame s : EvmYul.EVM.State} (h : s.toState = frame.toState)
    (hc : frame.executionEnv.code = ambient) : s.executionEnv.code = ambient :=
  (congrArg (fun x : EvmYul.State .EVM => x.executionEnv.code) h).trans hc

/-- Inhabited decoder/address premises for the general loop theorem. -/
theorem layout (frame : EvmYul.EVM.State) (hc : frame.executionEnv.code = ambient) :
    LoopLayout (origin := 0) image (emptyImage ⟨1, by decide⟩)
      (emptyImage ⟨37, by decide⟩) frame ⟨0, by decide⟩ ⟨72, by decide⟩ where
  shape := rfl
  headerBound := by decide
  exitBound := by decide
  headerAddress := rfl
  enter := by
    intro m s he
    have pc : s.pc = .ofNat 0 := pc_eq s ⟨0, by decide⟩ (Option.some.inj he.pc).symm
    refine ⟨fetch s 0 _ (env_eq he.state hc) pc d0, ?_⟩
    change some 1 = some (s.pc + .ofNat 1).toNat
    rw [pc]
    rfl
  guard := by
    intro mc s w tail rest he hs hr
    have pc : s.pc = .ofNat 1 := pc_eq s ⟨1, by decide⟩ (Option.some.inj he.pc).symm
    have env := env_eq he.state hc
    refine ⟨fetch s 1 _ env pc d1, ?_, ?_, ?_⟩
    · apply fetch (destState s) 2 _ (show (destState s).executionEnv.code = ambient from env) _ d2
      change s.pc + .ofNat 1 = .ofNat 2
      rw [pc]
      rfl
    · apply fetch (iszeroState s (.ofNat w.val) rest) 3 _
        (show (iszeroState s (.ofNat w.val) rest).executionEnv.code = ambient from env) _ d3
      change (s.pc + .ofNat 1) + .ofNat 1 = .ofNat 3
      rw [pc]
      rfl
    · apply fetch (pushState (iszeroState s (.ofNat w.val) rest) (.ofNat 72)) 36 _
        (show (pushState (iszeroState s (.ofNat w.val) rest) (.ofNat 72)).executionEnv.code = ambient from env) _ d36
      change ((s.pc + .ofNat 1) + .ofNat 1) + .ofNat 33 = .ofNat 36
      rw [pc]
      rfl
  zeroAddress := by
    intro mc s w tail rest he hs hr hz
    change some 72 = some (if EvmYul.UInt256.isZero (.ofNat w.val) != ⟨0⟩ then
      EvmYul.UInt256.ofNat 72 else (((s.pc + .ofNat 1) + .ofNat 1) + .ofNat 33) + .ofNat 1).toNat
    rw [hz]
    rfl
  nonzeroAddress := by
    intro mc s w tail rest he hs hr hn
    have pc : s.pc = .ofNat 1 := pc_eq s ⟨1, by decide⟩ (Option.some.inj he.pc).symm
    have hv : (EvmYul.UInt256.ofNat w.val).toNat = w.val := Nat.mod_eq_of_lt w.isLt
    have hz : EvmYul.UInt256.isZero (.ofNat w.val) = .ofNat 0 := by
      simp only [EvmYul.UInt256.isZero, EvmYul.UInt256.eq0, condition_beq, hv, hn, decide_false]
      rfl
    change some 37 = some (if EvmYul.UInt256.isZero (.ofNat w.val) != ⟨0⟩ then
      EvmYul.UInt256.ofNat 72 else (((s.pc + .ofNat 1) + .ofNat 1) + .ofNat 33) + .ofNat 1).toNat
    rw [hz, pc]
    rfl
  back := by
    intro m s he
    have pc : s.pc = .ofNat 37 := pc_eq s ⟨37, by decide⟩ (Option.some.inj he.pc).symm
    have env := env_eq he.state hc
    refine ⟨fetch s 37 _ env pc d37, ?_, ?_⟩
    · apply fetch (destState s) 38 _ (show (destState s).executionEnv.code = ambient from env) _ d38
      change s.pc + .ofNat 1 = .ofNat 38
      rw [pc]
      rfl
    · apply fetch (pushState (destState s) (.ofNat 0)) 71 _
        (show (pushState (destState s) (.ofNat 0)).executionEnv.code = ambient from env) _ d71
      change (s.pc + .ofNat 1) + .ofNat 33 = .ofNat 71
      rw [pc]
      rfl

theorem empty_certificate (frame : EvmYul.EVM.State) (base : Fin W) :
    DecodedCode frame (emptyImage base) := by
  apply DecodedCode.intro
  intro pre i rest hc
  have h := congrArg List.length hc
  simp only [List.length_nil, List.length_append, List.length_cons] at h
  omega

theorem certificate (frame : EvmYul.EVM.State) (hc : frame.executionEnv.code = ambient) :
    DecodedCode frame image := by
  apply DecodedCode.intro
  intro pre i rest he
  have hl : pre.length = 0 := by
    have h := congrArg List.length he
    change 1 = (pre ++ i :: rest).length at h
    simp only [List.length_append, List.length_cons] at h
    omega
  have hp : pre = [] := List.length_eq_zero_iff.mp hl
  subst pre
  have hi : i = .loop [] [] := (List.cons.inj he).1.symm
  subst i
  exact DecodedSite.loop image _ _ _ _ (layout frame hc)
    (empty_certificate _ _) (empty_certificate _ _)

/-- Any finite list of nonzero conditions followed by zero terminates.
The number of turns varies with the inhabited input, not evaluator fuel. -/
theorem source_iterations (conditions : List (Fin W)) (tail : List Word)
    (hn : ∀ w ∈ conditions, w.val ≠ 0) :
    loopIterN (run []) (run []) (conditions.length + 1)
      {Machine.init with stack := conditions.map Word.val ++ w[0] :: tail} =
      .inr (.ok {Machine.init with stack := tail} 0) := by
  induction conditions with
  | nil => rfl
  | cons w rest ih =>
    have hw := hn w (List.mem_cons_self)
    have hr : ∀ v ∈ rest, v.val ≠ 0 := fun v hv => hn v (List.mem_cons_of_mem w hv)
    simp only [List.length_cons, List.map_cons, List.cons_append, loopIterN, loopTurn,
      run, exec, if_neg hw]
    exact ih hr

theorem simulation (conditions : List (Fin W)) (tail : List EvmYul.UInt256)
    (hn : ∀ w ∈ conditions, w.val ≠ 0) :
    ∃ n t, fetchedSteps n (initial (conditions.map (fun w => .ofNat w.val) ++ .ofNat 0 :: tail)) = .ok t ∧
      t.pc.toNat = 72 ∧ words t.stack = words tail ∧
      t.toState = (initial (conditions.map (fun w => .ofNat w.val) ++ .ofNat 0 :: tail)).toState := by
  let stack := conditions.map (fun w => EvmYul.UInt256.ofNat w.val) ++ .ofNat 0 :: tail
  let m := {Machine.init with stack := conditions.map Word.val ++ w[0] :: words tail}
  have hs : m.stack = words stack := by
    dsimp [m, stack]
    induction conditions with
    | nil => rfl
    | cons w rest ih =>
      simp only [List.map_cons, List.cons_append, words_ofNat]
      exact congrArg (List.cons (Word.val w)) (ih (fun v hv => hn v (List.mem_cons_of_mem w hv)))
  have source : run code m = .ok {Machine.init with stack := words tail} 0 := by
    have h : (Instr.loop [] []).step m = .ok {Machine.init with stack := words tail} 0 :=
      loopRun_of_iterN (source_iterations conditions (words tail) hn)
    change ((Instr.loop [] []).step m).bind (fun m k => exec [] k m) = _
    rw [h]
    rfl
  have entry : Boundary image (initial stack) 0 m (initial stack) := ⟨by decide, rfl, hs, rfl, rfl⟩
  obtain ⟨n, t, ht, he⟩ := certified_run_simulation image (initial stack) (certificate _ rfl)
    m _ (initial stack) entry source
  exact ⟨n, t, ht, (Option.some.inj he.pc).symm, he.stack.symm, he.state⟩

private def observe (r : Except EvmYul.EVM.ExecutionException EvmYul.EVM.State) :
    Option (Nat × List Nat) := match r with
  | .ok s => some (s.pc.toNat, s.stack.map EvmYul.UInt256.toNat)
  | .error _ => none
#guard observe (fetchedSteps 5 (initial [.ofNat 0, .ofNat 9])) = some (72, [9])
#guard observe (fetchedSteps 29 (initial [.ofNat 1, .ofNat 2, .ofNat (W - 1), .ofNat 0, .ofNat 9])) = some (72, [9])
#guard observe (fetchedSteps 3 (initial [])) = none
example : fetchedSteps 3 (initial []) = .error .StackUnderflow := rfl
#guard (EvmYul.EVM.D_J ambient (.ofNat 0)).map EvmYul.UInt256.toNat == #[0, 1, 37, 72]

end Solidity.Evm.External.Assembly.StackLoop

namespace Solidity.Evm.External.Assembly.StackLoop
example : (Instr.loop [] []).step Machine.init = .fault := loopRun_of_iterN (n := 1) rfl
end Solidity.Evm.External.Assembly.StackLoop

/-- info: 'Solidity.Evm.External.Assembly.StackLoop.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.StackLoop.certificate
/-- info: 'Solidity.Evm.External.Assembly.StackLoop.simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.StackLoop.simulation
