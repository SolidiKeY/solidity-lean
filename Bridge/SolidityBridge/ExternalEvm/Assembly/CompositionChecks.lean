import SolidityBridge.ExternalEvm.Assembly.Composition

namespace Solidity.Evm.External.Assembly.ComposedBranch

/-- A relocated conditional followed by two real continuations. -/
def code : List Instr := [.jumpi 1, .push w[7], .push w[9]]
def bytes : List UInt8 := [0x5b] ++ push32 ⟨74, by decide⟩ ++ [0x57, 0x5b] ++
  push32 ⟨7, by decide⟩ ++ [0x5b] ++ push32 ⟨9, by decide⟩ ++ [0x5b]

def image : Image code 5 where
  bytes := bytes
  size := 103
  span_eq := rfl
  emitted := by
    simp only [code, emit.eq_def, emitInstr.eq_def, width, resolve, address]
    rfl
  length_eq := by decide +kernel
  fits := by decide
  destinations := by
    have hd : ∀ l : Label code, (address code 5 l).any
        (fun n => bytes[n - 5]? == some 0x5b) = true := by decide +kernel
    intro l
    have hh := hd l
    cases ha : address code 5 l with
    | none => simp only [ha, Option.any_none, Bool.false_eq_true] at hh
    | some n =>
      refine ⟨n, rfl, ?_⟩
      simpa only [ha, Option.any_some, beq_iff_eq] using hh
  refs := [74]
  targets_eq := by
    simp only [code, targets.eq_def, instrTargets.eq_def, width, resolve, address]
    rfl
  validRefs := by decide +kernel

def ambient : ByteArray := ⟨(List.replicate 5 0x00 ++ bytes ++ [0x00]).toArray⟩
def initial (c : EvmYul.UInt256) (tail : List EvmYul.UInt256) : EvmYul.EVM.State :=
  {(default : EvmYul.EVM.State) with
    pc := .ofNat 5
    stack := c :: tail
    executionEnv := {(default : EvmYul.ExecutionEnv .EVM) with code := ambient}}

example : Placed image (initial (.ofNat 1) []) := by
  unfold Placed
  decide +kernel

local instance : DecidableEq EvmYul.UInt256
  | ⟨a⟩, ⟨b⟩ => if h : a = b then .isTrue (congrArg EvmYul.UInt256.mk h)
    else .isFalse (fun he => h (congrArg EvmYul.UInt256.val he))

private theorem d5 : EvmYul.EVM.decode ambient (.ofNat 5) = some (.JUMPDEST, none) := by decide +kernel
private theorem d6 : EvmYul.EVM.decode ambient (.ofNat 6) =
    some (.Push .PUSH32, some (.ofNat 74, 32)) := by decide +kernel
private theorem d39 : EvmYul.EVM.decode ambient (.ofNat 39) = some (.JUMPI, none) := by decide +kernel
private theorem d40 : EvmYul.EVM.decode ambient (.ofNat 40) = some (.JUMPDEST, none) := by decide +kernel
private theorem d41 : EvmYul.EVM.decode ambient (.ofNat 41) =
    some (.Push .PUSH32, some (.ofNat 7, 32)) := by decide +kernel
private theorem d74 : EvmYul.EVM.decode ambient (.ofNat 74) = some (.JUMPDEST, none) := by decide +kernel
private theorem d75 : EvmYul.EVM.decode ambient (.ofNat 75) =
    some (.Push .PUSH32, some (.ofNat 9, 32)) := by decide +kernel

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

/-- All arithmetic/decoder assumptions are inhabited for a real relocated
image. This is universal over the input condition, stack tail and frame. -/
theorem decoded (frame : EvmYul.EVM.State) (hc : frame.executionEnv.code = ambient)
    (pre : List Instr) (i : Instr) (rest : List Instr) (he : code = pre ++ i :: rest)
    (m : Machine) (s : EvmYul.EVM.State) (entry : Boundary image frame pre.length m s) :
    PrimitiveLayout image pre.length i s := by
  have hi : code[pre.length]? = some i := by rw [he]; simp only [List.getElem?_append_right, le_refl, Nat.sub_self, List.getElem?_cons_zero]
  have hl : pre.length < 3 := by
    have h := congrArg List.length he
    simp only [code, List.length_cons, List.length_nil, List.length_append] at h
    omega
  have env : s.executionEnv.code = ambient :=
    (congrArg (fun x : EvmYul.State .EVM => x.executionEnv.code) entry.state).trans hc
  have indices : pre.length = 0 ∨ pre.length = 1 ∨ pre.length = 2 := by omega
  rcases indices with h | h | h
  · have hii : i = .jumpi 1 := by simpa only [h, code, List.getElem?_cons_zero, Option.some.injEq] using hi.symm
    subst i
    have pc : s.pc = .ofNat 5 := pc_eq s ⟨5, by decide⟩ (by
      have hp := entry.pc
      change address code 5 ⟨pre.length, entry.inBounds⟩ = some s.pc.toNat at hp
      simp only [h] at hp
      exact (Option.some.inj hp).symm)
    refine ⟨fetch s 5 _ env pc d5, ?_⟩
    intro c tail hs
    refine ⟨⟨74, by decide⟩, by rw [h]; split <;> decide, ?_, ?_, ?_⟩
    · by_cases hz : c.toNat = 0
      · simp only [hz, if_true, h]
        change some 40 = some (if c != ⟨0⟩ then EvmYul.UInt256.ofNat 74 else
          ((s.pc + ⟨1⟩) + .ofNat 33) + ⟨1⟩).toNat
        simp only [bne, condition_beq, hz, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
        rw [pc]
        rfl
      · simp only [hz, if_false, h]
        change some 74 = some (if c != ⟨0⟩ then EvmYul.UInt256.ofNat 74 else
          ((s.pc + ⟨1⟩) + .ofNat 33) + ⟨1⟩).toNat
        simp only [bne, condition_beq, hz, decide_false, Bool.not_false, if_true]
        rfl
    · apply fetch (destState s) 6 _ (show (destState s).executionEnv.code = ambient from env) _ d6
      change s.pc + ⟨1⟩ = .ofNat 6
      rw [pc]
      rfl
    · apply fetch (pushState (destState s) (.ofNat 74)) 39 _
        (show (pushState (destState s) (.ofNat 74)).executionEnv.code = ambient from env) _ d39
      change (s.pc + ⟨1⟩) + .ofNat 33 = .ofNat 39
      rw [pc]
      rfl
  · have hii : i = .push w[7] := by simpa only [h, code, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] using hi.symm
    subst i
    have pc : s.pc = .ofNat 40 := pc_eq s ⟨40, by decide⟩ (by
      have hp := entry.pc
      simp only [h] at hp
      exact (Option.some.inj hp).symm)
    refine ⟨fetch s 40 _ env pc d40, by rw [h]; decide, ?_, ?_⟩
    · simp only [h]
      change some 74 = some ((s.pc + ⟨1⟩) + .ofNat 33).toNat
      rw [pc]
      rfl
    · apply fetch (destState s) 41 _ (show (destState s).executionEnv.code = ambient from env) _ d41
      change s.pc + ⟨1⟩ = .ofNat 41
      rw [pc]
      rfl
  · have hii : i = .push w[9] := by simpa only [h, code, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] using hi.symm
    subst i
    have pc : s.pc = .ofNat 74 := pc_eq s ⟨74, by decide⟩ (by
      have hp := entry.pc
      simp only [h] at hp
      exact (Option.some.inj hp).symm)
    refine ⟨fetch s 74 _ env pc d74, by rw [h]; decide, ?_, ?_⟩
    · simp only [h]
      change some 108 = some ((s.pc + ⟨1⟩) + .ofNat 33).toNat
      rw [pc]
      rfl
    · apply fetch (destState s) 75 _ (show (destState s).executionEnv.code = ambient from env) _ d75
      change s.pc + ⟨1⟩ = .ofNat 75
      rw [pc]
      rfl

/-- A genuinely composed branch: conditional, skipped/retained PUSH7,
and common PUSH9, for every numeric input condition and stack tail. -/
theorem simulation (c : EvmYul.UInt256) (tail : List EvmYul.UInt256) :
    ∃ n t, fetchedSteps n (initial c tail) = .ok t ∧ t.pc.toNat = 108 ∧
      words t.stack = .val ⟨9, by decide⟩ ::
        (if c.toNat = 0 then .val ⟨7, by decide⟩ :: words tail else words tail) ∧
      t.toState = (initial c tail).toState ∧ t.memory = (initial c tail).memory := by
  let m := {Machine.init with stack := words (c :: tail)}
  let out := {Machine.init with stack := .val ⟨9, by decide⟩ ::
    (if c.toNat = 0 then .val ⟨7, by decide⟩ :: words tail else words tail)}
  have source : run code m = .ok out 0 := by
    by_cases hz : c.toNat = 0
    · simp only [run, code, exec, Instr.step, m, out, words, List.map_cons, hz,
        if_true, Out.bind, Machine.next]
    · simp only [run, code, exec, Instr.step, m, out, words, List.map_cons, hz,
        if_false, Out.bind, Machine.next]
  have entry : Boundary image (initial c tail) 0 m (initial c tail) :=
    ⟨by decide, rfl, rfl, rfl, rfl⟩
  obtain ⟨n, t, ht, hb⟩ := decoded_run_simulation image (initial c tail)
    (decoded _ rfl) m out (initial c tail) entry source
  refine ⟨n, t, ht, ?_, hb.stack.symm, hb.state, hb.memory⟩
  exact (Option.some.inj hb.pc).symm

end Solidity.Evm.External.Assembly.ComposedBranch

namespace Solidity.Evm.External.Assembly.ComposedBranch
private def observation (r : Except EvmYul.EVM.ExecutionException EvmYul.EVM.State) :
    Option (Nat × List Nat) := match r with
  | .ok s => some (s.pc.toNat, s.stack.map EvmYul.UInt256.toNat)
  | .error _ => none
#guard observation (fetchedSteps 5 (initial (.ofNat 1) [])) = some (108, [9])
#guard observation (fetchedSteps 7 (initial (.ofNat 0) [])) = some (108, [9, 7])
example : run code {Machine.init with stack := [w[1]]} =
    .ok {Machine.init with stack := [w[9]]} 0 := rfl
example : run code {Machine.init with stack := [w[0]]} =
    .ok {Machine.init with stack := [w[9], w[7]]} 0 := rfl
#guard (EvmYul.EVM.D_J ambient (.ofNat 0)).map EvmYul.UInt256.toNat == #[5, 40, 74, 108]
private def success (r : Except EvmYul.EVM.ExecutionException
    (EvmYul.EVM.ExecutionResult EvmYul.EVM.State)) : Bool := match r with
  | .ok (.success _ _) => true
  | _ => false
private def badJump (r : Except EvmYul.EVM.ExecutionException
    (EvmYul.EVM.ExecutionResult EvmYul.EVM.State)) : Bool := match r with
  | .error .BadJumpDestination => true
  | _ => false
#guard success (EvmYul.EVM.X 10 (EvmYul.EVM.D_J ambient (.ofNat 0))
  {(initial (.ofNat 1) []) with gasAvailable := .ofNat 10000})
#guard badJump (EvmYul.EVM.X 10 #[]
  {(initial (.ofNat 1) []) with gasAvailable := .ofNat 10000})
end Solidity.Evm.External.Assembly.ComposedBranch

/-- info: 'Solidity.Evm.External.Assembly.ComposedBranch.simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.ComposedBranch.simulation

namespace Solidity.Evm.External.Assembly.MisalignedPrefix
-- A direct JUMPDEST decode is insufficient for scanner membership: the
-- preceding PUSH32 consumes this byte as immediate data.
private def bytes : ByteArray := ⟨(([0x7f, 0x5b] : List UInt8) ++ List.replicate 31 0x00).toArray⟩
example : EvmYul.EVM.decode bytes (.ofNat 1) = some (.JUMPDEST, none) := rfl
#guard (EvmYul.EVM.D_J bytes (.ofNat 0)).isEmpty
end Solidity.Evm.External.Assembly.MisalignedPrefix
