import SolidityBridge.ExternalEvm.Assembly.Control

/-!
A divergence control on the actual fetched upstream step relation. The
constant-true core loop has arbitrarily long positive-length target prefixes.
This is not a success/divergence theorem for the finite-fuel, gas-checking X
driver, nor a general structured-loop compiler theorem.
-/
namespace Solidity.Evm.External.Assembly

/-- Counted fetched executions. Fuel is positive at every dispatcher step;
there is no assertion that the finite-fuel driver runs forever. -/
def fetchedSteps : Nat → EvmYul.EVM.State →
    Except EvmYul.EVM.ExecutionException EvmYul.EVM.State
  | 0, s => .ok s
  | n + 1, s => do
    let t ← EvmYul.EVM.step 1 0 none s
    fetchedSteps n t

theorem fetchedSteps_add (n k : Nat) (s : EvmYul.EVM.State) :
    fetchedSteps (n + k) s = (do
      let t ← fetchedSteps n s
      fetchedSteps k t) := by
  induction n generalizing s with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ n ih =>
    simp only [Nat.succ_add, fetchedSteps]
    cases EvmYul.EVM.step 1 0 none s with
    | error e => rfl
    | ok t => exact ih t

def trueLoopBytes : List UInt8 :=
  [0x5b, 0x5b] ++ push32 ⟨1, by decide⟩ ++ [0x5b, 0x15] ++
  push32 ⟨106, by decide⟩ ++ [0x57, 0x5b] ++ push32 ⟨0, by decide⟩ ++ [0x56, 0x5b]

theorem trueLoop_emitted : emit [.loop [.push w[1]] []] 0 = some trueLoopBytes := by
  simp only [emit.eq_def, emitInstr.eq_def, span, width]
  rfl

/-- Place the standalone image at a genuine entry boundary. -/
def trueHeader (s : EvmYul.EVM.State) : EvmYul.EVM.State :=
  {s with
    pc := .ofNat 0
    executionEnv := {s.executionEnv with code := ⟨trueLoopBytes.toArray⟩}}

private theorem gas_sub_zero (v : EvmYul.UInt256) : v - .ofNat 0 = v := by
  cases v with
  | mk v =>
    apply congrArg EvmYul.UInt256.mk
    apply Fin.ext
    change ((EvmYul.UInt256.size - 0) + v.val) % EvmYul.UInt256.size = v.val
    simp only [Nat.sub_zero, Nat.add_mod, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt v.isLt]

private def point (s : EvmYul.EVM.State) (pc count : Nat)
    (stack : List EvmYul.UInt256) : EvmYul.EVM.State :=
  {trueHeader s with
    pc := .ofNat pc
    stack := stack
    execLength := s.execLength + count}

local instance : DecidableEq EvmYul.UInt256
  | ⟨a⟩, ⟨b⟩ =>
    if h : a = b then .isTrue (congrArg EvmYul.UInt256.mk h)
    else .isFalse (fun hEq => h (congrArg EvmYul.UInt256.val hEq))

private theorem decode_0 :
    EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 0) =
      some (.JUMPDEST, none) := by decide +kernel

private theorem decode_1 :
    EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 1) =
      some (.JUMPDEST, none) := by decide +kernel

private theorem decode_2 :
    EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 2) =
      some (.Push .PUSH32, some (.ofNat 1, 32)) := by decide +kernel

private theorem decode_3 :
    EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 35) =
      some (.JUMPDEST, none) := by decide +kernel

private theorem decode_4 :
    EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 36) =
      some (.ISZERO, none) := by decide +kernel

private theorem decode_5 :
    EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 37) =
      some (.Push .PUSH32, some (.ofNat 106, 32)) := by decide +kernel

private theorem decode_6 :
    EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 70) =
      some (.JUMPI, none) := by decide +kernel

private theorem decode_7 :
    EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 71) =
      some (.JUMPDEST, none) := by decide +kernel

private theorem decode_8 :
    EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 72) =
      some (.Push .PUSH32, some (.ofNat 0, 32)) := by decide +kernel

private theorem decode_9 :
    EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 105) =
      some (.JUMP, none) := by decide +kernel

private theorem cycle_0 (s : EvmYul.EVM.State) :
    EvmYul.EVM.step 1 0 none (point s 0 0 (s.stack)) = .ok (point s 1 1 (s.stack)) := by
  have hf : Fetches (point s 0 0 (s.stack)) (.JUMPDEST, none) := by
    change (EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 0)).option
      (.error .StackUnderflow) Except.ok = _
    rw [decode_0]
    rfl
  rw [fetched_step 0 _ _ hf]
  change EvmYul.step (τ := .EVM) (.JUMPDEST) (none) (prepare (point s 0 0 (s.stack))) = _
  simp only [prepare, gas_sub_zero]
  rfl

private theorem cycle_1 (s : EvmYul.EVM.State) :
    EvmYul.EVM.step 1 0 none (point s 1 1 (s.stack)) = .ok (point s 2 2 (s.stack)) := by
  have hf : Fetches (point s 1 1 (s.stack)) (.JUMPDEST, none) := by
    change (EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 1)).option
      (.error .StackUnderflow) Except.ok = _
    rw [decode_1]
    rfl
  rw [fetched_step 0 _ _ hf]
  change EvmYul.step (τ := .EVM) (.JUMPDEST) (none) (prepare (point s 1 1 (s.stack))) = _
  simp only [prepare, gas_sub_zero]
  rfl

private theorem cycle_2 (s : EvmYul.EVM.State) :
    EvmYul.EVM.step 1 0 none (point s 2 2 (s.stack)) = .ok (point s 35 3 ((.ofNat 1 :: s.stack))) := by
  have hf : Fetches (point s 2 2 (s.stack)) (.Push .PUSH32, some (.ofNat 1, 32)) := by
    change (EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 2)).option
      (.error .StackUnderflow) Except.ok = _
    rw [decode_2]
    rfl
  rw [fetched_step 0 _ _ hf]
  change EvmYul.step (τ := .EVM) (.Push .PUSH32) (some (.ofNat 1, 32)) (prepare (point s 2 2 (s.stack))) = _
  simp only [prepare, gas_sub_zero]
  rfl

private theorem cycle_3 (s : EvmYul.EVM.State) :
    EvmYul.EVM.step 1 0 none (point s 35 3 ((.ofNat 1 :: s.stack))) = .ok (point s 36 4 ((.ofNat 1 :: s.stack))) := by
  have hf : Fetches (point s 35 3 ((.ofNat 1 :: s.stack))) (.JUMPDEST, none) := by
    change (EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 35)).option
      (.error .StackUnderflow) Except.ok = _
    rw [decode_3]
    rfl
  rw [fetched_step 0 _ _ hf]
  change EvmYul.step (τ := .EVM) (.JUMPDEST) (none) (prepare (point s 35 3 ((.ofNat 1 :: s.stack)))) = _
  simp only [prepare, gas_sub_zero]
  rfl

private theorem cycle_4 (s : EvmYul.EVM.State) :
    EvmYul.EVM.step 1 0 none (point s 36 4 ((.ofNat 1 :: s.stack))) = .ok (point s 37 5 ((.ofNat 0 :: s.stack))) := by
  have hf : Fetches (point s 36 4 ((.ofNat 1 :: s.stack))) (.ISZERO, none) := by
    change (EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 36)).option
      (.error .StackUnderflow) Except.ok = _
    rw [decode_4]
    rfl
  rw [fetched_step 0 _ _ hf]
  change EvmYul.step (τ := .EVM) (.ISZERO) (none) (prepare (point s 36 4 ((.ofNat 1 :: s.stack)))) = _
  simp only [prepare, gas_sub_zero]
  rfl

private theorem cycle_5 (s : EvmYul.EVM.State) :
    EvmYul.EVM.step 1 0 none (point s 37 5 ((.ofNat 0 :: s.stack))) = .ok (point s 70 6 ([.ofNat 106, .ofNat 0] ++ s.stack)) := by
  have hf : Fetches (point s 37 5 ((.ofNat 0 :: s.stack))) (.Push .PUSH32, some (.ofNat 106, 32)) := by
    change (EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 37)).option
      (.error .StackUnderflow) Except.ok = _
    rw [decode_5]
    rfl
  rw [fetched_step 0 _ _ hf]
  change EvmYul.step (τ := .EVM) (.Push .PUSH32) (some (.ofNat 106, 32)) (prepare (point s 37 5 ((.ofNat 0 :: s.stack)))) = _
  simp only [prepare, gas_sub_zero]
  rfl

private theorem cycle_6 (s : EvmYul.EVM.State) :
    EvmYul.EVM.step 1 0 none (point s 70 6 ([.ofNat 106, .ofNat 0] ++ s.stack)) = .ok (point s 71 7 (s.stack)) := by
  have hf : Fetches (point s 70 6 ([.ofNat 106, .ofNat 0] ++ s.stack)) (.JUMPI, none) := by
    change (EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 70)).option
      (.error .StackUnderflow) Except.ok = _
    rw [decode_6]
    rfl
  rw [fetched_step 0 _ _ hf]
  change EvmYul.step (τ := .EVM) (.JUMPI) (none) (prepare (point s 70 6 ([.ofNat 106, .ofNat 0] ++ s.stack))) = _
  simp only [prepare, gas_sub_zero]
  rfl

private theorem cycle_7 (s : EvmYul.EVM.State) :
    EvmYul.EVM.step 1 0 none (point s 71 7 (s.stack)) = .ok (point s 72 8 (s.stack)) := by
  have hf : Fetches (point s 71 7 (s.stack)) (.JUMPDEST, none) := by
    change (EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 71)).option
      (.error .StackUnderflow) Except.ok = _
    rw [decode_7]
    rfl
  rw [fetched_step 0 _ _ hf]
  change EvmYul.step (τ := .EVM) (.JUMPDEST) (none) (prepare (point s 71 7 (s.stack))) = _
  simp only [prepare, gas_sub_zero]
  rfl

private theorem cycle_8 (s : EvmYul.EVM.State) :
    EvmYul.EVM.step 1 0 none (point s 72 8 (s.stack)) = .ok (point s 105 9 ((.ofNat 0 :: s.stack))) := by
  have hf : Fetches (point s 72 8 (s.stack)) (.Push .PUSH32, some (.ofNat 0, 32)) := by
    change (EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 72)).option
      (.error .StackUnderflow) Except.ok = _
    rw [decode_8]
    rfl
  rw [fetched_step 0 _ _ hf]
  change EvmYul.step (τ := .EVM) (.Push .PUSH32) (some (.ofNat 0, 32)) (prepare (point s 72 8 (s.stack))) = _
  simp only [prepare, gas_sub_zero]
  rfl

private theorem cycle_9 (s : EvmYul.EVM.State) :
    EvmYul.EVM.step 1 0 none (point s 105 9 ((.ofNat 0 :: s.stack))) = .ok (point s 0 10 (s.stack)) := by
  have hf : Fetches (point s 105 9 ((.ofNat 0 :: s.stack))) (.JUMP, none) := by
    change (EvmYul.EVM.decode ⟨trueLoopBytes.toArray⟩ (.ofNat 105)).option
      (.error .StackUnderflow) Except.ok = _
    rw [decode_9]
    rfl
  rw [fetched_step 0 _ _ hf]
  change EvmYul.step (τ := .EVM) (.JUMP) (none) (prepare (point s 105 9 ((.ofNat 0 :: s.stack)))) = _
  simp only [prepare, gas_sub_zero]
  rfl

private theorem bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (do let t ← (Except.ok a : Except ε α); f t) = f a := rfl

/-- Ten actual fetched steps form one back edge, with explicit progress.
The separate step equations avoid exponential state reduction. -/
theorem trueLoop_cycle (s : EvmYul.EVM.State) :
    ∃ t, fetchedSteps 10 (trueHeader s) = .ok t ∧
      t.pc = .ofNat 0 ∧ t.stack = s.stack ∧
      t.executionEnv.code = ⟨trueLoopBytes.toArray⟩ ∧ t.toState = (trueHeader s).toState ∧
      t.execLength = s.execLength + 10 := by
  refine ⟨point s 0 10 s.stack, ?_, rfl, rfl, rfl, rfl, rfl⟩
  change fetchedSteps 10 (point s 0 0 s.stack) = _
  simp only [fetchedSteps, cycle_0, cycle_1, cycle_2, cycle_3, cycle_4,
    cycle_5, cycle_6, cycle_7, cycle_8, cycle_9, bind_ok]

theorem trueHeader_eq (s : EvmYul.EVM.State) (hp : s.pc = .ofNat 0)
    (hc : s.executionEnv.code = ⟨trueLoopBytes.toArray⟩) : trueHeader s = s := by
  unfold trueHeader
  rw [← hp, ← hc]

/-- Every n-turn prefix exists on actual fetched dispatcher steps. The
factor ten is the emitted cycle length, not a raised search/fuel bound. -/
theorem trueLoop_prefixes (n : Nat) (s : EvmYul.EVM.State) :
    ∃ t, fetchedSteps (10 * n) (trueHeader s) = .ok t ∧
      t.pc = .ofNat 0 ∧ t.stack = s.stack ∧
      t.executionEnv.code = ⟨trueLoopBytes.toArray⟩ := by
  induction n generalizing s with
  | zero => exact ⟨trueHeader s, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨t, ht, hp, hs, hc⟩ := ih s
    obtain ⟨u, hu, hpu, hsu, hcu, _, _⟩ := trueLoop_cycle t
    rw [trueHeader_eq t hp hc] at hu
    refine ⟨u, ?_, hpu, hsu.trans hs, hcu⟩
    rw [Nat.mul_succ, fetchedSteps_add, ht]
    exact hu

/-- The corresponding core loop never finishes a turn with an outcome. -/
theorem trueLoop_core (m : Machine) : (Instr.loop [.push w[1]] []).step m = .fault := by
  apply loopRun_of_forall
  intro n
  refine ⟨m, ?_⟩
  induction n with
  | zero => rfl
  | succ n ih => exact ih

end Solidity.Evm.External.Assembly
