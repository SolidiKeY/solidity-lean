import SolidityBridge.ExternalEvm.OutcomeDriver

/-! Actual one-step residual equations for the TWO original source PUSH
instructions only. No variable-width assembly or byte-memory framework. -/
namespace EvmYul.EVM.DriverProof

def legacy_push4_next (s : State) : State :=
  ({s with
    execLength := s.execLength + 1
    gasAvailable := s.gasAvailable - UInt256.ofNat 3}).replaceStackAndIncrPC
      (UInt256.ofNat 3735928559 :: s.stack) (pcΔ := 5)

theorem legacy_push4_step (fuel : Nat) (s : State) :
    step (fuel + 1) 3 (some ((.Push .PUSH4), some (.ofNat 3735928559, 4))) s =
      .ok (legacy_push4_next s) := by rfl

/-- Guard faults precede the actual evaluator's exhausted-fuel fault. -/
theorem legacy_push4_one_fuel (dest : Array UInt256) (s : State)
    (hf : fetched s = ((.Push .PUSH4), some (.ofNat 3735928559, 4))) :
    X 1 dest s =
      (if s.gasAvailable.toNat < 3 then .error .OutOfGass
       else if s.stack.length + 1 > 1024 then .error .StackOverflow
       else .error .OutOfFuel) := by
  rw [X_unfold, legacy_push4_checks dest s hf]
  by_cases hg : s.gasAvailable.toNat < 3
  · simp only [hg, if_true]
  · by_cases hs : s.stack.length + 1 > 1024
    · simp only [hg, hs, if_false, if_true]
    · simp only [hg, hs, if_false, Bind.bind, Except.bind]
      rfl

/-- Complete next-instruction state, including the full original stack tail. -/
theorem legacy_push4_iteration (fuel : Nat) (dest : Array UInt256) (s : State)
    (hf : fetched s = ((.Push .PUSH4), some (.ofNat 3735928559, 4))) :
    X (fuel + 2) dest s =
      (if s.gasAvailable.toNat < 3 then .error .OutOfGass
       else if s.stack.length + 1 > 1024 then .error .StackOverflow
       else X (fuel + 1) dest (legacy_push4_next s)) := by
  rw [X_unfold, legacy_push4_checks dest s hf]
  by_cases hg : s.gasAvailable.toNat < 3
  · simp only [hg, if_true]
  · by_cases hs : s.stack.length + 1 > 1024
    · simp only [hg, hs, if_false, if_true]
    · simp only [hg, hs, if_false, Bind.bind, Except.bind, hf, legacy_push4_step]
      rfl

#print axioms legacy_push4_step
#print axioms legacy_push4_one_fuel
#print axioms legacy_push4_iteration

def viaIR_push1_next (s : State) : State :=
  ({s with
    execLength := s.execLength + 1
    gasAvailable := s.gasAvailable - UInt256.ofNat 3}).replaceStackAndIncrPC
      (UInt256.ofNat 32 :: s.stack) (pcΔ := 2)

theorem viaIR_push1_step (fuel : Nat) (s : State) :
    step (fuel + 1) 3 (some ((.Push .PUSH1), some (.ofNat 32, 1))) s =
      .ok (viaIR_push1_next s) := by rfl

/-- Guard faults precede the actual evaluator's exhausted-fuel fault. -/
theorem viaIR_push1_one_fuel (dest : Array UInt256) (s : State)
    (hf : fetched s = ((.Push .PUSH1), some (.ofNat 32, 1))) :
    X 1 dest s =
      (if s.gasAvailable.toNat < 3 then .error .OutOfGass
       else if s.stack.length + 1 > 1024 then .error .StackOverflow
       else .error .OutOfFuel) := by
  rw [X_unfold, viaIR_push1_checks dest s hf]
  by_cases hg : s.gasAvailable.toNat < 3
  · simp only [hg, if_true]
  · by_cases hs : s.stack.length + 1 > 1024
    · simp only [hg, hs, if_false, if_true]
    · simp only [hg, hs, if_false, Bind.bind, Except.bind]
      rfl

/-- Complete next-instruction state, including the full original stack tail. -/
theorem viaIR_push1_iteration (fuel : Nat) (dest : Array UInt256) (s : State)
    (hf : fetched s = ((.Push .PUSH1), some (.ofNat 32, 1))) :
    X (fuel + 2) dest s =
      (if s.gasAvailable.toNat < 3 then .error .OutOfGass
       else if s.stack.length + 1 > 1024 then .error .StackOverflow
       else X (fuel + 1) dest (viaIR_push1_next s)) := by
  rw [X_unfold, viaIR_push1_checks dest s hf]
  by_cases hg : s.gasAvailable.toNat < 3
  · simp only [hg, if_true]
  · by_cases hs : s.stack.length + 1 > 1024
    · simp only [hg, hs, if_false, if_true]
    · simp only [hg, hs, if_false, Bind.bind, Except.bind, hf, viaIR_push1_step]
      rfl

#print axioms viaIR_push1_step
#print axioms viaIR_push1_one_fuel
#print axioms viaIR_push1_iteration

end EvmYul.EVM.DriverProof
