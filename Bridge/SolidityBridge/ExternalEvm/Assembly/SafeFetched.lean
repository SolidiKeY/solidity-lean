import SolidityBridge.ExternalEvm.Assembly.SafeTrace
namespace Solidity.Evm.External.Assembly
open EvmYul EvmYul.EVM

instance (destinations : List UInt256) (packet : Packet) (s : EVM.State) :
    Decidable (JumpSafe destinations packet s) := by
  unfold JumpSafe
  cases packet with
  | mk op arg => cases op <;> rename_i tag <;> cases tag <;> infer_instance

/-- Executable proof of opcode and destination safety for a finite fetched
prefix. It is separate from gas and from source/compiled simulation. -/
def SafeFetched (destinations : List UInt256) : Nat → EVM.State → Prop
  | 0, _ => True
  | n + 1, s => match EVM.decode s.executionEnv.code s.pc with
    | none => False
    | some packet => PurePacket packet ∧ JumpSafe destinations packet s ∧
      match EVM.step 1 0 (some packet) s with
      | .error _ => True
      | .ok next => SafeFetched destinations n next

def checkSafeFetched (destinations : List UInt256) : (n : Nat) → (s : EVM.State) →
    Option (PLift (SafeFetched destinations n s))
  | 0, _ => some ⟨trivial⟩
  | n + 1, s => match hd : EVM.decode s.executionEnv.code s.pc with
    | none => none
    | some packet => do
      let pure ← checkPure packet
      if safe : JumpSafe destinations packet s then
        match hs : EVM.step 1 0 (some packet) s with
        | .error _ => return ⟨by simp only [SafeFetched, hd, hs]; exact ⟨pure.down, safe, trivial⟩⟩
        | .ok next => do
          let tail ← checkSafeFetched destinations n next
          return ⟨by simp only [SafeFetched, hd, hs]; exact ⟨pure.down, safe, tail.down⟩⟩
      else none

theorem SafeFetched.trace {destinations : List UInt256} {n : Nat} {s t : EVM.State}
    (checked : SafeFetched destinations n s) (run : fetchedSteps n s = .ok t) :
    SafeTrace destinations n s t := by
  induction n generalizing s with
  | zero => cases run; exact .nil _
  | succ n ih =>
    simp only [SafeFetched] at checked
    cases hd : EVM.decode s.executionEnv.code s.pc with
    | none => simp only [hd] at checked
    | some packet =>
      rw [hd] at checked
      obtain ⟨pure, safe, rest⟩ := checked
      have fetch : Fetches s packet := by unfold Fetches EVM.fetchInstr; rw [hd]; rfl
      simp only [fetchedSteps] at run
      rw [fetched_step 0 _ _ fetch] at run
      cases hs : EVM.step 1 0 (some packet) s with
      | error e => simp only [hs, bind, Except.bind] at run; cases run
      | ok next =>
        rw [hs] at rest
        have head : EVM.step 1 0 none s = .ok next := by rw [fetched_step 0 _ _ fetch]; exact hs
        exact .cons packet fetch pure safe head (ih rest (by simpa only [hs, bind, Except.bind] using run))

end Solidity.Evm.External.Assembly
