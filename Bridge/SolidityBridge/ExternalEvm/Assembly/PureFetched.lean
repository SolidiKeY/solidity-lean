import SolidityBridge.ExternalEvm.Assembly.Driver
namespace Solidity.Evm.External.Assembly
open EvmYul EvmYul.EVM

/-- Pure decoded packets along a counted fetched prefix. Success is not a
premise: step errors remain admissible and are handled by the consuming trace. -/
def PureFetched : Nat → EVM.State → Prop
  | 0, _ => True
  | n + 1, s => match EVM.decode s.executionEnv.code s.pc with
    | none => False
    | some packet => PurePacket packet ∧ match EVM.step 1 0 (some packet) s with
      | .error _ => True
      | .ok next => PureFetched n next

def checkPureFetched : (n : Nat) → (s : EVM.State) → Option (PLift (PureFetched n s))
  | 0, _ => some ⟨trivial⟩
  | n + 1, s => match hd : EVM.decode s.executionEnv.code s.pc with
    | none => none
    | some packet => do
      let pure ← checkPure packet
      match hs : EVM.step 1 0 (some packet) s with
      | .error _ => return ⟨by simp only [PureFetched, hd, hs]; exact ⟨pure.down, trivial⟩⟩
      | .ok next => do
        let tail ← checkPureFetched n next
        return ⟨by simp only [PureFetched, hd, hs]; exact ⟨pure.down, tail.down⟩⟩

private def frameView (s : EVM.State) := (s.toState, s.memory)

private theorem pure_frame_map (s : EVM.State) (packet : Packet) (pure : PurePacket packet) :
    (EVM.step 1 0 (some packet) s).map frameView =
      (EVM.step 1 0 (some packet) s).map (fun _ => frameView s) := by
  cases pure with
  | dest => rfl
  | push w => rfl
  | pop => cases s with | mk shared pc stack length => cases stack <;> rfl
  | zero => cases s with | mk shared pc stack length => cases stack <;> rfl
  | jump => cases s with | mk shared pc stack length => cases stack <;> rfl
  | jumpi =>
    cases s with
    | mk shared pc stack length =>
      cases stack with
      | nil => rfl
      | cons a rest => cases rest <;> rfl

theorem pure_step_frame (s t : EVM.State) (packet : Packet) (pure : PurePacket packet)
    (step : EVM.step 1 0 (some packet) s = .ok t) :
    t.toState = s.toState ∧ t.memory = s.memory := by
  have h := pure_frame_map s packet pure
  rw [step] at h
  have he := Except.ok.inj h
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

/-- Frame preservation is proved by prefix induction rather than reducing
the entire concrete EVM state repeatedly inside a closed witness. -/
theorem PureFetched.frame {n : Nat} {s t : EVM.State} (pure : PureFetched n s)
    (trace : fetchedSteps n s = .ok t) : t.toState = s.toState ∧ t.memory = s.memory := by
  induction n generalizing s with
  | zero => cases trace; exact ⟨rfl, rfl⟩
  | succ n ih =>
    simp only [PureFetched] at pure
    cases hd : EVM.decode s.executionEnv.code s.pc with
    | none => simp only [hd] at pure
    | some packet =>
      rw [hd] at pure
      have fetch : Fetches s packet := by unfold Fetches EVM.fetchInstr; rw [hd]; rfl
      simp only [fetchedSteps] at trace
      rw [fetched_step 0 s packet fetch] at trace
      cases hs : EVM.step 1 0 (some packet) s with
      | error e => simp only [hs, bind, Except.bind] at trace; cases trace
      | ok next =>
        obtain ⟨packetPure, restPure⟩ := pure
        rw [hs] at restPure
        have head := pure_step_frame s next packet packetPure hs
        have tail := ih restPure (by simpa only [hs, bind, Except.bind] using trace)
        exact ⟨tail.1.trans head.1, tail.2.trans head.2⟩

end Solidity.Evm.External.Assembly
