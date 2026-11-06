import SolidityBridge.HashBridge.ChargedGuard

/-! Actual fetched/charged KECCAK edge into direct query receipts. These proof
fields observe the existing X computation; they do not choose an outcome or
supply source installation, padded-byte, native, or nested-query completeness. -/
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

/-- One successful actual checked edge, followed by the unchanged X tail.
The effectful updates are exact, not an equality of whole pre/post states. -/
structure CheckedHashEdge (fuel : Nat) (dest : Array UInt256) (s : EVM.State)
    (offset size : UInt256) (tail : List UInt256) (next : EVM.State) : Prop where
  guard : hashGuard s = .ok ()
  checked : checks dest s = .ok (hashMemoryCharged s,hashOpcodeCost s)
  evaluated : step (fuel+1) (hashOpcodeCost s) (some (.KECCAK256,none))
    (hashMemoryCharged s) = .ok next
  recorded : ExplicitPrefix 1 (hashMemoryCharged s) next
    [byteQuery (machineQuery s.toMachineState offset size)]
  stack : next.stack = actualDigest (machineQuery s.toMachineState offset size) :: tail
  world : next.toState = s.toState
  memory : next.memory = s.memory
  activeWords : next.activeWords = .ofNat
    (MachineState.M s.activeWords.toNat offset.toNat size.toNat)
  gas : next.gasAvailable = (hashMemoryCharged s).gasAvailable - .ofNat (hashOpcodeCost s)
  pc : next.pc = s.pc + .ofNat 1
  execLength : next.execLength = s.execLength + 1
  returnData : next.returnData = s.returnData
  H_return : next.H_return = s.H_return
  continues : X (fuel+2) dest s = X (fuel+1) dest next

/-- Conditional local producer; the all-fuel client below discharges the guard
by its actual error/ok split. No desired next state or reply is a premise. -/
theorem checked_hash_edge (fuel : Nat) (dest : Array UInt256) (s : EVM.State)
    (offset size : UInt256) (tail : List UInt256)
    (hf : fetched s = (.KECCAK256,none)) (hs : s.stack = offset :: size :: tail)
    (hg : hashGuard s = .ok ()) : ∃ next, CheckedHashEdge fuel dest s offset size tail next := by
  have hc : checks dest s = .ok (hashMemoryCharged s,hashOpcodeCost s) := by
    rw [hash_checks dest s hf,hg]
    rfl
  have hstack : (hashMemoryCharged s).stack = offset :: size :: tail := hs
  obtain ⟨next,he,hout,hworld,hmem,hactive,hgas,hpc,hexec,hret,hh⟩ :=
    keccak_step_cost fuel (hashOpcodeCost s) (hashMemoryCharged s) offset size tail hstack
  have hp : ExplicitPrefix 1 (hashMemoryCharged s) next
      (directQueries .KECCAK256 (hashMemoryCharged s) ++ []) := .cons he (.nil next)
  have hr : ExplicitPrefix 1 (hashMemoryCharged s) next
      [byteQuery (machineQuery s.toMachineState offset size)] := by
    simpa only [directQueries, hstack, beq_self_eq_true, if_pos rfl,
      List.append_nil, hash_charged_input] using hp
  have hx : X (fuel+2) dest s = X (fuel+1) dest next :=
    X_continue (fuel+1) dest s (hashMemoryCharged s) next (hashOpcodeCost s) hc
      (by simpa only [hf] using he) (by rw [hf]; rfl)
  exact ⟨next,⟨hg,hc,he,hr,hout,hworld,hmem,hactive,hgas,hpc,hexec,hret,hh,hx⟩⟩

/-- Exhaustive proof account for this first KECCAK edge. Low one fuel still
runs checks before failing in step0; positive branches retain actual X tail. -/
def HashDriverOutcome (fuel : Nat) (dest : Array UInt256) (s : EVM.State)
    (offset size : UInt256) (tail : List UInt256) : Prop :=
  match fuel with
  | 0 => X 0 dest s = .error .OutOfFuel
  | 1 => X 1 dest s = (do let _ ← hashGuard s; .error .OutOfFuel)
  | n+2 => match hashGuard s with
    | .error e => X (n+2) dest s = .error e
    | .ok () => ∃ next, CheckedHashEdge n dest s offset size tail next

/-- Actual all-fuel/all-check client: no passed guard, chosen reply, reached
state, enough gas/fuel, terminal certificate or jump membership is supplied. -/
theorem hash_driver_outcome (fuel : Nat) (dest : Array UInt256) (s : EVM.State)
    (offset size : UInt256) (tail : List UInt256)
    (hf : fetched s = (.KECCAK256,none)) (hs : s.stack = offset :: size :: tail) :
    HashDriverOutcome fuel dest s offset size tail := by
  cases fuel with
  | zero => rfl
  | succ f =>
    cases f with
    | zero =>
      change X 1 dest s = _
      rw [X_unfold,hash_checks dest s hf]
      cases hg : hashGuard s with
      | error e => rfl
      | ok ticket => cases ticket; rfl
    | succ n =>
      change (match hashGuard s with
        | .error e => X (n+2) dest s = .error e
        | .ok () => ∃ next, CheckedHashEdge n dest s offset size tail next)
      cases hg : hashGuard s with
      | error e =>
        apply check_failure (n+1) dest s e
        rw [hash_checks dest s hf,hg]
        rfl
      | ok ticket =>
        cases ticket
        exact checked_hash_edge n dest s offset size tail hf hs hg

end Solidity.HashBridge
