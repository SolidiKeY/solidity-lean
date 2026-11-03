import SolidityBridge.ExternalEvm.RequireCut

/-! Finite proof views for the ORIGINAL require helper's actual local
instructions. No alternate evaluator, assembler, source or default judgment.
Every view below is equated to the existing pinned X, including terminal data. -/
namespace EvmYul.EVM.DriverProof

def RequireLocalOp (op : Operation .EVM) : Prop :=
  op = .Push .PUSH0 ∨ op = .Push .PUSH1 ∨ op = .Push .PUSH2 ∨ op = .Push .PUSH4 ∨ op = .Push .PUSH20 ∨ op = .AND ∨ op = .EQ ∨ op = .DUP1 ∨ op = .DUP2 ∨ op = .SWAP1 ∨ op = .SWAP2 ∨ op = .SWAP5 ∨ op = .SHL ∨ op = .SUB ∨ op = .ISZERO ∨ op = .JUMPDEST ∨ op = .JUMP ∨ op = .JUMPI ∨ op = .REVERT

private theorem local_positive0 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.Push .PUSH0, arg)) s = step 1 cost (some (.Push .PUSH0, arg)) s := by rfl

private theorem local_positive1 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.Push .PUSH1, arg)) s = step 1 cost (some (.Push .PUSH1, arg)) s := by rfl

private theorem local_positive2 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.Push .PUSH2, arg)) s = step 1 cost (some (.Push .PUSH2, arg)) s := by rfl

private theorem local_positive3 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.Push .PUSH4, arg)) s = step 1 cost (some (.Push .PUSH4, arg)) s := by rfl

private theorem local_positive4 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.Push .PUSH20, arg)) s = step 1 cost (some (.Push .PUSH20, arg)) s := by rfl

private theorem local_positive5 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.AND, arg)) s = step 1 cost (some (.AND, arg)) s := by rfl

private theorem local_positive6 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.EQ, arg)) s = step 1 cost (some (.EQ, arg)) s := by rfl

private theorem local_positive7 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.DUP1, arg)) s = step 1 cost (some (.DUP1, arg)) s := by rfl

private theorem local_positive8 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.DUP2, arg)) s = step 1 cost (some (.DUP2, arg)) s := by rfl

private theorem local_positive9 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.SWAP1, arg)) s = step 1 cost (some (.SWAP1, arg)) s := by rfl

private theorem local_positive10 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.SWAP2, arg)) s = step 1 cost (some (.SWAP2, arg)) s := by rfl

private theorem local_positive11 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.SWAP5, arg)) s = step 1 cost (some (.SWAP5, arg)) s := by rfl

private theorem local_positive12 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.SHL, arg)) s = step 1 cost (some (.SHL, arg)) s := by rfl

private theorem local_positive13 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.SUB, arg)) s = step 1 cost (some (.SUB, arg)) s := by rfl

private theorem local_positive14 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.ISZERO, arg)) s = step 1 cost (some (.ISZERO, arg)) s := by rfl

private theorem local_positive15 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.JUMPDEST, arg)) s = step 1 cost (some (.JUMPDEST, arg)) s := by rfl

private theorem local_positive16 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.JUMP, arg)) s = step 1 cost (some (.JUMP, arg)) s := by rfl

private theorem local_positive17 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.JUMPI, arg)) s = step 1 cost (some (.JUMPI, arg)) s := by rfl

private theorem local_positive18 (fuel cost : Nat) (arg : Option (UInt256 × Nat)) (s : State) :
    step (fuel + 1) cost (some (.REVERT, arg)) s = step 1 cost (some (.REVERT, arg)) s := by rfl

theorem require_local_positive (fuel cost : Nat) (arg : Option (UInt256 × Nat))
    (s : State) (op : Operation .EVM) (hop : RequireLocalOp op) :
    step (fuel + 1) cost (some (op, arg)) s = step 1 cost (some (op, arg)) s := by
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact local_positive0 fuel cost arg s
  · exact local_positive1 fuel cost arg s
  · exact local_positive2 fuel cost arg s
  · exact local_positive3 fuel cost arg s
  · exact local_positive4 fuel cost arg s
  · exact local_positive5 fuel cost arg s
  · exact local_positive6 fuel cost arg s
  · exact local_positive7 fuel cost arg s
  · exact local_positive8 fuel cost arg s
  · exact local_positive9 fuel cost arg s
  · exact local_positive10 fuel cost arg s
  · exact local_positive11 fuel cost arg s
  · exact local_positive12 fuel cost arg s
  · exact local_positive13 fuel cost arg s
  · exact local_positive14 fuel cost arg s
  · exact local_positive15 fuel cost arg s
  · exact local_positive16 fuel cost arg s
  · exact local_positive17 fuel cost arg s
  · exact local_positive18 fuel cost arg s

private theorem drop_failed_guard {α : Type} (p : Prop) [Decidable p]
    (err : ExecutionException) (rest : Except ExecutionException α) (out : α)
    (h : (if p then .error err else rest) = .ok out) : rest = .ok out := by
  split at h
  · cases h
  · exact h

/-- Successful actual checks with zero memory expansion retain the complete
input state and return the actual C' charge. No affordability is assumed. -/
theorem checks_unexpanded (dest : Array UInt256) (s charged : State) (cost : Nat)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (hf : fetched s = (op, arg)) (hm : memoryExpansionCost s op = 0)
    (h : checks dest s = .ok (charged, cost)) : charged = s ∧ cost = C' s op := by
  simp only [checks, hf, hm, word_sub_zero, Nat.not_lt_zero, if_false,
    Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  repeat' apply drop_failed_guard at h
  have hp : (s, C' s op) = (charged, cost) := Except.ok.inj h
  exact ⟨(congrArg Prod.fst hp).symm, (congrArg Prod.snd hp).symm⟩

/-- An observation of one actual driver cut, retaining every terminal byte,
check/evaluator error, and all-fuel boundary. Not a replacement driver. -/
def requireLocalCut (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (fuel : Nat) (dest : Array UInt256) (s : State)
    (k : Nat → State → Except ExecutionException (ExecutionResult State)) :
    Except ExecutionException (ExecutionResult State) :=
  match fuel with
  | 0 => .error .OutOfFuel
  | 1 => do
    let _ ← checks dest s
    .error .OutOfFuel
  | n + 2 => do
    let (charged, cost) ← checks dest s
    let next ← step 1 cost (some (op, arg)) charged
    match terminalData next op with
    | none => k (n + 1) next
    | some bytes => if op == .REVERT then .ok (.revert next.gasAvailable bytes)
                    else .ok (.success next bytes)

theorem X_requireLocalCut (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (fuel : Nat) (dest : Array UInt256) (s : State) (hop : RequireLocalOp op)
    (hf : fetched s = (op, arg)) :
    X fuel dest s = requireLocalCut op arg fuel dest s (fun n next => X n dest next) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero =>
      rw [X_unfold]
      cases hc : checks dest s with
      | error e => simp only [requireLocalCut, hc, Bind.bind, Except.bind]
      | ok pair =>
        rcases pair with ⟨charged, cost⟩
        simp only [requireLocalCut, hc, Bind.bind, Except.bind]
        rfl
    | succ fuel =>
      rw [X_unfold]
      simp only [hf, require_local_positive fuel _ arg _ op hop, requireLocalCut]
      cases hc : checks dest s with
      | error e => rfl
      | ok pair => rcases pair with ⟨charged, cost⟩; rfl

/-- Continuation replacement only at genuine successful, nonterminal outputs. -/
theorem requireLocalCut_congr (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (fuel : Nat) (dest : Array UInt256) (s : State)
    (k l : Nat → State → Except ExecutionException (ExecutionResult State))
    (h : ∀ n charged cost next, checks dest s = .ok (charged, cost) →
      step 1 cost (some (op, arg)) charged = .ok next → terminalData next op = none →
      k n next = l n next) :
    requireLocalCut op arg fuel dest s k = requireLocalCut op arg fuel dest s l := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      simp only [requireLocalCut]
      cases hc : checks dest s with
      | error e => rfl
      | ok pair =>
        rcases pair with ⟨charged, cost⟩
        simp only [Bind.bind, Except.bind]
        cases he : step 1 cost (some (op, arg)) charged with
        | error e => rfl
        | ok next =>
          dsimp only
          cases ht : terminalData next op with
          | some bytes => rfl
          | none => exact h (fuel + 1) charged cost next hc he ht

#print axioms require_local_positive
#print axioms checks_unexpanded
#print axioms X_requireLocalCut
#print axioms requireLocalCut_congr
end EvmYul.EVM.DriverProof
