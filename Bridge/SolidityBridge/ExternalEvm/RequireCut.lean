import SolidityBridge.ExternalEvm.DriverPush
import SolidityBridge.ExternalEvm.ChargedDispatch
import SolidityBridge.ExternalEvm.StackOps

/-! Proof-only finite cut views of existing X for the ORIGINAL require blocks.
No assembler, operational driver or source/default judgment is installed.
The closed opcode/argument class fixes widths; equality to X anchors every use. -/
namespace EvmYul.EVM.DriverProof

def RequireInstruction (op : Operation .EVM) (arg : Option (UInt256 × Nat)) : Prop :=
  (∃ v, op = .Push .PUSH1 ∧ arg = some (v, 1)) ∨
  (∃ v, op = .Push .PUSH2 ∧ arg = some (v, 2)) ∨
  (∃ v, op = .Push .PUSH4 ∧ arg = some (v, 4)) ∨
  (∃ v, op = .Push .PUSH20 ∧ arg = some (v, 20)) ∨
  (op = .AND ∧ arg = none) ∨ (op = .EQ ∧ arg = none) ∨
  (op = .DUP2 ∧ arg = none) ∨ (op = .SWAP5 ∧ arg = none)

theorem RequireInstruction.pure {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    (hi : RequireInstruction op arg) : RequirePureOp op := by
  rcases hi with ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ |
    ⟨v, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp only [RequirePureOp, true_or, or_true]

private theorem positive0 (fuel cost : Nat) (s : State) (v : UInt256) :
    step (fuel + 1) cost (some (.Push .PUSH1, some (v, 1))) s =
      step 1 cost (some (.Push .PUSH1, some (v, 1))) s := by rfl

private theorem positive1 (fuel cost : Nat) (s : State) (v : UInt256) :
    step (fuel + 1) cost (some (.Push .PUSH2, some (v, 2))) s =
      step 1 cost (some (.Push .PUSH2, some (v, 2))) s := by rfl

private theorem positive2 (fuel cost : Nat) (s : State) (v : UInt256) :
    step (fuel + 1) cost (some (.Push .PUSH4, some (v, 4))) s =
      step 1 cost (some (.Push .PUSH4, some (v, 4))) s := by rfl

private theorem positive3 (fuel cost : Nat) (s : State) (v : UInt256) :
    step (fuel + 1) cost (some (.Push .PUSH20, some (v, 20))) s =
      step 1 cost (some (.Push .PUSH20, some (v, 20))) s := by rfl

private theorem positive4 (fuel cost : Nat) (s : State) :
    step (fuel + 1) cost (some (.AND, none)) s =
      step 1 cost (some (.AND, none)) s := by rfl

private theorem positive5 (fuel cost : Nat) (s : State) :
    step (fuel + 1) cost (some (.EQ, none)) s =
      step 1 cost (some (.EQ, none)) s := by rfl

private theorem positive6 (fuel cost : Nat) (s : State) :
    step (fuel + 1) cost (some (.DUP2, none)) s =
      step 1 cost (some (.DUP2, none)) s := by rfl

private theorem positive7 (fuel cost : Nat) (s : State) :
    step (fuel + 1) cost (some (.SWAP5, none)) s =
      step 1 cost (some (.SWAP5, none)) s := by rfl

theorem require_step_positive (fuel cost : Nat) (s : State)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (hi : RequireInstruction op arg) :
    step (fuel + 1) cost (some (op, arg)) s = step 1 cost (some (op, arg)) s := by
  rcases hi with ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ |
    ⟨v, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact positive0 fuel cost s v
  · exact positive1 fuel cost s v
  · exact positive2 fuel cost s v
  · exact positive3 fuel cost s v
  · exact positive4 fuel cost s
  · exact positive5 fuel cost s
  · exact positive6 fuel cost s
  · exact positive7 fuel cost s

theorem require_nonterminal (s : State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)) (hi : RequireInstruction op arg) :
    terminalData s op = none := by
  rcases hi with ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ |
    ⟨v, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rfl

def prepare3 (s : State) : State :=
  {s with execLength := s.execLength + 1
          gasAvailable := s.gasAvailable - .ofNat 3}

/-- Published numeric dispatcher reused at its actual charge, not re-proved arithmetic. -/
theorem require_and_form (fuel : Nat) (s : State) :
    step (fuel + 1) 3 (some (.AND, none)) s =
      execBinOp UInt256.land (prepare3 s) := by
  have charged : step (fuel + 1) 3 (some (.AND, none)) s =
      step (fuel + 1) 0 (some (.AND, none))
        (Solidity.Evm.External.debitOpcodeCost s 3) :=
    Solidity.Evm.External.BinaryOpcode.charged_dispatch .and s fuel 3
  have dispatched : step (fuel + 1) 0 (some (.AND, none))
      (Solidity.Evm.External.debitOpcodeCost s 3) =
      execBinOp UInt256.land
        (Solidity.Evm.External.prepare (Solidity.Evm.External.debitOpcodeCost s 3)) :=
    Solidity.Evm.External.BinaryOpcode.dispatch .and _ fuel
  rw [charged, dispatched]
  congr 1
  simp only [Solidity.Evm.External.prepare, Solidity.Evm.External.debitOpcodeCost,
    prepare3, word_sub_zero]

theorem require_eq_form (fuel : Nat) (s : State) :
    step (fuel + 1) 3 (some (.EQ, none)) s =
      execBinOp UInt256.eq (prepare3 s) := by
  have charged : step (fuel + 1) 3 (some (.EQ, none)) s =
      step (fuel + 1) 0 (some (.EQ, none))
        (Solidity.Evm.External.debitOpcodeCost s 3) :=
    Solidity.Evm.External.BinaryOpcode.charged_dispatch .eq s fuel 3
  have dispatched : step (fuel + 1) 0 (some (.EQ, none))
      (Solidity.Evm.External.debitOpcodeCost s 3) =
      execBinOp UInt256.eq
        (Solidity.Evm.External.prepare (Solidity.Evm.External.debitOpcodeCost s 3)) :=
    Solidity.Evm.External.BinaryOpcode.dispatch .eq _ fuel
  rw [charged, dispatched]
  congr 1
  simp only [Solidity.Evm.External.prepare, Solidity.Evm.External.debitOpcodeCost,
    prepare3, word_sub_zero]

/-- Exact charged stack transformers; published zero-cost dispatch remains intact. -/
theorem require_dup2_form (fuel : Nat) (s : State) :
    step (fuel + 1) 3 (some (.DUP2, none)) s = EvmYul.dup 2 (prepare3 s) := by
  have debit : step (fuel + 1) 3 (some (.DUP2, none)) s =
      step (fuel + 1) 0 (some (.DUP2, none))
        (Solidity.Evm.External.debitOpcodeCost s 3) := by
    change EvmYul.dup 2 _ = EvmYul.dup 2 _
    congr 1
    simp only [Solidity.Evm.External.debitOpcodeCost, word_sub_zero]
  have dispatched : step (fuel + 1) 0 (some (.DUP2, none))
      (Solidity.Evm.External.debitOpcodeCost s 3) =
      EvmYul.dup 2
        (Solidity.Evm.External.prepare (Solidity.Evm.External.debitOpcodeCost s 3)) :=
    Solidity.Evm.External.dup_dispatch (1 : Fin 16) _ fuel
  rw [debit, dispatched]
  congr 1
  simp only [Solidity.Evm.External.prepare, Solidity.Evm.External.debitOpcodeCost,
    prepare3, word_sub_zero]

theorem require_swap5_form (fuel : Nat) (s : State) :
    step (fuel + 1) 3 (some (.SWAP5, none)) s = EvmYul.swap 5 (prepare3 s) := by
  have debit : step (fuel + 1) 3 (some (.SWAP5, none)) s =
      step (fuel + 1) 0 (some (.SWAP5, none))
        (Solidity.Evm.External.debitOpcodeCost s 3) := by
    change EvmYul.swap 5 _ = EvmYul.swap 5 _
    congr 1
    simp only [Solidity.Evm.External.debitOpcodeCost, word_sub_zero]
  have dispatched : step (fuel + 1) 0 (some (.SWAP5, none))
      (Solidity.Evm.External.debitOpcodeCost s 3) =
      EvmYul.swap 5
        (Solidity.Evm.External.prepare (Solidity.Evm.External.debitOpcodeCost s 3)) :=
    Solidity.Evm.External.swap_dispatch (4 : Fin 16) _ fuel
  rw [debit, dispatched]
  congr 1
  simp only [Solidity.Evm.External.prepare, Solidity.Evm.External.debitOpcodeCost,
    prepare3, word_sub_zero]

/-- PC and full observable state are DERIVED from actual successful steps.
No source reachability or compiled-continuation premise occurs. -/
theorem require_step_preserves (s next : State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)) (hi : RequireInstruction op arg)
    (h : step 1 3 (some (op, arg)) s = .ok next) :
    next.toState = s.toState ∧
    next.pc = s.pc + UInt256.ofNat ((arg.map Prod.snd).getD 0 + 1) ∧
    next.memory = s.memory ∧ next.returnData = s.returnData ∧
    next.activeWords = s.activeWords ∧
    next.gasAvailable = s.gasAvailable - UInt256.ofNat 3 ∧
    next.execLength = s.execLength + 1 := by
  rcases hi with ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ |
    ⟨v, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [require_and_form 0] at h
    unfold execBinOp at h
    split at h
    · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases h
  · rw [require_eq_form 0] at h
    unfold execBinOp at h
    split at h
    · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases h
  · rw [require_dup2_form 0] at h
    unfold EvmYul.dup at h
    dsimp only at h
    split at h
    · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases h
  · rw [require_swap5_form 0] at h
    unfold EvmYul.swap at h
    dsimp only at h
    split at h
    · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases h

/-- Closed-form view of actual ordered checks for these finite nonmemory cuts. -/
def corridorChecks (op : Operation .EVM) (s : State) :
    Except ExecutionException (State × Nat) :=
  if s.gasAvailable.toNat < 3 then .error .OutOfGass
  else if s.stack.length < (δ op).getD 0 then .error .StackUnderflow
  else if s.stack.length - (δ op).getD 0 + (α op).getD 0 > 1024 then
    .error .StackOverflow
  else .ok (s, 3)

/-- Only an observation of checked step1, not an operational replacement. -/
def corridorNext (op : Operation .EVM) (arg : Option (UInt256 × Nat)) (s : State) :
    Except ExecutionException State := do
  let (charged, cost) ← corridorChecks op s
  step 1 cost (some (op, arg)) charged

theorem corridorNext_preserves (s next : State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)) (hi : RequireInstruction op arg)
    (h : corridorNext op arg s = .ok next) :
    next.toState = s.toState ∧
    next.pc = s.pc + UInt256.ofNat ((arg.map Prod.snd).getD 0 + 1) ∧
    next.memory = s.memory ∧ next.returnData = s.returnData ∧
    next.activeWords = s.activeWords ∧
    next.gasAvailable = s.gasAvailable - UInt256.ofNat 3 ∧
    next.execLength = s.execLength + 1 := by
  unfold corridorNext corridorChecks at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · exact require_step_preserves s next op arg hi h

/-- Finite continuation view. Fuel1 retains guard faults BEFORE step0 exhaustion. -/
def corridorCut (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (fuel : Nat) (s : State)
    (k : Nat → State → Except ExecutionException (ExecutionResult State)) :
    Except ExecutionException (ExecutionResult State) :=
  match fuel with
  | 0 => .error .OutOfFuel
  | 1 => do
    let _ ← corridorChecks op s
    .error .OutOfFuel
  | n + 2 => do
    let next ← corridorNext op arg s
    k (n + 1) next

/-- Exact equality to the existing pinned X for ALL fuel and ALL raw states. -/
theorem X_corridorCut (fuel : Nat) (dest : Array UInt256) (s : State)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (hi : RequireInstruction op arg) (hf : fetched s = (op, arg)) :
    X fuel dest s = corridorCut op arg fuel s (fun n next => X n dest next) := by
  have hc : checks dest s = corridorChecks op s := require_pure_checks dest s op arg hi.pure hf
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero =>
      rw [X_unfold, hc]
      cases hg : corridorChecks op s with
      | error e => simp only [corridorCut, hg, Bind.bind, Except.bind]
      | ok pair =>
        rcases pair with ⟨charged, cost⟩
        simp only [corridorCut, hg, Bind.bind, Except.bind]
        rfl
    | succ fuel =>
      rw [X_unfold, hc]
      cases hg : corridorChecks op s with
      | error e => simp only [corridorCut, corridorNext, hg, Bind.bind, Except.bind]
      | ok pair =>
        rcases pair with ⟨charged, cost⟩
        simp only [Bind.bind, Except.bind, hf,
          require_step_positive fuel cost charged op arg hi]
        cases he : step 1 cost (some (op, arg)) charged with
        | error e => simp only [corridorCut, corridorNext, hg, Bind.bind, Except.bind, he]
        | ok next =>
          simp only [require_nonterminal next op arg hi, corridorCut, corridorNext,
            hg, Bind.bind, Except.bind, he]

theorem corridorCut_congr (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (fuel : Nat) (s : State)
    (k l : Nat → State → Except ExecutionException (ExecutionResult State))
    (h : ∀ n next, corridorNext op arg s = .ok next → k n next = l n next) :
    corridorCut op arg fuel s k = corridorCut op arg fuel s l := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      simp only [corridorCut]
      cases he : corridorNext op arg s with
      | error e => rfl
      | ok next => exact h (fuel + 1) next he

#print axioms require_step_positive
#print axioms require_nonterminal
#print axioms require_and_form
#print axioms require_eq_form
#print axioms require_dup2_form
#print axioms require_swap5_form
#print axioms require_step_preserves
#print axioms corridorNext_preserves
#print axioms X_corridorCut
#print axioms corridorCut_congr
end EvmYul.EVM.DriverProof
