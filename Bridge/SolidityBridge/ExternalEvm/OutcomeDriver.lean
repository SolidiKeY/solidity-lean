import EvmYul.EVM.Semantics

/-! Proof views of the actual pinned X driver. No alternate execution driver.
The checked one-iteration equality below derives these views from X, including all ordered
faults, the smaller evaluator fuel and actual post-step halting data. -/
namespace EvmYul.EVM.DriverProof

abbrev fetched (s : State) : Operation .EVM × Option (UInt256 × Nat) := (decode s.executionEnv.code s.pc).getD (.STOP, none)

private def destinationAbsent (o : Option UInt256) (dest : Array UInt256) : Bool :=
  !(match o with | none => false | some n => dest.contains n)

private def writes (w : Operation .EVM) (s : Stack UInt256) : Bool :=
  w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
  (w = .CALL ∧ s[2]? ≠ some ⟨0⟩)

/-- Observation of the existing X local Z expression, not a new semantics. -/
def checks (validJumps : Array UInt256) (evmState : State) :
    Except ExecutionException (State × Nat) := do
  let w := (fetched evmState).1
  let cost₁ := memoryExpansionCost evmState w
  if evmState.gasAvailable.toNat < cost₁ then
    .error .OutOfGass
  let gasAvailable := evmState.gasAvailable - .ofNat cost₁
  let evmState := { evmState with gasAvailable := gasAvailable}
  let cost₂ := C' evmState w

  if evmState.gasAvailable.toNat < cost₂ then
    .error .OutOfGass

  if δ w = none then
    .error .InvalidInstruction

  if evmState.stack.length < (δ w).getD 0 then
    .error .StackUnderflow

  let invalidJump := destinationAbsent evmState.stack[0]? validJumps

  if w = .JUMP ∧ invalidJump then
    .error .BadJumpDestination

  if w = .JUMPI ∧ (evmState.stack[1]? ≠ some ⟨0⟩) ∧ invalidJump then
    .error .BadJumpDestination

  if w = .RETURNDATACOPY ∧ (evmState.stack.getD 1 ⟨0⟩).toNat + (evmState.stack.getD 2 ⟨0⟩).toNat > evmState.returnData.size then
    .error .InvalidMemoryAccess

  if evmState.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024 then
    .error .StackOverflow

  if (¬ evmState.executionEnv.perm) ∧ writes w evmState.stack then
    .error .StaticModeViolation

  if (w = .SSTORE) ∧ evmState.gasAvailable.toNat ≤ GasConstants.Gcallstipend then
    .error .OutOfGass

  if
    w.isCreate ∧ evmState.stack.getD 2 ⟨0⟩ > ⟨49152⟩
  then
    .error .OutOfGass

  pure (evmState, cost₂)

/-- Observation of X's H after the actual evaluator step. -/
def terminalData (s : State) (w : Operation .EVM) : Option ByteArray :=
  if w ∈ [.RETURN, .REVERT] then some s.toMachineState.H_return
  else if w ∈ [.STOP, .SELFDESTRUCT] then some .empty else none

theorem word_sub_zero (g : UInt256) : g - UInt256.ofNat 0 = g := by
  cases g with
  | mk g =>
    apply congrArg UInt256.mk
    change g - 0 = g
    exact sub_zero g

/-- The original function entries fetch JUMPDEST. All gas/stack outcomes
remain those of the actual driver; no source precondition is added. -/
theorem jumpdest_checks (dest : Array UInt256) (s : State)
    (hf : fetched s = (.JUMPDEST, none)) :
    checks dest s =
      (if s.gasAvailable.toNat < 1 then .error .OutOfGass
       else if s.stack.length > 1024 then .error .StackOverflow
       else .ok (s, 1)) := by
  have hj : (Operation.JUMPDEST : Operation .EVM) ≠ .JUMP := by decide
  have hji : (Operation.JUMPDEST : Operation .EVM) ≠ .JUMPI := by decide
  have hs : (Operation.JUMPDEST : Operation .EVM) ≠ .SSTORE := by decide
  have ht : (Operation.JUMPDEST : Operation .EVM) ≠ .TSTORE := by decide
  simp only [checks, hf, memoryExpansionCost, memoryExpansionCost.μᵢ',
    Nat.sub_self, word_sub_zero, Nat.not_lt_zero, if_false,
    C', GasConstants.Gjumpdest, δ, α, writes, destinationAbsent,
    Bind.bind, Except.bind, Pure.pure, Option.getD_some,
    reduceCtorEq, List.mem_cons, false_or, false_and,
    and_false, Nat.sub_zero, Nat.add_zero, Operation.isCreate,
    Bool.false_eq_true, Except.pure, hj, hji, hs, ht, List.not_mem_nil,
    decide_false]

/-- Actual fixed source PUSH instruction: exact charge/check outcomes. -/
theorem legacy_push4_checks (dest : Array UInt256) (s : State)
    (hf : fetched s = ((.Push .PUSH4), some (.ofNat 3735928559, 4))) :
    checks dest s =
      (if s.gasAvailable.toNat < 3 then .error .OutOfGass
       else if s.stack.length + 1 > 1024 then .error .StackOverflow
       else .ok (s, 3)) := by
  have hm : memoryExpansionCost s (.Push .PUSH4) = 0 := by
    change Cₘ s.activeWords - Cₘ s.activeWords = 0
    exact Nat.sub_self _
  have hc : ∀ t : State, C' t (.Push .PUSH4) = 3 := fun _ => rfl
  have hw : writes (.Push .PUSH4) s.stack = false := by rfl
  have hj : ((.Push .PUSH4) : Operation .EVM) ≠ .JUMP := by decide
  have hji : ((.Push .PUSH4) : Operation .EVM) ≠ .JUMPI := by decide
  have hr : ((.Push .PUSH4) : Operation .EVM) ≠ .RETURNDATACOPY := by decide
  have hs : ((.Push .PUSH4) : Operation .EVM) ≠ .SSTORE := by decide
  simp only [checks, hf, hm, word_sub_zero, hc, Nat.not_lt_zero, if_false,
    δ, α, Option.getD_some, Nat.sub_zero, Bind.bind, Except.bind,
    Pure.pure, Except.pure, hj, hji, hr, hs, hw, and_false, false_and,
    Bool.false_eq_true, Operation.isCreate, reduceCtorEq]

/-- Actual fixed source PUSH instruction: exact charge/check outcomes. -/
theorem viaIR_push1_checks (dest : Array UInt256) (s : State)
    (hf : fetched s = ((.Push .PUSH1), some (.ofNat 32, 1))) :
    checks dest s =
      (if s.gasAvailable.toNat < 3 then .error .OutOfGass
       else if s.stack.length + 1 > 1024 then .error .StackOverflow
       else .ok (s, 3)) := by
  have hm : memoryExpansionCost s (.Push .PUSH1) = 0 := by
    change Cₘ s.activeWords - Cₘ s.activeWords = 0
    exact Nat.sub_self _
  have hc : ∀ t : State, C' t (.Push .PUSH1) = 3 := fun _ => rfl
  have hw : writes (.Push .PUSH1) s.stack = false := by rfl
  have hj : ((.Push .PUSH1) : Operation .EVM) ≠ .JUMP := by decide
  have hji : ((.Push .PUSH1) : Operation .EVM) ≠ .JUMPI := by decide
  have hr : ((.Push .PUSH1) : Operation .EVM) ≠ .RETURNDATACOPY := by decide
  have hs : ((.Push .PUSH1) : Operation .EVM) ≠ .SSTORE := by decide
  simp only [checks, hf, hm, word_sub_zero, hc, Nat.not_lt_zero, if_false,
    δ, α, Option.getD_some, Nat.sub_zero, Bind.bind, Except.bind,
    Pure.pure, Except.pure, hj, hji, hr, hs, hw, and_false, false_and,
    Bool.false_eq_true, Operation.isCreate, reduceCtorEq]

/-- Closed opcode class needed by the two ORIGINAL straight-line corridors.
This is not an assembler or a claim about arbitrary instruction widths. -/
def RequirePureOp (op : Operation .EVM) : Prop :=
  op = .Push .PUSH1 ∨ op = .Push .PUSH2 ∨ op = .Push .PUSH4 ∨ op = .Push .PUSH20 ∨
  op = .AND ∨ op = .EQ ∨ op = .DUP2 ∨ op = .SWAP5

/-- Exact driver guards, including underflow and overflow for arbitrary tails. -/
theorem require_pure_checks (dest : Array UInt256) (s : State)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (hop : RequirePureOp op) (hf : fetched s = (op, arg)) :
    checks dest s =
      (if s.gasAvailable.toNat < 3 then .error .OutOfGass
       else if s.stack.length < (δ op).getD 0 then .error .StackUnderflow
       else if s.stack.length - (δ op).getD 0 + (α op).getD 0 > 1024 then
         .error .StackOverflow
       else .ok (s, 3)) := by
  have hm : memoryExpansionCost s op = 0 := by
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact Nat.sub_self _
  have hc : ∀ t : State, C' t op = 3 := by
    intro t
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl
  have hw : writes op s.stack = false := by
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl
  have hd : δ op ≠ none := by
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  have hj : op ≠ .JUMP := by
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  have hji : op ≠ .JUMPI := by
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  have hr : op ≠ .RETURNDATACOPY := by
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  have hs : op ≠ .SSTORE := by
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  have hcreate : op.isCreate = false := by
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl
  simp only [checks, hf, hm, word_sub_zero, hc, Nat.not_lt_zero, if_false,
    hd, hj, hji, hr, hs, hw, hcreate, and_false, false_and, Bool.false_eq_true,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms require_pure_checks

/-- Complete one-iteration equation, with actual byte fetch and both charges. -/
theorem X_unfold (fuel : Nat) (dest : Array UInt256) (s : State) :
    X (fuel + 1) dest s =
      (match checks dest s with
      | .error e => .error e
      | .ok (charged, cost) => do
        let next ← step fuel cost (some (fetched s)) charged
        match terminalData next (fetched s).1 with
        | none => X fuel dest next
        | some bytes =>
          if (fetched s).1 == .REVERT then .ok (.revert next.gasAvailable bytes)
          else .ok (.success next bytes)) := by
  rfl

theorem X_zero (dest : Array UInt256) (s : State) :
    X 0 dest s = .error .OutOfFuel := by rfl

theorem check_failure (fuel : Nat) (dest : Array UInt256) (s : State)
    (e : ExecutionException) (h : checks dest s = .error e) :
    X (fuel + 1) dest s = .error e := by
  rw [X_unfold, h]

theorem evaluator_failure (fuel : Nat) (dest : Array UInt256) (s charged : State)
    (cost : Nat) (e : ExecutionException) (hc : checks dest s = .ok (charged, cost))
    (he : step fuel cost (some (fetched s)) charged = .error e) :
    X (fuel + 1) dest s = .error e := by
  simp only [X_unfold, hc, he, Bind.bind, Except.bind]

theorem X_continue (fuel : Nat) (dest : Array UInt256) (s charged next : State)
    (cost : Nat) (hc : checks dest s = .ok (charged, cost))
    (he : step fuel cost (some (fetched s)) charged = .ok next)
    (hh : terminalData next (fetched s).1 = none) :
    X (fuel + 1) dest s = X fuel dest next := by
  simp only [X_unfold, hc, he, Bind.bind, Except.bind, hh]

/-- Every actual driver result has a stage witness; no branch is omitted. -/
inductive Classifies : Nat → Array UInt256 → State →
    Except ExecutionException (ExecutionResult State) → Prop where
  | zero (dest : Array UInt256) (s : State) : Classifies 0 dest s (.error .OutOfFuel)
  | guard (fuel : Nat) (dest : Array UInt256) (s : State) (e : ExecutionException) (h : checks dest s = .error e) :
      Classifies (fuel + 1) dest s (.error e)
  | evaluator (fuel : Nat) (dest : Array UInt256) (s charged : State) (cost : Nat) (e : ExecutionException)
      (hc : checks dest s = .ok (charged, cost))
      (he : step fuel cost (some (fetched s)) charged = .error e) :
      Classifies (fuel + 1) dest s (.error e)
  | tail (fuel : Nat) (dest : Array UInt256) (s charged : State) (cost : Nat) (next : State)
      (hc : checks dest s = .ok (charged, cost))
      (he : step fuel cost (some (fetched s)) charged = .ok next)
      (hh : terminalData next (fetched s).1 = none) :
      Classifies (fuel + 1) dest s (X fuel dest next)
  | revert (fuel : Nat) (dest : Array UInt256) (s charged : State) (cost : Nat) (next : State) (bytes : ByteArray)
      (hc : checks dest s = .ok (charged, cost))
      (he : step fuel cost (some (fetched s)) charged = .ok next)
      (hh : terminalData next (fetched s).1 = some bytes)
      (hr : ((fetched s).1 == .REVERT) = true) :
      Classifies (fuel + 1) dest s (.ok (.revert next.gasAvailable bytes))
  | success (fuel : Nat) (dest : Array UInt256) (s charged : State) (cost : Nat) (next : State) (bytes : ByteArray)
      (hc : checks dest s = .ok (charged, cost))
      (he : step fuel cost (some (fetched s)) charged = .ok next)
      (hh : terminalData next (fetched s).1 = some bytes)
      (hr : ((fetched s).1 == .REVERT) = false) :
      Classifies (fuel + 1) dest s (.ok (.success next bytes))

/-- A successful guard phase can still fail at the evaluator's smaller fuel. -/
theorem evaluator_zero (dest : Array UInt256) (s charged : State) (cost : Nat)
    (hc : checks dest s = .ok (charged, cost)) :
    X 1 dest s = .error .OutOfFuel := by
  exact evaluator_failure 0 dest s charged cost .OutOfFuel hc rfl

/-- Stage classification of EVERY actual result of the existing driver. -/
theorem classifies (fuel : Nat) (dest : Array UInt256) (s : State) :
    Classifies fuel dest s (X fuel dest s) := by
  cases fuel with
  | zero => exact .zero dest s
  | succ fuel =>
    cases hc : checks dest s with
    | error e =>
      rw [check_failure fuel dest s e hc]
      exact .guard fuel dest s e hc
    | ok chargedCost =>
      rcases chargedCost with ⟨charged, cost⟩
      cases he : step fuel cost (some (fetched s)) charged with
      | error e =>
        rw [evaluator_failure fuel dest s charged cost e hc he]
        exact .evaluator fuel dest s charged cost e hc he
      | ok next =>
        cases hh : terminalData next (fetched s).1 with
        | none =>
          rw [X_continue fuel dest s charged next cost hc he hh]
          exact .tail fuel dest s charged cost next hc he hh
        | some bytes =>
          cases hr : ((fetched s).1 == .REVERT) with
          | false =>
            have hx : X (fuel + 1) dest s = .ok (.success next bytes) := by
              simp only [X_unfold, hc, he, Bind.bind, Except.bind, hh, hr, Bool.false_eq_true, if_false]
            rw [hx]
            exact .success fuel dest s charged cost next bytes hc he hh hr
          | true =>
            have hx : X (fuel + 1) dest s = .ok (.revert next.gasAvailable bytes) := by
              simp only [X_unfold, hc, he, Bind.bind, Except.bind, hh, hr, if_true]
            rw [hx]
            exact .revert fuel dest s charged cost next bytes hc he hh hr

/-- A proof-stage witness never chooses a different operational result. -/
theorem Classifies.sound {fuel : Nat} {dest : Array UInt256} {s : State}
    {out : Except ExecutionException (ExecutionResult State)}
    (h : Classifies fuel dest s out) : X fuel dest s = out := by
  cases h with
  | zero dest s => exact X_zero dest s
  | guard fuel dest s e hc => exact check_failure fuel dest s e hc
  | evaluator fuel dest s charged cost e hc he =>
    exact evaluator_failure fuel dest s charged cost e hc he
  | tail fuel dest s charged cost next hc he hh =>
    exact X_continue fuel dest s charged next cost hc he hh
  | revert fuel dest s charged cost next bytes hc he hh hr =>
    simp only [X_unfold, hc, he, Bind.bind, Except.bind, hh, hr, if_true]
  | success fuel dest s charged cost next bytes hc he hh hr =>
    simp only [X_unfold, hc, he, Bind.bind, Except.bind, hh, hr, Bool.false_eq_true, if_false]

/-- Exact classification, with no operational choice made by a certificate. -/
theorem classifies_iff (fuel : Nat) (dest : Array UInt256) (s : State)
    (out : Except ExecutionException (ExecutionResult State)) :
    Classifies fuel dest s out ↔ X fuel dest s = out := by
  constructor
  · exact Classifies.sound
  · intro h
    rw [← h]
    exact classifies fuel dest s

/-- Inhabited guard success for the actual driver's empty-code STOP default. -/
def stopState : State :=
  { (default : State) with
    gasAvailable := .ofNat 0
    executionEnv := { (default : ExecutionEnv .EVM) with code := .empty }
    stack := [] }

theorem stop_checks : checks #[] stopState = .ok (stopState, 0) := by rfl

/-- Positive driver fuel is not positive evaluator fuel. -/
theorem stop_one_fuel : X 1 #[] stopState = .error .OutOfFuel := by
  exact evaluator_zero #[] stopState stopState 0 stop_checks

/-- The same inhabited state terminates successfully at sufficient driver fuel. -/
theorem stop_two_fuel : ∃ next, X 2 #[] stopState = .ok (.success next ByteArray.empty) := by
  exact ⟨_, rfl⟩

#print axioms legacy_push4_checks
#print axioms viaIR_push1_checks
#print axioms word_sub_zero
#print axioms jumpdest_checks
#print axioms stop_checks
#print axioms stop_one_fuel
#print axioms stop_two_fuel
#print axioms X_unfold
#print axioms X_zero
#print axioms check_failure
#print axioms evaluator_failure
#print axioms X_continue
#print axioms evaluator_zero
#print axioms classifies
#print axioms Classifies.sound
#print axioms classifies_iff

/-- Exact ordered checks of the two original next branch opcodes. The supplied
array remains arbitrary; this makes no D_J or fetched-target adequacy claim. -/
theorem require_branch_checks (dest : Array UInt256) (s : State)
    (op : Operation .EVM) (hop : op = .JUMP ∨ op = .JUMPI)
    (hf : fetched s = (op, none)) :
    checks dest s =
      (if s.gasAvailable.toNat < (if op = .JUMP then 8 else 10) then .error .OutOfGass
       else if s.stack.length < (if op = .JUMP then 1 else 2) then .error .StackUnderflow
       else if (op = .JUMP ∨ s.stack[1]? ≠ some ⟨0⟩) ∧
           destinationAbsent s.stack[0]? dest then .error .BadJumpDestination
       else if s.stack.length - (if op = .JUMP then 1 else 2) > 1024 then .error .StackOverflow
       else .ok (s, if op = .JUMP then 8 else 10)) := by
  have hm : memoryExpansionCost s op = 0 := by
    rcases hop with rfl | rfl
    all_goals exact Nat.sub_self _
  have hc : ∀ t : State, C' t op = (if op = .JUMP then 8 else 10) := by
    intro t
    rcases hop with rfl | rfl
    all_goals rfl
  have hw : writes op s.stack = false := by
    rcases hop with rfl | rfl
    all_goals rfl
  have hj : (Operation.JUMP : Operation .EVM) ≠ .JUMPI := by decide
  have hs1 : (Operation.JUMP : Operation .EVM) ≠ .SSTORE := by decide
  have hs2 : (Operation.JUMPI : Operation .EVM) ≠ .SSTORE := by decide
  rcases hop with rfl | rfl
  all_goals
    simp only [checks, hf, hm, hc, hw, word_sub_zero, Nat.not_lt_zero,
      if_false, δ, α, Bind.bind, Except.bind, Pure.pure, Except.pure,
      Option.getD_some, hj, Ne.symm hj, hs1, hs2, reduceCtorEq, false_or,
      true_or, false_and, and_false, true_and, Nat.add_zero,
      Operation.isCreate, Bool.false_eq_true, if_true]

/-- Actual full-state unconditional branch evaluator, arbitrary original tail. -/
theorem require_jump_step (fuel cost : Nat) (s : State) (target : UInt256)
    (tail : Stack UInt256) :
    step (fuel + 1) cost (some (.JUMP, none)) {s with stack := target :: tail} =
      .ok {s with
        execLength := s.execLength + 1
        gasAvailable := s.gasAvailable - .ofNat cost
        pc := target
        stack := tail} := by
  rfl

/-- Actual conditional branch, preserving all private memory/world fields. -/
theorem require_jumpi_step (fuel cost : Nat) (s : State) (target condition : UInt256)
    (tail : Stack UInt256) :
    step (fuel + 1) cost (some (.JUMPI, none)) {s with stack := target :: condition :: tail} =
      .ok {s with
        execLength := s.execLength + 1
        gasAvailable := s.gasAvailable - .ofNat cost
        pc := if condition != ⟨0⟩ then target else s.pc + ⟨1⟩
        stack := tail} := by
  rfl

/-- One actual branch iteration for positive evaluator fuel. Every ordered
check failure and evaluator error is retained; no successful target is assumed. -/
theorem require_branch_iteration (fuel : Nat) (dest : Array UInt256) (s : State)
    (op : Operation .EVM) (hop : op = .JUMP ∨ op = .JUMPI)
    (hf : fetched s = (op, none)) :
    X (fuel + 2) dest s =
      (do
        let (charged, cost) ← checks dest s
        let next ← step 1 cost (some (op, none)) charged
        X (fuel + 1) dest next) := by
  rw [X_unfold]
  cases hc : checks dest s with
  | error e => rfl
  | ok pair =>
    rcases pair with ⟨charged, cost⟩
    have he : step (fuel + 1) cost (some (op, none)) charged =
        step 1 cost (some (op, none)) charged := by
      rcases hop with rfl | rfl
      all_goals rfl
    simp only [Bind.bind, Except.bind, hf, he]
    cases hn : step 1 cost (some (op, none)) charged with
    | error e => rfl
    | ok next =>
      have ht : terminalData next op = none := by
        rcases hop with rfl | rfl
        all_goals rfl
      simp only [ht]

#print axioms require_branch_checks
#print axioms require_jump_step
#print axioms require_jumpi_step
#print axioms require_branch_iteration

theorem store_writes (xs : Stack UInt256) : writes .SSTORE xs = true := by rfl
theorem load_writes (xs : Stack UInt256) : writes .SLOAD xs = false := by rfl

end EvmYul.EVM.DriverProof
