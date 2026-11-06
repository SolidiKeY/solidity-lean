import SolidityBridge.ExternalEvm.RequireLocalState

/-! Checked boundary views of existing pinned STATICCALL. No new call or static
semantics: the actual call computation and recursive X remain on the right. -/
namespace EvmYul.EVM.DriverProof

def staticMemoryCharged (s : State) : State :=
  {s with gasAvailable := s.gasAvailable - UInt256.ofNat (memoryExpansionCost s .STATICCALL)}

def staticCost (s : State) : Nat := C' (staticMemoryCharged s) .STATICCALL

def staticGuard (s : State) : Except ExecutionException Unit :=
  if s.gasAvailable.toNat < memoryExpansionCost s .STATICCALL then .error .OutOfGass
  else if (staticMemoryCharged s).gasAvailable.toNat < staticCost s then .error .OutOfGass
  else if s.stack.length < 6 then .error .StackUnderflow
  else if s.stack.length - 6 + 1 > 1024 then .error .StackOverflow
  else .ok ()

theorem static_arity : δ (.STATICCALL : Operation .EVM) = some 6 ∧
    α (.STATICCALL : Operation .EVM) = some 1 := ⟨rfl, rfl⟩

theorem static_nonterminal (s : State) : terminalData s .STATICCALL = none := rfl

theorem static_checks (dest : Array UInt256) (s : State)
    (hf : fetched s = (.STATICCALL, none)) :
    checks dest s = (do let _ ← staticGuard s; pure (staticMemoryCharged s, staticCost s)) := by
  simp only [checks, hf, δ, α, Option.getD_some, Operation.isCreate,
    reduceCtorEq, false_and, Bool.false_eq_true, if_false,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  unfold staticGuard staticMemoryCharged staticCost
  simp only [staticMemoryCharged]
  split_ifs <;> try rfl
  rename_i hm hg hs hc hw
  have hb : (false : Bool) = true := hw.2
  cases hb

/-- The state's real call result determines all later fields. No world or
private-memory preservation across the external computation is asserted. -/
def staticPost (bit : UInt256) (out : State) (tail : Stack UInt256) : State :=
  out.replaceStackAndIncrPC (bit :: tail)

theorem staticPost_fields (bit : UInt256) (out : State) (tail : Stack UInt256) :
    (staticPost bit out tail).stack = bit :: tail ∧
    (staticPost bit out tail).pc = out.pc + UInt256.ofNat 1 ∧
    (staticPost bit out tail).execLength = out.execLength ∧
    (staticPost bit out tail).toState = out.toState ∧
    (staticPost bit out tail).toMachineState = out.toMachineState := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem static_step_call (n cost : Nat) (s : State)
    (requested target inOffset inSize outOffset outSize : UInt256) (tail : Stack UInt256)
    (hs : s.stack = requested :: target :: inOffset :: inSize :: outOffset :: outSize :: tail) :
    step (n+1) cost (some (.STATICCALL, none)) s = (do
      let (bit, out) ← call n cost s.executionEnv.blobVersionedHashes requested
        (.ofNat s.executionEnv.codeOwner) target target (.ofNat 0) (.ofNat 0)
        inOffset inSize outOffset outSize false {s with execLength := s.execLength + 1}
      pure (staticPost bit out tail)) := by
  have h : step (n+1) cost (some (.STATICCALL, none))
      {s with stack := requested :: target :: inOffset :: inSize :: outOffset :: outSize :: tail} =
      (do let (bit,out) ← call n cost s.executionEnv.blobVersionedHashes requested
            (.ofNat s.executionEnv.codeOwner) target target (.ofNat 0) (.ofNat 0)
            inOffset inSize outOffset outSize false
            {{s with stack := requested :: target :: inOffset :: inSize :: outOffset :: outSize :: tail}
              with execLength := s.execLength + 1}
          pure (staticPost bit out tail)) := by rfl
  rw [local_stack_eta s _ hs] at h
  exact h

theorem static_memory_ranges (s : State)
    (requested target inOffset inSize outOffset outSize : UInt256) (tail : Stack UInt256)
    (hs : s.stack = requested :: target :: inOffset :: inSize :: outOffset :: outSize :: tail) :
    memoryExpansionCost s .STATICCALL =
      Cₘ (UInt256.ofNat (MachineState.M
        (MachineState.M s.activeWords.toNat inOffset.toNat inSize.toNat)
        outOffset.toNat outSize.toNat)) - Cₘ s.activeWords := by
  rw [← local_stack_eta s _ hs]
  rfl

theorem static_cost_zero_value (s : State)
    (requested target inOffset inSize outOffset outSize : UInt256) (tail : Stack UInt256)
    (hs : s.stack = requested :: target :: inOffset :: inSize :: outOffset :: outSize :: tail) :
    C' s .STATICCALL = Ccall (AccountAddress.ofUInt256 target)
      (AccountAddress.ofUInt256 target) (.ofNat 0) requested s.accountMap s.toMachineState s.substate := by
  rw [← local_stack_eta s _ hs]
  rfl

/-- Driver zero fuel, ordered checks, exhausted evaluator and all call cases.
The actual call's smaller fuel, cost, state and bit are retained. -/
def staticCut (fuel : Nat) (dest : Array UInt256) (s : State) :
    Except ExecutionException (ExecutionResult State) :=
  match fuel with
  | 0 => .error .OutOfFuel
  | 1 => do let _ ← staticGuard s; .error .OutOfFuel
  | n+2 => do
    let _ ← staticGuard s
    let next ← step (n+1) (staticCost s) (some (.STATICCALL, none)) (staticMemoryCharged s)
    X (n+1) dest next

theorem staticCut_exact (fuel : Nat) (dest : Array UInt256) (s : State)
    (hf : fetched s = (.STATICCALL, none)) : X fuel dest s = staticCut fuel dest s := by
  cases fuel with
  | zero => rfl
  | succ n =>
    rw [X_unfold, static_checks dest s hf, hf]
    cases hg : staticGuard s with
    | error err => cases n <;> simp only [staticCut, hg, Bind.bind, Except.bind]
    | ok tag =>
      cases tag
      cases n with
      | zero => simp only [staticCut, hg, Bind.bind, Except.bind, Pure.pure, Except.pure]; rfl
      | succ n => simp only [staticCut, hg, Bind.bind, Except.bind, Pure.pure, Except.pure, static_nonterminal]

theorem staticCut_call (n : Nat) (dest : Array UInt256) (s : State)
    (requested target inOffset inSize outOffset outSize : UInt256) (tail : Stack UInt256)
    (hs : s.stack = requested :: target :: inOffset :: inSize :: outOffset :: outSize :: tail) :
    staticCut (n+2) dest s = (do
      let _ ← staticGuard s
      let (bit,out) ← call n (staticCost s) s.executionEnv.blobVersionedHashes requested
        (.ofNat s.executionEnv.codeOwner) target target (.ofNat 0) (.ofNat 0)
        inOffset inSize outOffset outSize false
        {staticMemoryCharged s with execLength := s.execLength + 1}
      X (n+1) dest (staticPost bit out tail)) := by
  change (do let _ ← staticGuard s
             let next ← step (n+1) (staticCost s) (some (.STATICCALL, none)) (staticMemoryCharged s)
             X (n+1) dest next) = _
  rw [static_step_call n (staticCost s) (staticMemoryCharged s)
    requested target inOffset inSize outOffset outSize tail hs]
  cases hg : staticGuard s with
  | error err => rfl
  | ok tag =>
    cases he : call n (staticCost s) s.executionEnv.blobVersionedHashes requested
      (.ofNat s.executionEnv.codeOwner) target target (.ofNat 0) (.ofNat 0)
      inOffset inSize outOffset outSize false
      {staticMemoryCharged s with execLength := s.execLength + 1} with
    | error err =>
      simp only [staticMemoryCharged] at he ⊢
      simp only [he, Bind.bind, Except.bind]
    | ok pair =>
      cases pair
      simp only [staticMemoryCharged] at he ⊢
      simp only [he, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem static_memory_fault (s : State)
    (h : s.gasAvailable.toNat < memoryExpansionCost s .STATICCALL) :
    staticGuard s = .error .OutOfGass := by unfold staticGuard; rw [if_pos h]

theorem static_opcode_fault (s : State)
    (hm : ¬ s.gasAvailable.toNat < memoryExpansionCost s .STATICCALL)
    (hc : (staticMemoryCharged s).gasAvailable.toNat < staticCost s) :
    staticGuard s = .error .OutOfGass := by unfold staticGuard; rw [if_neg hm, if_pos hc]

theorem static_underflow (s : State)
    (hm : ¬ s.gasAvailable.toNat < memoryExpansionCost s .STATICCALL)
    (hc : ¬ (staticMemoryCharged s).gasAvailable.toNat < staticCost s)
    (hs : s.stack.length < 6) : staticGuard s = .error .StackUnderflow := by
  unfold staticGuard; rw [if_neg hm, if_neg hc, if_pos hs]

theorem static_overflow (s : State)
    (hm : ¬ s.gasAvailable.toNat < memoryExpansionCost s .STATICCALL)
    (hc : ¬ (staticMemoryCharged s).gasAvailable.toNat < staticCost s)
    (hs : ¬ s.stack.length < 6) (ht : s.stack.length - 6 + 1 > 1024) :
    staticGuard s = .error .StackOverflow := by
  unfold staticGuard; rw [if_neg hm, if_neg hc, if_neg hs, if_pos ht]

/-- Provenance BEFORE the real call, not a preservation law across it. The
opcode debit is performed inside the existing call using its cost parameter. -/
theorem static_precall_fields (s : State) :
    ({staticMemoryCharged s with execLength := s.execLength + 1} : State).toState = s.toState ∧
    ({staticMemoryCharged s with execLength := s.execLength + 1} : State).memory = s.memory ∧
    ({staticMemoryCharged s with execLength := s.execLength + 1} : State).returnData = s.returnData ∧
    ({staticMemoryCharged s with execLength := s.execLength + 1} : State).pc = s.pc ∧
    ({staticMemoryCharged s with execLength := s.execLength + 1} : State).execLength = s.execLength + 1 ∧
    ({staticMemoryCharged s with execLength := s.execLength + 1} : State).gasAvailable =
      s.gasAvailable - UInt256.ofNat (memoryExpansionCost s .STATICCALL) := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end EvmYul.EVM.DriverProof
