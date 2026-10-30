import Solidity.Backend.Creation.Placement

/-! Finite constructor-prefix composition for the exact instruction slice.
Prefixes carry actual fetch/effect step certificates, never the desired final
result. Source initializer/inheritance/account/payment semantics remain separate.
This byte-content slice does not model the EVM stack cap: PUSH grows the stack.
Pinned-EVM agreement needs resource handling and headroom (wrapper growth is at
most three entries); the arbitrary-stack theorem is only a slice theorem.
-/
namespace Solidity.Backend.Creation

inductive Prefix (code : List UInt8) : List UInt8 → List StackWord → List UInt8 →
    List UInt8 → List StackWord → List UInt8 → Prop where
  | refl (stream : List UInt8) (stack : List StackWord) (memory : List UInt8) :
      Prefix code stream stack memory stream stack memory
  | step {stream tail final : List UInt8} {stack stack' finalStack : List StackWord}
      {memory memory' finalMemory : List UInt8} {i : Instr}
      (fetches : fetch stream = some (i, tail))
      (acts : effect code i stack memory = some (.next stack' memory'))
      (rest : Prefix code tail stack' memory' final finalStack finalMemory) :
      Prefix code stream stack memory final finalStack finalMemory

theorem Prefix.exec {code start final : List UInt8} {stack finalStack : List StackWord}
    {memory finalMemory : List UInt8}
    (p : Prefix code start stack memory final finalStack finalMemory)
    {result : Outcome} (h : Exec code final finalStack finalMemory result) :
    Exec code start stack memory result := by
  induction p with
  | refl => exact h
  | step hf he rest ih =>
    obtain ⟨fuel, hrun⟩ := ih h
    exact ⟨fuel + 1, by simpa only [run, hf, he] using hrun⟩

theorem readBytes_length (bytes : List UInt8) (offset length : Nat) :
    (readBytes bytes offset length).length = length := by
  simp only [readBytes, List.length_append, List.length_take, List.length_replicate]
  omega

theorem read_write_zero (memory bytes : List UInt8) :
    readBytes (writeBytes memory 0 bytes) 0 bytes.length = bytes := by
  have hw : writeBytes memory 0 bytes = bytes ++
      (memory ++ List.replicate (bytes.length - memory.length) 0).drop bytes.length := by
    simp only [writeBytes, patchAt, List.take_zero, List.nil_append, Nat.zero_add]
  rw [hw, readBytes_in_bounds]
  · simp only [List.drop_zero, List.take_left]
  · simp only [List.length_append]; omega

def exitWrapper (success : Bool) (n off : Immediate) : Program :=
  [n.instr, off.instr, .push 0 #v[], .op .CODECOPY, n.instr, .push 0 #v[],
    .op (if success then .RETURN else .REVERT)]

def exitOutcome (success : Bool) (bytes : List UInt8) : Outcome :=
  if success then .returned bytes else .reverted bytes

theorem exitWrapper_size (success : Bool) (n off : Immediate) :
    size (exitWrapper success n off) = size (placedWrapper n off) := by
  cases success <;> rfl

/-- Arbitrary prefix memory and stack are allowed: the wrapper overwrites exactly
what it returns; prefix memory outside that range does not affect the result. -/
theorem exit_exec (success : Bool) (n off : Immediate) (code tail : List UInt8)
    (stack : List StackWord) (memory : List UInt8) :
    Exec code (encode (exitWrapper success n off) ++ tail) stack memory
      (exitOutcome success (readBytes code off.value n.value)) := by
  have hn : ofBytesBE (toBytesBE n.width.val n.value).toList % (256 ^ 32) = n.value := by
    rw [n.read, Nat.mod_eq_of_lt n.fits]
  have hoff : ofBytesBE (toBytesBE off.width.val off.value).toList % (256 ^ 32) = off.value := by
    rw [off.read, Nat.mod_eq_of_lt off.fits]
  have hz : ofBytesBE (#v[] : Vector UInt8 0).toList % (256 ^ 32) = 0 := rfl
  have hread : readBytes (writeBytes memory 0 (readBytes code off.value n.value)) 0 n.value =
      readBytes code off.value n.value := by
    simpa only [readBytes_length] using read_write_zero memory (readBytes code off.value n.value)
  unfold exitWrapper
  simp only [encode_cons, encode_nil, List.append_nil, List.append_assoc]
  apply Exec.push
  apply Exec.push
  apply Exec.push
  apply Exec.copy
  apply Exec.push
  apply Exec.push
  simp only [hn, hoff, hz]
  cases success
  · simpa only [exitOutcome, Bool.false_eq_true, if_false, hread] using
      Exec.revert (code := code) tail (⟨0, by decide⟩ : StackWord) ⟨n.value, n.fits⟩ stack
        (writeBytes memory 0 (readBytes code off.value n.value))
  · simpa only [exitOutcome, if_true, hread] using
      Exec.ret (code := code) tail (⟨0, by decide⟩ : StackWord) ⟨n.value, n.fits⟩ stack
        (writeBytes memory 0 (readBytes code off.value n.value))

theorem Placement.exit (p : Placement pre bytes) (success : Bool) (args : List UInt8)
    (stack : List StackWord) (memory : List UInt8) :
    let code := pre ++ encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args
    Exec code (encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args) stack memory
      (exitOutcome success bytes) := by
  dsimp only
  have hoff : p.offsetWord.value = (pre ++ encode (exitWrapper success p.lengthWord p.offsetWord)).length := by
    rw [List.length_append, length_encode, exitWrapper_size]
    exact p.aligned
  have hr : readBytes (pre ++ encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args)
      p.offsetWord.value p.lengthWord.value = bytes := by
    rw [hoff, p.length_eq, readBytes_in_bounds]
    · rw [List.append_assoc (pre ++ _), List.drop_left, List.take_left]
    · simp only [List.length_append]; omega
  have h : Exec (pre ++ encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args)
      (encode (exitWrapper success p.lengthWord p.offsetWord) ++ (bytes ++ args)) stack memory
      (exitOutcome success (readBytes (pre ++ encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args)
        p.offsetWord.value p.lengthWord.value)) := exit_exec success p.lengthWord p.offsetWord
    (pre ++ encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args)
    (bytes ++ args) stack memory
  rw [hr] at h
  simpa only [List.append_assoc] using h

/-- Constructor prefix execution followed by exact return or exact revert. -/
theorem constructor_compose (p : Placement pre bytes) (success : Bool) (args : List UInt8)
    (stack : List StackWord) (memory : List UInt8)
    (steps : Prefix (pre ++ encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args)
      (pre ++ encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args) [] []
      (encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args) stack memory) :
    let code := pre ++ encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args
    Exec code code [] [] (exitOutcome success bytes) :=
  steps.exec (p.exit success args stack memory)

end Solidity.Backend.Creation
