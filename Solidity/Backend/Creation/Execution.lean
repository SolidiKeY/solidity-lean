import Solidity.Backend.Creation.Artifact

/-!
Independent semantics of the exact creation instruction slice. `Exec` consumes
raw instruction bytes from the front, using the existing intrinsic `Instr`.
PUSH values are reduced modulo the stack-word modulus. Memory reads and CODECOPY
zero-pad. Memory represents byte contents, not rounded allocation size or gas. Unsupported instructions have no derivation; this is not a full EVM,
gas/account/CREATE semantics. The initial creation memory/stack are empty.
-/
namespace Solidity.Backend.Creation

abbrev StackWord := Fin (256 ^ 32)

/-- EVM byte-range read, including zero-padding outside allocated bytes. -/
def readBytes (bytes : List UInt8) (offset length : Nat) : List UInt8 :=
  (bytes.drop offset).take length ++ List.replicate (length - (bytes.drop offset).length) 0

/-- Grow memory with zeroes, then overwrite the selected interval. -/
def writeBytes (memory : List UInt8) (offset : Nat) (bytes : List UInt8) : List UInt8 :=
  patchAt (memory ++ List.replicate (offset + bytes.length - memory.length) 0) offset bytes

inductive Outcome where
  | returned (bytes : List UInt8)
  | reverted (bytes : List UInt8)
  deriving DecidableEq, Repr

/-- Decode exactly one instruction, refusing truncated PUSH data. -/
def fetch : List UInt8 → Option (Instr × List UInt8)
  | [] => none
  | b :: bs =>
    match pushWidth b with
    | some n =>
      if h : n.val ≤ bs.length then
        some (.push n ⟨(bs.take n).toArray, by simp only [List.size_toArray, List.length_take]; omega⟩,
          bs.drop n)
      else none
    | none => (Op.ofCode b).map (fun o => (.op o, bs))

theorem fetch_encode (i : Instr) (tail : List UInt8) :
    fetch (i.encode ++ tail) = some (i, tail) := by
  cases i with
  | op o =>
    simp only [Instr.encode, List.cons_append, List.nil_append, fetch,
      Op.pushWidth_code, Op.ofCode_code, Option.map_some]
  | push n imm =>
    have hlen : n.val ≤ (imm.toList ++ tail).length := by
      simp only [List.length_append, Vector.length_toList]; omega
    have ht : (imm.toList ++ tail).take n = imm.toList := List.take_left' Vector.length_toList
    have hd : (imm.toList ++ tail).drop n = tail := List.drop_left' Vector.length_toList
    simp only [Instr.encode, List.cons_append, fetch, pushWidth_pushCode, hlen,
      dite_true, hd, Option.some.injEq, Prod.mk.injEq, and_true]
    congr

inductive Effect where
  | next (stack : List StackWord) (memory : List UInt8)
  | halt (result : Outcome)

/-- Instruction meaning, independent of its byte location and wrapper layout. -/
def effect (code : List UInt8) : Instr → List StackWord → List UInt8 → Option Effect
  | .push _ imm, stack, memory => some (.next
      (⟨ofBytesBE imm.toList % (256 ^ 32), Nat.mod_lt _ (by decide)⟩ :: stack) memory)
  | .op .CODECOPY, destination :: source :: length :: stack, memory =>
      some (.next stack (writeBytes memory destination.val (readBytes code source.val length.val)))
  | .op .RETURN, offset :: length :: _, memory =>
      some (.halt (.returned (readBytes memory offset.val length.val)))
  | .op .REVERT, offset :: length :: _, memory =>
      some (.halt (.reverted (readBytes memory offset.val length.val)))
  | _, _, _ => none

/-- Fuel bounds only this finite slice runner, not source recursion or gas. -/
def run : Nat → List UInt8 → List UInt8 → List StackWord → List UInt8 → Option Outcome
  | 0, _, _, _, _ => none
  | fuel + 1, code, stream, stack, memory =>
    match fetch stream with
    | none => none
    | some (i, tail) =>
      match effect code i stack memory with
      | none => none
      | some (.next stack' memory') => run fuel code tail stack' memory'
      | some (.halt result) => some result

/-- Actual finite byte execution, with empty creation stack/memory supplied by
installation theorems. Unsupported instructions and stack underflow are refused. -/
def Exec (code stream : List UInt8) (stack : List StackWord) (memory : List UInt8)
    (result : Outcome) : Prop := ∃ fuel, run fuel code stream stack memory = some result

theorem run_add {fuel : Nat} {code stream : List UInt8} {stack : List StackWord}
    {memory : List UInt8} {result : Outcome}
    (h : run fuel code stream stack memory = some result) (extra : Nat) :
    run (fuel + extra) code stream stack memory = some result := by
  induction fuel generalizing stream stack memory with
  | zero => cases h
  | succ fuel ih =>
    simp only [run] at h
    cases hf : fetch stream with
    | none => simp only [hf] at h; cases h
    | some pair =>
      obtain ⟨i, tail⟩ := pair
      simp only [hf] at h
      cases he : effect code i stack memory with
      | none => simp only [he] at h; cases h
      | some e =>
        cases e with
        | next stack' memory' =>
          simp only [he] at h
          simpa only [Nat.succ_add, run, hf, he] using ih h
        | halt r =>
          simpa only [Nat.succ_add, run, hf, he] using h

theorem Exec.deterministic {code stream : List UInt8} {stack : List StackWord}
    {memory : List UInt8} {r s : Outcome}
    (hr : Exec code stream stack memory r) (hs : Exec code stream stack memory s) : r = s := by
  obtain ⟨n, hn⟩ := hr
  obtain ⟨m, hm⟩ := hs
  have hnm : run (n + m) code stream stack memory = some r := run_add hn m
  have hmn : run (m + n) code stream stack memory = some s := run_add hm n
  rw [Nat.add_comm m n, hnm] at hmn
  exact Option.some.inj hmn

theorem Exec.push (n : Fin 33) (imm : Vector UInt8 n) (tail : List UInt8)
    (stack : List StackWord) (memory : List UInt8) (result : Outcome)
    (next : Exec code tail
      (⟨ofBytesBE imm.toList % (256 ^ 32), Nat.mod_lt _ (by decide)⟩ :: stack) memory result) :
    Exec code (Instr.encode (.push n imm) ++ tail) stack memory result := by
  obtain ⟨fuel, h⟩ := next
  exact ⟨fuel + 1, by simpa only [run, fetch_encode, effect] using h⟩

theorem Exec.copy (tail : List UInt8) (destination source length : StackWord)
    (stack : List StackWord) (memory : List UInt8) (result : Outcome)
    (next : Exec code tail stack
      (writeBytes memory destination.val (readBytes code source.val length.val)) result) :
    Exec code (Instr.encode (.op .CODECOPY) ++ tail)
      (destination :: source :: length :: stack) memory result := by
  obtain ⟨fuel, h⟩ := next
  exact ⟨fuel + 1, by simpa only [run, fetch_encode, effect] using h⟩

theorem Exec.ret (tail : List UInt8) (offset length : StackWord) (stack : List StackWord)
    (memory : List UInt8) :
    Exec code (Instr.encode (.op .RETURN) ++ tail) (offset :: length :: stack) memory
      (.returned (readBytes memory offset.val length.val)) :=
  ⟨1, by simp only [run, fetch_encode, effect]⟩

theorem Exec.revert (tail : List UInt8) (offset length : StackWord) (stack : List StackWord)
    (memory : List UInt8) :
    Exec code (Instr.encode (.op .REVERT) ++ tail) (offset :: length :: stack) memory
      (.reverted (readBytes memory offset.val length.val)) :=
  ⟨1, by simp only [run, fetch_encode, effect]⟩

theorem readBytes_in_bounds (bytes : List UInt8) (offset length : Nat)
    (h : offset + length ≤ bytes.length) :
    readBytes bytes offset length = (bytes.drop offset).take length := by
  have hz : length - (bytes.drop offset).length = 0 := by
    rw [List.length_drop]
    omega
  simp only [readBytes, hz, List.replicate_zero, List.append_nil]

theorem readBytes_self (bytes : List UInt8) : readBytes bytes 0 bytes.length = bytes := by
  rw [readBytes_in_bounds bytes 0 bytes.length (by omega)]
  simp only [List.drop_zero, List.take_length]

theorem writeBytes_empty (bytes : List UInt8) : writeBytes [] 0 bytes = bytes := by
  simp only [writeBytes, List.length_nil, Nat.zero_add, Nat.sub_zero, List.nil_append,
    patchAt, List.take_zero, List.nil_append, List.drop_replicate, Nat.sub_self, List.replicate_zero,
    List.append_nil]

theorem Artifact.read_runtime (a : Artifact Lib) :
    readBytes a.payload a.runtimeStart a.runtime.length = a.runtime := by
  have h : a.runtimeStart + a.runtime.length ≤ a.payload.length := by
    simp only [Artifact.payload, List.length_append, Artifact.initcode_length,
      Artifact.argsStart]
    omega
  rw [readBytes_in_bounds _ _ _ h]
  exact a.runtime_slice

/-- Generic execution lemma: bytes consumed by a wrapper are checked separately
from the copied range; `code` can be any input. -/
theorem wrapper_exec (n : Immediate) (code tail : List UInt8) :
    Exec code (encode (wrapper n) ++ tail) [] []
      (.returned (readBytes (readBytes code (runtimeOffset n) n.value) 0 n.value)) := by
  have hn : ofBytesBE (toBytesBE n.width.val n.value).toList % (256 ^ 32) = n.value := by
    rw [n.read, Nat.mod_eq_of_lt n.fits]
  have hoff : ofBytesBE (toBytesBE 1 (runtimeOffset n)).toList % (256 ^ 32) = runtimeOffset n := by
    rw [ofBytesBE_toBytesBE 1 _ (runtimeOffset_fits n)]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (runtimeOffset_fits n) (by decide))
  have hz : ofBytesBE (#v[] : Vector UInt8 0).toList % (256 ^ 32) = 0 := rfl
  unfold wrapper
  simp only [encode_cons, encode_nil, List.append_nil, List.append_assoc]
  apply Exec.push
  apply Exec.push
  apply Exec.push
  apply Exec.copy
  apply Exec.push
  apply Exec.push
  simp only [hn, hoff, hz, writeBytes_empty]
  apply Exec.ret

/-- Supplied runtime is installed by RETURN in this slice, for every byte list,
including empty runtime and arbitrary distinct constructor arguments. -/
theorem installs_runtime (a : Artifact Lib) :
    Exec a.payload a.payload [] [] (.returned a.runtime) := by
  have h : Exec a.payload (encode (wrapper a.lengthWord) ++ (a.runtime ++ a.args)) [] []
      (.returned (readBytes (readBytes a.payload (runtimeOffset a.lengthWord)
        a.lengthWord.value) 0 a.lengthWord.value)) := wrapper_exec a.lengthWord a.payload (a.runtime ++ a.args)
  change Exec a.payload (encode (wrapper a.lengthWord) ++ (a.runtime ++ a.args)) [] []
    (.returned (readBytes (readBytes a.payload a.runtimeStart a.runtime.length) 0 a.runtime.length)) at h
  rw [a.read_runtime, readBytes_self] at h
  simpa only [Artifact.payload, Artifact.initcode, List.append_assoc] using h

end Solidity.Backend.Creation
