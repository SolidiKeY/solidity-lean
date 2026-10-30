import Solidity.Backend.Creation.Execution

/-! Relocated wrapper slices, with an explicit arithmetic layout certificate.
The offset width is the existing minimal `byteWidth` of the chosen offset.
A pre-entry theorem assumes only byte layout and empty stack/memory at entry;
execution of arbitrary constructors is not assumed. -/
namespace Solidity.Backend.Creation

def placedWrapper (n off : Immediate) : Program :=
  [n.instr, off.instr, .push 0 #v[], .op .CODECOPY, n.instr, .push 0 #v[], .op .RETURN]

theorem placed_size (n off : Immediate) :
    size (placedWrapper n off) = 2 * n.width.val + off.width.val + 7 := by
  simp only [placedWrapper, size, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Immediate.instr, Instr.size]
  omega

theorem placed_exec (n off : Immediate) (code tail : List UInt8) :
    Exec code (encode (placedWrapper n off) ++ tail) [] []
      (.returned (readBytes (readBytes code off.value n.value) 0 n.value)) := by
  have hn : ofBytesBE (toBytesBE n.width.val n.value).toList % (256 ^ 32) = n.value := by
    rw [n.read, Nat.mod_eq_of_lt n.fits]
  have hoff : ofBytesBE (toBytesBE off.width.val off.value).toList % (256 ^ 32) = off.value := by
    rw [off.read, Nat.mod_eq_of_lt off.fits]
  have hz : ofBytesBE (#v[] : Vector UInt8 0).toList % (256 ^ 32) = 0 := rfl
  unfold placedWrapper
  simp only [encode_cons, encode_nil, List.append_nil, List.append_assoc]
  apply Exec.push
  apply Exec.push
  apply Exec.push
  apply Exec.copy
  apply Exec.push
  apply Exec.push
  simp only [hn, hoff, hz, writeBytes_empty]
  apply Exec.ret

/-- Alignment is a computable byte-length equality, never an execution premise. -/
structure Placement (pre runtime : List UInt8) where
  lengthWord : Immediate
  length_eq : lengthWord.value = runtime.length
  offsetWord : Immediate
  aligned : offsetWord.value = pre.length + size (placedWrapper lengthWord offsetWord)

theorem Placement.installs (p : Placement pre runtime) (args : List UInt8) :
    let code := pre ++ encode (placedWrapper p.lengthWord p.offsetWord) ++ runtime ++ args
    Exec code (encode (placedWrapper p.lengthWord p.offsetWord) ++ runtime ++ args) [] []
      (.returned runtime) := by
  dsimp only
  have hoff : p.offsetWord.value = (pre ++ encode (placedWrapper p.lengthWord p.offsetWord)).length := by
    rw [List.length_append, length_encode]
    exact p.aligned
  have hr : readBytes (pre ++ encode (placedWrapper p.lengthWord p.offsetWord) ++ runtime ++ args)
      p.offsetWord.value p.lengthWord.value = runtime := by
    rw [hoff, p.length_eq, readBytes_in_bounds]
    · rw [List.append_assoc (pre ++ _), List.drop_left, List.take_left]
    · simp only [List.length_append]; omega
  have h : Exec (pre ++ encode (placedWrapper p.lengthWord p.offsetWord) ++ runtime ++ args)
      (encode (placedWrapper p.lengthWord p.offsetWord) ++ (runtime ++ args)) [] []
      (.returned (readBytes (readBytes (pre ++ encode (placedWrapper p.lengthWord p.offsetWord) ++ runtime ++ args)
        p.offsetWord.value p.lengthWord.value) 0 p.lengthWord.value)) := placed_exec p.lengthWord p.offsetWord
    (pre ++ encode (placedWrapper p.lengthWord p.offsetWord) ++ runtime ++ args) (runtime ++ args)
  rw [hr, p.length_eq, readBytes_self] at h
  simpa only [List.append_assoc] using h

end Solidity.Backend.Creation
