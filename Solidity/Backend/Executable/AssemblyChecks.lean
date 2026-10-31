import Solidity.Backend.Executable.Assembly
import Solidity.Backend.Executable.PrefixChecks

/-! A real assembled backedge embedded behind a nonempty creation prefix.
The runtime target is zero, while its embedded creation offset is sixteen. -/
namespace Solidity.Backend.Executable.AssemblyChecks
open Creation PrefixChecks

def backedge : List (Item Nat Empty) := [.tag 0, .pushTag 0, .instr (.op .JUMP)]
def output : Assembled Empty := ⟨[.op .JUMPDEST, .push 0 #v[], .op .JUMP], []⟩

theorem actual_assembly : assemble 0 (fun x : Empty => nomatch x) backedge = some output := by
  have tag : tagOffset (fun _ : Nat => (0 : Fin 33)) backedge 0 = 0 := rfl
  have widened : widen 0 backedge (fun _ => 0) 0 = (0 : Fin 33) := by
    apply Fin.ext
    change min 32 (max 0 (byteWidth (0 + tagOffset (fun _ => 0) backedge 0))) = 0
    rw [tag, Nat.zero_add, byteWidth]
    rfl
  have fixed : (refs backedge).all (fun l => widen 0 backedge (fun _ => 0) l == (0 : Fin 33)) = true := by
    change (widen 0 backedge (fun _ => 0) 0 == (0 : Fin 33)) && true = true
    rw [widened]
    rfl
  have layout : layoutOk 0 backedge (fun _ => 0) = true := by decide +kernel
  unfold assemble asmWidths
  rw [fixWidths]
  simp only [fixed, dite_true, layout, if_true]
  rfl

def placement : Placement (encode copyPrefix) (encode output.code) :=
  copyPlacement [0x5b, 0x5f, 0x56] rfl

/-- Both constructor segments are inhabited; the returned runtime bytes retain the
actual assembled target and exact decoding, behind a two-word caller suffix. -/
theorem installed_backedge :
    let p := placement
    let code := encode copyPrefix ++ encode (exitWrapper true p.lengthWord p.offsetWord) ++
      encode output.code ++ [0xaa, 0xbb]
    Exec code code [one, zero] [] (.returned (encode output.code)) ∧
    decode (encode output.code) = some output.code ∧
    ∃ j imm, tagIndex backedge 0 = some j ∧
      output.code[j]? = some (.op .JUMPDEST) ∧
      output.code[1]? = some (.push (asmWidths 0 backedge 0) imm) ∧
      ofBytesBE imm.toList = offset output.code j ∧
      validJumpdest (encode output.code) (ofBytesBE imm.toList) = true := by
  let code : List UInt8 := encode copyPrefix ++ encode (exitWrapper true placement.lengthWord placement.offsetWord) ++
      encode output.code ++ [0xaa, 0xbb]
  let final : List UInt8 := encode (exitWrapper true placement.lengthWord placement.offsetWord) ++
      encode output.code ++ [0xaa, 0xbb]
  apply assembled_constructor_segments actual_assembly placement [0xaa, 0xbb]
    (encode [.push 1 #v[32], .op .CODECOPY] ++ final) [zero, one] [] [one, zero] []
    (writeBytes [] 32 (readBytes code 0 1))
  · simpa only [code, final, List.append_assoc] using first_segment code final
  · exact second_segment code final
  · rfl

/-- Mistaking a creation-image offset for a runtime offset is rejected. -/
example : placement.offsetWord.value = 16 ∧
    validJumpdest (encode output.code) 0 = true ∧
    validJumpdest (encode output.code) placement.offsetWord.value = false := by
  refine ⟨rfl, ?_, ?_⟩
  · simpa only [List.append_nil] using
      (validJumpdest_encode_append (p := output.code) (X := []) (k := 0) rfl)
  · apply Bool.eq_false_iff.mpr
    intro bad
    have impossible := (validJumpdest_iff _ _).mp bad
    have wrong : (encode output.code)[16]? = some Op.JUMPDEST.code := impossible.1
    cases wrong

/-- The branch instruction is actually present after the zero-target PUSH. -/
example : encode output.code = [0x5b, 0x5f, 0x56] := rfl

end Solidity.Backend.Executable.AssemblyChecks
