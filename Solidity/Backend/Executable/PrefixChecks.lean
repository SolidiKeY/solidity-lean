import Solidity.Backend.Executable.Prefix
import Solidity.Backend.Creation.ConstructorChecks

/-! Inhabited segmented byte prefixes, protected stack tails and distinct exits.
These controls consume the existing nonempty CODECOPY constructor fixture. -/
namespace Solidity.Backend.Executable.PrefixChecks
open Creation

def zero : StackWord := ⟨0, by decide⟩
def one : StackWord := ⟨1, by decide⟩

/-- The first two pushes leave actual operands for the second segment. -/
theorem first_segment (code tail : List UInt8) :
    Prefix code (encode copyPrefix ++ tail) [] []
      (encode [.push 1 #v[32], .op .CODECOPY] ++ tail) [zero, one] [] := by
  unfold copyPrefix
  simp only [encode_cons, encode_nil, List.append_nil, List.append_assoc]
  apply Prefix.step (fetch_encode (.push 1 #v[1]) _) rfl
  apply Prefix.step (fetch_encode (.push 0 #v[]) _) rfl
  exact .refl _ _ _

/-- CODECOPY consumes only its three operands and writes nonempty memory. -/
theorem second_segment (code tail : List UInt8) :
    Prefix code (encode [.push 1 #v[32], .op .CODECOPY] ++ tail) [zero, one] []
      tail [] (writeBytes [] 32 (readBytes code 0 1)) := by
  simp only [encode_cons, encode_nil, List.append_nil, List.append_assoc]
  apply Prefix.step (fetch_encode (.push 1 #v[32]) _) rfl
  apply Prefix.step (fetch_encode (.op .CODECOPY) _) rfl
  exact .refl _ _ _

/-- A protected two-word suffix survives both nonempty segments. -/
theorem nonempty_prefix_frame (code tail : List UInt8) :
    Prefix code (encode copyPrefix ++ tail) [one, zero] [] tail [one, zero]
      (writeBytes [] 32 (readBytes code 0 1)) :=
  prefix_stack_tail (prefix_trans (first_segment code tail) (second_segment code tail)) [one, zero]

/-- Actual two-segment constructor execution, for any certified placement. -/
theorem segmented (p : Placement (encode copyPrefix) bytes) (success : Bool)
    (args : List UInt8) (tail : List StackWord) :
    let code := encode copyPrefix ++ encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args
    Exec code code tail [] (exitOutcome success bytes) := by
  let code : List UInt8 := encode copyPrefix ++ encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args
  let final : List UInt8 := encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args
  apply constructor_segments p success args
    (encode [.push 1 #v[32], .op .CODECOPY] ++ final) [zero, one] [] tail []
    (writeBytes [] 32 (readBytes code 0 1))
  · simpa only [code, final, List.append_assoc] using first_segment code final
  · exact second_segment code final

/-- Nonempty runtime and nonempty arguments with a protected two-word tail. -/
theorem segmented_word (success : Bool) :
    let p := copyPlacement [0xde, 0xad, 0xbe] rfl
    let code := encode copyPrefix ++ encode (exitWrapper success p.lengthWord p.offsetWord) ++
      [0xde, 0xad, 0xbe] ++ [0xaa, 0xbb]
    Exec code code [one, zero] [] (exitOutcome success [0xde, 0xad, 0xbe]) :=
  segmented (copyPlacement [0xde, 0xad, 0xbe] rfl) success [0xaa, 0xbb] [one, zero]

def emptyPlacement : Placement (encode copyPrefix) [] where
  lengthWord := ⟨0, by decide⟩
  length_eq := rfl
  offsetWord := ⟨14, by decide⟩
  aligned := by
    rw [placed_size, length_encode]
    change 14 = 6 + (2 * byteWidth 0 + byteWidth 14 + 7)
    rw [byteWidth_small 14 (by decide) (by decide)]
    rw [byteWidth]
    rfl

/-- Empty runtime uses the same two real segments and a nonempty caller tail. -/
theorem segmented_empty (success : Bool) :
    let p := emptyPlacement
    let code := encode copyPrefix ++ encode (exitWrapper success p.lengthWord p.offsetWord) ++ [] ++ [0xaa]
    Exec code code [one] [] (exitOutcome success []) :=
  segmented emptyPlacement success [0xaa] [one]

/-- RETURN and REVERT stay distinct even when the returned byte list is empty. -/
example : let p := emptyPlacement
    let code := encode copyPrefix ++ encode (exitWrapper true p.lengthWord p.offsetWord) ++ [] ++ [0xaa]
    ¬ Exec code code [one] [] (.reverted []) :=
  returned_excludes_reverted (segmented_empty true)

/-- Appended constructor arguments cannot be reported as failure payload bytes. -/
example : let p := copyPlacement [0xde, 0xad, 0xbe] rfl
    let code := encode copyPrefix ++ encode (exitWrapper false p.lengthWord p.offsetWord) ++
      [0xde, 0xad, 0xbe] ++ [0xaa, 0xbb]
    ¬ Exec code code [one, zero] [] (.reverted [0xde, 0xad, 0xbe, 0xaa, 0xbb]) := by
  dsimp only
  intro bad
  have wrong : ([0xde, 0xad, 0xbe] : List UInt8) = [0xde, 0xad, 0xbe, 0xaa, 0xbb] :=
    reverted_bytes_unique (segmented_word false) bad
  cases wrong

/-- Prefix framing does not authorize CODECOPY to take missing operands from a caller tail. -/
example : effect [] (.op .CODECOPY) [one, zero] [] = none := rfl

end Solidity.Backend.Executable.PrefixChecks
