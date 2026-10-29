import Solidity.Backend.Creation.Constructor

namespace Solidity.Backend.Creation

/-- A real nonempty prefix: copies the first code byte to memory offset 32. -/
def copyPrefix : Program := [.push 1 #v[1], .push 0 #v[], .push 1 #v[32], .op .CODECOPY]

theorem copyPrefix_steps (code tail : List UInt8) :
    Prefix code (encode copyPrefix ++ tail) [] [] tail []
      (writeBytes [] 32 (readBytes code 0 1)) := by
  unfold copyPrefix
  simp only [encode_cons, encode_nil, List.append_nil, List.append_assoc]
  apply Prefix.step (fetch_encode (.push 1 #v[1]) _) rfl
  apply Prefix.step (fetch_encode (.push 0 #v[]) _) rfl
  apply Prefix.step (fetch_encode (.push 1 #v[32]) _) rfl
  apply Prefix.step (fetch_encode (.op .CODECOPY) _) rfl
  exact Prefix.refl _ _ _

def copyPlacement (bytes : List UInt8) (hlen : bytes.length = 3) : Placement (encode copyPrefix) bytes where
  lengthWord := ⟨3, by decide⟩
  length_eq := hlen.symm
  offsetWord := ⟨16, by decide⟩
  aligned := by
    rw [placed_size, length_encode]
    change 16 = 6 + (2 * byteWidth 3 + byteWidth 16 + 7)
    rw [byteWidth_small 3 (by decide) (by decide), byteWidth_small 16 (by decide) (by decide)]

theorem copyConstructor (success : Bool) (bytes args : List UInt8) (hlen : bytes.length = 3) :
    let p := copyPlacement bytes hlen
    let code := encode copyPrefix ++ encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args
    Exec code code [] [] (exitOutcome success bytes) := by
  dsimp only
  apply constructor_compose (copyPlacement bytes hlen) success args []
    (writeBytes [] 32 (readBytes (encode copyPrefix ++ encode (exitWrapper success
      (copyPlacement bytes hlen).lengthWord (copyPlacement bytes hlen).offsetWord) ++ bytes ++ args) 0 1))
  simpa only [List.append_assoc] using copyPrefix_steps
    (encode copyPrefix ++ encode (exitWrapper success (copyPlacement bytes hlen).lengthWord
      (copyPlacement bytes hlen).offsetWord) ++ bytes ++ args)
    (encode (exitWrapper success (copyPlacement bytes hlen).lengthWord
      (copyPlacement bytes hlen).offsetWord) ++ bytes ++ args)

example : let p := copyPlacement [0x60, 0x2a, 0] rfl
    let code := encode copyPrefix ++ encode (exitWrapper true p.lengthWord p.offsetWord) ++ [0x60, 0x2a, 0] ++ [0xaa, 0xbb]
    Exec code code [] [] (.returned [0x60, 0x2a, 0]) := copyConstructor true _ _ rfl

example : let p := copyPlacement [0xde, 0xad, 0xbe] rfl
    let code := encode copyPrefix ++ encode (exitWrapper false p.lengthWord p.offsetWord) ++ [0xde, 0xad, 0xbe] ++ [0xaa, 0xbb]
    Exec code code [] [] (.reverted [0xde, 0xad, 0xbe]) := copyConstructor false _ _ rfl

example : let p := copyPlacement [0xde, 0xad, 0xbe] rfl
    let code := encode copyPrefix ++ encode (exitWrapper false p.lengthWord p.offsetWord) ++ [0xde, 0xad, 0xbe] ++ [0xaa]
    ¬ Exec code code [] [] (.returned [0xde, 0xad, 0xbe]) := by
  dsimp only
  intro h
  have he : Outcome.reverted [0xde, 0xad, 0xbe] = .returned [0xde, 0xad, 0xbe] := Exec.deterministic (copyConstructor false [0xde, 0xad, 0xbe] [0xaa] rfl) h
  cases he

example : let p := copyPlacement [0xde, 0xad, 0xbe] rfl
    let code := encode copyPrefix ++ encode (exitWrapper false p.lengthWord p.offsetWord) ++ [0xde, 0xad, 0xbe] ++ [0xaa]
    ¬ Exec code code [] [] (.reverted [0xde, 0xad]) := by
  dsimp only
  intro h
  have he : Outcome.reverted [0xde, 0xad, 0xbe] = .reverted [0xde, 0xad] :=
    Exec.deterministic (copyConstructor false [0xde, 0xad, 0xbe] [0xaa] rfl) h
  have hn : Outcome.reverted [0xde, 0xad, 0xbe] ≠ .reverted [0xde, 0xad] := by decide
  exact hn he

example : let p := copyPlacement [0xde, 0xad, 0xbe] rfl
    let code := encode copyPrefix ++ encode (exitWrapper false p.lengthWord p.offsetWord) ++ [0xde, 0xad, 0xbe] ++ [0xaa]
    ¬ Exec code code [] [] (.reverted [0xde, 0xad, 0xbe, 0xaa]) := by
  dsimp only
  intro h
  have he : Outcome.reverted [0xde, 0xad, 0xbe] = .reverted [0xde, 0xad, 0xbe, 0xaa] :=
    Exec.deterministic (copyConstructor false [0xde, 0xad, 0xbe] [0xaa] rfl) h
  have hn : Outcome.reverted [0xde, 0xad, 0xbe] ≠ .reverted [0xde, 0xad, 0xbe, 0xaa] := by decide
  exact hn he

#print axioms Prefix.exec
#print axioms exit_exec
#print axioms constructor_compose
#print axioms copyConstructor
end Solidity.Backend.Creation
