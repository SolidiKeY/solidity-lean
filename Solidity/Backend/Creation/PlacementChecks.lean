import Solidity.Backend.Creation.Placement

namespace Solidity.Backend.Creation

theorem byteWidth_257 : byteWidth 257 = 2 := by
  rw [byteWidth]
  simp only [show (257 : Nat) ≠ 0 by decide, if_false]
  change byteWidth 1 + 1 = 2
  rw [byteWidth_small 1 (by decide) (by decide)]

def placement255 : Placement (List.replicate 245 0) [0x60, 0x2a, 0] where
  lengthWord := ⟨3, by decide⟩
  length_eq := rfl
  offsetWord := ⟨255, by decide⟩
  aligned := by
    rw [placed_size]
    simp only [List.length_replicate, Immediate.width]
    rw [byteWidth_small 3 (by decide) (by decide), byteWidth_small 255 (by decide) (by decide)]

def placement257 : Placement (List.replicate 246 0) [0x60, 0x2a, 0] where
  lengthWord := ⟨3, by decide⟩
  length_eq := rfl
  offsetWord := ⟨257, by decide⟩
  aligned := by
    rw [placed_size]
    simp only [List.length_replicate, Immediate.width]
    rw [byteWidth_small 3 (by decide) (by decide), byteWidth_257]

example : placement255.offsetWord.width.val = 1 :=
  byteWidth_small 255 (by decide) (by decide)
example : placement257.offsetWord.width.val = 2 := byteWidth_257
example : Exec (List.replicate 245 0 ++ encode (placedWrapper placement255.lengthWord placement255.offsetWord) ++ [0x60, 0x2a, 0] ++ [0xaa])
    (encode (placedWrapper placement255.lengthWord placement255.offsetWord) ++ [0x60, 0x2a, 0] ++ [0xaa])
    [] [] (.returned [0x60, 0x2a, 0]) := placement255.installs [0xaa]
example : Exec (List.replicate 246 0 ++ encode (placedWrapper placement257.lengthWord placement257.offsetWord) ++ [0x60, 0x2a, 0] ++ [0xbb])
    (encode (placedWrapper placement257.lengthWord placement257.offsetWord) ++ [0x60, 0x2a, 0] ++ [0xbb])
    [] [] (.returned [0x60, 0x2a, 0]) := placement257.installs [0xbb]

/-- info: 'Solidity.Backend.Creation.fetch_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fetch_encode
/-- info: 'Solidity.Backend.Creation.Placement.installs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Placement.installs
end Solidity.Backend.Creation
