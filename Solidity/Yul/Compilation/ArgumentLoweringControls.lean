import Solidity.Yul.Compilation.ArgumentLowering
import Solidity.Yul.Compilation.PureLoweringControls

namespace Solidity.Yul.Compilation
open Backend Scalar

def argumentDemo : LoweredArgs 3 2 (fun l => #v[l[0], l[0] * 3 - l[1]]) :=
  lowerArgCons (lowerLocal ⟨0, by decide⟩)
    (lowerArgCons arithmeticDemo (lowerNoArgs 3))

def invokeDifference := lowerInline argumentDemo subAritySlice
example : ∃ p, argumentDemo.code 2 = some p ∧
    run p [100, 101, 4, 5, 6, 77, 88] = some [4, 7, 100, 101, 4, 5, 6, 77, 88] :=
  ⟨_, rfl, argumentDemo.correct 2 _ rfl #v[4, 5, 6] #v[100, 101] [77, 88]⟩
example : ∃ p, invokeDifference.code 2 = some p ∧
    run p [100, 101, 4, 5, 6, 77, 88] =
      some [(4 : Word) - 7, 100, 101, 4, 5, 6, 77, 88] :=
  ⟨_, rfl, invokeDifference.correct 2 _ rfl #v[4, 5, 6] #v[100, 101] [77, 88]⟩
example : ∃ p, (lowerInline argumentDemo swapPairAritySlice).code 2 = some p ∧
    run p [100, 101, 4, 5, 6, 77, 88] = some [7, 4, 100, 101, 4, 5, 6, 77, 88] :=
  ⟨_, rfl, (lowerInline argumentDemo swapPairAritySlice).correct
    2 _ rfl #v[4, 5, 6] #v[100, 101] [77, 88]⟩
example : (lowerArgCons (lowerLocal (n := 16) ⟨15, by decide⟩)
    (lowerArgCons (lowerLiteral 7) (lowerNoArgs 16))).code 0 = none := rfl
example : run swapPairAritySlice.code [] = none := rfl
example : run subAritySlice.code [7] = none := rfl
example : ∃ p, (lowerInline
    (lowerArgCons (lowerLiteral (n := 0) (BitVec.ofNat 256 (2 ^ 200 + 257)))
      (lowerArgCons (lowerLiteral 7) (lowerNoArgs 0))) swapPairAritySlice).code 0 = some p ∧
    run p [77, 88] = some [7, BitVec.ofNat 256 (2 ^ 200 + 257), 77, 88] :=
  ⟨_, rfl, (lowerInline
    (lowerArgCons (lowerLiteral (n := 0) (BitVec.ofNat 256 (2 ^ 200 + 257)))
      (lowerArgCons (lowerLiteral 7) (lowerNoArgs 0))) swapPairAritySlice).correct
      0 _ rfl #v[] #v[] [77, 88]⟩
def constantPair := lowerInline
  (lowerArgCons (lowerLiteral (n := 0) (BitVec.ofNat 256 (2 ^ 200 + 257)))
    (lowerArgCons (lowerLiteral 7) (lowerNoArgs 0))) swapPairAritySlice
private def constantPairCode : Program :=
  [pushWord 7, pushWord (BitVec.ofNat 256 (2 ^ 200 + 257)), .op (.SWAP ⟨0, by decide⟩)]
example : constantPair.code 0 = some constantPairCode := rfl
example : stackBound constantPairCode 1022 = true := by decide +kernel
example : stackBound constantPairCode 1023 = false := by decide +kernel
example : 2 + 0 + 0 + [77, 88].length ≤ 1024 :=
  constantPair.capacity 0 constantPairCode rfl #v[] #v[] [77, 88] (by decide)

end Solidity.Yul.Compilation
