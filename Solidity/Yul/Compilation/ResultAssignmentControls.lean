import Solidity.Yul.Compilation.ResultAssignment

namespace Solidity.Yul.Compilation
open Backend Scalar
private def dirty : Word := BitVec.ofNat 256 (2 ^ 200 + 257)

def swapTargets : Vector (Fin 3) 2 := #v[⟨0, by decide⟩, ⟨1, by decide⟩]
def swapArgs := lowerArgCons (lowerLocal (n := 3) ⟨0, by decide⟩)
  (lowerArgCons (lowerLocal (n := 3) ⟨1, by decide⟩) (lowerNoArgs 3))
def swapResults := lowerInline swapArgs swapPairAritySlice
def snapshotSwap := lowerResultAssign swapTargets swapResults
def snapshotCode : Program :=
  [readSlot ⟨3, by decide⟩, readSlot ⟨3, by decide⟩, .op (.SWAP ⟨0, by decide⟩)] ++
    writeSlot ⟨3, by decide⟩ ++ writeSlot ⟨3, by decide⟩
example : snapshotSwap.code 2 = some snapshotCode := rfl
/-- RHS is evaluated before either destination update: real multi-result swap. -/
example : run snapshotCode [100, 101, dirty, 7, 99, 77, 88] =
    some [100, 101, 7, dirty, 99, 77, 88] :=
  snapshotSwap.correct 2 snapshotCode rfl #v[dirty, 7, 99] #v[100, 101] [77, 88]

example (locals : Vector Word 3) (values : Vector Word 2) :
    (assignResults 2 swapTargets values locals)[2] = locals[2] :=
  assignResults_other 2 swapTargets values locals ⟨2, by decide⟩ (by decide +kernel)

example (locals : Vector Word 3) (a b : Word) :
    assignResults 2 #v[(⟨1, by decide⟩ : Fin 3), ⟨1, by decide⟩] #v[a, b] locals =
      locals.set 1 b (by decide) := by
  change (locals.set 1 a (by decide)).set 1 b (by decide) = _
  exact Vector.set_set a (by decide)

def repeatedTargets : Vector (Fin 3) 2 := #v[⟨1, by decide⟩, ⟨1, by decide⟩]
def repeatedValues := lowerArgCons (lowerLiteral (n := 3) dirty)
  (lowerArgCons (lowerLiteral (n := 3) 257) (lowerNoArgs 3))
def repeatedAssign := lowerResultAssign repeatedTargets repeatedValues
example : ∃ p, repeatedAssign.code 1 = some p ∧
    run p [100, 8, 7, 9, 77, 88] = some [100, 8, 257, 9, 77, 88] :=
  ⟨_, rfl, repeatedAssign.correct 1 _ rfl #v[8, 7, 9] #v[100] [77, 88]⟩

example : resultWritesCode 1 #v[(⟨15, by decide⟩ : Fin 16)] 0 =
    some (writeSlot ⟨15, by decide⟩) := rfl
example (tail : Stack) : run (writeSlot ⟨15, by decide⟩)
    (dirty :: ((Vector.replicate 16 (9 : Word)).toList ++ tail)) =
      some (((Vector.replicate 16 (9 : Word)).set 15 dirty (by decide)).toList ++ tail) :=
  resultWritesCode_run 1 #v[(⟨15, by decide⟩ : Fin 16)] 0 _ rfl
    #v[dirty] (Vector.replicate 16 9) #v[] tail
example : resultWritesCode 1 #v[(⟨15, by decide⟩ : Fin 16)] 1 = none := rfl
example : resultWritesCode 2 #v[(⟨14, by decide⟩ : Fin 15), ⟨0, by decide⟩] 0 =
    some (writeSlot ⟨15, by decide⟩ ++ writeSlot ⟨0, by decide⟩) := rfl
example : resultWritesCode 2 #v[(⟨15, by decide⟩ : Fin 16), ⟨0, by decide⟩] 0 = none := rfl
example : resultWritesCode 17 (Vector.replicate 17 (⟨0, by decide⟩ : Fin 1)) 0 = none := rfl

def writePairCode : Program := writeSlot ⟨3, by decide⟩ ++ writeSlot ⟨3, by decide⟩
example : resultWritesCode 2 swapTargets 2 = some writePairCode := rfl
example : run writePairCode [dirty, 257, 100, 101, 8, 7, 9, 77, 88] =
    some [100, 101, dirty, 257, 9, 77, 88] :=
  resultWritesCode_run 2 swapTargets 2 writePairCode rfl #v[dirty, 257] #v[8, 7, 9]
    #v[100, 101] [77, 88]
example : stackBound writePairCode 1024 = true := by decide +kernel
example : stackBound writePairCode 1025 = false := by decide +kernel
example : stackBound writePairCode 2 = true ∧ run writePairCode [1, 2] = none :=
  ⟨by decide +kernel, rfl⟩
example : run snapshotCode [1, 2, 3] = none := rfl
example : stackBound snapshotCode 1022 = true := by decide +kernel
example : stackBound snapshotCode 1023 = false := by decide +kernel
example : run snapshotCode (100 :: 101 :: dirty :: 7 :: 99 :: List.replicate 1018 9) =
    some (100 :: 101 :: 7 :: dirty :: 99 :: List.replicate 1018 9) :=
  snapshotSwap.correct 2 snapshotCode rfl #v[dirty, 7, 99] #v[100, 101] (List.replicate 1018 9)
example : stackBound snapshotCode (100 :: 101 :: dirty :: 7 :: 99 ::
    List.replicate 1018 (9 : Word)).length = false := by decide +kernel
end Solidity.Yul.Compilation
