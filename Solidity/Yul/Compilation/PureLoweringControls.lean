import Solidity.Yul.Compilation.PureLowering

/-! Concrete generated-code controls, not source admission or final G24 adequacy. -/
namespace Solidity.Yul.Compilation
open Backend Scalar

private def dirty : Word := BitVec.ofNat 256 (2 ^ 200 + 257)

def arithmeticDemo : LoweredExpr 3 (fun l => l[0] * 3 - l[1]) :=
  lowerBinary selectSub
    (lowerBinary selectMul (lowerLocal ⟨0, by decide⟩) (lowerLiteral 3))
    (lowerLocal ⟨1, by decide⟩)

def arithmeticCode : Program :=
  [readSlot ⟨3, by decide⟩, pushWord 3, readSlot ⟨4, by decide⟩, .op .MUL, .op .SUB]

example : arithmeticDemo.code 2 = some arithmeticCode := rfl
example : run arithmeticCode [100, 101, 4, 5, 6, 77, 88] =
    some [7, 100, 101, 4, 5, 6, 77, 88] :=
  arithmeticDemo.correct 2 arithmeticCode rfl #v[4, 5, 6] #v[100, 101] [77, 88]

def assignmentDemo : LoweredStmt 3
    (fun l => (l.set 2 (l[0] * 3 - l[1]) (by decide)).set 1 dirty (by decide)) :=
  lowerSeq (lowerAssign ⟨2, by decide⟩ arithmeticDemo)
    (lowerAssign ⟨1, by decide⟩ (lowerLiteral dirty))

def assignmentCode : Program := arithmeticCode ++ writeSlot ⟨4, by decide⟩ ++
  ([pushWord dirty] ++ writeSlot ⟨3, by decide⟩)
example : assignmentDemo.code 2 = some assignmentCode := rfl
example : run assignmentCode [100, 101, 4, 5, 6, 77, 88] =
    some [100, 101, 4, dirty, 7, 77, 88] :=
  assignmentDemo.correct 2 assignmentCode rfl #v[4, 5, 6] #v[100, 101] [77, 88]
example : (run assignmentCode [100, 101, 4, 5, 6, 77, 88]).map (List.drop 5) =
    some [77, 88] := assignmentDemo.caller 2 assignmentCode rfl
      #v[4, 5, 6] #v[100, 101] [77, 88]

/-- The next statement reads the just-updated local rather than its old value. -/
def statefulDemo := lowerSeq assignmentDemo
  (lowerAssign ⟨0, by decide⟩ (lowerLocal (n := 3) ⟨2, by decide⟩))
example : ∃ p, statefulDemo.code 2 = some p ∧
    run p [100, 101, 4, 5, 6, 77, 88] = some [100, 101, 7, dirty, 7, 77, 88] :=
  ⟨_, rfl, statefulDemo.correct 2 _ rfl #v[4, 5, 6] #v[100, 101] [77, 88]⟩

example : (lowerLocal (n := 16) ⟨15, by decide⟩).code 0 =
    some [readSlot ⟨15, by decide⟩] := rfl
example : (lowerLocal (n := 16) ⟨15, by decide⟩).code 1 = none := rfl
example : (lowerBinary selectAdd (lowerLocal (n := 16) ⟨15, by decide⟩)
    (lowerLiteral 1)).code 0 = none := rfl
example : (lowerAssign (n := 15) ⟨14, by decide⟩ (lowerLiteral 7)).code 2 = none := rfl
example : run arithmeticCode [100, 101] = none := by decide +kernel
example : (lowerLiteral (n := 0) dirty).code 0 = some [pushWord dirty] := rfl
example : run [pushWord dirty] [77, 88] = some [dirty, 77, 88] := by
  simp only [run, step_pushWord, Option.bind_some]
example : ∃ p, (lowerBinary selectDiv (lowerLiteral (n := 0) 99) (lowerLiteral 0)).code 0 =
    some p ∧ run p [77, 88] = some [0, 77, 88] :=
  ⟨_, rfl, (lowerBinary selectDiv (lowerLiteral (n := 0) 99) (lowerLiteral 0)).correct
    0 _ rfl #v[] #v[] [77, 88]⟩
example : ∃ p, (lowerUnary selectIsZero (lowerLiteral (n := 0) 0)).code 0 = some p ∧
    run p [77, 88] = some [1, 77, 88] :=
  ⟨_, rfl, (lowerUnary selectIsZero (lowerLiteral (n := 0) 0)).correct
    0 _ rfl #v[] #v[] [77, 88]⟩
def selectDemo : LoweredExpr 3 (fun l => if l[0] = 0 then 11 else dirty) :=
  lowerSelect (lowerLocal ⟨0, by decide⟩) (lowerLiteral dirty) (lowerLiteral 11)
example : ∃ p, selectDemo.code 2 = some p ∧
    run p [100, 101, 0, 5, 6, 77, 88] = some [11, 100, 101, 0, 5, 6, 77, 88] :=
  ⟨_, rfl, selectDemo.correct 2 _ rfl #v[0, 5, 6] #v[100, 101] [77, 88]⟩
example : ∃ p, selectDemo.code 2 = some p ∧
    run p [100, 101, 257, 5, 6, 77, 88] = some [dirty, 100, 101, 257, 5, 6, 77, 88] :=
  ⟨_, rfl, selectDemo.correct 2 _ rfl #v[257, 5, 6] #v[100, 101] [77, 88]⟩
example : (lowerSelect (lowerLiteral (n := 16) 0)
    (lowerLocal ⟨15, by decide⟩) (lowerLiteral 11)).code 0 = none := rfl
example : ∃ p, (lowerAssign ⟨2, by decide⟩ selectDemo).code 2 = some p ∧
    run p [100, 101, 257, 5, 6, 77, 88] = some [100, 101, 257, 5, dirty, 77, 88] :=
  ⟨_, rfl, (lowerAssign ⟨2, by decide⟩ selectDemo).correct
    2 _ rfl #v[257, 5, 6] #v[100, 101] [77, 88]⟩
example : ∃ p, (lowerBinary selectDiv (lowerLiteral (n := 0) 9) (lowerLiteral 4)).code 0 =
    some p ∧ run p [77, 88] = some [2, 77, 88] :=
  ⟨_, rfl, (lowerBinary selectDiv (lowerLiteral (n := 0) 9) (lowerLiteral 4)).correct
    0 _ rfl #v[] #v[] [77, 88]⟩
example : ∃ p, (lowerBinary selectMod (lowerLiteral (n := 0) 9) (lowerLiteral 4)).code 0 =
    some p ∧ run p [77, 88] = some [1, 77, 88] :=
  ⟨_, rfl, (lowerBinary selectMod (lowerLiteral (n := 0) 9) (lowerLiteral 4)).correct
    0 _ rfl #v[] #v[] [77, 88]⟩

def blockDemo := lowerBlock (n := 3)
  [⟨_, lowerAssign ⟨2, by decide⟩ arithmeticDemo⟩,
   ⟨_, lowerAssign ⟨0, by decide⟩ (lowerLocal ⟨2, by decide⟩)⟩]
example : ∃ p, blockDemo.2.code 2 = some p ∧
    run p [100, 101, 4, 5, 6, 77, 88] = some [100, 101, 7, 5, 7, 77, 88] :=
  ⟨_, rfl, blockDemo.2.correct 2 _ rfl #v[4, 5, 6] #v[100, 101] [77, 88]⟩

def incrementDemo : LoweredStmt 1 (fun l => l.set 0 (l[0] + 1) (by decide)) :=
  lowerAssign ⟨0, by decide⟩ (lowerBinary selectAdd (lowerLocal ⟨0, by decide⟩) (lowerLiteral 1))
example : ∃ p, (lowerFixedRepeat incrementDemo 3).code 2 = some p ∧
    run p [100, 101, 4, 77, 88] = some [100, 101, 7, 77, 88] :=
  ⟨_, rfl, (lowerFixedRepeat incrementDemo 3).correct
    2 _ rfl #v[4] #v[100, 101] [77, 88]⟩
example : (lowerFixedRepeat (lowerAssign (n := 16) ⟨15, by decide⟩ (lowerLiteral 7)) 0).code 1 =
    some [] := rfl
example : (lowerFixedRepeat (lowerAssign (n := 16) ⟨15, by decide⟩ (lowerLiteral 7)) 1).code 1 =
    none := rfl

example : stackBound arithmeticCode 1021 = true := by decide +kernel
example : stackBound arithmeticCode 1022 = false := by decide +kernel
example : run arithmeticCode ([100, 101, 4, 5, 6] ++ List.replicate 1019 9) =
    some (7 :: ([100, 101, 4, 5, 6] ++ List.replicate 1019 9)) :=
  arithmeticDemo.correct 2 arithmeticCode rfl #v[4, 5, 6] #v[100, 101] _
example : stackBound arithmeticCode ([100, 101, 4, 5, 6] ++ List.replicate 1019 9).length =
    false := by decide +kernel
end Solidity.Yul.Compilation
