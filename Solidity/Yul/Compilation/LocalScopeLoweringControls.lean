import Solidity.Yul.Compilation.LocalScopeLowering
namespace Solidity.Yul.Compilation
open Backend Scalar
private def dirty : Word := BitVec.ofNat 256 (2 ^ 200 + 257)
def scopeInitializers := lowerArgCons (lowerLocal (n := 2) ⟨1, by decide⟩)
  (lowerArgCons (lowerLiteral (n := 2) dirty) (lowerNoArgs 2))
def scopeBody := lowerSeq
  (lowerAssign (n := 4) ⟨2, by decide⟩ (lowerLocal ⟨1, by decide⟩))
  (lowerAssign (n := 4) ⟨0, by decide⟩ (lowerLiteral 99))
def scopeCompiled := lowerLocalScope scopeInitializers scopeBody
def scopeCode : Program := [pushWord dirty, readSlot ⟨2, by decide⟩] ++
  ([readSlot ⟨1, by decide⟩] ++ writeSlot ⟨2, by decide⟩) ++
  ([pushWord 99] ++ writeSlot ⟨0, by decide⟩) ++ popPrefix 2
example : scopeCompiled.code 0 = some scopeCode := rfl
/-- Fresh mutations disappear, outer mutations and dirty bits survive. -/
example (tail : Stack) : run scopeCode ([8, 7] ++ tail) = some ([dirty, 7] ++ tail) :=
  scopeCompiled.correct 0 scopeCode rfl #v[8, 7] #v[] tail
example : scopeCompiled.code 1 = none := rfl
example : run scopeCode [8] = none := rfl
example : stackBound scopeCode 1021 = true := by decide +kernel
example : stackBound scopeCode 1022 = false := by decide +kernel
example : run scopeCode ([8, 7] ++ List.replicate 1022 9) =
    some ([dirty, 7] ++ List.replicate 1022 9) :=
  scopeCompiled.correct 0 scopeCode rfl #v[8, 7] #v[] (List.replicate 1022 9)

def innerScope := lowerLocalScope
  (lowerArgCons (lowerLiteral (n := 3) dirty) (lowerNoArgs 3))
  (lowerAssign (n := 4) ⟨2, by decide⟩ (lowerLocal ⟨0, by decide⟩))
def nestedScope := lowerLocalScope
  (lowerArgCons (lowerLiteral (n := 2) 100) (lowerNoArgs 2)) innerScope
example : ∃ p, nestedScope.code 0 = some p ∧
    run p [8, 7, 77, 88] = some [dirty, 7, 77, 88] :=
  ⟨_, rfl, nestedScope.correct 0 _ rfl #v[8, 7] #v[] [77, 88]⟩
example : (lowerLocalScope (lowerNoArgs 2) (lowerSkip 2)).code 0 = some [] := rfl
example : (lowerLocalScope
    (lowerArgCons (lowerLocal (n := 17) ⟨16, by decide⟩) (lowerNoArgs 17))
    (lowerSkip 18)).code 0 = none := rfl
example : (lowerLocalScope (lowerNoArgs 17)
    (lowerAssign (n := 17) ⟨16, by decide⟩ (lowerLiteral 9))).code 0 = none := rfl
example (locals : Vector Word 2) (tail : Stack) :
    run (popPrefix 0) (locals.toList ++ tail) = some (locals.toList ++ tail) := rfl
end Solidity.Yul.Compilation
