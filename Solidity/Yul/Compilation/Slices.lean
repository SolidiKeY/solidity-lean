import Solidity.Backend.Scalar.Heights

/-! Arity-indexed *preparation* contracts over the actual numeric slice.
These are not source simulation or pinned EVM correspondence certificates. -/
namespace Solidity.Yul.Compilation
open Backend
open Backend.Scalar

/-- Exact argument/result counts with arbitrary caller tail. The existential
result is intrinsic at its arity; the execution law is an explicit obligation. -/
structure Slice (args results : Nat) where
  code : Program
  correct : ∀ (xs : Vector Word args) (tail : Stack),
    ∃ ys : Vector Word results, run code (xs.toList ++ tail) = some (ys.toList ++ tail)

/-- Composition uses actual slice execution, rather than assuming stack deltas. -/
def Slice.comp {a b c : Nat} (f : Slice a b) (g : Slice b c) : Slice a c where
  code := f.code ++ g.code
  correct := by
    intro xs tail
    obtain ⟨ys, hf⟩ := f.correct xs tail
    obtain ⟨zs, hg⟩ := g.correct ys tail
    exact ⟨zs, run_comp hf hg⟩

theorem Slice.height {a b : Nat} (f : Slice a b) (xs : Vector Word a)
    (tail : Stack) : ∃ out : Stack,
    run f.code (xs.toList ++ tail) = some out ∧ out.length = b + tail.length := by
  obtain ⟨ys, h⟩ := f.correct xs tail
  exact ⟨ys.toList ++ tail, h, by simp only [List.length_append, Vector.length_toList]⟩

/-- Prefix capacity remains an independent obligation at the actual 1024 limit. -/
theorem Slice.capacity {a b : Nat} (f : Slice a b) (xs : Vector Word a)
    (tail : Stack) (hb : stackBound f.code (a + tail.length : Nat) = true) :
    b + tail.length ≤ 1024 := by
  obtain ⟨ys, h⟩ := f.correct xs tail
  have hc := run_capacity h
  simp only [List.length_append, Vector.length_toList] at hc
  exact hc hb

/-- A scoped stack slot has the actual Osaka DUP/SWAP range, with zero-based
position in the live stack. Deeper scopes need V12's spill convention. -/
def readSlot (i : Fin 16) : Instr := .op (.DUP i)
def writeSlot (i : Fin 16) : Program := [.op (.SWAP i), .op .POP]

theorem readSlot_correct (i : Fin 16) (stack : Stack) (value : Word)
    (present : stack[i.val]? = some value) :
    step (readSlot i) stack = some (value :: stack) := by
  simp only [readSlot, step, duplicate, present, Option.map_some]

/-- The old slot value is discarded; the exchanged tail is preserved exactly.
The exchange premise includes operand existence and the full resulting stack. -/
theorem writeSlot_correct (i : Fin 16) (value old : Word) (stack updated : Stack)
    (present : exchange value i.val stack = some (old, updated)) :
    run (writeSlot i) (value :: stack) = some updated := by
  simp only [writeSlot, run, step, swap, present, Option.map_some,
    Option.bind_some, pop]

example : run (writeSlot ⟨1, by decide⟩) [7, 10, 20, 99] = some [10, 7, 99] := rfl
example : step (readSlot ⟨1, by decide⟩) [10] = none := rfl

/-- A real PUSH1 certificate, universally quantified over the caller tail. -/
def pushConstant (b : UInt8) : Slice 0 1 where
  code := [pushByte b]
  correct := by
    intro xs tail
    have hx : xs.toList = [] := Vector.toList_eq_nil_iff.mpr rfl
    refine ⟨#v[BitVec.ofNat 256 b.toNat], ?_⟩
    rw [hx]
    exact congrArg (fun st => st.bind (run [])) (step_pushByte b tail)

def identitySlice (a : Nat) : Slice a a where
  code := []
  correct := fun xs _tail => ⟨xs, rfl⟩

example : (pushConstant 7 |>.comp (identitySlice 1)).code = [pushByte 7] := rfl
example : run (pushConstant 7 |>.comp (identitySlice 1)).code [99] = some [7, 99] :=
  by decide +kernel
example : ∃ out : Stack, run (pushConstant 7).code [99] = some out ∧ out.length = 2 :=
  Slice.height (pushConstant 7) #v[] [99]

/-- Two literal arguments, in the numeric executor's top-first order. -/
def literalPair (a b : UInt8) : Slice 0 2 where
  code := [pushByte b, pushByte a]
  correct := by
    intro xs tail
    have hx : xs.toList = [] := Vector.toList_eq_nil_iff.mpr rfl
    refine ⟨#v[BitVec.ofNat 256 a.toNat, BitVec.ofNat 256 b.toNat], ?_⟩
    rw [hx]
    simp only [List.nil_append, run, step_pushByte, Option.bind_some]
    rfl

/-- Word addition keeps all high bits; this does not import Solidity checked-add. -/
def addWords : Slice 2 1 where
  code := [.op .ADD]
  correct := by
    intro xs tail
    have hl : xs.toList.length = 2 := Vector.length_toList
    generalize he : xs.toList = words at hl ⊢
    cases words with
    | nil => cases hl
    | cons a words =>
      cases words with
      | nil => cases hl
      | cons b rest =>
        have hr : rest.length = 0 := by simp only [List.length_cons] at hl; omega
        have hn : rest = [] := List.length_eq_zero_iff.mp hr
        subst rest
        exact ⟨#v[a + b], rfl⟩

example : run ((literalPair 250 9).comp addWords).code [99] = some [259, 99] :=
  by decide +kernel
example : ∃ out : Stack,
    run ((literalPair 250 9).comp addWords).code [99] = some out ∧ out.length = 2 :=
  Slice.height ((literalPair 250 9).comp addWords) #v[] [99]
example : 1 + [99].length ≤ 1024 :=
  Slice.capacity ((literalPair 250 9).comp addWords) #v[] [99] (by decide +kernel)

#print axioms addWords
#print axioms pushConstant
#print axioms Slice.comp
#print axioms Slice.height
#print axioms Slice.capacity
end Solidity.Yul.Compilation
