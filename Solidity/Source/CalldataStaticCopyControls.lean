import Solidity.Source.Calldata
import Solidity.Source.SemanticsExamples


namespace Solidity.Source.CalldataStaticCopyControls

open Solidity.Source Solidity.Source.SemanticsExamples

def w (n : Nat) : List UInt8 := List.replicate 31 0 ++ [n.toUInt8]
def u : STy := .int IntTy.u256
def pair : STy := .array .memory u (some 2)
def frame : Fr := { F0 with cd := w 1 ++ w 2 ++ w 3 ++ w 4 }

def words (o : Option (Σ τ, Data EB.layout τ)) : Option (List (Option Nat)) :=
  match o with
  | some ⟨_, .array _ _ xs⟩ => some ((List.ofFn xs).map fun
      | .val v => (Val.word v).map (·.val)
      | _ => none)
  | _ => none

def nested := (cdToMem frame (.array .memory pair none) 0 2 : EM EB [] _).run (L0 EB, sB)
def fixed := (cdToMem frame pair 32 2 : EM EB [] _).run (L0 EB, sB)
def flat := (cdToMem frame (.array .memory u none) 0 4 : EM EB [] _).run (L0 EB, sB)
def dirty := (cdToMem { F0 with cd := w 1 ++ w 2 } (.array .memory .bool (some 2)) 0 2 :
  EM EB [] _).run (L0 EB, sB)
def dynamic := (cdToMem frame (.array .memory (.array .memory (.bytes .memory) (some 1)) none) 0 1 :
  EM EB [] _).run (L0 EB, sB)

theorem nested_copy :
    nested.1 = .ok (.val (.memRef rfl (sB.heap.next + 2))) ∧
    words (nested.2.2.heap.get sB.heap.next) = some [some 1, some 2] ∧
    words (nested.2.2.heap.get (sB.heap.next + 1)) = some [some 3, some 4] ∧
    (nested.2.2.heap.get (sB.heap.next + 2)).map (·.1) = some (.array .memory pair none) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

example :
    nested.2.2.heap.get (sB.heap.next + 2) =
      some ⟨.array .memory pair none,
        Data.array 2 (fun _ h => nomatch h)
          (finCons (.val (.memRef rfl sB.heap.next))
            (finCons (.val (.memRef rfl (sB.heap.next + 1))) Fin.elim0))⟩ := by
  rfl

theorem fixed_copy :
    fixed.1 = .ok (.val (.memRef rfl sB.heap.next)) ∧
    words (fixed.2.2.heap.get sB.heap.next) = some [some 2, some 3] := by
  refine ⟨rfl, rfl⟩

theorem flat_copy : words (flat.2.2.heap.get sB.heap.next) = some [some 1, some 2, some 3, some 4] := rfl

theorem dirty_reverts : dirty.1 = .error (.revert []) := rfl

theorem dynamic_stuck : dynamic.1 = .error (.stuck "calldata conversion") := rfl

end Solidity.Source.CalldataStaticCopyControls
