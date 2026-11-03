import Solidity.Yul.Compilation.ResultFrame
namespace Solidity.Yul.Compilation
open Backend Scalar
private def dirty : Word := BitVec.ofNat 256 (2 ^ 200 + 257)
def pairRetire : Program := retireResultLocals ⟨2, by decide⟩ 3
example : pairRetire = [.op (.SWAP ⟨0, by decide⟩), .op (.SWAP ⟨1, by decide⟩), .op .POP,
    .op (.SWAP ⟨0, by decide⟩), .op (.SWAP ⟨1, by decide⟩), .op .POP,
    .op (.SWAP ⟨0, by decide⟩), .op (.SWAP ⟨1, by decide⟩), .op .POP] := rfl
example (tail : Stack) : run pairRetire ([dirty, 257, 8, 7, 9] ++ tail) =
    some ([dirty, 257] ++ tail) :=
  retireResultFrame_run ⟨2, by decide⟩ #v[dirty, 257] #v[8, 7, 9] tail
example : run (pairRetire ++ retireResultLocals ⟨2, by decide⟩ 2)
    [dirty, 257, 8, 7, 9, 100, 101, 77, 88] = some [dirty, 257, 77, 88] :=
  run_comp (retireResultFrame_run ⟨2, by decide⟩ #v[dirty, 257] #v[8, 7, 9] [100, 101, 77, 88])
    (retireResultFrame_run ⟨2, by decide⟩ #v[dirty, 257] #v[100, 101] [77, 88])
example (results : Vector Word 16) (tail : Stack) :
    run (retireResultLocals ⟨16, by decide⟩ 2) (results.toList ++ [8, 9] ++ tail) =
      some (results.toList ++ tail) := by
  simpa only [List.append_assoc] using
    retireResultFrame_run ⟨16, by decide⟩ results #v[8, 9] tail
example : (resultSweep 16 (by decide))[15]? = some (.op (.SWAP ⟨15, by decide⟩)) := rfl
example : retireResultCode 16 2 = some (retireResultLocals ⟨16, by decide⟩ 2) := rfl
example : retireResultCode 17 2 = none := rfl
example (tail : Stack) : run (retireResultLocals ⟨0, by decide⟩ 2) ([8, 9] ++ tail) =
    some tail := retireResultFrame_run ⟨0, by decide⟩ #v[] #v[8, 9] tail
example (results : Vector Word 2) (tail : Stack) :
    run (retireResultLocals ⟨2, by decide⟩ 0) (results.toList ++ tail) =
      some (results.toList ++ tail) := rfl
example : run pairRetire [1, 2] = none := rfl
example : run (retireResultLocals ⟨1, by decide⟩ 1) [1] = none := rfl
example : stackBound pairRetire 3 = true ∧ run pairRetire [1, 2, 3] = none :=
  ⟨by decide +kernel, rfl⟩
example : stackBound pairRetire 1024 = true := by decide +kernel
example : stackBound pairRetire 1025 = false := by decide +kernel
example : run pairRetire ([dirty, 257, 8, 7, 9] ++ List.replicate 1020 77) =
    some ([dirty, 257] ++ List.replicate 1020 77) :=
  retireResultFrame_run ⟨2, by decide⟩ #v[dirty, 257] #v[8, 7, 9] (List.replicate 1020 77)

def frameResults := lowerArgCons (lowerLocal (n := 3) ⟨1, by decide⟩)
  (lowerArgCons (lowerLocal (n := 3) ⟨0, by decide⟩) (lowerNoArgs 3))
def closedFrame := (closeInlineBody ⟨2, by decide⟩ frameResults).get (by rfl)
example : closeInlineBody ⟨2, by decide⟩ frameResults = some closedFrame := rfl
example (tail : Stack) : run closedFrame.code ([dirty, 7, 99] ++ tail) =
    some ([7, dirty] ++ tail) := closedFrame.correct #v[dirty, 7, 99] tail
example : closedFrame.code = [readSlot ⟨0, by decide⟩, readSlot ⟨2, by decide⟩] ++ pairRetire := rfl
example : stackBound closedFrame.code 1022 = true := by decide +kernel
example : stackBound closedFrame.code 1023 = false := by decide +kernel
example : (closeInlineBody ⟨1, by decide⟩
    (lowerArgCons (lowerLocal (n := 17) ⟨16, by decide⟩) (lowerNoArgs 17))).isNone = true := rfl
/-- Concrete closed3→2 body used inside a second scoped argument compilation.
Input locals are consumed; outer locals/newer temporaries/caller are retained. -/
def inlineFrameArgs := lowerArgCons (lowerLocal (n := 2) ⟨0, by decide⟩)
  (lowerArgCons (lowerLocal (n := 2) ⟨1, by decide⟩)
    (lowerArgCons (lowerLiteral (n := 2) 99) (lowerNoArgs 2)))
def inlineClosedFrame := lowerInline inlineFrameArgs closedFrame
example : ∃ p, inlineClosedFrame.code 2 = some p ∧
    run p [100, 101, dirty, 7, 77, 88] =
      some [7, dirty, 100, 101, dirty, 7, 77, 88] :=
  ⟨_, rfl, inlineClosedFrame.correct 2 _ rfl #v[dirty, 7] #v[100, 101] [77, 88]⟩
end Solidity.Yul.Compilation
