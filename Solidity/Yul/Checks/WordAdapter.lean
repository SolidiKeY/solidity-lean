import Solidity.Yul.Checks.WordAdapterCode
set_option Elab.async false
namespace Solidity.Yul.Checks.WordAdapter
open Solidity.Yul.Checks.BlockTyping
example : prepared dirty = true := by decide
example : prepared bound = true := by decide
example : prepared mulDiv = true := by decide
example : prepared recursive = true := by decide
example : prepared looping = true := by decide
example : prepared pair = true := by decide
example : prepared switched = true := by decide
example : prepared division = true := by decide
example : prepared crossed = true := by decide
example : prepared never = true := by decide
example : prepared [decl "x" (lit 1)] = false := by decide
example : prepared [assign "k" (lit 1)] = false := by decide
example : prepared [assign "x" (varExpr "mem")] = false := by decide
example : prepared [fn "capture" [] ["r"] [assign "r" (varExpr "x")]] = false := by decide
example : prepared [fn "capture" [] ["r"] [assign "r" (field "selector")]] = false := by decide
example : prepared [fn "unused" [] ["r"] [assign "r" (call "gas" [])]] = false := by decide
example : prepared [.yulLeave] = false := by decide
example : prepared [.yulBreak] = false := by decide
example : prepared [.yulContinue] = false := by decide
example : prepared [assign "x" (call "mulDiv" [lit 1]),
  fn "mulDiv" ["a","b"] ["r"] []] = false := by decide
example : observe dirty 0 = none := rfl
example : observe dirty 32 = some [257,2,2^256-1,2^256-1] := by decide
example : observe bound 32 = some [258,2,0,0] := by decide
example : observe pair 32 = some [2,257,0,0] := by decide
example : observe switched 32 = some [257,2,0,0] := by decide
example : observe division 32 = some [0,0,0,0] := by decide
example : observe crossed 32 = some [257,2,257,2^256-1] := by decide
example : observe never 32 = none := by decide

example : observe mulDiv 32 = some [599,2,0,0] := by
  rw [observe_cache mulDiv mulDivPrepared 32 mulDivCode mulDiv_lowered]
  decide
example : observe recursive 32 = some [13,2,0,0] := by
  rw [observe_cache recursive recursivePrepared 32 recursiveCode recursive_lowered]
  decide
example : observe looping 32 = some [259,2,0,3] := by
  rw [observe_cache looping loopingPrepared 32 loopingCode looping_lowered]
  decide

def witness := (prepare mulDiv).toOption.get (by decide)
theorem inhabited : Nonempty
    (Solidity.Yul.ScopedSyntax.Prepared scope .A outside localNames (list mulDiv)) := ⟨witness⟩
example (mode : Solidity.Modality)
    (post : Closed.Flow ClosedSyntax.rootControl → Logic.Fml (0+wordCellCount types)) :
    ∃ premise, Nonempty (Logic.Rule
      (.modal mode Solidity.Yul.WordAdapter.model witness.rawProgram post) premise) :=
  witness.rawRule_exists mode post
end Solidity.Yul.Checks.WordAdapter
