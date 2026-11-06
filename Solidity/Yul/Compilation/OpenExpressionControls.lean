import Solidity.Yul.Compilation.OpenExpressions
namespace Solidity.Yul.Compilation.OpenExpressions.Controls
open Backend Scalar
open Solidity.Yul.Closed

def types : List ExternalType :=
  [.value (.unsigned 0),.value .boolean,.externalFunction,.constant (word 9)]
def small : WordCell types := .scalar ⟨.unsigned 0,.here⟩
def flag : WordCell types := .scalar ⟨.boolean,.there .here⟩
def function : Member types .externalFunction := .there (.there .here)
def state : WordState types 1 := ⟨fun _ => word 7,
  WordCells.write
    (WordCells.write
      (WordCells.write
        (WordCells.write (fun _ => word 0) small (word 257)) flag (word 2))
      (.address function) (word (2^256-1)))
    (.selector function) (word (2^32+1))⟩
def args (a b : Expr [] types 1 1) : Fin 2 → Expr [] types 1 1 := Fin.cases a (fun _ => b)
def constant : Expr [] types 1 1 := .external
  ⟨.there (.there (.there .here)),.plain,.constantRead⟩
def expression : Expr [] types 1 1 := .builtin (.pure .add)
  (args (.external small.readRef) (.builtin (.pure .mul) (args (.local 0) constant)))
def policy : Policy.ExprP .A expression := by apply (Policy.expr_iff .A _).mp; rfl
def compiled := (compile 3 expression policy).get (by rfl)
def code : Program := [pushWord 9,readSlot ⟨3,by decide⟩,.op .MUL,readSlot ⟨4,by decide⟩,.op .ADD]
example : compiled.lowered.code 2 = some code := rfl
example : DirectWords.eval 3 expression policy state = some (fun _ => word 320) := source compiled state
example : (encoded state).toList = [7,257,2,BitVec.ofNat 256 (2^256-1),BitVec.ofNat 256 (2^32+1)] := by decide
example : run code ([91,92] ++ ((encoded state).toList ++ [99])) =
    some (320 :: ([91,92] ++ ((encoded state).toList ++ [99]))) :=
  compiled.lowered.correct 2 code rfl (encoded state) #v[91,92] [99]
example : (compile 2 expression policy).isNone = true := rfl
example : DirectWords.eval 2 expression policy state = none := rfl
example : run code [] = none := rfl
example : stackBound code 1022 = true := by decide
example : stackBound code 1023 = false := by decide

def address : Expr [] types 1 1 := .external (WordCell.address function).readRef
def addressPolicy : Policy.ExprP .A address := by apply (Policy.expr_iff .A _).mp; rfl
def addressCompiled := (compile 1 address addressPolicy).get (by rfl)
example : DirectWords.eval 1 address addressPolicy state = some (fun _ => word (2^256-1)) :=
  source addressCompiled state
example : addressCompiled.lowered.code 12 = some [readSlot ⟨15,by decide⟩] := rfl
example : addressCompiled.lowered.code 13 = none := rfl

def selector : Expr [] types 1 1 := .external (WordCell.selector function).readRef
def selectorPolicy : Policy.ExprP .A selector := by apply (Policy.expr_iff .A _).mp; rfl
def selectorCompiled := (compile 1 selector selectorPolicy).get (by rfl)
example : DirectWords.eval 1 selector selectorPolicy state = some (fun _ => word (2^32+1)) :=
  source selectorCompiled state
example : selectorCompiled.lowered.code 2 = some [readSlot ⟨6,by decide⟩] := rfl
-- Raw cell meaning is preserved; Solidity pipeline interpretation is separate.
example : (state.cells small).val = 257 := by decide
example : (state.cells flag).val = 2 := by decide
end Solidity.Yul.Compilation.OpenExpressions.Controls
