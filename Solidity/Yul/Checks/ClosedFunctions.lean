
import Solidity.Yul.ClosedFunctions
import Solidity.Yul.Checks.Static

/-! Kernel lexical-closure controls and nontrivial recursive/mulDiv inhabitants.
There is no execution or horizon theorem in this module. -/
namespace Solidity.Yul.Checks.ClosedFunctions
open Solidity.Yul.Closed

abbrev valueSig : Sig := ⟨0, 1⟩
def returns (F : List Sig) (value : Nat) : Stmt F [] ⟨true, false⟩ 1 :=
  .assign (fun _ => .«local» 0) (.literal (word value))
def older : FunctionEnv [valueSig] :=
  .group [valueSig] .nil (.cons (returns [valueSig] 7) .nil)
def bodies : Bodies [valueSig, valueSig, valueSig] [] [valueSig, valueSig] :=
  .cons (returns [valueSig, valueSig, valueSig] 9)
    (.cons (returns [valueSig, valueSig, valueSig] 11) .nil)
def newer : FunctionEnv [valueSig, valueSig, valueSig] :=
  .group [valueSig, valueSig] older bodies

example : splitMember [valueSig, valueSig] [valueSig]
    (.here : Member [valueSig, valueSig, valueSig] valueSig) = .inl .here := rfl
example : splitMember [valueSig, valueSig] [valueSig]
    (.there .here : Member [valueSig, valueSig, valueSig] valueSig) = .inl (.there .here) := rfl
example : splitMember [valueSig, valueSig] [valueSig]
    (.there (.there .here) : Member [valueSig, valueSig, valueSig] valueSig) = .inr .here := rfl
example : (lookup newer .here).functions = [valueSig, valueSig, valueSig] := rfl
example : (lookup newer .here).environment = newer := rfl
example : (lookup newer .here).body = returns [valueSig, valueSig, valueSig] 9 := rfl
example : (lookup newer (.there .here)).environment = newer := rfl
example : (lookup newer (.there .here)).body = returns [valueSig, valueSig, valueSig] 11 := rfl
example : (lookup newer (.there (.there .here))).functions = [valueSig] := rfl
example : (lookup newer (.there (.there .here))).environment = older := rfl
example : (lookup newer (.there (.there .here))).body = returns [valueSig] 7 := rfl
example : lookup newer (.there (.there .here)) = lookup older .here :=
  lookup_old (signatures := [valueSig, valueSig]) older bodies .here
example : lookup newer (.there .here) = ⟨_, newer, bodyAt (.there .here) bodies⟩ :=
  lookup_new (signatures := [valueSig, valueSig]) older bodies (.there .here)

theorem no_empty_member {sig : Sig} (i : Member [] sig) : False := PEmpty.elim (peelMember i)
theorem no_external_reference (r : ExternalRef [] false) : False := by cases r.index

/-- Actual recursive code: decrement its own argument, leave at zero, and
return the recursively obtained word. Own argument/return slots are the only
local positions in the type; execution is deliberately a remaining obligation. -/
abbrev recursiveSig : Sig := ⟨1, 1⟩
def countdown : Stmt [recursiveSig] [] ⟨true, false⟩ 2 :=
  .seq (.if_ (.builtin (.pure .«iszero») (fun _ => .«local» 0))
    (.seq (.assign (fun _ => .«local» 1) (.literal (word 0))) .leave))
    (.assign (fun _ => .«local» 1)
      (.call .here (fun _ => .builtin (.pure .«sub»)
        (fun i => if i.val = 0 then .«local» 0 else .literal (word 1)))))
def recursiveEnv : FunctionEnv [recursiveSig] :=
  .group [recursiveSig] .nil (.cons countdown .nil)
example : (lookup recursiveEnv .here).environment = recursiveEnv := rfl
example : (lookup recursiveEnv .here).body = countdown := rfl

def mulDivEnv : FunctionEnv [⟨3, 1⟩] :=
  .group [⟨3, 1⟩] .nil (.cons Static.mulDivBody .nil)
example : (lookup mulDivEnv .here).body = Static.mulDivBody := rfl

/-- Zero arguments and zero results also retain a concrete typed body. -/
def voidEnv : FunctionEnv [⟨0, 0⟩] := .group [⟨0, 0⟩] .nil (.cons .leave .nil)
example : (lookup voidEnv .here).body = Stmt.leave := rfl


def emptyGroup : FunctionEnv [valueSig] := .group [] older .nil
example : lookup emptyGroup .here = lookup older .here :=
  lookup_old (signatures := []) older .nil .here

def firstMutual : Stmt [recursiveSig, recursiveSig] [] ⟨true, false⟩ 2 :=
  .assign (fun _ => .«local» 1) (.call (.there .here) (fun _ => .«local» 0))
def secondMutual : Stmt [recursiveSig, recursiveSig] [] ⟨true, false⟩ 2 :=
  .assign (fun _ => .«local» 1) (.call .here (fun _ => .«local» 0))
def mutualEnv : FunctionEnv [recursiveSig, recursiveSig] :=
  .group [recursiveSig, recursiveSig] .nil (.cons firstMutual (.cons secondMutual .nil))
example : (lookup mutualEnv .here).body = firstMutual := rfl
example : (lookup mutualEnv (.there .here)).body = secondMutual := rfl
example : (lookup mutualEnv .here).environment = mutualEnv := rfl
example : (lookup mutualEnv (.there .here)).environment = mutualEnv := rfl


end Solidity.Yul.Checks.ClosedFunctions
