
import Solidity.Yul.ClosedProfile
import Solidity.Yul.Checks.ClosedFunctions

/-! Pure-word profile witnesses/refusals and exact closure-selection controls.
These do not execute statements or certify whole-source block validity. -/
namespace Solidity.Yul.Checks.ClosedPure
open Solidity.Yul.Closed
open Solidity.Yul.Checks.ClosedFunctions

example : (checkWordBuiltin (.pure .«add»)).isSome = true := rfl
example : (checkWordBuiltin (.pure .«div»)).isSome = true := rfl
example : (checkWordBuiltin .pop).isSome = true := rfl
example : (checkWordBuiltin .mload).isSome = false := rfl
example : (checkWordBuiltin .sstore).isSome = false := rfl
example : (checkWordBuiltin .call).isSome = false := rfl
example : (checkWordBuiltin .gas).isSome = false := rfl
example : (checkWordBuiltin .codecopy).isSome = false := rfl
example : (checkWordBuiltin .callcode).isSome = false := rfl
theorem no_memory_builtin (d : WordBuiltinD .mload) : False := by cases d

def returnD (F : List Sig) (value : Nat) : WordStmtD (returns F value) := .assign .literal
def olderD : WordEnvD older := .group .nil (.cons (returnD [valueSig] 7) .nil)
def bodiesD : WordBodiesD bodies :=
  .cons (returnD [valueSig, valueSig, valueSig] 9)
    (.cons (returnD [valueSig, valueSig, valueSig] 11) .nil)
def newerD : WordEnvD newer := .group olderD bodiesD

example : (lookupWord newerD .here).closure = lookup newer .here := lookupWord_eq_lookup newerD .here
example : (lookupWord newerD (.there .here)).closure = lookup newer (.there .here) :=
  lookupWord_eq_lookup newerD (.there .here)
example : (lookupWord newerD (.there (.there .here))).closure = lookup older .here := rfl
example : (lookupWord newerD .here).environment = newerD := rfl
example : (lookupWord newerD (.there .here)).environment = newerD := rfl
example : (lookupWord newerD (.there (.there .here))).environment = olderD := rfl

def countdownD : WordStmtD countdown := by
  apply WordStmtD.seq
  · apply WordStmtD.if_
    · exact .builtin (.pure .«iszero») (fun _ => .local 0)
    · exact .seq (.assign .literal) .leave
  · apply WordStmtD.assign
    exact .call .here (fun _ => .builtin (.pure .«sub») (fun i => by
      split
      · exact .local 0
      · exact .literal))
def recursiveD : WordEnvD recursiveEnv := .group .nil (.cons countdownD .nil)
example : (lookupWord recursiveD .here).environment = recursiveD := rfl
example : (lookupWord recursiveD .here).closure.body = countdown := rfl

def mulDivD : WordStmtD Static.mulDivBody := by
  apply WordStmtD.assign
  exact .builtin (.pure .«div») (fun i => by
    split
    · exact .builtin (.pure .«mul») (fun j => by
        split
        · exact .local 0
        · exact .local 1)
    · exact .local 2)
def mulDivEnvironmentD : WordEnvD mulDivEnv := .group .nil (.cons mulDivD .nil)
example : (lookupWord mulDivEnvironmentD .here).closure.body = Static.mulDivBody := rfl

def firstMutualD : WordStmtD firstMutual := .assign (.call (.there .here) (fun _ => .local 0))
def secondMutualD : WordStmtD secondMutual := .assign (.call .here (fun _ => .local 0))
def mutualD : WordEnvD mutualEnv := .group .nil (.cons firstMutualD (.cons secondMutualD .nil))
example : (lookupWord mutualD .here).environment = mutualD := rfl
example : (lookupWord mutualD (.there .here)).environment = mutualD := rfl

def voidD : WordEnvD voidEnv := .group .nil (.cons .leave .nil)
example : (lookupWord voidD .here).closure.body = Stmt.leave := rfl
def loopD : WordStmtD Static.loop :=
  .for_ .skip .literal
    (.assign (.builtin (.pure .«add») (fun i => by
      split
      · exact .local 0
      · exact .literal)))
    (.seq (.if_ (.local 0) .break_) .continue_)

example : (WordBuiltinD.pure .«div»).eval (fun _ => word 0) 0 = word 0 := rfl
example : (WordBuiltinD.pure .«add»).eval (fun i => word (if i.val = 0 then 7 else 9)) 0 = word 16 := by decide
example : WordBuiltinD.pop.eval (fun _ => word 5) = Fin.elim0 := rfl


def memoryBody (F : List Sig) (control : Control) : Stmt F [] control 1 :=
  .assign (fun _ => .«local» 0)
    (.builtin .mload (fun _ => .literal (word 0)))
theorem memoryBody_not_profile (F : List Sig) (control : Control) :
    ¬ StmtWordP (memoryBody F control) := by
  intro h
  cases h.2.1
example : ¬ StmtWordP (Stmt.zero (n := 0) 1 (memoryBody [] ⟨false, false⟩)) :=
  memoryBody_not_profile [] ⟨false, false⟩
example (d : WordStmtD (memoryBody [] ⟨false, false⟩)) : False :=
  memoryBody_not_profile [] ⟨false, false⟩ d.profile

def memoryEnvironment : FunctionEnv [valueSig] :=
  .group [valueSig] .nil (.cons (memoryBody [valueSig] ⟨true, false⟩) .nil)
example : ¬ EnvWordP memoryEnvironment := by
  intro h
  exact memoryBody_not_profile [valueSig] ⟨true, false⟩ h.2.1

example : EnvWordP recursiveEnv := recursiveD.profile
example : EnvWordP mutualEnv := mutualD.profile
example : StmtWordP Static.loop := loopD.profile
example : StmtWordP Static.mulDivBody := mulDivD.profile
example : ClosureWordP (lookup newer .here) := lookup_profile newer newerD.profile .here
example : EnvWordP (lookup newer (.there (.there .here))).environment :=
  (lookup_profile newer newerD.profile (.there (.there .here))).1
example : StmtWordP (lookup newer (.there .here)).body :=
  (lookup_profile newer newerD.profile (.there .here)).2
example {F c n} {s : Stmt F [] c n} (left right : StmtWordP s) : left = right := rfl


end Solidity.Yul.Checks.ClosedPure
