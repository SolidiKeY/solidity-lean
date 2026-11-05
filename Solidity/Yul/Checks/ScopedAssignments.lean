import Solidity.Yul.ScopedAssignments
import Solidity.Yul.Checks.ScopedExpressions
/-! These controls concern concrete scope/arity/assignment certificates, not
Source admission, function bodies or physical/dirty execution. -/
namespace Solidity.Yul.Checks.ScopedAssignments
open Solidity.Source (Syn)
namespace Before
export Solidity.Yul.Checks.ScopedExpressions (path lit call tiny localChecked emptyCurrent)
export Solidity.Yul.Checks.ScopedExpressions.Before
  (types declarations checked root first second third depth)
end Before

abbrev one : Sig := ⟨1, 1⟩
abbrev two : Sig := ⟨0, 2⟩
def functions : FunctionNames [one, two] :=
  [("helper", ⟨one, .here⟩), ("duo", ⟨two, .there .here⟩)]
def locals : List (String × Fin 2) := [("own", 0), ("other", 1)]
def prepared {X} (scope : ExternalScope Before.types X) (paths : List (List String))
    (rhs : Syn .yulExpr) : Bool :=
  (Solidity.Yul.ScopedAssignments.check Before.checked scope locals functions paths rhs).isSome
def oldPrepared {X} (scope : ExternalScope Before.types X) (paths : List (List String))
    (rhs : Syn .yulExpr) : Bool :=
  (checkAssignment (Before.checked.readEnv scope locals functions)
    (ScopedNames.targetEnv Before.declarations scope locals) paths rhs).isSome
def put {X} (scope : ExternalScope Before.types X) (name : String) (parts : List String := []) : Bool :=
  prepared scope [name :: parts] (Before.lit 257)

example : put Before.root "a" = true := by decide
example : put Before.first "a" = false := by decide
example : put Before.root "m" = true := by decide
example : put Before.root "k" = false := by decide
example : put Before.root "L" = false := by decide
example : put Before.root "s0" ["slot"] = false := by decide
example : put Before.root "localStore" ["slot"] = true := by decide
example : put Before.root "localStore" ["offset"] = false := by decide
example : put Before.root "cal" ["length"] = true := by decide
example : put Before.root "cal" ["offset"] = true := by decide
example : put Before.root "f" ["selector"] = true := by decide
example : put Before.root "f" ["address"] = true := by decide
example : put Before.third "f" ["address"] = false := by decide
example : put Before.root "f.address" = false := by decide
example : put Before.root "f" ["address", "selector"] = false := by decide
example : put Before.root "own" = true := by decide
example : put Before.third "own" = true := by decide

example : prepared Before.root [["own"]] (Before.path "s0" ["slot"]) = true := by decide
example : oldPrepared Before.root [["own"]] (Before.path "s0.slot") = true := by decide
example : prepared Before.root [["own"]] (Before.path "s0.slot") = false := by decide
example : oldPrepared Before.root [["own"]]
    (Before.call "add" [Before.path "s0.slot", Before.lit 1]) = true := by decide
example : prepared Before.root [["own"]]
    (Before.call "add" [Before.path "s0.slot", Before.lit 1]) = false := by decide
example : prepared Before.third [["own"]]
    (Before.call "helper" [Before.path "s1" ["slot"]]) = true := by decide
example : prepared Before.third [["own"]]
    (Before.call "helper" [Before.path "s1.slot"]) = false := by decide

example : prepared Before.root [] (Before.lit 1) = false := by decide
example : prepared Before.root [[]] (Before.lit 1) = false := by decide
example : prepared Before.root [["own"], ["own"]] (Before.call "duo" []) = false := by decide
example : prepared Before.root [["own"], ["other"]] (Before.call "duo" []) = true := by decide
example : prepared Before.root [["f", "selector"], ["f", "address"]]
    (Before.call "duo" []) = true := by decide
example : prepared Before.root [["own"], ["other"]] (Before.lit 1) = false := by decide
example : prepared Before.root [["own"]] (Before.call "duo" []) = false := by decide
example : prepared Before.root [["own"]] (Before.call "helper" []) = false := by decide
example : prepared Before.third [["own"]] (Before.path "a") = false := by decide
example : prepared Before.third [["own"]] (Before.path "k") = true := by decide

def witness := (Solidity.Yul.ScopedAssignments.check Before.checked Before.root
  locals functions [["cal", "offset"]] (Before.call "helper" [Before.path "s1" ["slot"]])).get
    (by decide)

theorem inhabited : Nonempty (Solidity.Yul.ScopedAssignments.Checked Before.checked Before.root
    locals functions [["cal", "offset"]] (Before.call "helper" [Before.path "s1" ["slot"]])) :=
  ⟨witness⟩

example : Solidity.Yul.ScopedAssignments.check Before.checked Before.root locals functions
    [["cal", "offset"]] (Before.call "helper" [Before.path "s1" ["slot"]]) = some witness :=
  witness.complete
example : (Solidity.Yul.ScopedAssignments.targetsD witness.typed).terms ⟨0, by decide⟩ =
    .external ⟨.there (.there (.there (.there (.there (.there (.there .here)))))),
      .offset, .offsetWrite⟩ := rfl
example : Solidity.Yul.ScopedAssignments.Correct Before.checked Before.root locals functions
    witness.typed := witness.correct
example : Solidity.Yul.ScopedAssignments.TargetsCorrect Before.root locals
    (Solidity.Yul.ScopedAssignments.targetsD witness.typed) :=
  Solidity.Yul.ScopedAssignments.correct_targets _ _ _ _ _

example : (Solidity.Yul.ScopedAssignments.check Before.localChecked Before.emptyCurrent
    locals functions [["own"]] Before.tiny).isSome = true := by decide
example : (Solidity.Yul.ScopedAssignments.check Before.localChecked Before.emptyCurrent
    locals functions [["outside"]] Before.tiny).isNone = true := by decide
example : (Solidity.Yul.ScopedAssignments.check Before.localChecked Before.emptyCurrent
    locals functions [["own"]] (Before.path "outside")).isNone = true := by decide
example : (Solidity.Yul.ScopedAssignments.check Before.localChecked Before.emptyCurrent
    locals functions [["own"]] Before.tiny).map Solidity.Yul.ScopedAssignments.Checked.typed =
    checkAssignment (Before.localChecked.readEnv Before.emptyCurrent locals functions)
      (ScopedNames.targetEnv _ Before.emptyCurrent locals) [["own"]] Before.tiny :=
  Solidity.Yul.ScopedAssignments.closed_erasure _ _ _ _ _ _


def functionWitness := (Solidity.Yul.ScopedAssignments.check Before.checked Before.third
  locals functions [["own"]] (Before.path "k")).get (by decide)
example : ∀ position, ∃ index : Fin 2,
    (Solidity.Yul.ScopedAssignments.targetsD functionWitness.typed).terms position = .local index :=
  Solidity.Yul.ScopedAssignments.function_targets_local Before.second locals _
example : (Solidity.Yul.ScopedAssignments.targetsD functionWitness.typed).terms ⟨0, by decide⟩ =
    .local 0 := rfl
example : checkAssignment (Before.checked.readEnv Before.third locals functions)
    (ScopedNames.targetEnv Before.declarations Before.third locals) [["own"]] (Before.path "k") =
    some functionWitness.typed := functionWitness.old_result

/-- Namespace preparation does not manufacture coherence/lexical validity for
supplied local tables. These remain actual caller obligations, not conclusions. -/
def aliasedLocals : List (String × Fin 2) := [("own", 0), ("alias", 0)]
example : (Solidity.Yul.ScopedAssignments.check Before.checked Before.root aliasedLocals
    functions [["own"], ["alias"]] (Before.call "duo" [])).isSome = true := by decide
example : (Solidity.Yul.ScopedAssignments.check Before.checked Before.root
    ([("forged.name", 0)] : List (String × Fin 2)) functions [["forged.name"]]
    (Before.lit 257)).isSome = true := by decide

end Solidity.Yul.Checks.ScopedAssignments
