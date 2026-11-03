import Solidity.Yul.ScopedExpressions
import Solidity.Yul.Checks.ScopedNames
/-! Supplemental external-scope controls; local/function table validity and
Source occurrence attachment are deliberately not asserted by this property. -/
namespace Solidity.Yul.Checks.ScopedExpressions
open Solidity.Source (Syn)
open Solidity.Yul.ScopedNames
namespace Before
export Solidity.Yul.Checks.ScopedNames (checked selected)
export Solidity.Yul.Checks.ScopedNames.Before
  (types declarations root first second third depth shadowConstant shadowSlot)
end Before

def list {c} : List (Syn c) → Syn (.list c)
  | [] => .nil
  | first :: rest => .cons first (list rest)
def path (name : String) (parts : List String := []) : Syn .yulExpr := .yulPath name parts
def lit (value : Nat) : Syn .yulExpr := .yulLit (.dec value)
def call (name : String) (args : List (Syn .yulExpr)) : Syn .yulExpr := .yulCall name (list args)

def prepared {X} (scope : ExternalScope Before.types X) (term : Syn .yulExpr) : Bool :=
  (Solidity.Yul.ScopedExpressions.check Before.checked scope
    ([] : List (String × Fin 0)) ([] : FunctionNames []) term).isSome
def oldPrepared {X} (scope : ExternalScope Before.types X) (term : Syn .yulExpr) : Bool :=
  (inferExpr (Before.checked.readEnv scope ([] : List (String × Fin 0))
    ([] : FunctionNames [])) term).isSome

example : prepared Before.root (path "a") = true := by decide
example : prepared Before.first (path "a") = false := by decide
example : prepared Before.third (path "s1" ["slot"]) = true := by decide
example : prepared Before.third (path "s0" ["offset"]) = true := by decide
example : prepared Before.third (path "s1" ["length"]) = false := by decide
example : prepared Before.root (path "missing") = false := by decide
example : prepared Before.root (path "s0" ["slot", "offset"]) = false := by decide
example : prepared Before.root (path "s0" [""]) = false := by decide
example : prepared Before.root (path "s0" ["slot.bad"]) = false := by decide
example : prepared Before.root (path "cal" ["length"]) = true := by decide
example : prepared Before.first (path "cal" ["length"]) = false := by decide

/-- Genuine supplemental rejection: the old flat table alone accepts the
forged head, but the independent original-scope relation does not. -/
example : oldPrepared Before.root (path "s0.slot") = true := by decide
example : prepared Before.root (path "s0.slot") = false := by decide
example : oldPrepared Before.third (path "s0.slot") = true := by decide
example : prepared Before.third (path "s0.slot") = false := by decide
example : oldPrepared Before.root (call "add" [path "s0.slot", lit 1]) = true := by decide
example : prepared Before.root (call "add" [path "s0.slot", lit 1]) = false := by decide
example : prepared Before.third (call "add" [path "s0" ["slot"], lit 1]) = true := by decide

abbrev one : Sig := ⟨1, 1⟩
def functions : FunctionNames [one] := [("helper", ⟨one, .here⟩)]
def functionPrepared (term : Syn .yulExpr) : Bool :=
  (Solidity.Yul.ScopedExpressions.check Before.checked Before.root
    ([] : List (String × Fin 0)) functions term).isSome

example : functionPrepared (call "helper" [path "s0" ["slot"]]) = true := by decide
example : functionPrepared (call "helper" [path "s0.slot"]) = false := by decide
example : functionPrepared (call "helper" []) = false := by decide
example : functionPrepared (call "helper" [lit 1, lit 2]) = false := by decide
example : functionPrepared (call "add" [lit 1]) = false := by decide

/-- Actual local priority remains the original checker rule. This supplemental
property alone does NOT validate supplied local-name lexical validity/NoShadow. -/
def localPrepared (locals : List (String × Fin 1)) (term : Syn .yulExpr) : Bool :=
  (Solidity.Yul.ScopedExpressions.check Before.checked Before.root locals
    ([] : FunctionNames []) term).isSome

example : localPrepared [("a", 0)] (path "a") = true := by decide
example : localPrepared [("s0.slot", 0)] (path "s0.slot") = true := by decide
example : localPrepared [("own", 0)] (path "s0.slot") = false := by decide
example : localPrepared [("own", 0)] (call "add" [path "own", path "s0" ["slot"]]) =
    true := by decide

def expression := (Solidity.Yul.ScopedExpressions.check Before.checked Before.third
  ([] : List (String × Fin 0)) ([] : FunctionNames []) (path "s1" ["slot"])).get (by decide)

theorem inhabited : Nonempty (Solidity.Yul.ScopedExpressions.Checked Before.checked Before.third
    ([] : List (String × Fin 0)) ([] : FunctionNames []) (path "s1" ["slot"])) :=
  ⟨expression⟩

example : Solidity.Yul.ScopedExpressions.check Before.checked Before.third
    ([] : List (String × Fin 0)) ([] : FunctionNames []) (path "s1" ["slot"]) =
      some expression := expression.complete
example : expression.term = .external ⟨.there .here, .slot, .slotRead⟩ := rfl

def onlyLocal : List ExternalType := [.value (.unsigned 0)]
def localDeclarations : ExternalNames onlyLocal := [("outside", ⟨_, .here⟩)]
def localChecked : Solidity.Yul.ScopedNames.Checked localDeclarations := ⟨by decide⟩
def emptyCurrent : ExternalScope onlyLocal [] := .function .root
def tiny := call "add" [lit 257, lit 0]

/-- Original namespace is NONEMPTY; it is the CURRENT context that is empty. -/
example : (Solidity.Yul.ScopedExpressions.check localChecked emptyCurrent
    ([] : List (String × Fin 0)) ([] : FunctionNames []) tiny).isSome = true := by decide
example : (Solidity.Yul.ScopedExpressions.check localChecked emptyCurrent
    ([] : List (String × Fin 0)) ([] : FunctionNames []) (path "outside")).isNone = true := by decide
example : (Solidity.Yul.ScopedExpressions.check localChecked emptyCurrent
    ([] : List (String × Fin 0)) ([] : FunctionNames []) tiny).map
      Solidity.Yul.ScopedExpressions.Checked.toTyped =
    inferExpr (localChecked.readEnv emptyCurrent ([] : List (String × Fin 0))
      ([] : FunctionNames [])) tiny :=
  Solidity.Yul.ScopedExpressions.closed_erasure _ _ _ _ _

end Solidity.Yul.Checks.ScopedExpressions
