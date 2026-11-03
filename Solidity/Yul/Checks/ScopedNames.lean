import Solidity.Yul.ScopedNames
import Solidity.Yul.TierPolicy
import Solidity.Yul.Checks.ExternalScopes
/-! Constructed-table controls over the original supplied typed declarations.
These are not Source namespace, lexer/occurrence or physical/dirty semantics proofs. -/
namespace Solidity.Yul.Checks.ScopedNames
open Solidity.Yul.ScopedNames
namespace Before
export Solidity.Yul.Checks.ExternalScopes
  (types declarations root first second third depth shadowConstant shadowSlot)
end Before

def checked : Checked Before.declarations := ⟨by decide⟩

def observe {X write} (ref : ExternalRef X write) : Nat × Attribute :=
  (Before.depth ref.index, ref.attr)

def looked {X} (decls : ExternalNames Before.types)
    (scope : ExternalScope Before.types X) (name : String) (parts : List String)
    (write : Bool := false) : Option (Nat × Attribute) :=
  (resolve (names decls scope write) (externalKey name parts)).map observe

example : looked Before.declarations Before.root "a" [] = some (0, .plain) := by decide
example : looked Before.declarations Before.root "a" [] true = some (0, .plain) := by decide
example : looked Before.declarations Before.first "a" [] = none := by decide
example : looked Before.declarations Before.third "a" [] = none := by decide
example : looked Before.declarations Before.root "s1" ["slot"] = some (2, .slot) := by decide
example : looked Before.declarations Before.first "s1" ["slot"] = some (1, .slot) := by decide
example : looked Before.declarations Before.third "s0" ["slot"] = some (0, .slot) := by decide
example : looked Before.declarations Before.third "k" [] = some (2, .plain) := by decide
example : looked Before.declarations Before.third "transient" ["slot"] = some (4, .slot) := by decide
example : looked Before.declarations Before.root "localStore" ["slot"] true = some (8, .slot) := by decide
example : looked Before.declarations Before.root "localStore" ["offset"] true = none := by decide
example : looked Before.declarations Before.first "localStore" ["slot"] = none := by decide
example : looked Before.declarations Before.root "cal" ["offset"] true = some (7, .offset) := by decide
example : looked Before.declarations Before.root "cal" ["length"] true = some (7, .length) := by decide
example : looked Before.declarations Before.second "cal" ["length"] = none := by decide
example : looked Before.declarations Before.root "f" ["selector"] = some (6, .selector) := by decide
example : looked Before.declarations Before.root "f" ["address"] true = some (6, .address) := by decide
example : looked Before.declarations Before.second "f" ["selector"] = none := by decide
example : looked Before.declarations Before.second "s0" ["slot"] true = none := by decide
example : looked Before.declarations Before.root "missing" [] = none := by decide
example : looked Before.declarations Before.root "s0" ["slot", "offset"] = none := by decide
example : looked Before.declarations Before.root "s0" ["slot.bad"] = none := by decide
example : looked Before.declarations Before.root "s0" [""] = none := by decide

/-- Repeated candidates still use the original first declaration. -/
example : looked Before.shadowConstant Before.root "same" [] = some (0, .plain) := by decide
example : looked Before.shadowConstant Before.first "same" [] = none := by decide
example : looked Before.shadowConstant Before.third "same" [] = none := by decide
example : looked Before.shadowSlot Before.root "same" ["slot"] = none := by decide
example : looked Before.shadowSlot Before.third "same" ["slot"] = none := by decide

def badNames : ExternalNames Before.types := [("s0.slot", ⟨_, .there .here⟩)]
example : (check badNames).isNone = true := by decide
example : (check Before.declarations).isSome = true := by decide

/-- Outside the real no-dot QUERY premise, flattened keys can collide.
This supplied forged Syn head is not a parsed Source/Yul identifier. -/
example : looked Before.declarations Before.root "s0.slot" [] = some (1, .slot) := by decide
example : (checkScopedExternal Before.declarations Before.root "s0.slot" [] false).isNone =
    true := by decide

def selected :=
  (checkScopedExternal Before.declarations Before.second "s1" ["slot"] false).get (by decide)

def expression : ExprD (checked.readEnv Before.second ([] : List (String × Fin 0)) ([] : FunctionNames []))
    (.yulPath "s1" ["slot"]) 1 :=
  checked.externalExpr Before.second [] [] selected.2 (.inl (by decide))

theorem expression_inhabited : Nonempty (ExprD
    (checked.readEnv Before.second ([] : List (String × Fin 0)) ([] : FunctionNames []))
    (.yulPath "s1" ["slot"]) 1) := ⟨expression⟩

example : inferExpr (checked.readEnv Before.second ([] : List (String × Fin 0)) ([] : FunctionNames []))
    (.yulPath "s1" ["slot"]) = some ⟨1, expression⟩ := expression.complete
example : expression.term = .external selected.1 := rfl
example : Policy.checkExpr .A expression.term = .error (.needsTier .B) := rfl
example : Policy.checkExpr .B expression.term = .ok () := rfl

def writable :=
  (checkScopedExternal Before.declarations Before.root "cal" ["length"] true).get (by decide)

example : (checkTarget (targetEnv Before.declarations Before.root
    ([] : List (String × Fin 0))) "cal" ["length"]).map Sigma.fst =
      some (.external writable.1) :=
  checkTarget_external_complete [] writable.2 (.inl (by decide))

example : targetDeclarations Before.declarations Before.root = Before.declarations := rfl
example : targetDeclarations Before.declarations Before.third = [] := rfl
example : entries Before.declarations Before.third true = [] :=
  function_write_entries_empty _ _
example : (checkTarget (targetEnv Before.declarations Before.root
    [("own", (0 : Fin 1))]) "own" []).map (fun pair =>
      match pair.1 with | .local _ => true | .external _ => false) = some true := by decide

end Solidity.Yul.Checks.ScopedNames
