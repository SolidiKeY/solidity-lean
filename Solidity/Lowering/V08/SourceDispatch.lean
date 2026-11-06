import Solidity.Lowering.V08.SourceCallable
import Solidity.Lowering.V08.DeclarationRoles

/-! Published nonvirtual source callable selection. No compiler, linking,
modifier/body lowering, library deployment or target frame relation is added. -/
namespace Solidity.Lowering.V08.SourceDispatch
open Solidity Source

theorem free_selection {E : Source.Env} (global : Glob E) (contract : String) (declaration : Decl)
    (free : declaration.scope = none) : global.dispatchFn contract declaration = declaration := by
  unfold Source.Glob.dispatchFn
  cases signature : declaration.fnSig E with
  | none => rfl
  | some pair =>
    simp only [free,Option.isSome_none,Bool.false_and,Bool.false_eq_true,↓reduceIte]

theorem outside_selection {E : Source.Env} (global : Glob E) (contract : String) (declaration : Decl)
    (outside : ((E.linearize contract).getD [contract]).any (some · == declaration.scope) = false) :
    global.dispatchFn contract declaration = declaration := by
  unfold Source.Glob.dispatchFn
  cases signature : declaration.fnSig E with
  | none => rfl
  | some pair =>
    simp only [outside,Bool.and_false,Bool.false_eq_true,↓reduceIte]

theorem free_body {E : Source.Env} (global : Glob E) (contract : String) (declaration : Decl)
    (free : declaration.scope = none) :
    global.prog.body (global.dispatchFn contract declaration) = global.prog.body declaration := by
  rw [free_selection global contract declaration free]

theorem outside_body {E : Source.Env} (global : Glob E) (contract : String) (declaration : Decl)
    (outside : ((E.linearize contract).getD [contract]).any (some · == declaration.scope) = false) :
    global.prog.body (global.dispatchFn contract declaration) = global.prog.body declaration := by
  rw [outside_selection global contract declaration outside]

#print axioms free_selection
#print axioms outside_selection
#print axioms free_body
#print axioms outside_body
end Solidity.Lowering.V08.SourceDispatch
