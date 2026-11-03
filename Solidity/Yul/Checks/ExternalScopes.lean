import Solidity.Yul.ExternalScope
set_option Elab.async false

namespace Solidity.Yul.Checks.ExternalScopes

def types : List ExternalType :=
  [.value (.unsigned 0), .storage false false, .storage false false, .constant (word 9),
    .library, .memory, .externalFunction, .calldataDynamic, .storage true false,
    .storage false true]
def declarations : ExternalNames types :=
  [("a", ⟨_, .here⟩), ("s0", ⟨_, .there .here⟩), ("s1", ⟨_, .there (.there .here)⟩),
   ("k", ⟨_, .there (.there (.there .here))⟩),
   ("L", ⟨_, .there (.there (.there (.there .here)))⟩),
   ("m", ⟨_, .there (.there (.there (.there (.there .here))))⟩),
   ("f", ⟨_, .there (.there (.there (.there (.there (.there .here)))))⟩),
   ("cal", ⟨_, .there (.there (.there (.there (.there (.there (.there .here))))))⟩),
   ("localStore", ⟨_, .there (.there (.there (.there (.there (.there (.there (.there .here)))))))⟩),
   ("transient", ⟨_, .there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))⟩)]

def root : ExternalScope types types := .root
def first : ExternalScope types (globals types) := .function root
def second : ExternalScope types (globals (globals types)) := .function first
def third : ExternalScope types (globals (globals (globals types))) := .function second

def depth {α : Type} {X : List α} {ty : α} (index : Member X ty) : Nat := by
  apply Member.casesOn (motive := fun _ _ _ => Nat) index
  case here => intros; exact 0
  case there => intro a b rest previous; exact depth previous + 1
termination_by structural index

example : (checkScopedExternal declarations root "a" [] false).isSome = true := by decide
example : (checkScopedExternal declarations root "a" [] true).isSome = true := by decide
example : (checkScopedExternal declarations first "a" [] false).isNone = true := by decide
example : (checkScopedExternal declarations second "a" [] false).isNone = true := by decide
example : (checkScopedExternal declarations third "a" [] false).isNone = true := by decide
example : (checkScopedExternal declarations root "m" [] false).isSome = true := by decide
example : (checkScopedExternal declarations second "m" [] false).isNone = true := by decide
example : (checkScopedExternal declarations root "f" ["selector"] false).isSome = true := by decide
example : (checkScopedExternal declarations root "f" ["address"] true).isSome = true := by decide
example : (checkScopedExternal declarations second "f" ["selector"] false).isNone = true := by decide
example : (checkScopedExternal declarations second "f" ["address"] true).isNone = true := by decide
example : (checkScopedExternal declarations root "cal" ["offset"] false).isSome = true := by decide
example : (checkScopedExternal declarations root "cal" ["length"] true).isSome = true := by decide
example : (checkScopedExternal declarations second "cal" ["offset"] false).isNone = true := by decide
example : (checkScopedExternal declarations second "cal" ["length"] true).isNone = true := by decide
example : (checkScopedExternal declarations root "localStore" ["slot"] true).isSome = true := by decide
example : (checkScopedExternal declarations second "localStore" ["slot"] false).isNone = true := by decide
example : (checkScopedExternal declarations root "localStore" ["offset"] true).isNone = true := by decide
example : (checkScopedExternal declarations first "s0" ["slot"] false).isSome = true := by decide
example : (checkScopedExternal declarations second "s0" ["slot"] false).isSome = true := by decide
example : (checkScopedExternal declarations second "s1" ["slot"] false).isSome = true := by decide
example : (checkScopedExternal declarations third "s1" ["slot"] false).isSome = true := by decide
example : (checkScopedExternal declarations second "k" [] false).isSome = true := by decide
example : (checkScopedExternal declarations second "L" [] false).isSome = true := by decide
example : (checkScopedExternal declarations second "transient" ["slot"] false).isSome = true := by decide
example : (checkScopedExternal declarations second "s0" ["slot"] true).isNone = true := by decide
example : (checkScopedExternal declarations second "k" [] true).isNone = true := by decide
example : (checkScopedExternal declarations second "missing" [] false).isNone = true := by decide
example : (checkScopedExternal declarations second "s0" ["length"] false).isNone = true := by decide

example : (checkScopedExternal declarations root "s1" ["slot"] false).map
    (fun pair => depth pair.1.index) = some 2 := by decide
example : (checkScopedExternal declarations first "s1" ["slot"] false).map
    (fun pair => depth pair.1.index) = some 1 := by decide
example : (checkScopedExternal declarations second "s1" ["slot"] false).map
    (fun pair => depth pair.1.index) = some 1 := by decide
example : (checkScopedExternal declarations third "s0" ["slot"] false).map
    (fun pair => depth pair.1.index) = some 0 := by decide
example : (checkScopedExternal declarations third "k" [] false).map
    (fun pair => depth pair.1.index) = some 2 := by decide
example : (checkScopedExternal declarations third "transient" ["slot"] false).map
    (fun pair => depth pair.1.index) = some 4 := by decide

/-- A captured local must not expose the readable constant behind its name. -/
def shadowConstant : ExternalNames types :=
  [("same", ⟨.value (.unsigned 0), .here⟩),
   ("same", ⟨.constant (word 9), .there (.there (.there .here))⟩)]
example : (checkScopedExternal shadowConstant root "same" [] false).map
    (fun pair => depth pair.1.index) = some 0 := by decide
example : (checkScopedExternal shadowConstant first "same" [] false).isNone = true := by decide
example : (checkScopedExternal shadowConstant second "same" [] false).isNone = true := by decide
example : (checkScopedExternal shadowConstant third "same" [] false).isNone = true := by decide

/-- An illegal suffix on the selected local must not expose the older slot. -/
def shadowSlot : ExternalNames types :=
  [("same", ⟨.value (.unsigned 0), .here⟩),
   ("same", ⟨.storage false false, .there .here⟩)]
example : (checkScopedExternal shadowSlot root "same" ["slot"] false).isNone = true := by decide
example : (checkScopedExternal shadowSlot second "same" ["slot"] false).isNone = true := by decide

end Solidity.Yul.Checks.ExternalScopes
