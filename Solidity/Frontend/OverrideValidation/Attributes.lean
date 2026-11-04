import Solidity.Frontend.OverrideValidation.Identity

/-!
# Reading all override-capable families from existing Source declarations

These are projections and type computations on S00/S01, not a second AST.
A getter remains the original state-variable declaration. In particular,
its generated external signature never replaces its declaration identity.
-/

namespace Solidity.Frontend.OverrideValidation

open Solidity.Source

inductive Family where
  | function | fallback | receive | getter | modifier
  deriving DecidableEq, Repr

/-- Public state variables participate as getters; other data is not callable. -/
def family (d : Decl) : Option Family :=
  match d.kind, d.top, d.node with
  | .function, _, .function .. => some .function
  | .fallback, _, .fallback .. => some .fallback
  | .receive, _, .receive .. => some .receive
  | .modifier, _, .modifier .. => some .modifier
  | .stateVar, _, .stateVar _ (some .pub) _ _ _ _ _ => some .getter
  | _, _, _ => none

/-- The written override specifier, retaining every full identifier path. -/
def overridePaths (d : Decl) : Option (List IdPath) :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ _ _ _ _ o _ _ => o
  | .fallback, _, .fallback _ _ _ _ _ o _ => o
  | .receive, _, .receive _ _ _ _ o _ => o
  | .modifier, _, .modifier _ _ _ o _ => o
  | .stateVar, _, .stateVar _ _ _ o _ _ _ => o
  | _, _, _ => none

/-- Explicit virtualness; getters can never be virtual. -/
def writtenVirtual (d : Decl) : Bool :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ _ _ _ v _ _ _ => v
  | .fallback, _, .fallback _ _ _ _ v _ _ => v
  | .receive, _, .receive _ _ _ v _ _ => v
  | .modifier, _, .modifier _ _ v _ _ => v
  | _, _, _ => false

/-- External visibility is the callable visibility of a public getter. -/
def visibility (d : Decl) : Option Visibility :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ v _ _ _ _ _ _ => v
  | .fallback, _, .fallback _ ext _ _ _ _ _ => if ext then some .external else none
  | .receive, _, .receive ext _ _ _ _ _ => if ext then some .external else none
  | .stateVar, _, .stateVar _ (some .pub) _ _ _ _ _ => some .external
  | .modifier, _, .modifier .. => some .internal
  | _, _, _ => none

/-- Constant getters are pure; other getters are view. -/
def mutability (d : Decl) : Option Mutability :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ _ m _ _ _ _ _ => m
  | .fallback, _, .fallback _ _ m _ _ _ _ => m
  | .receive, _, .receive _ pay _ _ _ _ => if pay then some .payable else none
  | .stateVar, _, .stateVar _ _ (some .constant) _ _ _ _ => some .pure
  | .stateVar, _, .stateVar _ _ _ _ _ _ _ => some .view
  | _, _, _ => none

/-- Public variables provide their getter without a user-written body. -/
def implemented (d : Decl) : Bool := family d == some .getter || d.hasBody

/-- S01's value return types for a struct getter omit arrays and mappings. -/
def getterField (t : STy) : Bool :=
  match t with
  | .array .. | .mapping .. => false
  | _ => true

/-- Peel indexed getter arguments, preserving nominal types and struct fields. -/
def getterSignature (E : Env) : STy → Option (List STy × List STy)
  | .mapping key value => (getterSignature E value).map fun (ps, rs) => (key :: ps, rs)
  | .array _ value _ => (getterSignature E value).map fun (ps, rs) => (STy.int IntTy.u256 :: ps, rs)
  | .struct _ name => (E.structFields name .storage).map fun fs =>
      ([], (fs.map Prod.snd).filter getterField)
  | t => some ([], [t])

/-- The callable types are extracted from the original declaration syntax. -/
def signature (E : Env) (d : Decl) : Option (List STy × List STy) :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ ps _ _ _ _ _ rs _ => do
    return (← ps.tys E d.scope .memory, ← rs.tys E d.scope .memory)
  | .fallback, _, .fallback .fbNoParams _ _ _ _ _ _ => some ([], [])
  | .fallback, _, .fallback (.fbParams p ps rs) _ _ _ _ _ _ => do
    return (← (Syn.cons p ps).tys E d.scope .memory, ← rs.tys E d.scope .memory)
  | .receive, _, .receive .. => some ([], [])
  | .modifier, _, .modifier _ .none _ _ _ => some ([], [])
  | .modifier, _, .modifier _ (.some ps) _ _ _ => do
    return (← ps.tys E d.scope .memory, [])
  | .stateVar, _, .stateVar _ (some .pub) _ _ _ _ _ => d.varTy E >>= getterSignature E
  | _, _, _ => none

end Solidity.Frontend.OverrideValidation
