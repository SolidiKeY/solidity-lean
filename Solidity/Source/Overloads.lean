import Solidity.Source.Typing

/-!
# Overloads across bases (G12)

S01's `Env.lookup` takes the first scope of a contract's linearization that
declares a name, so a function overloaded between a contract and its base
was not one overload set ("What S01 does not do").  solc imports every
inherited member into the derived contract's scope; a base function is
hidden only by a more derived function with the same parameter types (its
override), and `private` members of bases are not inherited.

`InheritedFn E c x d` states that: `d` is a function named `x`, visible
from `c`, declared in scope `b` of `c`'s linearization `pre ++ b :: post`,
and no function named `x` visible in a scope of `pre` has its parameter
types.  The checker is `Env.inheritedFns` in
`Solidity/Frontend/Static/Overloads.lean`.

Not modelled: a public state variable overriding a base function (its
getter) and a non-function member do not hide base functions here; S01's
`WellFormed` does not yet check overrides (G14).

Parameter types are compared with S01's structural `STy.sameList`; a
function whose signature does not elaborate is never the same as another
(it is refused by `WellFormed` anyway).
-/

namespace Solidity.Source

/-- The linearization lookup uses: `[c]` when there is none. -/
def Env.chain (E : Env) (c : String) : List String := (E.linearize c).getD [c]

/-- The functions named `x` declared in scope `b`, visible from `c` and
callable there by name (not `external`; S01's `Decl.callableFrom`). -/
def Env.visibleFns (E : Env) (c b x : String) : List Decl :=
  (E.visible (Option.some c) (Option.some b) x).filter fun d =>
    d.kind == .function && d.callableFrom (Option.some c)

/-- Two functions with the same parameter types. -/
def Decl.sameParams (E : Env) (d d' : Decl) : Bool :=
  match d.fnSig E, d'.fnSig E with
  | Option.some (ps, _), Option.some (ps', _) => STy.sameList ps ps'
  | _, _ => false

/-- **The inherited overload set**: `d` is an overload of `x` in contract
`c`, declared in a scope `b` of the linearization and not hidden by a more
derived function with its parameter types. -/
def InheritedFn (E : Env) (c x : String) (d : Decl) : Prop :=
  ∃ pre b post, E.chain c = pre ++ b :: post ∧ d ∈ E.visibleFns c b x ∧
    ∀ b', b' ∈ pre → ∀ d', d' ∈ E.visibleFns c b' x → d'.sameParams E d = false

end Solidity.Source
