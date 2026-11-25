import Solidity.Correctness.Lowering.Total.CalleeResolution

/-! Assembled callee declarations under Source name resolution: an ordinary
unique name, two entries retaining one name (an overload set, no selection), a
prefix declaration colliding with a function name, local shadowing and the
empty name. Execution is not checked. -/
namespace Solidity.Examples.Lowering.Total.CalleeResolution

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.Decode
open Solidity.Correctness.Lowering.Total.CalleeAliases
open Solidity.Correctness.Lowering.Total.CalleeResolution

/-- `function NAME() internal {}` with retained source identity. -/
def fn (name : String) : FunDecl :=
  { sourceDecl := some { name, callable := .local .internalFn }, params := [], body := [] }

/-- Distinct names behind distinct aliases. -/
def renamed : List (Name × FunDecl) := [("get_0", fn "get"), ("set_1", fn "set")]
/-- Two aliases, one retained source name `h`. -/
def overload : List (Name × FunDecl) := [("h_0", fn "h"), ("h_1", fn "h")]
/-- A prefix `error f();` colliding with the function `f`. -/
def errorF : Source.Syn (.list (.part false)) := .cons (.error "f" .nil) .nil
def single : List (Name × FunDecl) := [("f_0", fn "f")]
/-- Alias `f` twice: lookup selects `first`; `second` is shadowed as an alias only. -/
def dupAlias : List (Name × FunDecl) := [("f", fn "first"), ("f", fn "second")]

def unitOf (pre : Source.Syn (.list (.part false))) (fs : List (Name × FunDecl)) :
    Option (Source.Syn .unit) :=
  Callee.withFunctions tablesS [] "C" pre fs
/-- Names and kinds of the actual lookup in scope `C`. -/
def lookupOf (pre : Source.Syn (.list (.part false))) (fs : List (Name × FunDecl)) (x : String) :
    Option (List (String × Bool)) :=
  (unitOf pre fs).map fun u =>
    (u.env.lookup (some "C") x).map fun d => (d.name, d.kind == .function)
/-- What `Env.resolve` denotes: a local index, a declaration count, or a builtin. -/
def resolveOf (pre : Source.Syn (.list (.part false))) (fs : List (Name × FunDecl))
    (locals : List String) (x : String) : Option (Option (Nat ⊕ Nat)) :=
  (unitOf pre fs).map fun u => (u.env.resolve locals (some "C") x).bind fun
    | .loc i => some (.inl i)
    | .decls ds => some (.inr ds.length)
    | .builtin _ => none

/-! Unique name, overload set, prefix collision, local shadowing, empty name. -/
#guard lookupOf .nil renamed "get" == some [("get", true)]
#guard lookupOf .nil renamed "get_0" == some []
#guard lookupOf .nil overload "h" == some [("h", true), ("h", true)]
#guard lookupOf errorF single "f" == some [("f", false), ("f", true)]
#guard resolveOf .nil renamed [] "get" == some (some (.inr 1))
#guard resolveOf .nil overload [] "h" == some (some (.inr 2))
#guard resolveOf .nil renamed ["x", "get"] "get" == some (some (.inl 1))
#guard lookupOf .nil [("e", fn "")] "" == some []
#guard lookupOf .nil dupAlias "first" == some [("first", true)]
#guard lookupOf .nil dupAlias "second" == some [("second", true)]
#guard lookupOf .nil dupAlias "f" == some []

/-- The assembled contract linearizes to itself. -/
example {u} (hu : unitOf .nil renamed = some u) : u.env.linearize "C" = some ["C"] :=
  linearize_scope hu

/-- Ordinary unique name: `get_0` lands on the only declaration of `get`,
derived from explicit uniqueness and noncollision. -/
example {u} (hu : unitOf .nil renamed = some u) :
    ∃ out, out.name = "get" ∧ DeclaredUniquely u "C" out ∧
      out ∈ u.env.lookup (some "C") "get" := by
  obtain ⟨out, source, hm, hs, hn, _, _, hk⟩ := alias_lookup hu (a := "get_0") rfl
  cases hs
  have huniq : RetainedUniquely renamed "get" := by
    intro i j e e' s s' hi hj hs hs' hn hn'
    rcases i with _ | _ | i <;> rcases j with _ | _ | j <;>
      simp only [renamed, fn, List.getElem?_cons_zero, List.getElem?_cons_succ,
        List.getElem?_nil, Option.some.injEq, reduceCtorEq] at hi hj <;>
      subst hi hj <;> simp only [Option.some.injEq] at hs hs' <;> subst hs hs' <;>
      simp_all
  obtain ⟨out', hm', hd⟩ := alias_declaredUniquely hu (a := "get_0") rfl rfl (by decide) huniq
    (by simp [PrefixClear, Source.Syn.collect])
  cases hm.symm.trans hm'
  exact ⟨out, hn, hd, (hk (by decide)).2.2⟩

/-- Overloads: resolution denotes both `h` candidates as a set; `h_0`'s
declaration is a member but is not selected, and uniqueness fails. -/
example {u} (hu : unitOf .nil overload = some u) :
    ∃ out, Source.Resolves u.env [] (some "C") "h"
        (.decls (candidates tablesS [] "C" .nil overload "h")) ∧
      (candidates tablesS [] "C" .nil overload "h").length = 2 ∧
      out ∈ candidates tablesS [] "C" .nil overload "h" ∧ ¬ DeclaredUniquely u "C" out := by
  obtain ⟨out, source, hm, hs, hn, _, _, hk⟩ := alias_lookup hu (a := "h_0") rfl
  cases hs
  obtain ⟨hr, _⟩ := alias_resolves hu (a := "h_0") rfl rfl (by decide) (locals := []) rfl
  obtain ⟨hc, _, _⟩ := hk (by decide)
  have hlen : (candidates tablesS [] "C" .nil overload "h").length = 2 := by
    have : entriesNamed tablesS [] "C" overload "h" = [out, out] := by
      simp [entriesNamed, overload, hm, Option.filter, hn]
    simp [candidates, prefixNamed, Source.Syn.collect, this]
  refine ⟨out, hr, hlen, hc, fun h => ?_⟩
  have := congrArg List.length h
  rw [declared_scope hu, hn, hlen] at this
  cases this

/-- Prefix collision: `error f()` is a candidate before the function `f`; the
function is still in the actual lookup, but uniqueness fails. -/
example {u} (hu : unitOf errorF single = some u) :
    ∃ out, (candidates tablesS [] "C" errorF single "f").length = 2 ∧
      (prefixNamed "C" errorF "f").length = 1 ∧
      out ∈ u.env.lookup (some "C") "f" ∧ ¬ DeclaredUniquely u "C" out := by
  obtain ⟨out, source, hm, hs, hn, _, _, hk⟩ := alias_lookup hu (a := "f_0") rfl
  cases hs
  have he : entriesNamed tablesS [] "C" single "f" = [out] := by
    simp [entriesNamed, single, hm, Option.filter, hn]
  have hlen : (candidates tablesS [] "C" errorF single "f").length = 2 := by
    simp only [candidates, if_neg (by decide : "f" ≠ ""), List.length_append, he]
    rfl
  refine ⟨out, hlen, rfl, (hk (by decide)).2.2, fun h => ?_⟩
  have := congrArg List.length h
  rw [declared_scope hu, hn, hlen] at this
  cases this

/-- Duplicate aliases: `f` selects `first`; the shadowed entry `second` is
still a Source declaration under its own name. -/
example {u} (hu : unitOf .nil dupAlias = some u) :
    ∃ out, out.name = "first" ∧ out ∈ u.env.lookup (some "C") "first" := by
  obtain ⟨out, source, _, hs, hn, _, _, hk⟩ := alias_lookup hu (a := "f") rfl
  cases hs
  exact ⟨out, hn, (hk (by decide)).2.2⟩

/-- Empty name: lookup in the assembled scope finds nothing. -/
example {u} (hu : unitOf .nil [("e", fn "")] = some u) : u.env.lookup (some "C") "" = [] :=
  lookup_empty hu

/-- Local shadowing: a local `get` hides the declaration. -/
example {u} (_ : unitOf .nil renamed = some u) :
    u.env.resolve ["x", "get"] (some "C") "get" = some (.loc 1) :=
  alias_local rfl

/-- The empty name has no candidates. -/
example : candidates tablesS [] "C" .nil renamed "" = [] := candidates_empty

end Solidity.Examples.Lowering.Total.CalleeResolution
