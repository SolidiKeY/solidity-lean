import Solidity.Calculus.Spec

/-! Preparation for the existing lexical local renamer. Duplicate declarations
in one source scope remain errors; nested scopes may shadow. The seed reserves
state/parameter names and quantified loop binders, including unused binders. -/
namespace Solidity.Frontend.ExecutableAst.Shared.Scope
open Solidity

def nextIndex (seed : Nat) (indices : List Nat) : Nat := indices.foldl max seed + 1

theorem le_foldMax (seed : Nat) (indices : List Nat) : seed ≤ indices.foldl max seed := by
  induction indices generalizing seed with
  | nil => exact Nat.le_refl seed
  | cons x xs ih =>
    exact Nat.le_trans (Nat.le_max_left seed x) (ih (max seed x))

theorem member_lt_nextIndex (seed : Nat) (indices : List Nat) (i : Nat)
    (member : i ∈ indices) : i < nextIndex seed indices := by
  induction indices generalizing seed with
  | nil => cases member
  | cons x xs ih =>
    cases member with
    | head =>
      exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_max_right seed i) (le_foldMax (max seed i) xs))
    | tail _ h => exact ih (max seed x) h

private def invariantBinders : RawInv → List String
  | .all _ x body => x :: invariantBinders body
  | _ => []

def reservedNames (C : Contract) (d : FunDecl) : List String :=
  C.vars.map (·.1) ++ d.params.map (·.1) ++ d.rets.map (·.1) ++
    RawStmt.namesList d.body ++ RawStmt.declsList d.body ++
    d.body.flatMap (RawStmt.flatMapDeep fun
      | .whileLoop a _ _ | .doWhile a _ _ | .forLoop a _ _ _ _ | .loop a _ _ =>
          a.qinv.flatMap invariantBinders
      | _ => [])

def bodySeed (C : Contract) (d : FunDecl) : Nat :=
  nextIndex (max C.rootMaxIdx (RawStmt.maxIdxs d.body))
    ((reservedNames C d).map fun name => (Var.ofName name).idx)

theorem reserved_lt_bodySeed (C : Contract) (d : FunDecl) (name : String)
    (member : name ∈ reservedNames C d) : (Var.ofName name).idx < bodySeed C d := by
  exact member_lt_nextIndex _ _ _ (List.mem_map.mpr ⟨name, member, rfl⟩)

/-- Validate names within each scope before fresh labels can hide duplicates. -/
partial def validateScopes (initial : List String) (body : List RawStmt) : Except String Unit := do
  let mut seen : List String := []
  for name in initial do
    if seen.contains name then throw s!"{name} is already declared, or names a state variable"
    seen := name :: seen
  for statement in body do
    for name in statement.owns do
      if seen.contains name then throw s!"{name} is already declared, or names a state variable"
      seen := name :: seen
    match statement with
    | .tryCall _ _ _ returns ok err code panic other =>
      validateScopes (returns.map (·.2)) ok
      validateScopes [] err
      validateScopes code.toList panic
      validateScopes [] other
    | _ =>
      for block in statement.blocks do validateScopes [] block

end Solidity.Frontend.ExecutableAst.Shared.Scope
