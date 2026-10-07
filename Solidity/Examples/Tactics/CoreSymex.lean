import Solidity.Calculus.Core.Step
import Solidity.Calculus.Core.Quote
import Solidity.Calculus.Core.Print
import Solidity.Calculus.Close

/-!
# The strategy on scoped formulas

`Calculus/Core/Step.lean`'s `symex` on three programs of the worked
examples, each read into the scoped syntax (`Prog.resolve`), run to its end
by the compiled code, quoted back (`Core.Fml.quote`) and checked by the
kernel: `coreSymex` adds the theorem `symex n φ = ψ`, proved by `Eq.refl`.

Each result is also checked against today's strategy: its erasure is what
`Symex.lean`'s `symex` leaves of the same formula, once the third goal of
each branch (the cover, which the scoped calculus does not have) is dropped,
with the same fresh names.  What is printed is the scoped result
(`Core.Fml.show`): a scope end pops its locals invisibly, so it reads as
today's.

`docs/intrinsic.md` ("M6a lane") has the kernel times beside today's.
-/

namespace Solidity.Examples.Tactics.CoreSymex

open Solidity Lean Meta

local instance : InContract := ⟨StandardExample⟩

private abbrev SE := StandardExample

/-- Today's formula with each branch's cover goal dropped. -/
private partial def dropCover : Solidity.Fml SE → Solidity.Fml SE
  | .and (.imp c a) (.and (.imp c' b) x) =>
    let q := Solidity.Fml.quote (mkConst ``StandardExample)
    if q x == q (Premise.coverFml .box c c') || q x == q (Premise.coverFml .diamond c c') then
      .and (.imp c (dropCover a)) (.imp c' (dropCover b))
    else .and (.imp c (dropCover a)) (.and (.imp c' (dropCover b)) (dropCover x))
  | .and a b => .and (dropCover a) (dropCover b)
  | .imp a b => .imp a (dropCover b)
  | .upd m U φ => .upd m U (dropCover φ)
  | .not φ => .not (dropCover φ)
  | .havoc φ => .havoc (dropCover φ)
  | .all x p φ => .all x p (dropCover φ)
  | .anon xs φ => .anon xs (dropCover φ)
  | φ => φ

/-- The fuel: enough for every program below. -/
private def fuel : Nat := 1000

/-- Run `Core.symex` on `φ` read into the scoped syntax, check that its
erasure is today's result, add `name : Core.symex fuel φ' = ψ` checked by
the kernel, and print `ψ`. -/
private def coreSymex (name : Lean.Name) (φ : Solidity.Fml SE) : MetaM Unit := do
  let c := mkConst ``StandardExample
  let .modal m P _ := φ | throwError "not a modality"
  let .ok ⟨_, Pc⟩ := Core.Prog.resolve (C := SE) [] P | throwError "the program does not resolve"
  let φc : Core.Fml SE [] := .modal m Pc .nil .tt
  let ψ := Core.symex fuel φc
  let today := dropCover (symex fuel (.modal m P .tt))
  unless Solidity.Fml.quote c (ψ.erase []) == Solidity.Fml.quote c today do
    throwError "the erasure is not today's result:\n{← Core.legacyShow c (ψ.erase [])}\n\
      today:\n{← Core.legacyShow c today}"
  let ctx := Core.Quote.qCtxRaw []
  let lhs := mkAppN (mkConst ``Core.symex) #[c, ctx, toExpr fuel, Core.Fml.quote c φc]
  let rhs := Core.Fml.quote c ψ
  let ty ← mkEq lhs rhs
  addDecl (.thmDecl { name, levelParams := [], type := ty, value := ← mkEqRefl rhs })
  logInfo (← ψ.show c [])

/-! ## A branch on a read, then a read -/

private def branchφ : Solidity.Fml SE :=
  dl!{ [ if (alice.age > 4) { total = 1; } else { total = 2; }; uint y = total; ] true }

/--
info: { se2 := find(storage, alice.age) } { se1 := se2 > 4 } ((se1 ≐ true → { storage := save(storage, total, 1) } { y := find(storage, total) } true) ∧ (se1 ≐ false → { storage := save(storage, total, 2) } { y := find(storage, total) } true))
-/
#guard_msgs in
run_meta coreSymex `Solidity.Examples.Tactics.CoreSymex.branch branchφ

/-! ## Reads and writes of a member -/

private def memberφ : Solidity.Fml SE := dl!{ [ uint x = alice.age; uint y = x + 1; alice.age = y; ] true }

/-- info: { x := find(storage, alice.age) } { y := x + 1 } { storage := save(storage, alice.age, y) } true -/
#guard_msgs in
run_meta coreSymex `Solidity.Examples.Tactics.CoreSymex.member memberφ

/-! ## A default, a `require`, a write -/

private def guardφ : Solidity.Fml SE :=
  dl!{ [ uint x; x = 4; uint y = x + 1; require(y > 3); total = y; ] true }

/--
info: { x := 0 } { x := 4 } { y := x + 1 } { se1 := y > 3 } ((se1 ≐ true → { storage := save(storage, total, y) } true) ∧ (se1 ≐ false → true))
-/
#guard_msgs in
run_meta coreSymex `Solidity.Examples.Tactics.CoreSymex.guard guardφ

end Solidity.Examples.Tactics.CoreSymex
