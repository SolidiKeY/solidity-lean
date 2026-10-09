import Solidity.Calculus.Step
import Solidity.Calculus.Quote
import Solidity.Calculus.Print
import Solidity.Calculus.NFmlClose

/-!
# The strategy on scoped formulas

`Calculus/Step.lean`'s `symex` on three programs of the worked
examples, each read into the scoped syntax (`Prog.resolve`), run to its end
by the compiled code, quoted back (`Fml.quote`) and checked by the
kernel: `coreSymex` adds the theorem `symex n φ = ψ`, proved by `Eq.refl`.

What is printed is the scoped result (`Fml.show`): a scope end pops
its locals invisibly.  Until W4 `calc-del` each result was also checked
against today's strategy (its erasure, each branch's cover dropped, with the
same fresh names); that strategy is deleted, and the results printed here
are those it agreed with.

`docs/intrinsic.md` ("M6a lane") has the kernel times beside today's.
-/

namespace Solidity.Examples.Tactics.CoreSymex

open Solidity Lean Meta

local instance : InContract := ⟨StandardExample⟩

private abbrev SE := StandardExample

/-- The fuel: enough for every program below. -/
private def fuel : Nat := 1000

/-- Run `symex` on `φ` read into the scoped syntax, add `name : symex fuel φ' = ψ` checked by
the kernel, and print `ψ`. -/
private def coreSymex (name : Lean.Name) (φ : Solidity.Surface.Fml SE) : MetaM Unit := do
  let c := mkConst ``StandardExample
  let .modal m P _ := φ | throwError "not a modality"
  let .ok ⟨_, Pc⟩ := Prog.resolve (C := SE) [] P | throwError "the program does not resolve"
  let φc : Fml SE [] := .modal m Pc .nil .tt
  let ψ := symex fuel φc
  let ctx := Quote.qCtxRaw []
  let lhs := mkAppN (mkConst ``symex) #[c, ctx, toExpr fuel, Fml.quote c φc]
  let rhs := Fml.quote c ψ
  let ty ← mkEq lhs rhs
  addDecl (.thmDecl { name, levelParams := [], type := ty, value := ← mkEqRefl rhs })
  logInfo (← ψ.show c [])

/-! ## A branch on a read, then a read -/

private def branchφ : Solidity.Surface.Fml SE :=
  dl!{ [ if (alice.age > 4) { total = 1; } else { total = 2; }; uint y = total; ] true }

/--
info: { se2 := find(storage, alice.age) } { se1 := se2 > 4 } ((se1 ≐ true → { storage := save(storage, total, 1) } { y := find(storage, total) } true) ∧ (se1 ≐ false → { storage := save(storage, total, 2) } { y := find(storage, total) } true))
-/
#guard_msgs in
run_meta coreSymex `Solidity.Examples.Tactics.CoreSymex.branch branchφ

/-! ## Reads and writes of a member -/

private def memberφ : Solidity.Surface.Fml SE := dl!{ [ uint x = alice.age; uint y = x + 1; alice.age = y; ] true }

/-- info: { x := find(storage, alice.age) } { y := x + 1 } { storage := save(storage, alice.age, y) } true -/
#guard_msgs in
run_meta coreSymex `Solidity.Examples.Tactics.CoreSymex.member memberφ

/-! ## A default, a `require`, a write -/

private def guardφ : Solidity.Surface.Fml SE :=
  dl!{ [ uint x; x = 4; uint y = x + 1; require(y > 3); total = y; ] true }

/--
info: { x := 0 } { x := 4 } { y := x + 1 } { se1 := y > 3 } ((se1 ≐ true → { storage := save(storage, total, y) } true) ∧ (se1 ≐ false → true))
-/
#guard_msgs in
run_meta coreSymex `Solidity.Examples.Tactics.CoreSymex.guard guardφ

end Solidity.Examples.Tactics.CoreSymex
