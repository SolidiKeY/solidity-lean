import Solidity.Calculus.StatePartsScoped
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Update simplification on scoped formulas

`Calculus/UpdRuleScoped.lean`'s rules and `Calculus/StatePartsScoped.lean`'s
merges on scoped formulas, each computed by the kernel (`rfl`) and used on a
`⊨` goal through `Valid.of_simpUpdsS`/`Valid.of_updAtS`, then closed by
`sol_close`.  The rules give the formula they rewrite, one way, so they
apply at its positive positions only: the last example's update under a
negation stays.
-/

namespace Solidity.Examples.Tactics.UpdRulesScoped

local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-! ## Rule by rule, and all at once -/

/-- `sequentialToParallel`: `x = 1; y = x;`'s two updates as one, `x` read
as what the first update sets it to. -/
example : (dl!{ { x := 1 } { y := x } y == 1 }).updAtS .sequentialToParallel =
    some dl!{ { x := 1 ‖ y := 1 } y == 1 } := rfl

/-- `simpUpdsS` merges every stack. -/
example : (dl!{ { x := 1 } { y := x } y == 1 }).simpUpdsS = dl!{ { x := 1 ‖ y := 1 } y == 1 } :=
  rfl

/-- The merged leaf proves the stack. -/
example : ⊨ dl!{ { x := 1 } { y := x } y == 1 } := by
  refine Valid.of_simpUpdsS ?_
  show ⊨ dl!{ { x := 1 ‖ y := 1 } y == 1 }
  sol_close

/-- `applyOnRigid`: a goal reading only what the update sets, under the
diamond for an update that cannot halt (`x` a parameter, set to `1`). -/
example : (dl![.diamond]{ { x := 1 } x == 1 }).updAtS .applyOnRigid =
    some dl![.diamond]{ ∀ uint x; 1 == 1 } := rfl

/-- A rule under a negation is not applied: it gives the formula it
rewrites, not the converse. -/
example : (dl!{ ¬ { x := 1 } { y := x } y == 1 }).updAtS .sequentialToParallel = none := rfl

/-! ## Over a storage or memory write

`Upd.seqPar` reads the second update in the first one's state exactly, so it
refuses a memory term after a storage write; the storage merge reads it
where a write looks (`Calculus/StatePartsScoped.lean`). -/

example : (dl!{ { storage := save(storage, alice.age, 1) } { memory := addM(memory, Person) } true }).updAtS
    .sequentialToParallel = none := rfl

example : (dl!{ { storage := save(storage, alice.age, 1) } { memory := addM(memory, Person) } true }).mergeAtS
    .storage = some dl!{ { storage := save(storage, alice.age, 1) ‖ memory := addM(memory, Person) } true } :=
  rfl

/-- A storage read after a storage write reads the write. -/
example : (dl!{ { storage := save(storage, alice.age, 1) } { v := find(storage, alice.age) } v == 1 }).mergeAtS
    .storage = some dl!{ { storage := save(storage, alice.age, 1) ‖
      v := find(save(storage, alice.age, 1), alice.age) } v == 1 } := rfl

/-- `{memory := M}{V}`: `M` for `memory` in `V`. -/
example : (dl!{ { memory := addM(memory, Person) } { memory := addM(memory, Person) } true }).mergeAtS
    .memory = some dl!{ { memory := addM(memory, Person) ‖
      memory := addM(addM(memory, Person), Person) } true } := rfl

end Solidity.Examples.Tactics.UpdRulesScoped
