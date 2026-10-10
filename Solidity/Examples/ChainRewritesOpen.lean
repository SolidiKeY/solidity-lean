import Solidity.Calculus.RewriteChains
import Solidity.Calculus.Rewrite
import Solidity.Examples.Chains.Storage
import Solidity.Calculus.LastLine
import Solidity.Calculus.Surface

/-!
# Chain rewrites while the program is open

`Examples/ChainRewrites.lean`'s rewrites on the scoped line itself, before
the program is done
(`Calculus/RewriteScoped.lean`, `Link.rw`): the reverting branch stays
`[ revert(); ] φ`, and the strategy goes on from the line a rewrite
leaves, so a step and a rewrite are links of one chain.  A literal law in
an update's right-hand sides (`FmlRw.lit`), `applyOnRigid` along the
skeleton of the formula under the update (`FmlRw.applyOnRigid`: the update
cannot halt, or the box), `concrete` (`FmlRw.concrete`) and
`simplifyUpdate` (`FmlRw.simplifyUpdate`: what the update pops, under the
box, and its shadowed writes), each proved by `rfl` over the
postcondition and the program it does not look at; `~~>` finds up to three
of them and the merges past a line of the derivation.  A
term taclet in a box update (`FmlRw.lawUpd`) is the box's.  Under a
modality variable `m` each rewrite runs as the diamond and as the box, and
applies where both give the same line with `m` read back. -/

namespace Solidity.Examples.ChainRewritesOpen

open scoped Scoped

local instance : InContract := ⟨StandardExample⟩

section Open
variable (m : Modality)

/-- `applyOnRigid` and `concrete` with the revert still to run, then the
step that runs it (`revertBox`). -/
example (φ : Post StandardExample []) :
    dl![.box]{ { se1 := false } ((se1 ≐ true → φ) ∧ (se1 ≐ false → [ revert(); ] φ)) }
    ~[applyOnRigid]~>
      dl![.box]{ (false ≐ true → { se1 := false } φ) ∧
        (false ≐ false → { se1 := false } [ revert(); ] φ) }
    ~[concrete]~> dl![.box]{ { se1 := false } [ revert(); ] φ }
    ~[revertBox]~> dl![.box]{ { se1 := false } true } := by
  sol_chain

/-- `uint8 x = 250; x += 10;` (`Chains.CheckedArithmetic`): the check's
branches folded before the revert runs, the strategy's steps and the
rewrites in one chain. -/
example (φ : Post StandardExample [.val .uint]) :
    dl!{ [ uint8 x = 250; x += 10; ] φ }
    ~*> dl![.box]{ { x := 250 } { x := x + 10 } { se1 := x <= 255 }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → [ revert(); ] φ)) }
    ~[sequentialToParallel]~> dl![.box]{ { x := 250 ‖ x := 250 + 10 ‖ se1 := 250 + 10 <= 255 }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → [ revert(); ] φ)) }
    ~[add_literals]~> dl![.box]{ { x := 250 ‖ x := 260 ‖ se1 := 260 <= 255 }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → [ revert(); ] φ)) }
    ~[leq_literals]~> dl![.box]{ { x := 250 ‖ x := 260 ‖ se1 := false }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → [ revert(); ] φ)) }
    ~[applyOnRigid]~> dl![.box]{ (false ≐ true → { x := 250 ‖ x := 260 ‖ se1 := false } φ) ∧
          (false ≐ false → { x := 250 ‖ x := 260 ‖ se1 := false } [ revert(); ] φ) }
    ~[concrete]~> dl![.box]{ { x := 250 ‖ x := 260 ‖ se1 := false } [ revert(); ] φ }
    ~[revertBox]~> dl![.box]{ { x := 250 ‖ x := 260 ‖ se1 := false } true } := by
  sol_chain

/-- The same under the diamond: the revert is `false`. -/
example (φ : Post StandardExample [.val .uint]) :
    dl!{ ⟨ uint8 x = 250; x += 10; ⟩ φ }
    ~*> dl!{ { x := 250 } { x := x + 10 } { se1 := x <= 255 }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨ revert(); ⟩ φ)) }
    ~[sequentialToParallel]~> dl!{ { x := 250 ‖ x := 250 + 10 ‖ se1 := 250 + 10 <= 255 }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨ revert(); ⟩ φ)) }
    ~[add_literals]~> dl!{ { x := 250 ‖ x := 260 ‖ se1 := 260 <= 255 }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨ revert(); ⟩ φ)) }
    ~[leq_literals]~> dl!{ { x := 250 ‖ x := 260 ‖ se1 := false }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨ revert(); ⟩ φ)) }
    ~[applyOnRigid]~> dl!{ (false ≐ true → { x := 250 ‖ x := 260 ‖ se1 := false } φ) ∧
          (false ≐ false → { x := 250 ‖ x := 260 ‖ se1 := false } ⟨ revert(); ⟩ φ) }
    ~[concrete]~> dl!{ { x := 250 ‖ x := 260 ‖ se1 := false } ⟨ revert(); ⟩ φ }
    ~[revertDiamond]~> dl!{ { x := 250 ‖ x := 260 ‖ se1 := false } false } := by
  sol_chain

-- Under the diamond an update that may halt is not pushed through: the
-- line after would hold where the update halts, the line before not.
/--
error: ~[applyOnRigid]~>: applyOnRigid does not apply to
  dl{ { se1 := 1 / 0 == 0 } ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨ revert(); ⟩ φ)) }
while the program is open
-/
#guard_msgs in
example (φ : Post StandardExample []) :
    dl!{ { se1 := 1 / 0 == 0 } ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨ revert(); ⟩ φ)) }
    ~[applyOnRigid]~> _ := by
  sol_chain

/-- `findOnSave` in a box update, onto a literal (`FmlRw.lawUpd`), with the
revert still to run, then the step that runs it. -/
example (φ : Post StandardExample [.val .uint]) :
    dl![.box]{ { x := find(save(storage, alice.age, 42), alice.age) } [ revert(); ] φ }
    ~[findOnSave]~> dl![.box]{ { x := 42 } [ revert(); ] φ }
    ~[revertBox]~> dl![.box]{ { x := 42 } true } := by
  sol_chain

-- Under the diamond the law is not applied in the update: `{ x := 42 }`
-- runs where the read halts.
/--
error: ~[findOnSave]~>: findOnSave does not apply to
  dl{ { x := find(save(storage, alice.age, 42), alice.age) } ⟨ revert(); ⟩ φ }
while the program is open
-/
#guard_msgs in
example (φ : Post StandardExample [.val .uint]) :
    dl!{ { x := find(save(storage, alice.age, 42), alice.age) } ⟨ revert(); ⟩ φ }
    ~[findOnSave]~> _ := by
  sol_chain

/-- `add_literals` under `m` with the revert still to run: a literal law is
exact, so the diamond and the box give one line. -/
example (φ : Post StandardExample [.val .uint]) :
    dl![m]{ { x := 250 + 10 } ⟨[ revert(); ]⟩ φ }
    ~[add_literals]~> dl![m]{ { x := 260 } ⟨[ revert(); ]⟩ φ } := by
  sol_chain

/-- The check's branches folded under `m`: `{ se1 := false }` cannot halt,
so `applyOnRigid` applies under the diamond too. -/
example (φ : Post StandardExample []) :
    dl![m]{ { se1 := false } ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ)) }
    ~[applyOnRigid]~>
      dl![m]{ (false ≐ true → { se1 := false } φ) ∧
        (false ≐ false → { se1 := false } ⟨[ revert(); ]⟩ φ) }
    ~[concrete]~> dl![m]{ { se1 := false } ⟨[ revert(); ]⟩ φ } := by
  sol_chain

-- Under `m` an update that may halt is not pushed through: the diamond
-- refuses it.
/--
error: ~[applyOnRigid]~>: applyOnRigid does not apply to
  dl{ { se1 := 1 / 0 == 0 } (se1 ≐ false → ⟨[ revert(); ]⟩ φ) }
while the program is open
-/
#guard_msgs in
example (φ : Post StandardExample []) :
    dl![m]{ { se1 := 1 / 0 == 0 } (se1 ≐ false → ⟨[ revert(); ]⟩ φ) }
    ~[applyOnRigid]~> _ := by
  sol_chain

-- Nor a term taclet in the update: it is the box's.
/--
error: ~[findOnSave]~>: findOnSave does not apply to
  dl{ { x := find(save(storage, alice.age, 42), alice.age) } ⟨[ revert(); ]⟩ φ }
while the program is open
-/
#guard_msgs in
example (φ : Post StandardExample [.val .uint]) :
    dl![m]{ { x := find(save(storage, alice.age, 42), alice.age) } ⟨[ revert(); ]⟩ φ }
    ~[findOnSave]~> _ := by
  sol_chain

/-- `simplifyUpdate` under `m` with the revert still to run: the declaration
`x := 250` takes the write that shadows it (`Upd.redecl`, KeY's shadowed
elementary dropped); its right-hand side cannot halt, so under the diamond
too. -/
example (φ : Post StandardExample [.val .uint]) :
    dl![m]{ { x := 250 } { x := x + 10 } ⟨[ revert(); ]⟩ φ }
    ~[sequentialToParallel]~> dl![m]{ { x := 250 ‖ x := 250 + 10 } ⟨[ revert(); ]⟩ φ }
    ~[simplifyUpdate]~> dl![m]{ { x := 250 + 10 } ⟨[ revert(); ]⟩ φ } := by
  sol_chain

/-- The same as one `~~>` (`openRwPath`). -/
example (φ : Post StandardExample [.val .uint]) :
    dl![m]{ { x := 250 } { x := x + 10 } ⟨[ revert(); ]⟩ φ }
    ~~> dl![m]{ { x := 250 + 10 } ⟨[ revert(); ]⟩ φ } := by
  sol_chain

/-- Under the box a shadowed write that may halt goes too: where it halts,
the box line holds. -/
example (φ : Post StandardExample [.val .uint]) :
    dl![.box]{ { x := 1 / 0 ‖ x := 1 } [ revert(); ] φ }
    ~[simplifyUpdate]~> dl![.box]{ { x := 1 } [ revert(); ] φ } := by
  sol_chain

-- Under the diamond it stays: the line after would hold where it halts.
/--
error: ~[simplifyUpdate]~>: simplifyUpdate does not apply to
  dl{ { x := 1 / 0 ‖ x := 1 } ⟨ revert(); ⟩ φ }
while the program is open
-/
#guard_msgs in
example (φ : Post StandardExample [.val .uint]) :
    dl!{ { x := 1 / 0 ‖ x := 1 } ⟨ revert(); ⟩ φ } ~[simplifyUpdate]~> _ := by
  sol_chain

-- `~~>` while the program is open finds the line after up to three rewrites
-- past a line of the derivation, else says so.
/--
error: ~~>: the line after is no line of the derivation of
  dl{ { x := 250 } { x := x + 10 } ⟨[ revert(); ]⟩ φ }
nor reached from one by sequentialToParallel, applyOnRigid, applyOnPV, concrete, simplifyUpdate (at most 3 of them) while the program is open
  (the line after depends on the modality m, through a rule that reads it (`revertBox`, `revertDiamond`, a loop's invariant rule): go on after `cases m`)
-/
#guard_msgs in
example (φ : Post StandardExample [.val .uint]) :
    dl![m]{ { x := 250 } { x := x + 10 } ⟨[ revert(); ]⟩ φ }
    ~~> dl![m]{ { x := 7 } ⟨[ revert(); ]⟩ φ } := by
  sol_chain

/-- `sequentialToParallel` under a branch with the revert still to run
(`FmlRw.mergeIn`): the first merge the line's connectives lead to. -/
example (φ : Post StandardExample [.val .uint, .val .uint]) (ψ : Post StandardExample [.val .uint]) :
    dl![.box]{ (x ≐ 1 → { x := 1 } { y := x } [ revert(); ] φ) ∧ (x ≐ 2 → ψ) }
    ~[sequentialToParallel]~>
      dl![.box]{ (x ≐ 1 → { x := 1 ‖ y := 1 } [ revert(); ] φ) ∧ (x ≐ 2 → ψ) } := by
  sol_chain

/-- `add_literals` in an equation of the line, the revert still to run
(`FmlRw.litEq`): an equivalence, so on the left of the implication too. -/
example (φ : Post StandardExample []) :
    dl![m]{ (250 + 10 ≐ 260 → ⟨[ revert(); ]⟩ φ) }
    ~[add_literals]~> dl![m]{ (260 ≐ 260 → ⟨[ revert(); ]⟩ φ) } := by
  sol_chain

/-- `~=>` with the revert still to run: each line picks its rewrite. -/
example (φ : Post StandardExample []) :
    dl![m]{ { se1 := false } ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ)) }
    ~=> dl![m]{ (false ≐ true → { se1 := false } φ) ∧
          (false ≐ false → { se1 := false } ⟨[ revert(); ]⟩ φ) }
    ~=> dl![m]{ { se1 := false } ⟨[ revert(); ]⟩ φ } := by
  sol_chain

/-- The same as a `calc`, each step's line computed from the line before
(`pendingLines`, the rewrite found by `sol_chain`). -/
example (φ : Post StandardExample []) :
    dl![m]{ { se1 := false } ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ)) }
      ~~> dl![m]{ { se1 := false } ⟨[ revert(); ]⟩ φ } :=
  calc dl![m]{ { se1 := false } ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ)) }
    _ ~[applyOnRigid]~> dl![m]{ (false ≐ true → { se1 := false } φ) ∧
          (false ≐ false → { se1 := false } ⟨[ revert(); ]⟩ φ) } := by sol_chain
    _ ~[concrete]~> dl![m]{ { se1 := false } ⟨[ revert(); ]⟩ φ } := by sol_chain

-- The line prints as it is written, the postcondition under the capture
-- too (a reading of `φ` past `se1`'s scope).
/--
info: fun φ =>
  dl{
    { se1 := false }
      ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ)) } : Post StandardExample [] → Fml StandardExample []
-/
#guard_msgs in
#check fun (φ : Post StandardExample []) =>
  dl![m]{ { se1 := false } ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ)) }

/-- The same line under the diamond, `⟨ revert(); ⟩` (a regression: its
postcondition under the capture once printed ill-typed), a chain's line
like the others. -/
example (φ : Post StandardExample []) :
    dl!{ { se1 := false } ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨ revert(); ⟩ φ)) }
    ~[applyOnRigid]~> dl!{ (false ≐ true → { se1 := false } φ) ∧
      (false ≐ false → { se1 := false } ⟨ revert(); ⟩ φ) }
    ~[concrete]~> dl!{ { se1 := false } ⟨ revert(); ⟩ φ } := by
  sol_chain

/-- `sequentialToParallel` over a storage write with the revert still to
run (`FmlRw.stateMerge`, `Upd.mergeSt?`): the read after the write reads
the written storage. -/
example (φ : Post StandardExample [.val .uint]) :
    dl![.box]{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) }
      [ revert(); ] φ }
    ~[sequentialToParallel]~>
      dl![.box]{ { storage := save(storage, alice.age, 42) ‖
        x := find(save(storage, alice.age, 42), alice.age) } [ revert(); ] φ } := by
  sol_chain

/-- Over locals and a memory write (`Upd.mergeMemL?`, `ChainRewrites`'
locals-then-memory merge): the write after reads the allocation and the
heap it leaves. -/
example (φ : Post StandardExample [.mem (.struct "Person")]) :
    dl![.box]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
      { memory := write(memory, carol.age, 42) } [ revert(); ] φ }
    ~[sequentialToParallel]~>
      dl![.box]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) ‖
        memory := write(addM(memory, Person), freshId(addM(memory, Person)).age, 42) }
        [ revert(); ] φ } := by
  sol_chain

/-- `applyOnPV` with the revert still to run (`FmlRw.applyOnPV`): the update
writes the storage, so it is not applied whole, but the capture it leaves
holding `true` is read as `true` in the branches' conditions, which
`concrete` then folds. -/
example (φ : Post StandardExample []) :
    dl![.box]{ { storage := save(storage, alice.age, 1) ‖ se1 := true }
      ((se1 ≐ true → φ) ∧ (se1 ≐ false → [ revert(); ] φ)) }
    ~[applyOnPV]~> dl![.box]{ { storage := save(storage, alice.age, 1) ‖ se1 := true }
      ((true ≐ true → φ) ∧ (true ≐ false → [ revert(); ] φ)) }
    ~[concrete]~> dl![.box]{ { storage := save(storage, alice.age, 1) ‖ se1 := true } φ } := by
  sol_chain

set_option sol_chain.scopedPast true in
/-- Past the program, under `sol_chain.scopedPast`, `sequentialToParallel`
merges the scoped line too, where that gives the line written (decision 93,
revisited): here over the storage write (`FmlRw.stateMerge`).  The
strategy's own last line declares `x` behind a hidden binder, which no
scoped merge crosses, so `ageWriteReadValue` would go on on the erasure. -/
example : dl![.box]{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) } x ≐ 42 }
    ~[sequentialToParallel]~> dl![.box]{ { storage := save(storage, alice.age, 42) ‖
      x := find(save(storage, alice.age, 42), alice.age) } x ≐ 42 } := by
  sol_chain

end Open

end Solidity.Examples.ChainRewritesOpen
