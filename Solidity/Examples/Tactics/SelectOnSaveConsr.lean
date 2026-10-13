import Solidity.Calculus.RewriteSyntax
import Solidity.Calculus.RewriteChains
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.RewriteSyntax

/-!
# Select on save meets a `consr` path

KeY builds a path by appending on the right: `storageFieldWriteSave` writes
`{storage := save(storage, consr(sp, fld), se)}`, and the interpreter's
`Tm.eval` returns `segs ++ [.field f]` the same way.  Reading a write back
walks the path from the left: `SVal.save` and `SVal.find` unfold only on
`Seg.field name :: rest`, as the theory's `findDefinitionCons` and
`selectOnSaveCons` match `cons(a, flds)`.

`ageWriteRead` reads the leaf on the typed state, where the problem no
longer bites: a typed reference is a root followed by a typed path
(`SRef.append`, built on the right as KeY builds it), and the typed laws
read a write at the reference it wrote, whole (`Storage.findOnSave`), so
no step reassociates a path.  The write is named with what those laws say
(`CloseS.wp_box_write_prim`, `sol_close`'s first pass), and the read after
it is the write's by that fact alone.

`ageWriteReadKeY` proves the same program in solkey's order and never leaves
the sequent: after the calculus steps there is no interpreter reasoning at
all.  The two updates are merged first (`sequentialToParallel`,
`Proves.mergeStorage`): the storage write is substituted into the read, so
the context is one parallel update
`{storage := save(storage, alice.age, 42) ‖ x := find(save(storage, alice.age, 42), alice.age)}`.
The comparison `x = 42` then splits into `defined(x)`, `defined(42)` and the
Theory equation `x ≐ 42` (`Proves.eqDSplit`).  `defined(x)` is proved from
the update that wrote `x` (`Proves.definedWritten`), `defined(42)` from
nothing (`Proves.definedLit`).  The merged update is applied to the
equation and dropped in one step (`Proves.applyOnRigidBox`, through
`sol_apply_upd`); it writes the storage too, which it may because `x ≐ 42`
reads no storage.  The one storage step, the read of the
write, is the term taclet `findOnSave` on scoped terms
(`TermTaclet.findOnSave`, `Calculus/TermLib.lean`), applied by
`Proves.rewrite`; its soundness is the Theory's `Obs.findOnSave`
(`TermTaclet.sound`).  `42 ≐ 42` closes by `Proves.eqRefl`.

The `consr` path has not gone away, it has moved into the Theory.
`alice.age` denotes a typed storage location (`SLoc`, `Tm.denote` of
`.field`), and the Theory's laws are stated once over any location
(`Obs.findOnSave`, `Obs.findOnDelAt`); the bridge to the run
(`SVal.obs_saveM`) walks the path, never a derivation.  What the
derivation still sees of it is the side condition `p.hasSeg`, that a
`consr`-built path is not empty; `sol_rw` closes it by `rfl` once the match
has fixed `p`, so the law is named bare.

The formulas and the sequent are the scoped ones (`open scoped
Solidity.Scoped`): the leaf `ageWriteRead` reads by hand is the scoped
leaf (`sol_leaf`) read on the typed state (`sol_close_unwrap`, `holds`,
its terms a constructor at a time), the interpreter, where
the `consr` path is; the merge, the
split and the rewrite of `ageWriteReadKeY` are the scoped sequent's
(`Calculus/UpdateRules.lean`, read by today's lines in
`Calculus/RewriteSyntax.lean`), and the read `x` is a hidden binder of
its context, which prints as nothing.

The same lines as one chain (`Calculus/Chains.lean`) are
`ChainRewrites.ageWriteReadKeYValue`; `ChainRewrites.ageReadMembers` goes on past
`find(save(storage, alice.age, 42), alice.age)` to solkey's read of the write, a
member at a time.
-/

namespace Solidity.Examples.Tactics.SelectOnSaveConsr

open Semantics SemanticsProperties Close

local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-- `alice.age = 42; uint x = alice.age;` leaves `x == 42`. -/
theorem ageWriteRead : ⊢ dl!{ [ alice.age = 42; uint x = alice.age; ] x == 42 } := by
  apply update .storageFieldWriteSave
  -- dl{ { storage := save(storage, alice.age, 42) } ⟹ [ uint x = alice.age; ] x = 42 }
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  apply empty
  -- dl{ { storage := save(storage, alice.age, 42) }, { x := find(storage, alice.age) } ⟹ x = 42 }
  sol_leaf
  sol_close_unwrap
  intro σ
  -- the leaf read on the typed state (`holds`), a term at a time: the write
  -- named with what the typed laws say of the storage it leaves
  -- (`CloseS.wp_box_write_prim`: solkey's `findOnSave` at `alice.age`, the
  -- frame elsewhere)
  sol_close_eval
  intro st' _ hread _ _ _
  rw [CloseS.landedAll_def]
  intro x n _ _
  -- the read after it is of the write: `42`
  rw [hread]
  exact fun _ => rfl

/-- The same program as solkey takes it: the calculus steps, the updates
merged, the comparison split, the merged update applied, the read of the
write rewritten by the Theory law `findOnSave`, `42 ≐ 42` closed by
reflexivity. -/
theorem ageWriteReadKeY : ⊢ dl!{ [ alice.age = 42; uint x = alice.age; ] x == 42 } := by
  apply update .storageFieldWriteSave
  -- dl{ { storage := save(storage, alice.age, 42) } ⟹ [ uint x = alice.age; ] x = 42 }
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  apply empty
  -- dl{ { storage := save(storage, alice.age, 42) }, { x := find(storage, alice.age) } ⟹ x = 42 }
  refine Proves.mergeStorage ?_
  -- sequentialToParallel:
  -- dl{ { storage := save(storage, alice.age, 42)
  --       ‖ x := find(save(storage, alice.age, 42), alice.age) } ⟹ x = 42 }
  refine Proves.eqDSplit ?_ ?_ ?_
  · -- dl{ { storage := … ‖ x := find(save(storage, alice.age, 42), alice.age) } ⟹ defined(x) }
    exact Proves.definedWritten
  · -- dl{ { storage := … ‖ x := … } ⟹ defined(42) }
    exact Proves.definedLit
  · -- dl{ { storage := … ‖ x := find(save(storage, alice.age, 42), alice.age) } ⟹ x ≐ 42 }
    sol_apply_upd
    -- applyOnRigidBox, the merged update dropped:
    -- dl{ ⟹ find(save(storage, alice.age, 42), alice.age) ≐ 42 }
    rw [findOnSave]
    -- findOnSave: dl{ ⟹ 42 ≐ 42 }
    exact Proves.eqRefl

/-- `findOnSave` while the program is still open: the read of the write in
the postcondition of `[ alice.age = 1; ]` (`Proves.rewrite`, every equation
of the sequent, decision 90), then the strategy. -/
example : ⊢ dl!{ [ alice.age = 1; ] find(save(storage, bob.age, 7), bob.age) ≐ 7 } := by
  rw [findOnSave]
  -- dl{ ⟹ [ alice.age = 1; ] 7 ≐ 7 }
  sol_prove

/-- The same in the context: a precondition rewritten with the program open. -/
example : ⊢ dl!{ find(save(storage, bob.age, 7), bob.age) ≐ 7 → [ alice.age = 1; ] true } := by
  apply impRight
  rw [findOnSave]
  -- dl{ 7 ≐ 7 ⟹ [ alice.age = 1; ] true }
  sol_prove

/-! A precondition rewritten beside an explicit `∀` in the context: the
context keeps its mark (`Walk.rwHyps` rewrites only the preconditions), so
`sol_prove` still counts no parameter (`Seq.paramCount`) and keeps `x`'s
range, which `x + 1` needs (decision 28). -/

/-- info: some (0) -/
#guard_msgs in
example : ⊢ dl!{ ∀ uint x; find(save(storage, bob.age, 7), bob.age) ≐ 7 →
    x <= 100 → ⟨ uint y = x + 1; ⟩ y == x + 1 } := by
  apply allRight
  apply impRight
  rw [findOnSave]
  -- dl{ ∀ uint x, 7 ≐ 7 ⟹ x <= 100 → ⟨ uint y = x + 1; ⟩ y == x + 1 }
  run_tac do
    let ty ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    Lean.logInfo m!"{← Seq.paramCount ty.appFn!.appArg! (← Symex.evaluable ty.appArg!)}"
  sol_prove

end Solidity.Examples.Tactics.SelectOnSaveConsr
