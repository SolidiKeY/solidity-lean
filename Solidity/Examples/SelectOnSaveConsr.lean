import Solidity.Calculus.Rewrite
import Solidity.Calculus.Chains

/-!
# Select on save meets a `consr` path

KeY builds a path by appending on the right: `storageFieldWriteSave` writes
`{storage := save(storage, consr(sp, fld), se)}`, and the interpreter's
`PTerm.eval` returns `segs ++ [.field f]` the same way.  Reading a write back
walks the path from the left: `SVal.save` and `SVal.find` unfold only on
`Seg.field name :: rest`, as the theory's `findDefinitionCons` and
`selectOnSaveCons` match `cons(a, flds)`.

`ageWriteRead` shows the problem where it bites, at the interpreter: `apply`
for every step of the calculus, then `rw` on the semantics until the goal is
closed, with no `sol_close`.  Once the program is gone the path in the goal,
`[] ++ [.field "age"]`, blocks every rewrite until it is reassociated into
`cons` form — a step solkey has no taclet for (`consr(nil, a) ⇝ cons(a, nil)`).
Each `fail_if_success` marks a rewrite that the `consr` path blocks.
`Modality.wp_box_saveStorage` would hand over the read-after-write at any path
and hide the problem, so the write is read back by hand.  (`sol_close` does
the reassociation silently: `List.nil_append` and `List.cons_append` are in
its `close_rw` set.)

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
reads no storage (`Fml.stFree`).  The one storage step, the read of the
write, is the term taclet `findOnSave` (`Calculus/TermTaclets.lean`),
applied by `Proves.rewrite`; its soundness is the Theory's
`find_copyTo_same` (`TermTaclet.sound`).  `42 ≐ 42` closes by `Proves.eqRefl`.

The `consr` path has not gone away, it has moved into the Theory.
`alice.age` still denotes `[.field "alice"] ++ [.field "age"]`
(`PTerm.denote` of `.field`), and the Theory's laws are stated at a list path:
`find_copyTo_same` at any `p ≠ []`, and the rule-shaped `findDelAt` at
`p ++ [a]` (`find_delAt_field`, which splits the read with `find_append`).
The reassociation happens once, inside the proof of the law
(`find_save_same` walks `p` from the left), never in a derivation.  What the
derivation still sees of it is the side condition `p.hasSeg`, that a
`consr`-built path is not empty; `sol_rw` closes it by `rfl` once the match
has fixed `p`, so the law is named bare.  The context too is
`consr`-shaped, `[] ++ [h₁] ++ [h₂]`; the rules take it as
`Γ ++ [.upd .box U]`.

`ageWriteReadKeYChain` is `ageWriteReadKeY`'s lines as one chain
(`Calculus/Chains.lean`), proved by one `sol_chain`: the program in one
`~*>` link, then `~=>` links, each line picking the rewrite that reaches it.
It is at `x ≐ 42`, since a chain has no link that splits `==`
(`Proves.eqDSplit`).  Past `find(save(storage, alice.age, 42), alice.age)`
it opens `findOnSave` into solkey's read of the write, a member at a time
(`Calculus/TermTaclets.lean`): `findMemberCons` reads `alice.age` from its
head, `select(select(…, alice), age)` — the `consr` path turned into `cons`
form inside its proof, solkey's `consRcons` and `consRnil`, then
`findDefinitionMemberCons` — and `selectOnSaveMember`, solkey's
`selectOnSaveCons`, pushes the write into `alice`; the read of the write at
the last member is `findOnSave` again.
-/

namespace Solidity.Examples.SelectOnSaveConsr

open Proves Semantics SemanticsProperties Close

local instance : InContract := ⟨StandardExample⟩

/-- `alice.age = 42; uint x = alice.age;` leaves `x == 42`. -/
theorem ageWriteRead : ⊢ dl!{ [ alice.age = 42; uint x = alice.age; ] x == 42 } := by
  apply update .storageFieldWriteSave
  -- dl{ { storage := save(storage, alice.age, 42) } ⟹ [ uint x = alice.age; ] x = 42 }
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  apply empty
  -- dl{ { storage := save(storage, alice.age, 42) }, { x := find(storage, alice.age) } ⟹ x = 42 }
  refine close ?_
  unfold Valid
  intro σ
  -- the context is `consr`-built too
  rw [List.nil_append, List.singleton_append, Hyp.wrap, Hyp.wrap, Hyp.wrap]
  rw [holds_upd, Upd.apply, List.foldlM_cons, Modality.wp_bind, UpdElem.write_storage,
    Modality.wp_bind, STerm.eval_save, Simple.lower, SPath.lower, Loc.lower, Term.eval_lit,
    Modality.wp_bind, Modality.wp_ok, STerm.eval_storage, Modality.wp_bind, Modality.wp_ok,
    PTerm.eval_field, PTerm.eval_root, Modality.wp_bind, Modality.wp_bind, Modality.wp_ok,
    Modality.wp_ok]
  dsimp only
  rw [Modality.wp_box]
  intro τ hsave
  rw [Modality.wp_ok, List.foldlM_nil, Modality.wp_pure, holds_upd, Upd.apply, List.foldlM_cons,
    Modality.wp_bind, UpdElem.write_val, Modality.wp_bind, Term.eval_find, STerm.eval_storage,
    Modality.wp_bind, Modality.wp_ok]
  rw [PTerm.eval_field, PTerm.eval_root, Modality.wp_bind, Modality.wp_bind, Modality.wp_ok,
    Modality.wp_ok, Modality.wp_bind]
  dsimp only
  -- select on save, by hand: what did the write leave at `alice`?
  unfold State.saveStorage at hsave
  unfold State.findStorage
  cases hv : lookupBy "alice" σ.storage with
  | none =>
    rw [hv] at hsave
    cases hsave
  | some v =>
    rw [hv] at hsave
    dsimp only at hsave
    cases v with
    | struct fields =>
      -- the path is `[] ++ [age]`, the equation wants `age :: rest`
      fail_if_success rw [SVal.save] at hsave
      rw [List.nil_append, SVal.save] at hsave
      cases ha : lookupBy "age" fields with
      | none =>
        rw [ha] at hsave
        cases hsave
      | some old =>
        rw [ha] at hsave
        dsimp only at hsave
        rw [SVal.save] at hsave
        cases hsave
        dsimp only
        rw [lookupBy_setBy_self]
        dsimp only
        -- the same block on the read
        fail_if_success rw [SVal.find]
        rw [List.nil_append, SVal.find, lookupBy_setBy_self]
        dsimp only
        rw [SVal.find, Modality.wp_ok, asValue_toSVal, Modality.wp_ok, Modality.wp_ok,
          List.foldlM_nil, Modality.wp_pure]
        -- `x = 42`
        rw [holds_eqD, Close.Term.eval_pv, State.getEnv_setEnv_self, Modality.wp_bind,
          Modality.wp_ok, bindingVal_val, Modality.wp_ok, Term.eval_lit, Modality.wp_ok]
    | _ =>
      rw [List.nil_append, SVal.save] at hsave
      cases hsave

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

/-- `ageWriteReadKeY`'s lines as one chain: the program in one link, then
the read-back, each line picking its rewrite, down to solkey's read of the
write one member at a time. -/
def ageWriteReadKeYChain :
    dl!{ [ alice.age = 42; uint x = alice.age; ] x ≐ 42 }
    ~*> dl![.box]{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) } x ≐ 42 }
    ~=> dl![.box]{ { storage := save(storage, alice.age, 42)
          ‖ x := find(save(storage, alice.age, 42), alice.age) } x ≐ 42 }   -- sequentialToParallel
    ~=> dl!{ find(save(storage, alice.age, 42), alice.age) ≐ 42 }           -- applyOnRigidBox
    ~=> dl!{ select(select(save(storage, alice.age, 42), alice), age) ≐ 42 }
                                  -- consRcons, consRnil, findDefinitionMemberCons/Prim
    ~=> dl!{ select(store(select(storage, alice), age, 42), age) ≐ 42 }
                                  -- selectOnSaveCons, alice = alice
    ~=> dl!{ 42 ≐ 42 } := by      -- selectOnSaveCons, age = age, at the end of the path
  sol_chain

end Solidity.Examples.SelectOnSaveConsr
