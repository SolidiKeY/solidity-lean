import Solidity.Calculus.Rewrite

/-!
# Select on save meets a `consr` path

KeY builds a path by appending on the right: `storageFieldWriteSave` writes
`{storage := save(storage, consr(sp, fld), se)}`, and the interpreter's
`PTerm.eval` returns `segs ++ [.field f]` the same way.  Reading a write back
walks the path from the left: `SVal.save` and `SVal.find` unfold only on
`Seg.field name :: rest`, as the theory's `findDefinitionCons` and
`selectOnSaveCons` match `cons(a, flds)`.  So once the program is gone, the
path in the goal, `[] ++ [.field "age"]`, blocks every rewrite until it is
reassociated into `cons` form — a step solkey has no taclet for
(`consr(nil, a) ⇝ cons(a, nil)`).  Even the derivation's context comes out
`consr`-shaped: `[] ++ [h₁] ++ [h₂]`.

The proof below is `apply` for every step of the calculus, then `rw` until
the goal is closed, with no `sol_close`.  Each `fail_if_success` marks a
rewrite that the `consr` path blocks.  `Modality.wp_box_saveStorage` would
hand over the read-after-write at any path and hide the problem, so the
write is read back by hand.  `sol_close` does the reassociation silently:
`List.nil_append` and `List.cons_append` are in its `close_rw` set.

`ageWriteReadKeY` proves the same program in solkey's order, without
leaving the sequent (`Calculus/Rewrite.lean`): `sequentialToParallel`
merges the two updates into `{storage := S ‖ x := find(S, alice.age)}`,
`findOnSave` rewrites the read inside it, `applyOnPV` the local in the goal,
`simplifyUpdate` drops the dead element, `eqClose` closes `42 = 42`.  Two
steps differ from KeY's.  `findOnSave` fires *inside* the update, where the
write is known to succeed: `applyOnRigid` would drop the update, and with it
the fact that `alice` exists, leaving `find(S, alice.age) = 42`, false where
the write is stuck — KeY's terms do not halt, these do.  And `findOnSave` is
one rule on the whole path, so the consr problem does not arise: solkey has
no such taclet, and reaches a read of a write through `findDefinitionCons`
and `selectOnSaveCons`, which want the path in `cons` form.
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
        rw [holds_eq, Close.Term.eval_pv, State.getEnv_setEnv_self, Modality.wp_bind,
          Modality.wp_ok, bindingVal_val, Modality.wp_ok, Term.eval_lit, Modality.wp_ok]
    | _ =>
      rw [List.nil_append, SVal.save] at hsave
      cases hsave

/-- The same program step by step as solkey takes it: the updates merged
into one parallel update, the read rewritten inside it, the local applied,
the dead element dropped, `42 = 42` closed. -/
theorem ageWriteReadKeY : ⊢ dl!{ [ alice.age = 42; uint x = alice.age; ] x == 42 } := by
  apply update .storageFieldWriteSave
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  apply empty
  -- dl{ { storage := save(storage, alice.age, 42) }, { x := find(storage, alice.age) } ⟹ x = 42 }
  refine Proves.mergeStorage ?_
  -- sequentialToParallel:
  -- dl{ { storage := save(storage, alice.age, 42) ‖ x := find(save(storage, alice.age, 42), alice.age) }
  --     ⟹ x = 42 }
  refine Proves.rewriteUpd 0 Hyp.EqRun.findOnSave ?_
  -- findOnSave: dl{ { storage := save(storage, alice.age, 42) ‖ x := 42 } ⟹ x = 42 }
  refine Proves.rewrite 1 Hyp.EqUnder.applyOnPV ?_
  -- applyOnPV: dl{ { storage := save(storage, alice.age, 42) ‖ x := 42 } ⟹ 42 = 42 }
  refine Proves.simplify (Γ := []) ?_
  -- simplifyUpdate: dl{ { storage := save(storage, alice.age, 42) } ⟹ 42 = 42 }
  exact Proves.eqClose

end Solidity.Examples.SelectOnSaveConsr
