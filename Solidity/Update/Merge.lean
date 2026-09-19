import Solidity.Update.Step
import Solidity.Update.SimpAttr
import Solidity.RuleSoundness
import Solidity.SemanticsProperties

/-!
# The merge kit: reading through a binding

The last line of almost every derivation upstream collapses the accumulated
stack into one parallel update:

```
{sp := alice·account} {storage := save(storage, sp·balance, rv)}
= {sp := alice·account ‖ storage := save(storage, alice·account·balance, rv)}
```

`Upd.Par.seq_single` (`Update.lean`) is the *law* behind that line, but it
leaves the right-hand side as `{u}t` — the second update's reader composed
with the first update.  Turning `{u}(sp·balance)` into `alice·account·balance`
is not the law: it is the fact that a reader which went through the alias `sp`
in the updated state reads the aliased path in the original one, and that a
reader which mentions none of the updated names reads the same thing either
way.

This module is those two facts, one lemma per interpreter reader, and nothing
else.  Every lemma is tagged `@[upd_merge_set]`, which is the simp set the
`upd_merge` tactic runs (`Examples/Common.lean`).

The freshness side is stated with `RuleSoundness.usesVar`, the same *syntactic*
notion the rewrite-soundness theorems use: on a concrete derivation line it is
`decide`-able, so the tactic discharges it rather than asking for it.

Kept apart from `Update/Step.lean` so that the sequent layer — which the
notation and the step tactics need — does not drag in `RuleSoundness`.
-/

namespace Solidity
namespace Wp

open Semantics RuleSoundness

/-! ## The components a binding does not touch

`setEnv` writes the environment and nothing else, so every storage and heap
reader sees through it.  These are `rfl`, and they are in the set because the
merged spelling reaches them under a binding the unmerged one does not have. -/

@[upd_merge_set] theorem storage_setEnv (s : State) (n : Name) (b : Binding) :
    (s.setEnv n b).storage = s.storage := rfl

@[upd_merge_set] theorem heap_setEnv (s : State) (n : Name) (b : Binding) :
    (s.setEnv n b).heap = s.heap := rfl

@[upd_merge_set] theorem nextId_setEnv (s : State) (n : Name) (b : Binding) :
    (s.setEnv n b).nextId = s.nextId := rfl

@[upd_merge_set] theorem net_setEnv (s : State) (n : Name) (b : Binding) :
    (s.setEnv n b).net = s.net := rfl

@[upd_merge_set] theorem selfBalance_setEnv (s : State) (n : Name) (b : Binding) :
    (s.setEnv n b).selfBalance = s.selfBalance := rfl

@[upd_merge_set] theorem findStorage_setEnv (s : State) (n : Name) (b : Binding)
    (r : Name) (sg : List Seg) :
    (s.setEnv n b).findStorage r sg = s.findStorage r sg := rfl

@[upd_merge_set] theorem getObj_setEnv (s : State) (n : Name) (b : Binding)
    (id : Nat) : (s.setEnv n b).getObj id = s.getObj id := rfl

/-- A storage write does not read the environment, so a binding in front of it
comes back out -- which is how the merged spelling, whose write is stated
against the *original* state, reaches the same tree. -/
@[upd_merge_set] theorem saveStorage_setEnv (s : State) (n : Name) (b : Binding)
    (r : Name) (sg : List Seg) (v : SVal) :
    (s.setEnv n b).saveStorage r sg v =
      (s.saveStorage r sg v).map (fun t => t.setEnv n b) := by
  simp only [State.saveStorage, State.setEnv, Except.map, bind, Except.bind]
  cases lookupBy r s.storage with
  | none => simp
  | some v' => cases hv : v'.save sg v <;> simp [hv]

/-- KeY `simplifyUpdate1-3`: the later binding of a name absorbs the earlier,
which is what collapses the declaration-then-assignment pair a value capture
leaves behind (`{rv := default(T)}{rv := e}`). -/
@[upd_merge_set] theorem setEnv_setEnv_absorb' (s : State) (n : Name)
    (b b' : Binding) : (s.setEnv n b).setEnv n b' = s.setEnv n b' :=
  SemanticsProperties.State.setEnv_setEnv_absorb s n b b'

/-! ## Reading the name that was just bound -/

@[upd_merge_set] theorem stackVal_setEnv_self (s : State) (n : Name) (v : Value) :
    stackVal (s.setEnv n (Binding.val v)) n = .ok v := by
  simp [stackVal, State.setEnv]

@[upd_merge_set] theorem memRef_setEnv_self (s : State) (n : Name) (id : Nat) :
    memRef (s.setEnv n (Binding.mref id)) n = .ok id := by
  simp [memRef, State.setEnv]

/-- `read(m)` on the memory identity just bound -- `memRef_setEnv_self` through
the place reader. -/
@[upd_merge_set] theorem memBase_setEnv_alias {n : Name} {k : Kind} {t : Ty}
    {fld : Field} (h : fld.name = n) (s : State) (id : Nat) :
    memBase (s.setEnv n (Binding.mref id)) (WrappedExpr.var k t fld) = .ok id := by
  subst h; simp [memBase, memRef_setEnv_self]

/-- A storage alias: the calculus's `sp := alice·account`, read back.

The name is a *hypothesis* rather than the projection `fld.name`, because that
is what lets this fire as a rewrite: the update carries the literal name and
the place carries the whole field, and simp will not match a literal against a
projection of a metavariable. -/
@[upd_merge_set] theorem varPath_setEnv_alias {n : Name} {fld : Field}
    (h : fld.name = n) (s : State) (r : Name) (sg : List Seg) :
    varPath (s.setEnv n (Binding.spath r sg)) fld = .ok (r, sg) := by
  subst h; simp [varPath, State.setEnv]

/-! ## Reading past a binding of another name -/

@[upd_merge_set] theorem stackVal_setEnv_ne {m n : Name} (h : m ≠ n)
    (s : State) (b : Binding) :
    stackVal (s.setEnv n b) m = stackVal s m := by
  simp [stackVal, State.setEnv, lookupBy_setBy_ne h]

/-- A memory write does not read the environment either, so a binding in front
of it comes back out -- the heap twin of `saveStorage_setEnv`, and what a
memory merge line reaches once `mv := ref(…)` has been opened. -/
@[upd_merge_set] theorem writeMemField_setEnv (s : State) (n : Name) (b : Binding)
    (id : Nat) (f : Name) (mv : MVal) :
    writeMemField (s.setEnv n b) id f mv =
      (writeMemField s id f mv).map (fun t => t.setEnv n b) := by
  simp only [writeMemField, getObj_setEnv, Except.map, bind, Except.bind]
  cases s.getObj id with
  | error _ => rfl
  | ok obj => cases obj <;> rfl

@[upd_merge_set] theorem writeMemIndex_setEnv (s : State) (n : Name) (b : Binding)
    (id : Nat) (i : Int) (mv : MVal) :
    writeMemIndex (s.setEnv n b) id i mv =
      (writeMemIndex s id i mv).map (fun t => t.setEnv n b) := by
  simp only [writeMemIndex, getObj_setEnv, Except.map, bind, Except.bind]
  cases s.getObj id with
  | error _ => rfl
  | ok obj =>
      cases obj with
      | struct _ => rfl
      | array elems =>
          by_cases hb : 0 ≤ i ∧ i.toNat < elems.length <;>
            simp [hb, State.setObj, State.setEnv]

@[upd_merge_set] theorem memRef_setEnv_ne {m n : Name} (h : m ≠ n)
    (s : State) (b : Binding) :
    memRef (s.setEnv n b) m = memRef s m := by
  simp [memRef, State.setEnv, lookupBy_setBy_ne h]

@[upd_merge_set] theorem varPath_setEnv_ne {n : Name} {fld : Field}
    (h : fld.name ≠ n) (s : State) (b : Binding) :
    varPath (s.setEnv n b) fld = varPath s fld := by
  simp [varPath, State.setEnv, lookupBy_setBy_ne h]

theorem name_ne_of_usesVar {k : Kind} {t : Ty} {fld : Field} {n : Name}
    (h : usesVar (WrappedExpr.var k t fld) n = false) : fld.name ≠ n := by
  simp only [usesVar, decide_eq_false_iff_not] at h; exact h

@[upd_merge_set] theorem simpleVal_setEnv_fresh {n : Name} (s : State)
    (b : Binding) {e : WrappedExpr} (h : usesVar e n = false) :
    simpleVal (s.setEnv n b) e = simpleVal s e := by
  cases e with
  | var k t fld =>
      have hne := name_ne_of_usesVar h
      cases k <;>
        simp [simpleVal, stackVal_setEnv_ne hne, varPath_setEnv_ne hne,
          findStorage_setEnv]
  | _ => rfl

@[upd_merge_set] theorem simpleInt_setEnv_fresh {n : Name} (s : State)
    (b : Binding) {e : WrappedExpr} (h : usesVar e n = false) :
    simpleInt (s.setEnv n b) e = simpleInt s e := by
  simp [simpleInt, simpleVal_setEnv_fresh s b h]

/-- A path whose root -- and whose indices -- do not mention `n` addresses the
same storage cell after `n` is bound.  The induction is `placePath`'s own,
which is why the merged line needs that reader to recurse into its base. -/
@[upd_merge_set] theorem placePath_setEnv_fresh {n : Name} (s : State)
    (b : Binding) : ∀ {e : WrappedExpr}, usesVar e n = false ->
      placePath (s.setEnv n b) e = placePath s e
  | .var _ _ _, h => by simp [placePath, varPath_setEnv_ne (name_ne_of_usesVar h)]
  | .field _ _ base _, h => by
      simp [placePath, placePath_setEnv_fresh s b (e := base) h]
  | .index _ _ base ix, h => by
      simp only [usesVar, Bool.or_eq_false_iff] at h
      simp [placePath, placePath_setEnv_fresh s b (e := base) h.1,
        simpleInt_setEnv_fresh s b h.2]
  | .pushPlace _, _ => rfl
  | .bool _, _ => rfl
  | .intLit _ _, _ => rfl
  | .mkCall .., _ => rfl
  | .mkBinop .., _ => rfl
  | .mkUnop .., _ => rfl
  | .mkIncDec .., _ => rfl
  | .mkTernary .., _ => rfl

@[upd_merge_set] theorem memBase_setEnv_fresh {n : Name} (s : State)
    (b : Binding) {e : WrappedExpr} (h : usesVar e n = false) :
    memBase (s.setEnv n b) e = memBase s e := by
  cases e with
  | var k t fld => simp [memBase, memRef_setEnv_ne (name_ne_of_usesVar h)]
  | _ => rfl

@[upd_merge_set] theorem readMem_setEnv_fresh {n : Name} (s : State)
    (b : Binding) {e : WrappedExpr} (h : usesVar e n = false) :
    readMem (s.setEnv n b) e = readMem s e := by
  cases e with
  | var k t fld => simp [readMem, memRef_setEnv_ne (name_ne_of_usesVar h)]
  | field k t base f =>
      have hb := memBase_setEnv_fresh (n := n) s b (e := base) h
      simp [readMem, hb, getObj_setEnv]
  | index k t base ix =>
      simp only [usesVar, Bool.or_eq_false_iff] at h
      have hb := memBase_setEnv_fresh (n := n) s b (e := base) h.1
      have hi := simpleInt_setEnv_fresh (n := n) s b (e := ix) h.2
      simp [readMem, hb, hi, getObj_setEnv]
  | _ => rfl

@[upd_merge_set] theorem readVal_setEnv_fresh {n : Name} (s : State)
    (b : Binding) {e : WrappedExpr} (h : usesVar e n = false) :
    readVal (s.setEnv n b) e = readVal s e := by
  cases e with
  | var k t fld =>
      have hne := name_ne_of_usesVar h
      have hp := placePath_setEnv_fresh (n := n) s b
        (e := WrappedExpr.var k t fld) h
      cases k <;> simp [readVal, hp, stackVal_setEnv_ne hne, findStorage_setEnv]
  | field k t base f =>
      have hp := placePath_setEnv_fresh (n := n) s b
        (e := WrappedExpr.field k t base f) h
      have hm := readMem_setEnv_fresh (n := n) s b
        (e := WrappedExpr.field k t base f) h
      cases k <;> simp [readVal, hp, hm, findStorage_setEnv]
  | index k t base ix =>
      have hp := placePath_setEnv_fresh (n := n) s b
        (e := WrappedExpr.index k t base ix) h
      have hm := readMem_setEnv_fresh (n := n) s b
        (e := WrappedExpr.index k t base ix) h
      cases k <;> simp [readVal, hp, hm, findStorage_setEnv]
  | _ => rfl

end Wp
end Solidity
