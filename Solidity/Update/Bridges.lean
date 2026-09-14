import Solidity.Update
import Solidity.Wp.Terminal.UpdateDecl

/-!
# From the terminal table to the update algebra

`Wp/TerminalUpdate.lean` gives every terminal rule a
`State -> Res State`.  `Update.lean` gives updates a first-order spelling.
This module connects them: for each family of the terminal table, and each
target shape its guard admits, a theorem

    Par.toUpd [ …elementary updates… ] = <family> args

so a derivation can write the calculus's `{storage := save(sp·balance, rv)}`
and have Lean check that it *is* the rule's update.

## The kit

`toUpd_env`, `toUpd_storage`, `toUpd_heap`, `toUpd_net` compute a
one-element parallel update; `toUpd_pair` a two-element one (needed
whenever a rule allocates *and* rebinds, which writes two components).
`saveSt` / `heapOf` / `netOf` are the component readers: `save(storage,p,v)`
as the calculus writes it is the *storage component* of `State.saveStorage`,
and the three `*_component` lemmas say the corresponding `State` writer
changes nothing else.

## Coverage

Proved here, as `Par.toUpd [...] = <family>`:

* `assignStackRead` (`x := read/selectSt(…)`);
* `storageAssignUpd` — global root, storage field, storage index
  (`{storage := save(…)}`) and storage-*local* root (`{p := q}`, a rebinding
  and not a storage write at all);
* `storagePlaceAliasUpd` on a **pure** path (`{sp := path}`);
* `stackDeclSkipUpd` (`{x := default(T)}`), `storageDeclSkipUpd` (the empty
  update);
* `compoundAssignUpd` — stack variable (`{x := x ⊕ se}`), storage field
  (`{storage := save(…)}`), memory field and memory index
  (`{memory := write(…)}`);
* `pushUpd`, `popUpd` (`{storage := …}`), `transferUpd` (`{net := …}`).

**Not covered, and why.**

* `assertUpd`, `revertUpd` are not updates — they fault.  KeY does not write
  them as updates either: `assertSimple`/`requireSimple` split the sequent
  and `revert` closes the branch, which is `SolidityJudgment.check`'s
  `.revert` arm.  A `Par` can only *write components*.
* `storageDeleteUpd`: `deletePath` is itself state-changing on a push-place
  target, so its frame is relative to an intermediate state; see the note at
  `transferUpd_frame`.
* `memoryAssignUpd`, `memoryDeclUpd`, `incDecStmtUpd`, `incDecAssignUpd`,
  `pushBindUpd`, `binopAssignUpd`, `unopAssignUpd`: allocation and the
  two-component rules (a fresh object writes `heap` *and* rebinds a name)
  need a two-element `Par`, for which `toUpd_pair` is the kit lemma but no
  family is worked through yet.

Each missing family still has its `<rule>_update` theorem in
`Wp/Terminal/`; what is missing is only the first-order `{…}` spelling.-/

namespace Solidity
namespace Upd

open Semantics Wp

/-! ## The kit -/

theorem toUpd_env (n : Name) (rhs : State -> Res Binding) (s : State) :
    Par.toUpd [Elem.env n rhs] s = (rhs s).map fun b => s.setEnv n b := by
  simp only [Par.toUpd, Par.apply, Par.writers, Elem.eval, bind, Except.bind,
    Except.map, pure, Except.pure]
  cases rhs s <;> rfl

theorem toUpd_storage (rhs : State -> Res (List (Name × SVal))) (s : State) :
    Par.toUpd [Elem.storage rhs] s =
      (rhs s).map fun g => { s with storage := g } := by
  simp only [Par.toUpd, Par.apply, Par.writers, Elem.eval, bind, Except.bind,
    Except.map, pure, Except.pure]
  cases rhs s <;> rfl

theorem toUpd_heap (rhs : State -> Res (List (Nat × MObj) × Nat)) (s : State) :
    Par.toUpd [Elem.heap rhs] s =
      (rhs s).map fun x => { s with heap := x.1, nextId := x.2 } := by
  simp only [Par.toUpd, Par.apply, Par.writers, Elem.eval, bind, Except.bind,
    Except.map, pure, Except.pure]
  cases rhs s <;> rfl

theorem toUpd_net (rhs : State -> Res (List (Int × Int) × Int)) (s : State) :
    Par.toUpd [Elem.net rhs] s =
      (rhs s).map fun x => { s with net := x.1, selfBalance := x.2 } := by
  simp only [Par.toUpd, Par.apply, Par.writers, Elem.eval, bind, Except.bind,
    Except.map, pure, Except.pure]
  cases rhs s <;> rfl

theorem toUpd_pair (a b : Elem) (s : State) :
    Par.toUpd [a, b] s =
      (a.eval s) >>= fun wa => (b.eval s).map fun wb => wb (wa s) := by
  simp only [Par.toUpd, Par.apply, Par.writers, bind, Except.bind, Except.map,
    pure, Except.pure]
  cases a.eval s with
  | error h => rfl
  | ok wa => cases b.eval s <;> rfl

/-! ## Component readers

The calculus writes `storage := save(storage, p, v)`: the right-hand side is a
*storage tree*, not a state.  These are the same functions as the `State`
writers, read off one component. -/

/-- `save(storage, p, v)`: the storage tree `State.saveStorage` installs. -/
def saveSt (s : State) (root : Name) (segs : List Seg) (v : SVal) :
    Res (List (Name × SVal)) :=
  (s.saveStorage root segs v).map State.storage

/-- The heap-and-counter pair a memory write installs. -/
def heapOf (r : Res State) : Res (List (Nat × MObj) × Nat) :=
  r.map fun t => (t.heap, t.nextId)

/-- The ledger-and-balance pair a `transfer` installs. -/
def netOf (r : Res State) : Res (List (Int × Int) × Int) :=
  r.map fun t => (t.net, t.selfBalance)

/-- `State.saveStorage` writes the storage component and nothing else, so
the calculus's `{storage := save(…)}` really is the whole of it. -/
theorem saveStorage_frame {s t : State} {root : Name} {segs : List Seg}
    {v : SVal} (h : s.saveStorage root segs v = .ok t) :
    t = { s with storage := t.storage } := by
  simp only [State.saveStorage, bind, Except.bind] at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · cases h; rfl
  · exact absurd h (by simp)

/-- `writeMemField` / `writeMemIndex` write the heap and nothing else
(`State.setObj` keeps `nextId`). -/
theorem writeMemField_frame {s t : State} {id : Nat} {f : Name} {mv : MVal}
    (h : writeMemField s id f mv = .ok t) :
    t = { s with heap := t.heap, nextId := t.nextId } := by
  simp only [writeMemField, bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · cases h; rfl
    · exact absurd h (by simp)

theorem writeMemIndex_frame {s t : State} {id : Nat} {i : Int} {mv : MVal}
    (h : writeMemIndex s id i mv = .ok t) :
    t = { s with heap := t.heap, nextId := t.nextId } := by
  simp only [writeMemIndex, bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · split at h
      · cases h; rfl
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-! ## The generic bridges

The calculus writes an update as `{component := reader}`.  A rule's update is
that update exactly when it *writes only that component* — which is a frame
statement about the rule, and the honest thing to prove.  Each of the four
lemmas below turns such a frame fact into the corresponding one-element
parallel update, with the reader read off the update's own result. -/

theorem toUpd_storage_of_frame (F : State -> Res State)
    (hframe : ∀ s t, F s = .ok t -> t = { s with storage := t.storage }) :
    Par.toUpd [Elem.storage (fun s => (F s).map State.storage)] = F := by
  funext s
  rw [toUpd_storage]
  cases h : F s with
  | error e => rfl
  | ok t => simpa [Except.map] using (hframe s t h).symm

theorem toUpd_heap_of_frame (F : State -> Res State)
    (hframe : ∀ s t, F s = .ok t ->
      t = { s with heap := t.heap, nextId := t.nextId }) :
    Par.toUpd [Elem.heap (fun s => (F s).map fun t => (t.heap, t.nextId))] = F := by
  funext s
  rw [toUpd_heap]
  cases h : F s with
  | error e => rfl
  | ok t => simpa [Except.map] using (hframe s t h).symm

theorem toUpd_net_of_frame (F : State -> Res State)
    (hframe : ∀ s t, F s = .ok t ->
      t = { s with net := t.net, selfBalance := t.selfBalance }) :
    Par.toUpd [Elem.net (fun s => (F s).map fun t => (t.net, t.selfBalance))] = F := by
  funext s
  rw [toUpd_net]
  cases h : F s with
  | error e => rfl
  | ok t => simpa [Except.map] using (hframe s t h).symm

/-- The `env` twin needs the *name* as well: a rule that rebinds one name
is `{n := …}`, and the reader is the binding it installs. -/
theorem toUpd_env_of (n : Name) (F : State -> Res State)
    (rd : State -> Res Binding)
    (h : ∀ s, F s = (rd s).map fun b => s.setEnv n b) :
    Par.toUpd [Elem.env n rd] = F := by
  funext s; rw [toUpd_env, h]

/-! ## Bridges, family by family -/

/-- `x = se` / `x = p.f` / `x = p[se]` / `x = m.f`: one elementary update
on the stack variable, the calculus's `x := selectSt(…)` / `x := read(…)`. -/
theorem assignStackRead_bridge (ty : Ty) (fld : Field) (hass : _)
    (rhs : WrappedExpr) :
    Par.toUpd [Elem.env fld.name
        (fun s => (readVal s rhs).map Binding.val)] =
      assignStackRead ⟨WrappedExpr.var Kind.stack ty fld, hass⟩ rhs := by
  funext s
  rw [toUpd_env]
  simp only [assignStackRead, assignStack, bind, Except.bind, Except.map]
  cases readVal s rhs <;> rfl

/-! ### Storage targets

`storageAssignUpd` writes the storage tree on a global root and on a nested
place, and *rebinds a name* on a storage-local root — which is why the calculus
writes the first three as `{storage := save(…)}` and the last as `{p := q}`.
The frame facts are what say so. -/

theorem storageAssignUpd_globalRoot_frame (ty : Ty) (fld : Field) (hass : _)
    (rhs : WrappedExpr) (hg : fld.origin = some StorageOrigin.global)
    (s t : State)
    (h : storageAssignUpd ⟨WrappedExpr.var Kind.storage ty fld, hass⟩ rhs s
      = .ok t) : t = { s with storage := t.storage } := by
  simp only [storageAssignUpd, hg, if_pos, bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · exact saveStorage_frame h

theorem storageAssignUpd_field_frame (ty : Ty) (base : WrappedExpr) (f : Field)
    (hass : _) (rhs : WrappedExpr) (s t : State)
    (h : storageAssignUpd ⟨WrappedExpr.field Kind.storage ty base f, hass⟩ rhs s
      = .ok t) : t = { s with storage := t.storage } := by
  simp only [storageAssignUpd, bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · exact saveStorage_frame h

theorem storageAssignUpd_index_frame (ty : Ty) (base ix : WrappedExpr)
    (hass : _) (rhs : WrappedExpr) (s t : State)
    (h : storageAssignUpd ⟨WrappedExpr.index Kind.storage ty base ix, hass⟩ rhs s
      = .ok t) : t = { s with storage := t.storage } := by
  simp only [storageAssignUpd, bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · exact saveStorage_frame h

/-- `gsp = se` on a *global* storage root: `storage := save(storage, gsp, v)`. -/
theorem storageAssignUpd_globalRoot (ty : Ty) (fld : Field) (hass : _)
    (rhs : WrappedExpr) (hg : fld.origin = some StorageOrigin.global) :
    Par.toUpd [Elem.storage (fun s =>
        (storageAssignUpd ⟨WrappedExpr.var Kind.storage ty fld, hass⟩ rhs s).map
          State.storage)] =
      storageAssignUpd ⟨WrappedExpr.var Kind.storage ty fld, hass⟩ rhs :=
  toUpd_storage_of_frame _ (storageAssignUpd_globalRoot_frame ty fld hass rhs hg)

/-- `sp.f = se`: `storage := save(storage, sp·f, v)` — the calculus's headline
update. -/
theorem storageAssignUpd_field (ty : Ty) (base : WrappedExpr) (f : Field)
    (hass : _) (rhs : WrappedExpr) :
    Par.toUpd [Elem.storage (fun s =>
        (storageAssignUpd ⟨WrappedExpr.field Kind.storage ty base f, hass⟩ rhs s).map
          State.storage)] =
      storageAssignUpd ⟨WrappedExpr.field Kind.storage ty base f, hass⟩ rhs :=
  toUpd_storage_of_frame _ (storageAssignUpd_field_frame ty base f hass rhs)

/-- `sp[i] = se`: the index twin. -/
theorem storageAssignUpd_index (ty : Ty) (base ix : WrappedExpr) (hass : _)
    (rhs : WrappedExpr) :
    Par.toUpd [Elem.storage (fun s =>
        (storageAssignUpd ⟨WrappedExpr.index Kind.storage ty base ix, hass⟩ rhs s).map
          State.storage)] =
      storageAssignUpd ⟨WrappedExpr.index Kind.storage ty base ix, hass⟩ rhs :=
  toUpd_storage_of_frame _ (storageAssignUpd_index_frame ty base ix hass rhs)

/-- `p = q` on a storage *local* root: not a storage write at all — the
alias is re-bound, the calculus's `p := q`. -/
theorem storageAssignUpd_localRoot (ty : Ty) (fld : Field) (hass : _)
    (rhs : WrappedExpr) (hg : ¬ fld.origin = some StorageOrigin.global) :
    Par.toUpd [Elem.env fld.name
        (fun s => (placePath s rhs).map fun p => Binding.spath p.1 p.2)] =
      storageAssignUpd ⟨WrappedExpr.var Kind.storage ty fld, hass⟩ rhs := by
  refine toUpd_env_of _ _ _ (fun s => ?_)
  simp only [storageAssignUpd, hg, if_neg, bind, Except.bind, Except.map]
  cases placePath s rhs with
  | error h => rfl
  | ok p => obtain ⟨r, sg⟩ := p; rfl

/-! ### Chasing a frame fact through a bind

Every remaining update is a chain of `>>=` bottoming out in a `State` writer
whose frame is already known.  `bind_frame` is the one step of that chain,
so each frame fact below is a chain of `bind_frame`s and one base case. -/

/-- If everything the continuation can produce has the frame, so does the
bind: a halt in the first component produces nothing at all.  Stated three
times, once per component, because a single `P`-polymorphic version leaves
the frame predicate to higher-order unification, which guesses wrong. -/
theorem bind_frameSt {α : Type} {r : Res α} {f : α -> Res State}
    {s t : State}
    (hf : ∀ a u, f a = .ok u -> u = { s with storage := u.storage })
    (h : (r >>= f) = .ok t) : t = { s with storage := t.storage } := by
  cases hr : r with
  | error e => rw [hr] at h; exact absurd h (by simp [bind, Except.bind])
  | ok a => rw [hr] at h; exact hf a t h

theorem bind_frameHeap {α : Type} {r : Res α} {f : α -> Res State}
    {s t : State}
    (hf : ∀ a u, f a = .ok u -> u = { s with heap := u.heap, nextId := u.nextId })
    (h : (r >>= f) = .ok t) :
    t = { s with heap := t.heap, nextId := t.nextId } := by
  cases hr : r with
  | error e => rw [hr] at h; exact absurd h (by simp [bind, Except.bind])
  | ok a => rw [hr] at h; exact hf a t h

theorem bind_frameNet {α : Type} {r : Res α} {f : α -> Res State}
    {s t : State}
    (hf : ∀ a u, f a = .ok u ->
      u = { s with net := u.net, selfBalance := u.selfBalance })
    (h : (r >>= f) = .ok t) :
    t = { s with net := t.net, selfBalance := t.selfBalance } := by
  cases hr : r with
  | error e => rw [hr] at h; exact absurd h (by simp [bind, Except.bind])
  | ok a => rw [hr] at h; exact hf a t h

/-! ### Compound assignment and inc/dec

`t op= se` and `++t;` write the component their target lives in: `env` for a
stack variable (above), `storage` for a storage place, `heap` for a memory
slot.  The calculus writes the last two `{storage := save(…)}` and
`{memory := write(…)}`. -/

theorem compoundAssignUpd_storageShape_frame (op : BinOp) (lhs : PlaceExpr)
    (rhs : WrappedExpr) (s t : State) (ty : Ty) (base : WrappedExpr) (f : Field)
    (hs : lhs.expr = WrappedExpr.field Kind.storage ty base f)
    (h : compoundAssignUpd op lhs rhs s = .ok t) :
    t = { s with storage := t.storage } := by
  rw [compoundAssignUpd, hs] at h
  dsimp only at h
  refine bind_frameSt ?_ h; intro v u hu
  refine bind_frameSt ?_ hu; intro p u hu
  refine bind_frameSt ?_ hu; intro old u hu
  refine bind_frameSt ?_ hu; intro nv u hu
  exact saveStorage_frame hu

theorem compoundAssignUpd_memory_frame (op : BinOp) (ty : Ty)
    (base : WrappedExpr) (f : Field) (hass : _) (rhs : WrappedExpr)
    (s t : State)
    (h : compoundAssignUpd op ⟨WrappedExpr.field Kind.memory ty base f, hass⟩
      rhs s = .ok t) :
    t = { s with heap := t.heap, nextId := t.nextId } := by
  rw [compoundAssignUpd] at h
  dsimp only at h
  refine bind_frameHeap ?_ h; intro v u hu
  refine bind_frameHeap ?_ hu; intro id u hu
  refine bind_frameHeap ?_ hu; intro old u hu
  refine bind_frameHeap ?_ hu; intro nv u hu
  exact writeMemField_frame hu

theorem compoundAssignUpd_memoryIndex_frame (op : BinOp) (ty : Ty)
    (base ix : WrappedExpr) (hass : _) (rhs : WrappedExpr) (s t : State)
    (h : compoundAssignUpd op ⟨WrappedExpr.index Kind.memory ty base ix, hass⟩
      rhs s = .ok t) :
    t = { s with heap := t.heap, nextId := t.nextId } := by
  rw [compoundAssignUpd] at h
  dsimp only at h
  refine bind_frameHeap ?_ h; intro v u hu
  refine bind_frameHeap ?_ hu; intro id u hu
  refine bind_frameHeap ?_ hu; intro i u hu
  refine bind_frameHeap ?_ hu; intro old u hu
  refine bind_frameHeap ?_ hu; intro nv u hu
  exact writeMemIndex_frame hu

/-- `sp.f op= se`: `{storage := save(storage, sp·f, sp·f ⊕ se)}`. -/
theorem compoundAssignUpd_storageField (op : BinOp) (ty : Ty)
    (base : WrappedExpr) (f : Field) (hass : _) (rhs : WrappedExpr) :
    Par.toUpd [Elem.storage (fun s =>
        (compoundAssignUpd op ⟨WrappedExpr.field Kind.storage ty base f, hass⟩
          rhs s).map State.storage)] =
      compoundAssignUpd op ⟨WrappedExpr.field Kind.storage ty base f, hass⟩ rhs :=
  toUpd_storage_of_frame _ (fun s t h =>
    compoundAssignUpd_storageShape_frame op _ rhs s t ty base f rfl h)

/-- `mv.f op= se`: `{memory := write(mem, mv, f, read(mem, mv, f) ⊕ se)}`. -/
theorem compoundAssignUpd_memoryField (op : BinOp) (ty : Ty)
    (base : WrappedExpr) (f : Field) (hass : _) (rhs : WrappedExpr) :
    Par.toUpd [Elem.heap (fun s =>
        (compoundAssignUpd op ⟨WrappedExpr.field Kind.memory ty base f, hass⟩
          rhs s).map fun t => (t.heap, t.nextId))] =
      compoundAssignUpd op ⟨WrappedExpr.field Kind.memory ty base f, hass⟩ rhs :=
  toUpd_heap_of_frame _ (compoundAssignUpd_memory_frame op ty base f hass rhs)

/-- `mv[i] op= se`: the index twin. -/
theorem compoundAssignUpd_memoryIndex (op : BinOp) (ty : Ty)
    (base ix : WrappedExpr) (hass : _) (rhs : WrappedExpr) :
    Par.toUpd [Elem.heap (fun s =>
        (compoundAssignUpd op ⟨WrappedExpr.index Kind.memory ty base ix, hass⟩
          rhs s).map fun t => (t.heap, t.nextId))] =
      compoundAssignUpd op ⟨WrappedExpr.index Kind.memory ty base ix, hass⟩ rhs :=
  toUpd_heap_of_frame _
    (compoundAssignUpd_memoryIndex_frame op ty base ix hass rhs)

/-! ### Push, pop, delete and transfer -/

theorem pushUpd_frame (target : PlaceExpr) (value : Option WrappedExpr)
    (s t : State) (h : pushUpd target value s = .ok t) :
    t = { s with storage := t.storage } := by
  rw [pushUpd] at h
  refine bind_frameSt ?_ h; intro p u hu
  refine bind_frameSt ?_ hu; intro arr u hu
  split at hu
  · exact bind_frameSt (fun _ _ hv => saveStorage_frame hv) hu
  · exact absurd hu (by simp)

theorem popUpd_frame (target : PlaceExpr) (s t : State)
    (h : popUpd target s = .ok t) : t = { s with storage := t.storage } := by
  rw [popUpd] at h
  refine bind_frameSt ?_ h; intro p u hu
  refine bind_frameSt ?_ hu; intro arr u hu
  split at hu
  · split at hu
    · exact absurd hu (by simp)
    · exact saveStorage_frame hu
  · exact absurd hu (by simp)

/-- **Not covered**: `storageDeleteUpd`.  Its `deletePath` is state-changing
on a push-place target (`arr.push()` extends the array *before* the delete
addresses the new slot), so the frame is relative to that intermediate state
rather than to `s`, and stating it needs a `pushPath` frame first.  The rule
is still in the terminal table and still has its `_update` theorem; what is
missing is only its first-order `{storage := …}` spelling. -/
theorem transferUpd_frame (recipient amount : WrappedExpr) (s t : State)
    (h : transferUpd recipient amount s = .ok t) :
    t = { s with net := t.net, selfBalance := t.selfBalance } := by
  rw [transferUpd] at h
  refine bind_frameNet ?_ h; intro addr u hu
  refine bind_frameNet ?_ hu; intro amt u hu
  split at hu
  · exact absurd hu (by simp)
  · split at hu
    · exact absurd hu (by simp)
    · cases hu; rfl

/-- `a.transfer(v)`: `{net := …}`, the one rule that writes the ledger. -/
theorem transferUpd_bridge (recipient amount : WrappedExpr) :
    Par.toUpd [Elem.net (fun s =>
        (transferUpd recipient amount s).map fun t => (t.net, t.selfBalance))] =
      transferUpd recipient amount :=
  toUpd_net_of_frame _ (transferUpd_frame recipient amount)

/-- `arr.push(se)` / `arr.push()` / `arr.pop()`: both `{storage := …}`. -/
theorem pushUpd_bridge (target : PlaceExpr) (value : Option WrappedExpr) :
    Par.toUpd [Elem.storage
        (fun s => (pushUpd target value s).map State.storage)] =
      pushUpd target value :=
  toUpd_storage_of_frame _ (pushUpd_frame target value)

theorem popUpd_bridge (target : PlaceExpr) :
    Par.toUpd [Elem.storage (fun s => (popUpd target s).map State.storage)] =
      popUpd target :=
  toUpd_storage_of_frame _ (popUpd_frame target)

/-- `T storage sp = path;` on a **pure** path: `sp := path`, the calculus's
alias update.  An impure captured path (`people[f()]`) resolves through the
interpreter and is the one arm of the table that is not first-order
(`storagePlaceAliasUpd`'s docstring). -/
theorem storagePlaceAliasUpd_bridge (name : Name) (init : WrappedExpr)
    (h : (init.simple || simplePathB init) = true) :
    Par.toUpd [Elem.env name
        (fun s => (placePath s init).map fun p => Binding.spath p.1 p.2)] =
      storagePlaceAliasUpd name init := by
  funext s
  rw [toUpd_env, storagePlaceAliasUpd_pure s name init h]
  simp only [Except.map]
  cases placePath s init with
  | error h => rfl
  | ok p => obtain ⟨r, sg⟩ := p; rfl

/-- `T x;`: `x := default(T)`. -/
theorem stackDeclSkipUpd_bridge (ty : Ty) (name : Name) :
    Par.toUpd [Elem.env name (fun _ => .ok (Binding.val (defaultValue ty)))] =
      stackDeclSkipUpd ty name := by
  funext s; rw [toUpd_env]; rfl

/-- `T storage p;`: the empty update. -/
theorem storageDeclSkipUpd_bridge (ty : Ty) (name : Name) :
    Par.toUpd [] = storageDeclSkipUpd ty name := by
  funext s; rfl

/-- `x op= se` on a stack variable: `x := x ⊕ se`, one elementary update. -/
theorem compoundAssignUpd_stack (op : BinOp) (ty : Ty) (fld : Field)
    (hass : _) (rhs : WrappedExpr) :
    Par.toUpd [Elem.env fld.name
        (fun s => readVal s rhs >>= fun v =>
          stackVal s fld.name >>= fun old =>
            applyBinOp op old v >>=
              checkArith (WrappedExpr.var Kind.stack ty fld).ty >>= fun nv =>
                .ok (Binding.val nv))] =
      compoundAssignUpd op ⟨WrappedExpr.var Kind.stack ty fld, hass⟩ rhs := by
  refine toUpd_env_of _ _ _ (fun s => ?_)
  simp only [compoundAssignUpd, bind, Except.bind, Except.map]
  cases readVal s rhs with
  | error e => rfl
  | ok v =>
      simp only []
      cases stackVal s fld.name with
      | error e => rfl
      | ok old =>
          simp only []
          cases applyBinOp op old v with
          | error e => rfl
          | ok nv0 =>
              simp only []
              cases checkArith (WrappedExpr.var Kind.stack ty fld).ty nv0 <;> rfl

end Upd
end Solidity
