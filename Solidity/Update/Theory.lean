import Solidity.SemanticsProperties
import Solidity.Update.Eval
import Solidity.Theory.Denote
import Solidity.Theory.Memory

/-!
# A rule's update, read as a KeY term

`Rules.lean` states each terminal rule's update as first-order syntax —
`{storage := save(storage, p, se)}` — and `Update/Eval.lean` gives that syntax
its meaning by running the interpreter: `StorageUpd.save` becomes
`State.saveStorage`.  That is a perfectly good semantics and it is *not* the
one the taclet has.  KeY's `save` is an uninterpreted symbol constrained by
`structRules.key`, and until `Theory/Storage.lean` there was nothing in this
package that could tell the two apart, because there was no `save`.  (And
they *do* differ: KeY's `save` keeps a location's mapping members under a
struct written over it; the interpreter refuses that program.  The last
section says where the two meet.)

This module reads a rule's storage update as a **term** of that theory over
the pre-state and proves that denoting the term gives back exactly what
`Update/Eval.lean` computes:

    storageRhs u s = storageRhsT u s

Composed with `Update/TacletTable.lean`'s bridges and `Wp.terminalUpdate_sound`,
that reads: the taclet's own term is what `execStmt` does.  Every taclet of
`Theory/Storage.lean` is therefore a fact about this package's wp semantics
rather than about a private model — in particular the frame law
`StValue.find_save_frame`, which `Semantics` never had.

## Why `storageRhsT` is a copy

`storageRhsT` is `Update.storageRhs` with its one write, `Upd.saveSt`,
replaced by `theoryWrite` — the same write read as `denoteSt (write …)`, the
walk of `Theory/Storage.lean` that KeY's `save` puts its leaf under.
Everything else, the path readers and the value readers, is shared verbatim.
That is deliberate, and the same discipline `Update/Eval.lean` sets for
itself: if the term reading had its own arithmetic and its own path
resolution, the theorem below would be comparing two of my own definitions.
Sharing the readers means it is about the one thing that differs — whether the
*update shape* a rule states denotes the interpreter's write.

The duplication is the point rather than an accident: `storageRhsT` is the
KeY reading, `storageRhs` is the interpreter's, and `storageRhs_eq_theory` is
the claim that they agree.

## What is covered, exactly

Two of `Rules.UpdElem`'s constructors: `.storage` (every `StorageUpd`) and
`.heap` (both `HeapUpd`s).  Those are the elements whose right-hand side *is*
a data-structure term, and together they are every `{storage := …}` and
`{memory := write(…)}` the rule table writes.

The rest of `UpdElem` is **not** covered here and does not claim to be.
`.bind`, `.bumpOf`, `.transfer` and `.havoc` carry no term of either theory.
`.memDecl` and `.memDelete` do — KeY writes them
`{memory := copySt(addM(memory, r), r, find(storage, sp))}` — but `copySt`
lives in `structMemoryRules.key`, which `Solidity/Theory/` does not model.
The path identities that make KeY's `copySt` a pure operation on terms are in
`Theory/Memory.lean`, so what that row needs is the three taclets themselves
rather than a change of model.  `docs/lean-key-rule-map.md` records it.

## Where the term is not KeY's, spelled out

* **push and pop.** KeY writes two saves in one parallel update, the new slot
  and the new length.  The slot index is the array's *old* length, which is
  outside it, so that term cannot denote through a `putAt` that mirrors
  `SVal.save` — see `Theory/Denote.lean`.  The term here writes the extended
  array at the array's own path, the shape both `Rules.StorageUpd.push`
  (already a merge of KeY's three push taclets) and `Update.pushStorage` use.
* **the leaf.** Every `save(storage, p, v)` upstream keeps its leaf — a struct
  written over a location keeps the location's mapping members — and
  `theoryWrite` reads the walk without it.  `theorySave` below is upstream's
  spelling, and the `theorySave_eq_theoryWrite*` theorems are why
  `storageRhsT` may read every write as the walk: for a primitive payload
  there is nothing to keep (every `.save` arm, and the `length` a push or pop
  writes); and on a struct copy the interpreter is stuck wherever the two
  would differ (`Semantics.tyHasMapping` — solc ≥ 0.7 rejects the program).
  The slot a `push` lands on is *not* fresh — it is the one a `pop` cleared
  and gave back, mapping members included (`Semantics.pushSlot`).
* **the copy rules.** The source is the `SVal` that `rhsSVal` read, as a
  `sval` leaf, because `rhsSVal` also covers the primitive and memory sources
  that one `Rules` constructor merges.  `Theory.denote_find` is the statement
  that the storage case of that read is KeY's `find`.
-/

namespace Solidity
namespace Update

open Semantics Wp Rules Theory

/-! ## One write, read as a term -/

/-- The tree a storage root holds, failing where `State.saveStorage` fails on
an unknown root. -/
def rootTree (s : State) (root : Name) : Res SVal :=
  match lookupBy root s.storage with
  | some v => .ok v
  | none => .error .stuck

/-- `{storage := save(storage, p, w)}` read as the walk: the storage component
the term denotes with its leaf collapsed.  This is the only place the two
readings differ. -/
def theoryWrite (s : State) (root : Name) (segs : List Seg) (w : SVal) :
    Res (List (Name × SVal)) :=
  (rootTree s root) >>= fun v0 =>
    (denoteSt (StValue.write (StValue.sval v0) segs (StValue.sval w))).map
      fun v => setBy root v s.storage

/-- `{storage := save(storage, p, w)}` as upstream spells it, leaf included: a
mapping member of the location kept under a struct written over it. -/
def theorySave (s : State) (root : Name) (segs : List Seg) (w : SVal) :
    Res (List (Name × SVal)) :=
  (rootTree s root) >>= fun v0 =>
    (denoteSt (StValue.save (StValue.sval v0) segs (StValue.sval w))).map
      fun v => setBy root v s.storage

/-- **The collapse.** Where the location's current value carries no mapping —
the whole fragment the interpreter admits — upstream's term denotes the write
the rule table already reads.  Off that fragment it does not, and the fold did
not change this: `Counterexamples/MappingSideConditions.lean`'s M2 is the
witness. -/
theorem theorySave_eq_theoryWrite (s : State) (root : Name) (segs : List Seg)
    (w cur v0 : SVal) (hroot : rootTree s root = .ok v0)
    (hcur : StValue.find (StValue.sval v0) segs = StValue.sval cur)
    (hnm : svalHasMapping cur = false) :
    theorySave s root segs w = theoryWrite s root segs w := by
  unfold theorySave theoryWrite
  rw [hroot]
  simp only [bind, Except.bind]
  rw [denote_save hcur hnm, denote_write]

/-- And for a payload that is not a struct, with no side condition at all:
every primitive write, and the `length` a push or pop writes. -/
theorem theorySave_eq_theoryWrite_prim (s : State) (root : Name) (segs : List Seg)
    (w : SVal) (hw : ∀ fs, w ≠ SVal.struct fs) :
    theorySave s root segs w = theoryWrite s root segs w := by
  unfold theorySave theoryWrite
  cases rootTree s root with
  | error e => rfl
  | ok v0 =>
      simp only [bind, Except.bind]
      rw [denote_save_prim hw, denote_write]

/-- **The bridge, once.** Every storage update the rule table states ends in
one `Upd.saveSt`, and that write *is* the walk of KeY's `save` term denoted. -/
theorem saveSt_eq_theory (s : State) (root : Name) (segs : List Seg) (w : SVal) :
    Upd.saveSt s root segs w = theoryWrite s root segs w := by
  unfold Upd.saveSt State.saveStorage theoryWrite rootTree
  cases lookupBy root s.storage with
  | none => rfl
  | some v0 =>
      simp only [bind, Except.bind, denote_write, Except.map]
      cases v0.save segs w <;> rfl

/-- The same write where `Rules.StorageUpd.clear` spells it out. -/
theorem saveStorage_map_eq_theory (s : State) (root : Name) (segs : List Seg)
    (w : SVal) :
    (s.saveStorage root segs w).map State.storage = theoryWrite s root segs w :=
  saveSt_eq_theory s root segs w

/-! ## The rule's `storage := …`, read as a term -/

/-- `Update.storageSave` with the write read as a term. -/
def storageSaveT (s : State) (target : WrappedExpr) (v : SVal) :
    Res (List (Name × SVal)) :=
  locPath s target >>= fun p => theoryWrite s p.1 p.2 v

/-- `Update.storageSave` with the write read as upstream's term, leaf included
— what the seven `*CopySource` / `…StoreRoot` rules state. -/
def storageKeySaveT (s : State) (target : WrappedExpr) (v : SVal) :
    Res (List (Name × SVal)) :=
  locPath s target >>= fun p => theorySave s p.1 p.2 v

/-- The collapse at the update level: `storageRhsT`'s `.copy` arm may read the
copy as `storageSaveT`. -/
theorem storageKeySaveT_eq_storageSaveT {s : State} {target : WrappedExpr} {v : SVal}
    {root : Name} {segs : List Seg} {v0 cur : SVal}
    (hloc : locPath s target = .ok (root, segs))
    (hroot : rootTree s root = .ok v0)
    (hcur : StValue.find (StValue.sval v0) segs = StValue.sval cur)
    (hnm : svalHasMapping cur = false) :
    storageKeySaveT s target v = storageSaveT s target v := by
  unfold storageKeySaveT storageSaveT
  rw [hloc]
  simp only [bind, Except.bind]
  exact theorySave_eq_theoryWrite s root segs v cur v0 hroot hcur hnm

/-- `Update.pushStorage` with the write read as a term. -/
def pushStorageT (arr : WrappedExpr) (value : Option WrappedExpr) (s : State) :
    Res (List (Name × SVal)) :=
  placePath s arr >>= fun p => s.findStorage p.1 p.2 >>= fun cur =>
    match cur, arr.ty with
    | SVal.array elems shadow, Ty.ref (RefTy.array elemTy) =>
        (match value with
          | none => .ok (pushSlot elemTy shadow).1
          | some rhs => rhsSVal s rhs) >>= fun newElem =>
          theoryWrite s p.1 p.2
            (SVal.array (elems ++ [newElem]) (pushSlot elemTy shadow).2)
    | _, _ => .error .stuck

/-- `Update.storageRhs` with the write read as a term.  Compare arm by arm
with `Update/Eval.lean`: only `Upd.saveSt` has moved. -/
def storageRhsT (u : StorageUpd) (s : State) : Res (List (Name × SVal)) :=
  match u with
  | .save target t => Sym.eval s t >>= fun v => storageSaveT s target v.toSVal
  | .copy target src => rhsSVal s src >>= fun v => storageSaveT s target v
  | .copyFromMem target src => rhsSVal s src >>= fun v => storageSaveT s target v
  | .push arr value => pushStorageT arr value s
  | .pushPlace place =>
      match place with
      | WrappedExpr.pushPlace arr => pushStorageT arr none s
      | _ => .error .stuck
  | .pop arr =>
      placePath s arr >>= fun p => s.findStorage p.1 p.2 >>= fun cur =>
        match cur with
        | SVal.array elems shadow =>
            match elems.reverse with
            | [] => .error .revert
            | last :: restRev =>
                theoryWrite s p.1 p.2
                  (SVal.array restRev.reverse (last.defaultOf :: shadow))
        | _ => .error .stuck
  | .clear target =>
      deletePath s target >>= fun x =>
        x.1.findStorage x.2.1 x.2.2 >>= fun cur =>
          theoryWrite x.1 x.2.1 x.2.2 cur.defaultOf

/-- **The storage half of the headline.** A rule's stated `storage := …`,
read as a term of `structRules.key`'s theory and denoted, is exactly the
update `Update/Eval.lean` computes by running the interpreter. -/
theorem storageRhs_eq_theory (u : StorageUpd) (s : State) :
    storageRhs u s = storageRhsT u s := by
  cases u <;>
    simp only [storageRhs, storageRhsT, storageSave, storageSaveT, pushStorage,
      pushStorageT, saveSt_eq_theory, saveStorage_map_eq_theory] <;>
    rfl

/-- …as an equality of readers, which is the form every consumer needs: it
rewrites under `elemPar`, `UpdTerm.toUpd`, `goalsExec` and `StepEffect.wp`
alike, so the whole wp reading of a rule can be taken over KeY's terms. -/
theorem storageRhs_eq_theory' : storageRhs = storageRhsT := by
  funext u s
  exact storageRhs_eq_theory u s

/-- The same claim where a rule writes it: a `{storage := …}` element of a
`\replacewith`, evaluated, is the KeY term denoted. -/
theorem toUpd_storage_eq_theory (u : StorageUpd) (s : State) :
    UpdTerm.toUpd [UpdElem.storage u] s =
      (storageRhsT u s).map fun g => { s with storage := g } := by
  have h : UpdTerm.toUpd [UpdElem.storage u] s =
      (storageRhs u s).map fun g => { s with storage := g } := by
    simp only [UpdTerm.toUpd, UpdTerm.toPar, List.flatMap]
    exact Upd.toUpd_storage _ s
  rw [h, storageRhs_eq_theory]

/-! ## The rule's `memory := …`, read as a term

The memory half.  `Theory/Memory.lean` holds the algebra; its denotation is
here because it needs `writeMemField`/`allocDefault`, and because this is
where it is used. -/

/-- What a memory slot's contents denotes.  A path identity denotes the object
it names, which is where the two models are brought together: KeY's
`idC(idp, flds)` is a *name*, the interpreter's `Nat` is the object, and
`Theory.Memory.resolve` walks the one to the other.  `dflt` carries no sort
and so no value, exactly as `StValue.dflt` does. -/
def denoteMV (h : List (Nat × MObj)) : Theory.MemValue -> Res MVal
  | .prim p => .ok (.prim p)
  | .ident i =>
      match Theory.Memory.resolve h i with
      | some n => .ok (.ref n)
      | none => .error .stuck
  | .dflt => .error .stuck

/-- An interpreter slot value, made a `MemValue` and denoted again, is itself.
Every term the rules build is rooted at such a value, which is why the bridges
below stay equations rather than equations under a side condition. -/
@[simp] theorem denoteMV_toMemValue (h : List (Nat × MObj)) (mv : MVal) :
    denoteMV h (Theory.MVal.toMemValue mv) = .ok mv := by
  cases mv <;> rfl

/-- What a memory term denotes: the heap-and-counter pair the calculus writes
as one (`Upd.Elem.heap`), because an allocation moves both. -/
def denoteMem (s : State) : Theory.Memory -> Res (List (Nat × MObj) × Nat)
  | .mtMem => .ok ([], 0)
  | .pre => .ok (s.heap, s.nextId)
  | .write mem id a v =>
      denoteMem s mem >>= fun hn =>
        (match Theory.Memory.resolve hn.1 id with
          | some n => .ok n
          | none => .error .stuck) >>= fun n =>
          denoteMV hn.1 v >>= fun mv =>
            match a with
            | Seg.field f => Upd.heapOf (writeMemField { s with heap := hn.1, nextId := hn.2 } n f mv)
            | Seg.at i => Upd.heapOf (writeMemIndex { s with heap := hn.1, nextId := hn.2 } n i mv)
  | .addM mem idp ty =>
      denoteMem s mem >>= fun hn =>
        if idp = hn.2 then
          (allocDefault { s with heap := hn.1, nextId := hn.2 } ty).map
            fun x => (x.1.heap, x.1.nextId)
        else .error .stuck

/-- One write on the pre-state leaf is the interpreter's slot write.  The
identity is the root one, `idC(n, nil)`, which resolves to `n` itself. -/
theorem denoteMem_write_pre (s : State) (id : Nat) (a : Seg) (mv : MVal) :
    denoteMem s (.write .pre (.idCC id) a (Theory.MVal.toMemValue mv)) =
      (match a with
       | Seg.field f => Upd.heapOf (writeMemField s id f mv)
       | Seg.at i => Upd.heapOf (writeMemIndex s id i mv)) := by
  cases a <;> cases mv <;> rfl

/-! ## What `new` means

KeY's allocating taclets carry `new(memory, freshIdp)` into the antecedent:
the root they mint is one nothing has been allocated at.  Here that is not an
assumption but a consequence of the denotation, and this is the theorem.  Read
it as: once a memory term has been denoted, every identity at or above the
counter it leaves behind is fresh in the term — which is exactly what a rule
firing next is allowed to assume of the root it invents. -/

/-- A write installs a heap and leaves the counter where it was. -/
theorem writeMemField_nextId {s t : State} {id : Nat} {f : Name} {mv : MVal}
    (h : writeMemField s id f mv = .ok t) : t.nextId = s.nextId := by
  unfold writeMemField at h
  cases ho : s.getObj id with
  | error e => rw [ho] at h; exact absurd h (by simp [bind, Except.bind])
  | ok obj =>
      rw [ho] at h
      cases obj with
      | struct fields =>
          simp only [bind, Except.bind, Except.ok.injEq] at h
          exact h ▸ rfl
      | array elems => exact absurd h (by simp [bind, Except.bind])

theorem writeMemIndex_nextId {s t : State} {id : Nat} {i : Int} {mv : MVal}
    (h : writeMemIndex s id i mv = .ok t) : t.nextId = s.nextId := by
  unfold writeMemIndex at h
  cases ho : s.getObj id with
  | error e => rw [ho] at h; exact absurd h (by simp [bind, Except.bind])
  | ok obj =>
      rw [ho] at h
      cases obj with
      | array elems =>
          simp only [bind, Except.bind] at h
          split at h
          · simp only [Except.ok.injEq] at h; exact h ▸ rfl
          · exact absurd h (by simp)
      | struct fields => exact absurd h (by simp [bind, Except.bind])

/-- A slot write denotes at the counter the memory under it left behind: it
allocates nothing. -/
theorem denoteMem_write_counter {s : State} {mem : Theory.Memory}
    {id : Theory.Identity} {a : Seg} {v : Theory.MemValue}
    {h' : List (Nat × MObj)} {n' : Nat}
    (hd : denoteMem s (.write mem id a v) = .ok (h', n')) :
    ∃ g, denoteMem s mem = .ok (g, n') := by
  rw [denoteMem] at hd
  cases hm0 : denoteMem s mem with
  | error e => rw [hm0] at hd; exact absurd hd (by simp [bind, Except.bind])
  | ok hn =>
      rw [hm0] at hd
      simp only [bind, Except.bind] at hd
      cases hres : (match Theory.Memory.resolve hn.1 id with
                    | some n => (.ok n : Res Nat) | none => .error .stuck) with
      | error e => rw [hres] at hd; exact absurd hd (by simp)
      | ok n =>
          rw [hres] at hd
          cases hmv : denoteMV hn.1 v with
          | error e => rw [hmv] at hd; exact absurd hd (by simp)
          | ok mv =>
              rw [hmv] at hd
              simp only [] at hd
              have hcount : hn.2 = n' := by
                cases a with
                | field f =>
                    simp only [Upd.heapOf] at hd
                    cases hw : writeMemField
                        { s with heap := hn.1, nextId := hn.2 } n f mv with
                    | error e => rw [hw] at hd; exact absurd hd (by simp [Except.map])
                    | ok t =>
                        rw [hw] at hd
                        simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hd
                        exact (writeMemField_nextId hw).symm.trans hd.2
                | «at» i =>
                    simp only [Upd.heapOf] at hd
                    cases hw : writeMemIndex
                        { s with heap := hn.1, nextId := hn.2 } n i mv with
                    | error e => rw [hw] at hd; exact absurd hd (by simp [Except.map])
                    | ok t =>
                        rw [hw] at hd
                        simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hd
                        exact (writeMemIndex_nextId hw).symm.trans hd.2
              subst hcount
              exact ⟨hn.1, rfl⟩

/-- An `addM` denotes only at the counter it names, and leaves it behind. -/
theorem denoteMem_addM_counter {s : State} {mem : Theory.Memory} {idp : Nat}
    {ty : RefTy} {h' : List (Nat × MObj)} {n' : Nat}
    (hd : denoteMem s (.addM mem idp ty) = .ok (h', n')) :
    ∃ g, denoteMem s mem = .ok (g, idp) ∧ idp < n' := by
  rw [denoteMem] at hd
  cases hm0 : denoteMem s mem with
  | error e => rw [hm0] at hd; exact absurd hd (by simp [bind, Except.bind])
  | ok hn =>
      rw [hm0] at hd
      simp only [bind, Except.bind] at hd
      split at hd
      case isFalse hne => exact absurd hd (by simp)
      case isTrue heq =>
        cases ha : allocDefault { s with heap := hn.1, nextId := hn.2 } ty with
        | error e => rw [ha] at hd; exact absurd hd (by simp [Except.map])
        | ok x =>
            rw [ha] at hd
            simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hd
            have hlt : hn.2 < x.1.nextId :=
              SemanticsProperties.allocDefault_nextId_lt ha
            exact ⟨hn.1, by rw [heq], by rw [← hd.2]; omega⟩

/-- **`new`, discharged.** A denoted memory term is fresh at every identity
its counter has not reached.  The `pre` leaf is the heap invariant
(`HeapWellFormed`), a `write` allocates nothing, and an `addM` mints the
counter it found and then advances past it — so the root it named is *not*
fresh afterwards, which is `newFromAdd`'s `\then` branch. -/
theorem denoteMem_new {s : State}
    (hwf : SemanticsProperties.HeapWellFormed s) :
    ∀ (mem : Theory.Memory) (h' : List (Nat × MObj)) (n' : Nat),
      denoteMem s mem = .ok (h', n') ->
        ∀ m, n' ≤ m -> Theory.Memory.new s.heap mem m = true := by
  intro mem
  induction mem with
  | mtMem => intro h' n' _ m _; rfl
  | pre =>
      intro h' n' hd m hm
      simp only [denoteMem, Except.ok.injEq, Prod.mk.injEq] at hd
      simp only [Theory.Memory.new, Option.isNone_iff_eq_none]
      exact hwf m (hd.2 ▸ hm)
  | write mem id a v ih =>
      intro h' n' hd m hm
      obtain ⟨g, hg⟩ := denoteMem_write_counter hd
      simpa only [Theory.Memory.new] using ih g n' hg m hm
  | addM mem idp ty ih =>
      intro h' n' hd m hm
      obtain ⟨g, hg, hlt⟩ := denoteMem_addM_counter hd
      have hne : idp ≠ m := by omega
      simp only [Theory.Memory.new, if_neg hne]
      exact ih g idp hg m (by omega)

/-- `Update.memWrite` with the write read as a term. -/
def memWriteT (s : State) (target : WrappedExpr) (mv : MVal) :
    Res (List (Nat × MObj) × Nat) :=
  match target with
  | WrappedExpr.field Kind.memory _ base f =>
      memBase s base >>= fun id =>
        denoteMem s (.write .pre (.idCC id) (Seg.field f.name)
          (Theory.MVal.toMemValue mv))
  | WrappedExpr.index Kind.memory _ base ix =>
      memBase s base >>= fun id => simpleInt s ix >>= fun i =>
        denoteMem s (.write .pre (.idCC id) (Seg.at i)
          (Theory.MVal.toMemValue mv))
  | _ => .error .stuck

theorem memWrite_eq_theory (s : State) (target : WrappedExpr) (mv : MVal) :
    memWrite s target mv = memWriteT s target mv := by
  cases target <;>
    simp only [memWrite, memWriteT, denoteMem_write_pre] <;>
    rename_i k _ _ _ <;> cases k <;> rfl

/-- `Update.heapRhs` with the write read as a term. -/
def heapRhsT (u : HeapUpd) (s : State) : Res (List (Nat × MObj) × Nat) :=
  match u with
  | .write target t => Sym.eval s t >>= fun v => memWriteT s target v.toMVal
  | .writeRef target src => rhsMVal s src >>= fun x => memWriteT x.1 target x.2

/-- **The memory half of the headline.** A rule's stated `memory := …`, read
as a term of `memoryRules.key`'s theory and denoted, is the update
`Update/Eval.lean` computes. -/
theorem heapRhs_eq_theory (u : HeapUpd) (s : State) :
    heapRhs u s = heapRhsT u s := by
  cases u <;> simp only [heapRhs, heapRhsT, memWrite_eq_theory]

theorem heapRhs_eq_theory' : heapRhs = heapRhsT := by
  funext u s
  exact heapRhs_eq_theory u s

/-! ## Sanity

`storageRootWriteStore`'s update on a concrete store, computed both ways. -/

example :
    storageRhs (.save (SoliditySyntax.rootExpr "age") (.read (WrappedExpr.intLit Ty.uint 42)))
        State.exampleStore
      = storageRhsT (.save (SoliditySyntax.rootExpr "age")
          (.read (WrappedExpr.intLit Ty.uint 42))) State.exampleStore :=
  storageRhs_eq_theory _ _

end Update
end Solidity
