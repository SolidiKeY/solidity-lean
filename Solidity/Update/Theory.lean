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
package that could tell the two apart, because there was no `save`.

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
replaced by `theoryWrite` — the same write read as `denoteSt (save …)`.
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
lives in `structMemoryRules.key`, which `Solidity/Theory/` does not model:
with identities resolved to the interpreter's `Nat` (`Theory/Memory.lean`), a
copy is not a pure operation on terms, because every nested object it makes
needs a fresh one.  KeY's path identities are what make its `copySt` pure, and
porting them is what that row needs.  `docs/lean-key-rule-map.md` records it.

## Where the term is not KeY's, spelled out

* **push and pop.** KeY writes two saves in one parallel update, the new slot
  and the new length.  The slot index is the array's *old* length, which is
  outside it, so that term cannot denote through a `putAt` that mirrors
  `SVal.save` — see `Theory/Denote.lean`.  The term here writes the extended
  array at the array's own path, the shape both `Rules.StorageUpd.push`
  (already a merge of KeY's three push taclets) and `Update.pushStorage` use.
* **the copy rules.** KeY writes `save(storage, p, find<[StValue]>(storage,
  src))`; the source here is the `SVal` that `rhsSVal` read, as a `sval` leaf,
  because `rhsSVal` also covers the primitive and memory sources that one
  `Rules` constructor merges.  `Theory.denote_find` is the statement that the
  storage case of that read is KeY's `find`.
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

/-- `{storage := save(storage, p, w)}`: the storage component KeY's term
denotes.  This is the only place the two readings differ. -/
def theoryWrite (s : State) (root : Name) (segs : List Seg) (w : SVal) :
    Res (List (Name × SVal)) :=
  (rootTree s root) >>= fun v0 =>
    (denoteSt (StValue.save (StValue.sval v0) segs (StValue.sval w))).map
      fun v => setBy root v s.storage

/-- **The bridge, once.** Every storage update the rule table states ends in
one `Upd.saveSt`, and that write *is* KeY's `save` term denoted. -/
theorem saveSt_eq_theory (s : State) (root : Name) (segs : List Seg) (w : SVal) :
    Upd.saveSt s root segs w = theoryWrite s root segs w := by
  unfold Upd.saveSt State.saveStorage theoryWrite rootTree
  cases lookupBy root s.storage with
  | none => rfl
  | some v0 =>
      simp only [bind, Except.bind, denote_save, Except.map]
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

/-- `Update.pushStorage` with the write read as a term. -/
def pushStorageT (arr : WrappedExpr) (value : Option WrappedExpr) (s : State) :
    Res (List (Name × SVal)) :=
  placePath s arr >>= fun p => s.findStorage p.1 p.2 >>= fun cur =>
    match cur, arr.ty with
    | SVal.array elems, Ty.ref (RefTy.array elemTy) =>
        (match value with
          | none => .ok (defaultForTy elemTy)
          | some rhs => rhsSVal s rhs) >>= fun newElem =>
          theoryWrite s p.1 p.2 (SVal.array (elems ++ [newElem]))
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
        | SVal.array elems =>
            match elems.reverse with
            | [] => .error .revert
            | _ :: restRev => theoryWrite s p.1 p.2 (SVal.array restRev.reverse)
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

/-- What a memory slot's contents denotes.  `dflt` carries no sort and so no
value, exactly as `StValue.dflt` does. -/
def denoteMV : Theory.MemValue -> Res MVal
  | .mval v => .ok v
  | .dflt => .error .stuck

/-- What a memory term denotes: the heap-and-counter pair the calculus writes
as one (`Upd.Elem.heap`), because an allocation moves both. -/
def denoteMem (s : State) : Theory.Memory -> Res (List (Nat × MObj) × Nat)
  | .mtMem => .ok ([], 0)
  | .pre => .ok (s.heap, s.nextId)
  | .write mem id a v =>
      denoteMem s mem >>= fun hn =>
        denoteMV v >>= fun mv =>
          match a with
          | Seg.field f => Upd.heapOf (writeMemField { s with heap := hn.1, nextId := hn.2 } id f mv)
          | Seg.at i => Upd.heapOf (writeMemIndex { s with heap := hn.1, nextId := hn.2 } id i mv)
  | .addM mem ty =>
      denoteMem s mem >>= fun hn =>
        (allocDefault { s with heap := hn.1, nextId := hn.2 } ty).map
          fun x => (x.1.heap, x.1.nextId)

/-- One write on the pre-state leaf is the interpreter's slot write. -/
theorem denoteMem_write_pre (s : State) (id : Nat) (a : Seg) (mv : MVal) :
    denoteMem s (.write .pre id a (.mval mv)) =
      (match a with
       | Seg.field f => Upd.heapOf (writeMemField s id f mv)
       | Seg.at i => Upd.heapOf (writeMemIndex s id i mv)) := by
  cases a <;> rfl

/-- `Update.memWrite` with the write read as a term. -/
def memWriteT (s : State) (target : WrappedExpr) (mv : MVal) :
    Res (List (Nat × MObj) × Nat) :=
  match target with
  | WrappedExpr.field Kind.memory _ base f =>
      memBase s base >>= fun id =>
        denoteMem s (.write .pre id (Seg.field f.name) (.mval mv))
  | WrappedExpr.index Kind.memory _ base ix =>
      memBase s base >>= fun id => simpleInt s ix >>= fun i =>
        denoteMem s (.write .pre id (Seg.at i) (.mval mv))
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
