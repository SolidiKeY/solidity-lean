import Solidity.Semantics.Properties
import Solidity.Update.Eval
import Solidity.Theory.Memory

/-!
# A rule's memory update, read as a KeY term

`Calculus/Rules.lean` states each terminal rule's update as first-order syntax —
`{memory := write(memory, id, a, v)}` — and `Update/Eval.lean` gives that
syntax its meaning by running the interpreter.  KeY's `write`, `addM` and
`read` are uninterpreted symbols constrained by `memoryRules.key`, and
`Theory/Memory.lean` is that theory as terms.  This module reads a rule's
`memory := …` as a term of it over the pre-state heap (`Memory.pre`) and
proves that denoting the term gives back exactly what `Update/Eval.lean`
computes:

    heapRhs u s = heapRhsT u s

`heapRhsT` is `Update.heapRhs` with its one write, `Update.memWrite`,
replaced by `memWriteT` — the same write read as `denoteMem (write …)`.
Everything else, the path readers and the value readers, is shared verbatim,
so the theorem is about the one thing that differs: whether the *update
shape* a rule states denotes the interpreter's write.

`denoteMem_new` is the other export: KeY's freshness premise `new(memory, r)`
on `memoryDeclNew` is discharged by the denotation, since the interpreter's
allocator never reuses a root.

There is no storage half any more.  `Theory/Storage.lean` is a theory over
free terms, as `structRules.key` is, and the fragment of programs its
collapsing leaf describes is exactly the fragment the AST admits
(`TypedStmt.Assign.mk`, `stmtTypingOk`): a storage-to-storage copy of a type
that carries a mapping is not a statement, so there is nothing left for a
denotation to reconcile.
-/

namespace Solidity
namespace Update

open Semantics Wp Rules Theory

/-! ## The rule's `memory := …`, read as a term

The memory half.  `Theory/Memory.lean` holds the algebra; its denotation is
here because it needs `writeMemField`/`allocDefault`, and because this is
where it is used. -/

/-- What a memory slot's contents denotes.  A path identity denotes the object
it names, which is where the two models are brought together: KeY's
`idC(idp, flds)` is a *name*, the interpreter's `Nat` is the object, and
`Theory.Memory.resolve` walks the one to the other.  `dflt` carries no sort
and so no value; it is resolved by the sort of the read. -/
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
  -- The leaf carries its heap (`Theory/Terms.lean`), so a term denotes only
  -- against the state it is a term *about*.
  | .pre h => if h = s.heap then .ok (h, s.nextId) else .error .stuck
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
        if idp.toNat = hn.2 then
          (allocDefault { s with heap := hn.1, nextId := hn.2 } ty).map
            fun x => (x.1.heap, x.1.nextId)
        else .error .stuck
  -- `copySt` has no denotation yet: the interpreter's copy allocates the
  -- object it copies into, so a `copySt` over an `addM` would denote to one
  -- object too many.  Nothing builds one — `memWriteT` below only ever writes
  -- on the `pre` leaf — and giving it the composite reading the calculus needs
  -- is `Update/Theory.lean`'s next row, not this one's.
  | .copySt _ _ _ => .error .stuck

/-- One write on the pre-state leaf is the interpreter's slot write.  The
identity is the root one, `idC(n, nil)`, which resolves to `n` itself. -/
theorem denoteMem_write_pre (s : State) (id : Nat) (a : Seg) (mv : MVal) :
    denoteMem s (.write (.pre s.heap) (.idCC (.ofNat id)) a (Theory.MVal.toMemValue mv)) =
      (match a with
       | Seg.field f => Upd.heapOf (writeMemField s id f mv)
       | Seg.at i => Upd.heapOf (writeMemIndex s id i mv)) := by
  cases a <;> cases mv <;>
    simp only [denoteMem, if_pos rfl, Theory.Memory.resolve_idCC, denoteMV,
      denoteMV_toMemValue, bind, Except.bind] <;> rfl

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
theorem denoteMem_addM_counter {s : State} {mem : Theory.Memory}
    {idp : Theory.IdentityPrim}
    {ty : RefTy} {h' : List (Nat × MObj)} {n' : Nat}
    (hd : denoteMem s (.addM mem idp ty) = .ok (h', n')) :
    ∃ g, denoteMem s mem = .ok (g, idp.toNat) ∧ idp.toNat < n' := by
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
        ∀ m, n' ≤ m -> Theory.Memory.new mem (.ofNat m) = true := by
  intro mem
  induction mem using Theory.Memory.inductionOn with
  | h0 => intro h' n' _ m _; rfl
  | h1 hp =>
      intro h' n' hd m hm
      by_cases hs : hp = s.heap
      · subst hs
        simp only [denoteMem, if_true, Except.ok.injEq, Prod.mk.injEq,
          reduceIte] at hd
        simp only [Theory.Memory.new, Option.isNone_iff_eq_none]
        exact hwf m (hd.2 ▸ hm)
      · simp only [denoteMem, if_neg hs] at hd
        cases hd
  | h2 mem id a v ih =>
      intro h' n' hd m hm
      obtain ⟨g, hg⟩ := denoteMem_write_counter hd
      simpa only [Theory.Memory.new] using ih g n' hg m hm
  | h3 mem idp ty ih =>
      intro h' n' hd m hm
      obtain ⟨g, hg, hlt⟩ := denoteMem_addM_counter hd
      have hne : idp ≠ Theory.IdentityPrim.ofNat m := by
        intro he
        exact absurd (congrArg Theory.IdentityPrim.toNat he) (by simp; omega)
      simp only [Theory.Memory.new, if_neg hne]
      exact ih g idp.toNat hg m (by omega)
  | h4 mem idp st _ => intro h' n' hd m hm; simp [denoteMem] at hd

/-- `Update.memWrite` with the write read as a term. -/
def memWriteT (s : State) (target : WrappedExpr) (mv : MVal) :
    Res (List (Nat × MObj) × Nat) :=
  match target with
  | WrappedExpr.field Kind.memory _ base f =>
      memBase s base >>= fun id =>
        denoteMem s (.write (.pre s.heap) (.idCC (.ofNat id)) (Seg.field f.name)
          (Theory.MVal.toMemValue mv))
  | WrappedExpr.index Kind.memory _ base ix =>
      memBase s base >>= fun id => simpleInt s ix >>= fun i =>
        denoteMem s (.write (.pre s.heap) (.idCC (.ofNat id)) (Seg.at i)
          (Theory.MVal.toMemValue mv))
  | _ => .error .stuck

theorem memWrite_eq_theory (s : State) (target : WrappedExpr) (mv : MVal) :
    (memWriteIn s target mv).map (fun t => (t.heap, t.nextId))
      = memWriteT s target mv := by
  cases target with
  | field k _ base f =>
      cases k <;> try rfl
      simp only [memWriteIn, memWriteT, denoteMem_write_pre, bind, Except.bind]
      cases memBase s base <;> rfl
  | index k _ base ix =>
      cases k <;> try rfl
      simp only [memWriteIn, memWriteT, denoteMem_write_pre, bind, Except.bind]
      cases memBase s base <;> try rfl
      cases simpleInt s ix <;> rfl
  | _ => rfl

/-- `Update.heapRhs` with the write read as a term.

The reading covers a `write` on the `memory` variable, which is what it covered
before `Rules.MemTerm` existed.  `addM` and `copySt` are not here: denoting
them means reconciling KeY's lazy allocation with `Semantics.allocDefault`'s
eager one, and the two disagree about *which* root a nested type gets — the
row is `docs/lean-key-rule-map.md`'s, not this file's. -/
def heapRhsT (t : MemTerm) (s : State) : Res (List (Nat × MObj) × Nat) :=
  match t with
  | .write .cur target (.sym v) => Sym.eval s v >>= fun w => memWriteT s target w.toMVal
  | .write .cur target (.image src) => rhsMVal s src >>= fun x => memWriteT x.1 target x.2
  | _ => heapRhs t s

/-- **The memory half of the headline.** A rule's stated `memory := …`, read
as a term of `memoryRules.key`'s theory and denoted, is the update
`Update/Eval.lean` computes. -/
theorem heapRhs_eq_theory (t : MemTerm) (s : State) :
    heapRhs t s = heapRhsT t s := by
  match t with
  | .write .cur target (.sym v) =>
      simp only [heapRhs, heapRhsT, memEval, Except.map, bind, Except.bind]
      cases Sym.eval s v <;>
        simp only [Except.map, bind, Except.bind, <- memWrite_eq_theory] <;>
        (try rfl) <;> (rename_i w; cases memWriteIn s target w.toMVal <;> rfl)
  | .write .cur target (.image src) =>
      simp only [heapRhs, heapRhsT, memEval, Except.map, bind, Except.bind]
      cases rhsMVal s src <;>
        simp only [Except.map, bind, Except.bind, <- memWrite_eq_theory] <;>
        (try rfl) <;> (rename_i x; cases memWriteIn x.1 target x.2 <;> rfl)
  | .cur => rfl
  | .addM _ _ => rfl
  | .copySt _ _ _ => rfl
  | .write (.addM _ _) _ _ => rfl
  | .write (.copySt _ _ _) _ _ => rfl
  | .write (.write _ _ _) _ _ => rfl
  | .write .cur _ .fresh => rfl
  | .write .cur _ (.defVal _) => rfl

theorem heapRhs_eq_theory' : heapRhs = heapRhsT := by
  funext u s
  exact heapRhs_eq_theory u s

end Update
end Solidity
