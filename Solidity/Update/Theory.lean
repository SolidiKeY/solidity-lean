import Solidity.SemanticsProperties
import Solidity.Update.Eval
import Solidity.Theory.Memory

/-!
# A rule's memory update, read as a KeY term

`Rules.lean` states each terminal rule's update as first-order syntax —
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

end Update
end Solidity
