import Solidity.Calculus.Close
import Solidity.Calculus.MemRead
import Solidity.Calculus.StateParts
import Solidity.Calculus.SlotLemmas
import Solidity.Theory.Bridge.Denote
import Solidity.Typing.CanonTest

/-!
# Deciding the storage goals: `sol_decide`

`sol_close` (`Close.lean`) is a tactic: it proves what its `simp` set and
the facts the formula states reach, and a goal it leaves open may be valid.
Two storage keys the formula does not separate are the typical case:
`[ balances[k] = 5; balances[j] = 5; ] balances[k] == 5` is valid, since
either write leaves `5`, but no fact says `k = j` or `k ≠ j`.  A read below
a deleted struct is the other.  This module is mini-solkey's Chapter 15
(`Ch15_Decide`) for the storage fragment: the search replaced by a function,
and a proof that the function loses nothing.

* `Fml.toL` pushes the updates `sol_symex` leaves into the formula
  (mini-solkey's `Fml.applyUpds`).  A term here halts, so a box update's
  term becomes a premise that it returns and a diamond update's a conjunct;
  `Fml.toL_holds` is exact, halts included.
* `LFml.elim` turns every read of a write into a case tree over key
  equalities whose leaves read the initial storage only.  At each write the
  written path and the read one are compared from the root (`cmpSegs`,
  mini-solkey's four cases: equal, above, below, apart).  Each read is
  guarded by what makes it return — the writes under it succeed
  (`LStor.okE`) — and peeled one write at a time (`LStor.readU`, and
  `hasU`/`mapU` for whether a location, or a mapping, is there, `lenU` for
  an array's length: a `delete` empties a dynamic array and keeps a
  fixed-size one's length).
* `Fml.valid_iff_reduce`: `⊨ φ` exactly when `φ.reduce`, the two steps
  composed, holds in every state.  Every step is an equivalence.
* `sol_decide` (`DecideComplete.lean`) rewrites the goal by it, computes the
  reduction, and rewrites once more by `Fml.valid_iff_cons`: the reads of the
  starting storage free, under the constraints a storage puts on them.
  `sol_decide_heuristic`, here, is the finishing step without them.

What the storage adds to mini-solkey's words:

* **Halting.**  A term is a run of the interpreter; the reduction changes the
  order of the runs (a guard, then the read), so two terms are compared by
  what they return (`Sim`), which is all a formula sees.
* **Shapes.**  A read above a write finds a struct, an array or a mapping,
  which is no word; a read below a written word finds nothing.  A write
  succeeds exactly where a read of the same path does, an array's `length`
  aside (`save_ok_iff_find_ok`).
* **`delete`.**  At or below the deleted location, before any key, a read
  finds the default of what was there (`find_defaultOf`): `0` for a `uint`,
  `false` for a `bool`.  Below a key it finds the old entry when the location
  above the key is a mapping, and nothing when it is an array, which
  `delete` empties (`defaultOf_find_at`); the reduction guards such a read by
  a mapping test.

**No well-typed storage is assumed**, and none is needed for the
equivalence: it holds of every state, which is what `⊨` quantifies over.
The price is that a goal true only of well-typed storage is not valid:
`[ delete alice.account; ] alice.account.balance == 0` fails where the old
balance is a `bool` (`Examples/Tactics/Decide.lean`, `deleteWithoutWrite`), while the
same goal after a write of a `uint` is decided.

**Completeness.**  The reduction loses nothing, so `sol_decide` fails on an
invalid formula, as it should.  What it leaves reads a partial tree with
shapes, array bounds and lengths; the constraints between those reads, and
that every choice meeting them is a storage's (mini-solkey's
`LFml.valid_iff`), are `DecideComplete.lean`'s.

**Array bounds.**  The program checks an index where it takes a path
(`State.checkIndex`) and then reads or writes the slot, past the end
included; the target language reads and writes the live storage
(`SVal.findLive`, `SVal.saveLive`), where an index past the end halts.  The
two agree where the path is checked against the storage it reads, which is
what the fragment keeps to (`PTerm.toL_chk`, `live_bridge`).  Binding an
alias returns where its indices are in bounds (`guardPath`); an alias
through an index is checked then and not when used, so a write to the
storage leaves it stale (`SymB.onWrite`).  A stale alias keeps the
slot-level path it was bound to, as KeY's `consr(sp, at(i))` does: a write
or a push of a word through it is the slot-level node `LStor.stale`
(`STerm.toLS`), and a read through it is outside the fragment.  The slot
readers (`LStor.slotU`, `slotHasU`, `slotLenU`) see such a write where a
later `push()` recycles the slot it lands in.

**The fragment** (`Fml.inL`): no modality (run `sol_symex` first) but the
`⟨[ revert(); ]⟩` a branch's cover keeps (`Premise.coverFml`: `true` under
the box, `false` under the diamond), one
element per update, a local, an alias or the storage updated; an equation
as `eqD a b`, both sides defined (a bare `a ≐ b` compares the Theory
values, and a term that halts still denotes one: `Fml.eqDView`), or a bare
`a ≐ b` of a literal (or `msg.sender`) and a literal or a local, where the
two readings agree (`Term.eqLit`: the branch condition `se1 ≐ true` of an
`if`); literals, values of the transaction (`msg.sender`, which no update
changes: `Rel.tx`), locals, operators, conditionals, reads of `storage` and an array's length
(`values.length`, `LStor.lenU`); one write of a value, one `delete`, one
`push` or `pop` (`LStor.arr`), or one copy of a subtree of `storage`
(`alice = bob;`, `LStor.copy`) over `storage` per update; every alias bound by an update
and, through an index, used before the next write to the storage; a storage
variable bound to the storage (`old` of a specification, read as a snapshot:
`LTerm.findP`); a ledger entry or a payment (`transfer`'s), which no term of
the fragment reads; a quantifier over a local the updates before it do not
read (`LFml.all`, a specification's `\forall`).  Memory is in it as solkey
writes it (`LMem`): `memory`, its allocations (an identity only in the pair
that allocates it, `pairL`, or as the reference a `delete` writes,
`freshRef`), a copy from storage in its pair (`pairMem`), and writes,
within `memSize` of them, and the reads the clauses of
`Calculus/MemRead.lean` resolve; a write of a memory object into storage
(`alice = carol;`), as a copy of its view (`memL`, `LStor.view`), where the
memory's and the identity's guards are literals.  Outside it: a `push` of a
memory object, a read of the ledger (`net(a)`).  Of the gaps `Close.lean`
lists, this closes the keys the formula does not separate, the reads below
a deleted struct, the memory defaults and the distinct allocations.

**Arrays and copies** are eliminated as far as the storage before them
says: a read below a pushed array compares its index with the old length
(`arrKey`); a read below a copy reads the source, through its members and
key by key (`copyKeys`, `overlay_findLive_fields`,
`overlay_findLive_nomap`); where the source is a view of memory, it reads
memory along the same path (`findOnCopy`), and the view has its own root
wherever it returns (`isViewRoot`).  The slot a `push()` of a struct or an array
recycles (`pushSlot`) is read where the storage just below says what it
holds (`LStor.slotU`): the element a `pop` of the same array removed,
cleared or kept, or the first element a `delete` of it cleared.  What is
kept whole, as a term over the written storage the closer cannot see into,
is that slot over any other write, and a read below a key of a copy where
the source has a mapping (a mapping met in both keeps the target's
entries).  Such a term is still exact; it only leaves the leaf to the
premises that mention it, or to the closer's typing of reads below a
push (`Facts.slotTy`, `Calculus/Closer.lean`).
-/

namespace Solidity

namespace Decide

open Semantics SemanticsProperties

/-! ## Memory, as solkey writes it

The updates' memory is an `LMem` over the initial one, written as solkey
writes it (`Calculus/DecideLang.lean`) and read by the clauses of
`Calculus/MemRead.lean`.  An allocation takes the next ordinal
(`LMem.nAlloc`, KeY's `freshIdp`) and is in the fragment where the kernel
decides that its default copies (`allocOk`); a memory longer than `memSize`
writes is left outside, since every read walks it.  Every clause is a
taclet of solkey's `memoryRules.key` or `structMemoryRules.key`, under
solkey's name: `docs/lean-key-rule-map.md` ("The closer's memory clauses")
pairs each with its interpreter lemma (`Calculus/MemNames.lean`) and the
`Theory/` lemma it transcribes. -/

section MemBase
open MemNames

/-- What returns exactly where `t` returns an integer: the index of `xs[t]`. -/
def isIntL (t : LTerm) : LTerm :=
  match t.ground? with
  | some (.int _) => .lit (.bool true)
  | _ => .kite t t (.lit (.bool true)) (.lit (.bool true))

/-- The ordinal the next allocation of the memory takes (`freshIdp`).  A
walk of the memory, not cached in `Sym`: `okU` recomputes it at each
allocation, O(W²) over at most `memSize` nodes. -/
def LMem.nAlloc : LMem → Nat
  | .init => 0
  | .addM m _ _ | .newArr m _ _ _ | .copySt m _ _ _ => m.nAlloc + 1
  | .write m _ _ _ => m.nAlloc

/-- A fresh `R` copies into memory: no mapping, and a well-formed default
(both decided by the kernel: `Ty.mapFree`, `Ty.okDeep`). -/
def allocOk (R : RefTy) : Bool := (Ty.ref R).mapFree && (Ty.ref R).okDeep

/-- The most writes and allocations a leaf's memory may hold: each read of
memory walks them (`LMem.readT`), so the translation costs their number
times the reads.  The bound is enforced where the memory is built, so the
translation never walks a longer one: `UpdElem.toL` of a memory and `pairL`
refuse a memory past it, before any read (`fitsClose` runs before `inL`).
`TestSuite` needs at most 9. -/
def memSize : Nat := 400

/-- The memory holds at most `n` writes and allocations. -/
def LMem.within : Nat → LMem → Bool
  | _, .init => true
  | 0, _ => false
  | n + 1, .addM m _ _ | n + 1, .newArr m _ _ _ | n + 1, .copySt m _ _ _
  | n + 1, .write m _ _ _ => m.within n

/-- The allocations of a memory's run, in order; none where it halts. -/
def LMem.births (σ : State) (M : LMem) : Births :=
  match M.run σ with
  | .ok r => r.2
  | .error _ => []

theorem LMem.births_of_run {σ μ : State} {M : LMem} {B : Births} (h : M.run σ = .ok (μ, B)) :
    M.births σ = B := by
  simp only [LMem.births, h]


/-- **`mapFree` decides `tyHasMapping`** on the structs `mapFreeStructs`
lists, checked once each: the kernel evaluates the first, not the second
(well-founded through `structDef`). -/
theorem _root_.Solidity.Ty.mapFree_sound : ∀ {T : Ty}, T.mapFree = true → tyHasMapping T = false
  | .prim _, _ => by rw [tyHasMapping]
  | .ref (.mapping ..), h => by simp only [Ty.mapFree, Bool.false_eq_true] at h
  | .ref (.struct s), h => by
    simp only [Ty.mapFree, mapFreeStructs, List.mem_cons, List.not_mem_nil, or_false,
      decide_eq_true_eq] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
    all_goals simp only [tyHasMapping, structDef, String.reduceEq, imp_self, fieldsHaveMapping,
      Bool.or_self]
  | .ref (.array e), h => by
    rw [tyHasMapping]; exact Ty.mapFree_sound (by simpa only [Ty.mapFree] using h)
  | .ref (.fixed e _), h => by
    rw [tyHasMapping]; exact Ty.mapFree_sound (by simpa only [Ty.mapFree] using h)

/-- The value copies into memory: `copyStToM` returns, in one state and so
in every one (`copyStToM_ok_any`). -/
def Cps (v : SVal) : Prop := ∃ σ r, copyStToM σ v = .ok r

theorem Cps.at {v : SVal} (h : Cps v) (σ : State) : ∃ r, copyStToM σ v = .ok r := by
  obtain ⟨σ', r, h⟩ := h
  exact copyStToM_ok_any v σ' σ r h

theorem copyStFields_ok_iff : ∀ (fs : List (Name × SVal)) (σ : State),
    (∃ r, copyStFields σ fs = .ok r) ↔ ∀ p ∈ fs, Cps p.2
  | [], σ => iff_of_true ⟨_, rfl⟩ fun _ h => nomatch h
  | (n, w) :: rest, σ => by
    rw [List.forall_mem_cons]
    constructor
    · rintro ⟨r, h⟩
      obtain ⟨σ₁, mv, mrest, h1, h2, -⟩ := copyStFields_cons_inv (τ := r.1) (mfs := r.2) h
      exact ⟨⟨σ, _, h1⟩, (copyStFields_ok_iff rest σ₁).1 ⟨_, h2⟩⟩
    · rintro ⟨hw, hr⟩
      obtain ⟨⟨σ₁, mv⟩, h1⟩ := hw.at σ
      obtain ⟨⟨τ, mrest⟩, h2⟩ := (copyStFields_ok_iff rest σ₁).2 hr
      exact ⟨_, by rw [copyStFields, h1, Res.ok_bind']; dsimp only; rw [h2]; rfl⟩

theorem copyStElems_ok_iff : ∀ (es : List SVal) (σ : State),
    (∃ r, copyStElems σ es = .ok r) ↔ ∀ x ∈ es, Cps x
  | [], σ => iff_of_true ⟨_, rfl⟩ fun _ h => nomatch h
  | w :: rest, σ => by
    rw [List.forall_mem_cons]
    constructor
    · rintro ⟨r, h⟩
      obtain ⟨σ₁, mv, mrest, h1, h2, -⟩ := copyStElems_cons_inv (τ := r.1) (mes := r.2) h
      exact ⟨⟨σ, _, h1⟩, (copyStElems_ok_iff rest σ₁).1 ⟨_, h2⟩⟩
    · rintro ⟨hw, hr⟩
      obtain ⟨⟨σ₁, mv⟩, h1⟩ := hw.at σ
      obtain ⟨⟨τ, mrest⟩, h2⟩ := (copyStElems_ok_iff rest σ₁).2 hr
      exact ⟨_, by rw [copyStElems, h1, Res.ok_bind']; dsimp only; rw [h2]; rfl⟩

theorem Cps.struct_iff (fs : List (Name × SVal)) : Cps (.struct fs) ↔ ∀ p ∈ fs, Cps p.2 := by
  constructor
  · rintro ⟨σ, r, h⟩
    obtain ⟨τ₁, mfs, hf, -, -⟩ := copyStToM_struct_inv (τ := r.1) (mv := r.2) h
    exact (copyStFields_ok_iff fs σ).1 ⟨_, hf⟩
  · intro h
    obtain ⟨⟨τ, mfs⟩, hf⟩ := (copyStFields_ok_iff fs { storage := [] }).2 h
    exact ⟨{ storage := [] }, _, by rw [copyStToM, hf]; rfl⟩

theorem Cps.array_iff (es sh : List SVal) (fx : Bool) : Cps (.array es sh fx) ↔ ∀ x ∈ es, Cps x := by
  constructor
  · rintro ⟨σ, r, h⟩
    obtain ⟨τ₁, mes, he, -, -⟩ := copyStToM_array_inv (τ := r.1) (mv := r.2) h
    exact (copyStElems_ok_iff es σ).1 ⟨_, he⟩
  · intro h
    obtain ⟨⟨τ, mes⟩, he⟩ := (copyStElems_ok_iff es { storage := [] }).2 h
    exact ⟨{ storage := [] }, _, by rw [copyStToM, he]; rfl⟩

theorem Cps.not_map (e : List (Int × SVal)) (d : SVal) : ¬ Cps (.map e d) :=
  fun ⟨_, r, h⟩ => (copyStToM_map_inv (τ := r.1) (mv := r.2) h).elim

theorem seq_rets (σ : State) (d a : LTerm) :
    Rets ((LTerm.seq d a).eval σ) ↔ Rets (d.eval σ) ∧ Rets (a.eval σ) := by
  constructor
  · rintro ⟨v, h⟩
    obtain ⟨x, hx, ha⟩ := Res.bind_eq_ok.1 h
    exact ⟨⟨x, hx⟩, ⟨v, ha⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨v, ha⟩⟩
    exact ⟨v, by simp only [LTerm.eval, hx, Res.ok_bind, ha]⟩

theorem lit_rets (σ : State) (v : Value) : Rets ((LTerm.lit v).eval σ) := ⟨v, rfl⟩

/-- A run's births are as many as its allocations. -/
theorem LMem.run_nAlloc (σ : State) : (m : LMem) → ∀ {μ : State} {B : Births},
    m.run σ = .ok (μ, B) → B.length = m.nAlloc
  | .init, μ, B, h => by
    simp only [LMem.run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  | .addM m k R, μ, B, h => by
    obtain ⟨μ', B', id, hr, -, -, rfl⟩ := LMem.run_addM h
    simp only [List.length_append, List.length_singleton, LMem.nAlloc, LMem.run_nAlloc σ m hr]
  | .newArr m k R n, μ, B, h => by
    obtain ⟨μ', B', id, c, hr, -, -, -, rfl⟩ := LMem.run_newArr h
    simp only [List.length_append, List.length_singleton, LMem.nAlloc, LMem.run_nAlloc σ m hr]
  | .copySt m k s q, μ, B, h => by
    obtain ⟨μ', B', id, hr, -, -, rfl⟩ := LMem.run_copySt h
    simp only [List.length_append, List.length_singleton, LMem.nAlloc, LMem.run_nAlloc σ m hr]
  | .write m j b v, μ, B, h => by
    obtain ⟨μ', n', ad, mv, hr, -⟩ := LMem.run_write h
    exact LMem.run_nAlloc σ m hr

theorem copy_ref {σ τ : State} {v : SVal} {mv : MVal} (h : copyStToM σ v = .ok (τ, mv))
    (hv : ∀ p, v ≠ .prim p) : ∃ id, mv = .ref id := by
  cases v with
  | prim p => exact absurd rfl (hv p)
  | struct fs =>
    obtain ⟨τ₁, _, _, _, rfl⟩ := copyStToM_struct_inv h
    exact ⟨_, rfl⟩
  | array es sh fx =>
    obtain ⟨τ₁, _, _, _, rfl⟩ := copyStToM_array_inv h
    exact ⟨_, rfl⟩
  | map e d => exact (copyStToM_map_inv h).elim

theorem defaultForTy_ref_ne (R : RefTy) (p : PrimVal) : defaultForTy (.ref R) ≠ .prim p := by
  cases R <;> simp only [defaultForTy, ne_eq, reduceCtorEq, not_false_eq_true]

theorem Cps.default {T : Ty} (hm : T.mapFree = true) (hd : T.okDeep = true) :
    Cps (defaultForTy T) := by
  obtain ⟨τ, mv, h⟩ := copyStToM_ok_noMap { storage := [] } (defaultForTy T) T
    (defaultForTy_canonB hd) (Ty.mapFree_sound hm)
  exact ⟨_, _, h⟩

theorem allocOk_cps {R : RefTy} (h : allocOk R = true) : Cps (defaultForTy (.ref R)) := by
  simp only [allocOk, Bool.and_eq_true] at h
  exact Cps.default h.1 h.2

theorem allocOk_newArr {R : RefTy} (h : allocOk R = true) (c : Int) :
    Cps (newArrVal R c) ∧ ∀ p, newArrVal R c ≠ .prim p := by
  cases R with
  | array E =>
    simp only [allocOk, Bool.and_eq_true, Ty.mapFree, Ty.okDeep] at h
    refine ⟨(Cps.array_iff _ _ _).2 fun x hx => ?_, fun p => by
      simp only [newArrVal, ne_eq, reduceCtorEq, not_false_eq_true]⟩
    rw [List.eq_of_mem_replicate hx]
    exact Cps.default h.1 h.2
  | struct _ | fixed _ _ | mapping _ _ => exact ⟨allocOk_cps h, defaultForTy_ref_ne _⟩

end MemBase


/-! ## Pushing the updates in

`sol_symex` leaves `{U₁} … {Uₙ} φ`.  Each update is pushed into what follows
it: a local becomes the term it was bound to, an alias the path, `storage`
the stack of writes.  Under the box the update's own term becomes a
premise, under the diamond a conjunct: a run that halts proves every box
formula and no diamond one, and `eq t t` says exactly that `t` returns.
This is mini-solkey's `Fml.applyUpds` (Chapter 14), and here it is exact,
halts included. -/

/-- What an update bound a name to. -/
inductive SymB where
  | val (t : LTerm)
  | path (q : LPath)
  /-- An alias through an index, bound before the storage last changed: it
  was checked against a storage that is gone.  It keeps its slot-level path
  `q`, as KeY's `consr(sp, at(i))` does: a write through it is a slot-level
  write (`STerm.staleWrite?`), a read through it is outside the fragment. -/
  | stale (q : LPath)
  /-- A storage variable bound to a storage: `old` of `{ old := storage }`. -/
  | stor (s : LStor)
  /-- A memory local bound to the object a name denotes. -/
  | mref (i : LId)
  deriving Inhabited

/-- The updates so far: the names bound, newest first, the storage, and the
memory. -/
structure Sym where
  env : List (Var × SymB)
  stor : LStor
  mem : LMem := .init

/-- No update yet. -/
def Sym.empty : Sym := ⟨[], .init, .init⟩

variable {C : Contract}

/-- A path whose key is not an integer: what an alias bound to a value
resolves to. -/
def LPath.stuck : LPath := .at (.root "") .err

/-- What a storage write stores: a word, or the subtree at a path of a
storage (`alice = bob;`). -/
inductive LVal where
  | word (t : LTerm)
  | sub (s : LStor) (q : LPath)
  /-- `new R(n)`'s value, copied into memory. -/
  | arr (R : RefTy) (n : LTerm)
  /-- The object `i` of the memory `m`, copied back (`copyMem`). -/
  | mem (m : LMem) (i : LId)
  deriving Inhabited

/-- What a storage write takes: a word, a subtree, or a memory object (its
view), not a fresh array. -/
def LVal.storable : LVal → Bool
  | .word _ | .sub _ _ | .mem _ _ => true
  | .arr _ _ => false

/-- What `toL` gives at each sort: a value an `LTerm`, a path an `LPath`, a
storage an `LStor`, a stored value an `LVal`; a memory sort its symbolic
reading with the term that returns exactly where it does (none outside the
fragment): an identity the name of an object (`LId`), an address the name
and what selects in it, a memory the writes and allocations (`LMem`), a
memory value what the slot holds. -/
@[reducible] def _root_.Solidity.Srt.LTy : Srt → Type
  | .val => LTerm
  | .path => LPath
  | .st => LStor
  | .sv => LVal
  | .ident => Option (LId × LTerm)
  | .addr => Option (LId × LSel × LTerm)
  | .mem => Option (LMem × LTerm)
  | .mv => Option (LMV × LTerm)

/-- A constant with the updates `ρ` pushed in. -/
def _root_.Solidity.Op0.toL (ρ : Sym) : Op0 s → s.LTy
  | .lit v => key{ lit(v) }
  | .env k => key{ env(k) }
  | .root r => .root r
  | .storage => ρ.stor
  | .memory => some (ρ.mem, key{ true })

/-- A unary symbol over its argument's `toL`. -/
def _root_.Solidity.Op1.toL : Op1 a s → a.LTy → s.LTy
  | .unop op p, x => LTerm.mkUn op p x
  | .net, _ => .err
  | .netOf _, _ => .err
  | .delValue, _ => .err
  | .field f, x => key{ x.f }
  | .next, _ => .stuck
  | .select _, _ => .init
  | .sval, x => .word x
  | .newArr R, x => .arr R x
  | .alloc _, _ => none
  | .mfield f, i => i.map fun p => (p.1, .fld f, p.2)
  | .addM R, m => m.bind fun p =>
    if allocOk R then some (key{ addM(‹p.1›, shaped(‹p.1.nAlloc›, R)) }, p.2) else none
  | .mval, x => some (.word x, x)
  | .ref, i => i.map fun p => (.ref p.1, p.2)
  | .wt _, _ => .err

/-- `read(m, a)` pushed in: the memory's guard, the address's, then the word
`LMem.readT` finds (`readOnWrite`, `readOnAddM`); none where it finds none. -/
def readM : Option (LMem × LTerm) → Option (LId × LSel × LTerm) → Option LTerm
  | some (M, g), some (j, sel, g') => (M.readT j sel).map fun r => seqL g (seqL g' r)
  | _, _ => none

/-- `mlen(m, i)` pushed in: the length `LMem.lenT` finds (`initSize`). -/
def lenM : Option (LMem × LTerm) → Option (LId × LTerm) → Option LTerm
  | some (M, g), some (j, g') => (M.lenT j).map fun r => seqL g (seqL g' r)
  | _, _ => none

/-- `read(m, a)` of a reference slot pushed in: the name `LMem.readI` finds
(`initIdentity`), guarded by the test that it denotes an object. -/
def ireadM : Option (LMem × LTerm) → Option (LId × LSel × LTerm) → Option (LId × LTerm)
  | some (M, g), some (j, sel, g') =>
    (M.readI j sel).bind fun j' => (M.nameG j').map fun n => (j', seqL g (seqL g' n))
  | _, _ => none

/-- `copySt(m, new R(n))` pushed in: one node (`memoryArrayFreshAlloc`), at
the next ordinal, where `R`'s default copies; `n` must be an integer. -/
def newM : Option (LMem × LTerm) → LVal → Option (LMem × LTerm)
  | some (M, g), .arr R n =>
    if allocOk R then
      some (key{ write(addM(M, shaped(‹M.nAlloc›, R)), idC(‹M.nAlloc›, nil), size, n) },
        seqL g (isIntL n))
    else none
  | _, _ => none

/-- `write(m, a, v)` pushed in: the value's guard, the memory's, the
address's, then the write's own (`LMem.writeG`: a member of a struct, an
element below the length). -/
def writeM : Option (LMem × LTerm) → Option (LId × LSel × LTerm) → Option (LMV × LTerm) →
    Option (LMem × LTerm)
  | some (M, g), some (j, sel, g'), some (w, g'') =>
    (M.writeG j sel).map fun gw => (key{ write(M, j, sel, w) }, seqL g'' (seqL g (seqL g' gw)))
  | _, _, _ => none

/-- `copyMem(m, i)` pushed in: the object `i` names in `m`, read as storage
through its view (`LStor.view`), where both guards are literals.  A view
keeps no guard of its own, so a guard that may halt leaves the copy outside
the fragment. -/
def memL : Option (LMem × LTerm) → Option (LId × LTerm) → Option LVal
  | some (M, key{ lit(_) }), some (j, key{ lit(_) }) => some (.mem M j)
  | _, _ => none

theorem memL_getD (x : Option (LMem × LTerm)) (y : Option (LId × LTerm)) :
    (memL x y).getD (.word .err) = .word .err ∨
      ∃ M j, (memL x y).getD (.word .err) = .mem M j := by
  unfold memL
  split
  · exact .inr ⟨_, _, rfl⟩
  · exact .inl rfl

theorem memL_some {M : LMem} {g : LTerm} {j : LId} {g' : LTerm}
    (h : (memL (some (M, g)) (some (j, g'))).isSome = true) :
    (∃ c, g = .lit c) ∧ ∃ c', g' = .lit c' := by
  cases g <;> cases g' <;> first
    | exact ⟨⟨_, rfl⟩, _, rfl⟩
    | simp only [memL, Option.isSome_none, Bool.false_eq_true] at h

theorem newM_memL (m x : Option (LMem × LTerm)) (y : Option (LId × LTerm)) :
    newM m ((memL x y).getD (.word .err)) = none := by
  rcases memL_getD x y with h | ⟨M, j, h⟩ <;> rw [h] <;> rcases m with _ | ⟨_, _⟩ <;> rfl

/-- A binary symbol over its arguments' `toL`. -/
def _root_.Solidity.Op2.toL : Op2 a b s → a.LTy → b.LTy → s.LTy
  | .binop op p, x, y => LTerm.mkBin op p x y
  | .find, x, y => key{ find(x, y) }
  | .len, x, y => key{ find(x, y.length) }
  | .read, m, a => (readM m a).getD .err
  | .mlen, m, i => (lenM m i).getD .err
  | .at, x, y => key{ x[y] }
  | .nextIn, _, _ => .stuck
  | .delAt, x, y => key{ delAt(x, y) }
  | .pushSlot E, x, y => key{ arr(slot(E), x, y, true) }
  | .pop, x, y => key{ arr(pop(false), x, y, true) }
  | .shrink, x, y => key{ arr(pop(true), x, y, true) }
  | .extend E, x, y => key{ arr(slot(E), x, y, true) }
  | .sfind, x, y => .sub x y
  | .copyMem, m, i => (memL m i).getD (.word .err)
  | .iread, m, a => ireadM m a
  | .copy, _, _ => none
  | .mat, i, t => i.map fun p => (p.1, key{ at(t) }, seqL p.2 (isIntL t))
  | .copySt, m, v => newM m v

/-- A ternary symbol over its arguments' `toL`. -/
def _root_.Solidity.Op3.toL : Op3 a b c s → a.LTy → b.LTy → c.LTy → s.LTy
  | .ite, x, y, z => key{ if(x) then y else z }
  | .save, x, y, .word t => key{ save(x, y, t) }
  | .save, x, y, .sub s q => key{ save(x, y, find(s, q)) }
  | .save, x, y, .mem m i => key{ save(x, y, copyMem(mtSt, m, i)) }
  | .save, x, _, .arr _ _ => x
  | .push, x, y, .word t => key{ push(x, y, t) }
  | .push, x, y, .sub s q =>
    key{ save(arr(slot(‹.uint›), x, y, true), y[find(x, y.length)], find(s, q)) }
  | .push, x, _, .arr _ _ | .push, x, _, .mem _ _ => x
  | .atIn, _, _, _ => .stuck
  | .write, m, a, v => writeM m a v

/-- The type `addM(memory)` allocates. -/
def addMOf? : MTerm C → Option RefTy
  | MTerm.addM MTerm.memory R => some R
  | _ => none

/-- The type `freshId(addM(memory))`, written as a reference, allocates. -/
def allocRefOf? : MValT C → Option RefTy
  | MValT.ref (ITerm.alloc MTerm.memory R) => some R
  | _ => none

/-- The value of `write(addM(memory), a, freshId(addM(memory)))`, a
reference member deleted (`memoryFieldDeleteReference`): the root the
allocation under the write takes, the next ordinal.  Elsewhere `z`. -/
def freshRef (ρ : Sym) (m : MTerm C) (v : MValT C) (z : Option (LMV × LTerm)) :
    Option (LMV × LTerm) :=
  match addMOf? m, allocRefOf? v with
  | some R, some R' =>
    if R = R' then some (.ref key{ idC(‹ρ.mem.nAlloc›, nil) }, key{ true }) else z
  | _, _ => z

/-- A ternary symbol over its arguments' `toL`, a write of a fresh root
apart (`freshRef`). -/
def _root_.Solidity.Op3.toLAt (ρ : Sym) : Op3 a b c s → Tm C a → Tm C c → a.LTy → b.LTy → c.LTy →
    s.LTy
  | .write, m, v, x, y, z => writeM x y (freshRef ρ m v z)
  | o, _, _, x, y, z => o.toL x y z

/-- The path has no index: `alice.account`, not `people[i]`. -/
def LPath.noAt : LPath → Bool
  | .root _ => true
  | .field q _ => q.noAt
  | .at _ _ => false

/-- The path up to its last index: `people[i]` of `people[i].age`; none for
`alice.account`. -/
def LPath.lastAt : LPath → Option LPath
  | .root _ => none
  | .field q _ => q.lastAt
  | .at q k => some (.at q k)

/-- What makes binding an alias to `q` return, in the storage `s`: its keys
return, and every index on it is in bounds where the program checks it
(`State.checkIndex`), which is the location up to the last index being there
(`LStor.hasU`). -/
def guardPath (s : LStor) (q : LPath) : LTerm :=
  match q.lastAt with
  | none => .pok q
  | some q' => .seq (.pok q) (.has s q')

/-- The storage a storage variable is bound to: `old` of `{ old := storage }`. -/
def _root_.Solidity.Tm.storLocal? (ρ : Sym) : Tm C .st → Option LStor
  | .pvS x =>
    match lookupBy x ρ.env with
    | some (.stor s) => some s
    | _ => none
  | _ => none

/-- A binary symbol over its arguments' `toL`, a read of a storage variable
apart: `find(old, p)` is the path checked against the storage the updates
left (`guardPath`), then the snapshot read there (`LTerm.findP`), as the
program's read is. -/
def _root_.Solidity.Op2.toLAt (ρ : Sym) : Op2 a b s → Tm C a → a.LTy → b.LTy → s.LTy
  | .find, t, x, y =>
    match t.storLocal? ρ with
    | some st => .seq (guardPath ρ.stor y) (.findP st y)
    | none => .find x y
  | o, _, x, y => o.toL x y

theorem _root_.Solidity.Tm.storLocal?_isSome {ρ : Sym} {s : Tm C .st}
    (h : (s.storLocal? ρ).isSome = true) :
    ∃ x S, s = .pvS x ∧ lookupBy x ρ.env = some (.stor S) := by
  unfold Tm.storLocal? at h
  split at h
  · rename_i x
    split at h
    · rename_i S hl
      exact ⟨x, S, rfl, hl⟩
    · simp only [Option.isSome_none, Bool.false_eq_true] at h
  · simp only [Option.isSome_none, Bool.false_eq_true] at h

/-- A term with the updates `ρ` pushed in: after `{ y := find(storage,
balances[k]) }`, `y` is that read; after `{ sp1 := alice.account }`,
`sp1.balance` is `alice.account.balance`; after `{ storage := save(storage,
balances[k], 5) }`, `storage` is that write. -/
def _root_.Solidity.Tm.toL (ρ : Sym) : Tm C s → s.LTy
  | .pvV x =>
    match lookupBy x ρ.env with
    | some (.val t) => t
    | some (.path _) | some (.stale _) | some (.stor _) | some (.mref _) => .err
    | none => .var x
  | .pvP x =>
    match lookupBy x ρ.env with
    | some (.path q) => q
    | _ => .stuck
  | .pvS _ => .init
  | .pvI x =>
    match lookupBy x ρ.env with
    | some (.mref i) => some (i, .lit (.bool true))
    | _ => none
  | .app0 o => o.toL ρ
  | .app1 o a => o.toL (a.toL ρ)
  | .app2 o a b => Op2.toLAt ρ o a (a.toL ρ) (b.toL ρ)
  | .app3 o a b c => Op3.toLAt ρ o a c (a.toL ρ) (b.toL ρ) (c.toL ρ)

/-- A write to the storage leaves an alias through an index stale: the
program checked it against the storage before. -/
def SymB.onWrite : SymB → SymB
  | .path q => if q.noAt then .path q else .stale q
  | b => b

/-- The locals a symbol reads. -/
def SymB.vars : SymB → List Var
  | .val t => t.vars
  | .path q => q.vars
  | .stale q => q.vars
  | .stor s => s.vars
  | .mref _ => []

/-- The locals the updates so far read: a quantifier may bind none of them. -/
def Sym.vars (ρ : Sym) : List Var :=
  ρ.stor.vars ++ ρ.env.flatMap (fun b => b.2.vars) ++ ρ.mem.vars

/-- The updates so far, with `x` free again: bound by a quantifier, `x` is
the local itself. -/
def Sym.free (ρ : Sym) (x : Var) : Sym := { ρ with env := (x, .val (.var x)) :: ρ.env }

/-- The storage the updates left, `storage`. -/
def _root_.Solidity.Tm.isStorage : Tm C s → Bool
  | STerm.storage => true
  | _ => false

theorem _root_.Solidity.STerm.isStorage_eq {s : STerm C} (h : s.isStorage = true) :
    s = .storage := by
  unfold Tm.isStorage at h
  split at h
  · rfl
  · cases h

/-- A constant in the fragment: a literal, a value of the transaction, a
root, `storage`. -/
def _root_.Solidity.Op0.inL : Op0 s → Bool
  | .lit _ | .env _ | .root _ | .storage | .memory => true

/-- A unary symbol in the fragment, its argument in it (`hb`); an
allocation where its default copies (`allocOk`).  The identity an allocation
takes only with it (`allocPair?`, `freshRef`). -/
def _root_.Solidity.Op1.inL : Op1 a s → a.LTy → Bool → Bool
  | .unop .., _, hb | .field _, _, hb | .sval, _, hb => hb
  | .newArr _, _, hb | .mfield _, _, hb | .mval, _, hb | .ref, _, hb => hb
  | .addM R, x, hb => hb && Option.isSome (Op1.toL (.addM R) x)
  | _, _, _ => false

/-- A name a reference slot holds, of an object the memory before the update
already has: so it denotes the same object in every memory the update
builds over it. -/
def irOk (ρ : Sym) : Option (LId × LTerm) → Bool
  | some (j, _) => decide (j.root < ρ.mem.nAlloc)
  | none => false

/-- A binary symbol in the fragment, its arguments in it (`ha`, `hb`); a
read or a delete is of `storage` itself; a read of memory where the clauses
find what it reads. -/
def _root_.Solidity.Op2.inL (ρ : Sym) : Op2 a b s → Tm C a → a.LTy → b.LTy → Bool → Bool → Bool
  | .binop .., _, _, _, ha, hb | .at, _, _, _, ha, hb => ha && hb
  | .find, s, _, _, _, hb => (s.isStorage || (s.storLocal? ρ).isSome) && hb
  | .len, s, _, _, _, hb | .delAt, s, _, _, _, hb | .sfind, s, _, _, _, hb => s.isStorage && hb
  | .pushSlot _, s, _, _, _, hb | .extend _, s, _, _, _, hb | .pop, s, _, _, _, hb
  | .shrink, s, _, _, _, hb =>
    s.isStorage && hb
  | .read, _, x, y, ha, hb => ha && hb && (readM x y).isSome
  | .mlen, _, x, y, ha, hb => ha && hb && (lenM x y).isSome
  | .mat, _, _, _, ha, hb => ha && hb
  | .iread, _, x, y, ha, hb => ha && hb && irOk ρ (ireadM x y)
  | .copySt, _, x, y, ha, hb => ha && hb && (newM x y).isSome
  | .copyMem, _, x, y, ha, hb => ha && hb && (memL x y).isSome
  | _, _, _, _, _, _ => false

/-- A ternary symbol in the fragment: a conditional, or a write or a push
over `storage` itself; a push of a word; a write of memory where its guard
is found, its value in the fragment or a fresh root (`freshRef`). -/
def _root_.Solidity.Op3.inL (ρ : Sym) : Op3 a b c s → Tm C a → Tm C c → a.LTy → b.LTy → c.LTy →
    Bool → Bool → Bool → Bool
  | .ite, _, _, _, _, _, hc, ha, hb => hc && ha && hb
  | .save, s, _, _, _, z, _, hp, hv => s.isStorage && hp && hv && z.storable
  | .push, s, .app1 .sval _, _, _, _, _, hp, hv | .push, s, .app2 .sfind _ _, _, _, _, _, hp, hv =>
    s.isStorage && hp && hv
  | .write, m, v, x, y, z, hm, ha, hv =>
    hm && ha && (hv || (freshRef ρ m v none).isSome) && (writeM x y (freshRef ρ m v z)).isSome
  | _, _, _, _, _, _, _, _, _ => false

/-- The fragment: storage, and memory as the updates write it, every alias
bound by an update.  A read is of the storage the updates left, `find(storage, p)`: its
path is checked against that storage, and read there.  A path's alias only
where an update bound it (`Person storage p = alice;` does), and to a path
with no index.  A storage: one write, one `delete`, one `push` of a word or
`push()`, or one `pop`, over the storage the updates left.  A storage
variable (`old`) bound by an update, read at a path the storage the updates
left checks.  A stored value: a word, or a copy of a subtree of the storage
the updates left (`alice = bob;`).  A memory: `memory`, an allocation, a
write; a read of it where its clauses find the word, the name or the length
(`readM`, `ireadM`, `lenM`). -/
def _root_.Solidity.Tm.inL (ρ : Sym) : Tm C s → Bool
  | .pvV _ => true
  | .pvP x =>
    match lookupBy x ρ.env with
    | some (.path _) | some (.val _) => true
    | some (.stale _) | some (.stor _) | some (.mref _) | none => false
  | .pvS _ => false
  | .pvI x =>
    match lookupBy x ρ.env with
    | some (.mref _) => true
    | _ => false
  | .app0 o => o.inL
  | .app1 o a => o.inL (a.toL ρ) (a.inL ρ)
  | .app2 o a b => o.inL ρ a (a.toL ρ) (b.toL ρ) (a.inL ρ) (b.inL ρ)
  | .app3 o a b c => o.inL ρ a c (a.toL ρ) (b.toL ρ) (c.toL ρ) (a.inL ρ) (b.inL ρ) (c.inL ρ)


/-- A unary symbol of `sameShape`: `¬`, a member. -/
def _root_.Solidity.Op1.shape : Op1 a s → Bool → Bool
  | .unop .., b | .field _, b => b
  | _, _ => false

/-- A storage variable: `old`. -/
def _root_.Solidity.Tm.isPvS : Tm C .st → Bool
  | .pvS _ => true
  | _ => false

/-- A binary symbol of `sameShape`: an operator, an index, a read of `storage`
or of a storage variable. -/
def _root_.Solidity.Op2.shape : Op2 a b s → Tm C a → Bool → Bool → Bool
  | .binop .., _, x, y | .at, _, x, y => x && y
  | .find, s, _, y => (s.isStorage || s.isPvS) && y
  | .len, s, _, y => s.isStorage && y
  | _, _, _, _ => false

/-- The terms `sameL` compares: literals, values of the transaction, locals,
operators, conditionals and reads of `storage`, over paths of roots, aliases,
members and indices. -/
def _root_.Solidity.Tm.sameShape : Tm C s → Bool
  | .pvV _ | .pvP _ => true
  | .pvS _ | .pvI _ => false
  | .app0 o => match o with
    | .lit _ | .env _ | .root _ => true
    | _ => false
  | .app1 o a => o.shape a.sameShape
  | .app2 o a b => o.shape a a.sameShape b.sameShape
  | .app3 o a b c => match o with
    | .ite => a.sameShape && b.sameShape && c.sameShape
    | _ => false

/-- The same term of the fragment, as a `Bool` the kernel computes: how
`Fml.inL` recognises `eqD a b` (`Fml.eqDView`).  Outside the fragment it is
`false`, which only narrows the fragment. -/
def _root_.Solidity.Tm.sameL (a b : Tm C s) : Bool := a.sameShape && decide (a = b)

/-- `eqD a b`, `defined a ∧ (defined b ∧ a = b)` (`Update.lean`), split at
its outer conjunction: the equation of the fragment.  A bare `a = b` reads
the Theory (`holds`), where a term that halts still denotes something, so
the fragment takes an equation only with both sides defined. -/
def _root_.Solidity.Fml.eqDView : Fml C → Fml C → Option (Term C × Term C)
  | .defined a, .and (.defined b) (.eq a' b') =>
    if a.sameL a' && b.sameL b' then some (a, b) else none
  | _, _ => none

/-- A literal or a local: a term whose Theory value is its value where it
returns, and no primitive where it halts (`Term.atom_equiv_prim`). -/
def _root_.Solidity.Term.isAtom : Term C → Bool
  | .lit _ | .pv _ => true
  | _ => false

/-- A literal, or a value of the transaction (`msg.sender`): a term that
returns one value, the same in every state the updates reach. -/
def _root_.Solidity.Term.isLitLike : Term C → Bool
  | .lit _ | .env _ => true
  | _ => false

/-- A total equation `a ≐ b` the fragment takes: a literal (or `msg.sender`)
against a literal or a local, `se1 ≐ true` of a symbolically executed `if`,
`msg.sender ≐ r` of a precondition.  There the total reading is the partial
one (`Fml.toL_holds`); `x ≐ y` of two unbound locals is not, since both
denote the empty struct. -/
def _root_.Solidity.Term.eqLit (a b : Term C) : Bool :=
  (a.isLitLike && b.isAtom) || (b.isLitLike && a.isAtom)

/-- What returns exactly where the amount `a` of a payment is not
negative: `a < 0 ? err : true`. -/
def payGuard (a : LTerm) : LTerm :=
  .ite (.binop .lt .uint a (.lit (.int 0))) .err (.lit (.bool true))

theorem payGuard_eval (σ : State) (a : LTerm) {y : Value} {j : Int} (ha : a.eval σ = .ok y)
    (hj : y.asInt = .ok j) : (payGuard a).eval σ =
      if j < 0 then .error .stuck else .ok (.bool true) := by
  cases y with
  | bool b => simp only [Value.asInt, reduceCtorEq] at hj
  | int n =>
    simp only [Value.asInt, Except.ok.injEq] at hj
    subst hj
    by_cases hn : n < 0 <;>
      simp only [payGuard, LTerm.eval, bind, Except.bind, ha, evalBinop, applyBinOp, Value.asInt,
          hn, decide_true, checkArith, pickBranch, ↓reduceIte, decide_false]

/-- The slot-level path of a stale alias, and of its members: `r.value`
after `{ r := tokens[0] }` and a write.  KeY's `consr(r, value)` keeps the
slot `at(0)` the alias was bound to, whether or not it is still live. -/
def _root_.Solidity.Tm.slotPath? (ρ : Sym) : Tm C u → Option LPath
  | .pvP x =>
    match lookupBy x ρ.env with
    | some (.stale q) => some q
    | _ => none
  | PTerm.field p f => (Tm.slotPath? ρ p).map fun q => key{ q.f }
  | _ => none

/-- A write through a stale alias: a word written (`storageFieldWriteSave`)
or pushed (`storagePushValueSave`) at its slot-level path. -/
def _root_.Solidity.STerm.staleWrite? (ρ : Sym) : STerm C → Option (Option AOp × LPath × Term C)
  | STerm.save STerm.storage p (SValT.val t) => (p.slotPath? ρ).map fun q => (none, q, t)
  | STerm.push STerm.storage p (SValT.val t) =>
    (p.slotPath? ρ).map fun q => (some .push, q, t)
  | _ => none

/-- A storage update pushed in: a write through a stale alias is the
slot-level node `LStor.stale`, any other as `toL` gives it. -/
def _root_.Solidity.STerm.toLS (ρ : Sym) (s : STerm C) : LStor :=
  match s.staleWrite? ρ with
  | some (op, q, t) => .stale op ρ.stor q (t.toL ρ)
  | none => s.toL ρ

/-- The storage updates `toLS` is exact on: a write through a stale alias
of a word in the fragment, or a storage `inL` admits. -/
def _root_.Solidity.STerm.inLS (ρ : Sym) (s : STerm C) : Bool :=
  match s.staleWrite? ρ with
  | some (_, _, t) => t.inL ρ
  | none => s.inL ρ

/-- One update: the term that has to return, and the names it binds. -/
def _root_.Solidity.UpdElem.toL (ρ : Sym) : UpdElem C → LTerm × Sym
  | .val x t => (t.toL ρ, { ρ with env := (x, .val (t.toL ρ)) :: ρ.env })
  | .path x p =>
    (guardPath ρ.stor (p.toL ρ), { ρ with env := (x, .path (p.toL ρ)) :: ρ.env })
  | .storage s =>
    (.sok (s.toLS ρ), { ρ with stor := s.toLS ρ, env := ρ.env.map fun b => (b.1, b.2.onWrite) })
  | .store x s => (.sok (s.toL ρ), { ρ with env := (x, .stor (s.toL ρ)) :: ρ.env })
  -- a ledger entry: it returns where the address and the amount are integers,
  -- which `kite` asks; the ledger itself is not pushed in (nothing reads it)
  | .net r _ a => (.kite (r.toL ρ) (a.toL ρ) (.lit (.bool true)) (.lit (.bool true)), ρ)
  -- a payment: the same, and the amount not negative
  | .pay r a => (.kite (r.toL ρ) (a.toL ρ) (payGuard (a.toL ρ)) (payGuard (a.toL ρ)), ρ)
  | .mref x i =>
    match i.toL ρ with
    | some (j, g) => (g, { ρ with env := (x, .mref j) :: ρ.env })
    | none => (.err, ρ)
  | .memory m =>
    match m.toL ρ with
    | some (M, g) => if M.within memSize then (g, { ρ with mem := M }) else (.err, ρ)
    | none => (.err, ρ)
  | .selfBalance .. | .saveNet .. => (.err, ρ)

/-- The memory an update leaves holds at most `memSize` writes and
allocations. -/
def memWithin : Option (LMem × LTerm) → Bool
  | some (M, _) => M.within memSize
  | none => false

/-- An update in the fragment: a local, an alias, the storage, a storage
variable bound to it, a ledger entry (`transfer`'s, which no term of the
fragment reads), a memory local bound to a name, or the memory (within
`memSize`); no funds. -/
def _root_.Solidity.UpdElem.inL (ρ : Sym) : UpdElem C → Bool
  | .val _ t => t.inL ρ
  | .path _ p => p.inL ρ
  | .storage s => s.inLS ρ
  | .store _ s => s.inL ρ
  | .net r _ a | .pay r a => r.inL ρ && a.inL ρ
  | .mref _ i => i.inL ρ
  | .memory m => m.inL ρ && memWithin (m.toL ρ)
  | .selfBalance .. | .saveNet .. => false

/-- `{x := freshId(addM(memory)) ‖ memory := addM(memory)}`, or the same of
`copySt(memory, v)`: the identity is the root the memory's allocation takes
(`memoryReferenceDeclFreshAlloc`, `memoryArrayFreshAlloc`).  The pair is
kept whole, one Skolem for KeY's `freshIdp`: the name exists only in the
memory after the allocation. -/
def allocPair? (i : ITerm C) (mm : MTerm C) : Bool :=
  match i, mm with
  | ITerm.alloc MTerm.memory R, MTerm.addM MTerm.memory R' => decide (R = R')
  | ITerm.copy MTerm.memory v, MTerm.copySt MTerm.memory v' => decide (v = v')
  | _, _ => false

/-- `copySt(memory, find(storage, p))`, a copy from storage
(`memoryStorageCopy`): its path. -/
def copyOf? : MTerm C → Option (PTerm C)
  | MTerm.copySt MTerm.memory (SValT.find STerm.storage p) => some p
  | _ => none

theorem copyOf?_some {mm : MTerm C} {p : PTerm C} (h : copyOf? mm = some p) :
    mm = .app2 .copySt (.app0 .memory) (.app2 .sfind (.app0 .storage) p) := by
  unfold copyOf? at h
  split at h
  · cases h
    rfl
  · cases h

/-- A copy from storage's guard (Lean only): the subtree copies, which
`copyStToM` refuses on a mapping, and is no word, so the copy is an object
(`readFromCopyToStorage` reads it). -/
def copyG (s : LStor) (q : LPath) : LTerm :=
  key{ (copyOk(s, q); if(‹isT key{ find(s, q) }›) then err else true) }

/-- The memory of an allocation's pair: a copy from storage is the node
`LMem.copySt` at the next ordinal, under `copyG`; any other memory as
`toL` gives it.  A copy from storage is in the fragment only in its pair,
where the identity's `asRef` refuses the word `copySt` alone would copy. -/
def pairMem (ρ : Sym) (mm : MTerm C) : Option (LMem × LTerm) :=
  match copyOf? mm with
  | some p =>
    some (key{ copySt(‹ρ.mem›, ‹ρ.mem.nAlloc›, find(‹ρ.stor›, ‹p.toL ρ›)) }, copyG ρ.stor (p.toL ρ))
  | none => mm.toL ρ

/-- The pair's memory in the fragment: a copy from storage at a path in
it, or a memory `inL` admits. -/
def pairIn (ρ : Sym) (mm : MTerm C) : Bool :=
  match copyOf? mm with
  | some p => p.inL ρ
  | none => mm.inL ρ

/-- A parallel update that is an allocation's pair: `x`, its identity and
the memory. -/
def pairView : UpdElem C → UpdElem C → List (UpdElem C) → Option (Var × ITerm C × MTerm C)
  | .mref x i, .memory mm, [] => some (x, i, mm)
  | _, _, _ => none

theorem pairView_some {e₁ e₂ : UpdElem C} {rest : List (UpdElem C)} {x : Var} {i : ITerm C}
    {mm : MTerm C} (h : pairView e₁ e₂ rest = some (x, i, mm)) :
    e₁ = .mref x i ∧ e₂ = .memory mm ∧ rest = [] := by
  unfold pairView at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

/-- The pair pushed in: the memory's guard, and `x` bound to the root of the
next ordinal. -/
def pairL (ρ : Sym) (x : Var) (i : ITerm C) (mm : MTerm C) : Option (LTerm × Sym) :=
  if allocPair? i mm then
    (pairMem ρ mm).bind fun p => if p.1.within memSize then
      some (p.2, { ρ with env := (x, .mref key{ idC(‹ρ.mem.nAlloc›, nil) }) :: ρ.env, mem := p.1 })
    else none
  else none

/-- The update's term as a premise (box) or a conjunct (diamond). -/
def guardM : Modality → LTerm → LFml → LFml
  | .box, g, φ => .imp (.eq g g) φ
  | .diamond, g, φ => .and (.eq g g) φ

/-- A program that starts with `revert();`: it halts, whatever follows. -/
def _root_.Solidity.Prog.reverts : Prog C → Bool
  | .revert :: _ => true
  | _ => false

theorem _root_.Solidity.Prog.reverts_eq {P : Prog C} (h : P.reverts = true) :
    ∃ ω, P = .revert :: ω := by
  unfold Prog.reverts at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

/-- A formula with its updates pushed in. -/
def _root_.Solidity.Fml.toL : Sym → Fml C → LFml
  | _, .tt => .tt
  | ρ, .eq a b => .eq (a.toL ρ) (b.toL ρ)
  | ρ, .defined t => .eq (t.toL ρ) (t.toL ρ)
  | ρ, .not φ => .not (φ.toL ρ)
  | ρ, .and φ ψ =>
    match Fml.eqDView φ ψ with
    | some (a, b) => .eq (a.toL ρ) (b.toL ρ)
    | none => .and (φ.toL ρ) (ψ.toL ρ)
  | ρ, .imp φ ψ => .imp (φ.toL ρ) (ψ.toL ρ)
  | ρ, .upd _ [] φ => φ.toL ρ
  | ρ, .upd m [e] φ => guardM m (e.toL ρ).1 (φ.toL (e.toL ρ).2)
  | ρ, .upd m (e₁ :: e₂ :: rest) φ =>
    match pairView e₁ e₂ rest with
    | some (x, i, mm) =>
      match pairL ρ x i mm with
      | some (g, ρ') => guardM m g (φ.toL ρ')
      | none => .tt
    | none => .tt
  | _, .modal .box _ _ => .tt
  | _, .modal .diamond _ _ => .not .tt
  | ρ, .all x p φ => .all x p (φ.toL (ρ.free x))
  | _, .havoc _ | _, .anon .. => .tt

/-- The fragment `Fml.toL` is exact on: no modality, one element per update
but an allocation's pair (`pairL`), and every alias bound by an update. -/
def _root_.Solidity.Fml.inL : Sym → Fml C → Bool
  | _, .tt => true
  | _, .eq a b => a.eqLit b
  | ρ, .defined t => t.inL ρ
  | ρ, .not φ => φ.inL ρ
  | ρ, .and φ ψ =>
    match Fml.eqDView φ ψ with
    | some (a, b) => a.inL ρ && b.inL ρ
    | none => φ.inL ρ && ψ.inL ρ
  | ρ, .imp φ ψ => φ.inL ρ && ψ.inL ρ
  | ρ, .upd _ [] φ => φ.inL ρ
  | ρ, .upd _ [e] φ => e.inL ρ && φ.inL (e.toL ρ).2
  | ρ, .upd _ (e₁ :: e₂ :: rest) φ =>
    match pairView e₁ e₂ rest with
    | some (x, i, mm) =>
      match pairL ρ x i mm with
      | some (_, ρ') => pairIn ρ mm && ρ'.mem.within memSize && φ.inL ρ'
      | none => false
    | none => false
  | _, .modal _ P _ => P.reverts
  | ρ, .all x _ φ => !ρ.vars.contains x && φ.inL (ρ.free x)
  | _, .havoc _ | _, .anon .. => false


/-! ### The updates pushed in keep the meaning -/

/-- The storage as one tree reads at `r.segs` what the storage reads at the
root `r`: `balances[k]` is `[balances, k]`. -/
theorem find_root (τ : State) (r : Name) (segs : List Seg) :
    (SVal.struct τ.storage).find (.field r :: segs) = τ.findStorage r segs := by
  simp only [SVal.find, State.findStorage]

/-- A write at the root `r` of the one tree is `saveStorage` at `r`:
`balances[k] = 5;` either way. -/
theorem save_root (τ : State) (r : Name) (segs : List Seg) (new : SVal) :
    (SVal.struct τ.storage).save (.field r :: segs) new =
      τ.saveStorage r segs new >>= fun τ' => .ok (.struct τ'.storage) := by
  simp only [SVal.save, State.saveStorage]
  cases hl : lookupBy r τ.storage with
  | none => rfl
  | some v =>
    simp only
    cases hs : v.save segs new <;> simp only [bind, Except.bind]

/-- A path up to its last index: `[people, at i]` of `[people, at i, age]`. -/
def lastAtSegs (qs : List Seg) : List Seg := (qs.reverse.dropWhile fun s => !Seg.isAt s).reverse

/-- Every index of the path is in bounds of what the storage holds live:
the location up to the last index is there, live.  What the program's checks
leave of a path it took (`PTerm.toL_chk`). -/
def LiveTo (T : SVal) (qs : List Seg) : Prop := ∃ c, T.findLive (lastAtSegs qs) = .ok c

/-- What a name holds after the updates, against what its symbol says; a
memory local's name read in the births `B` of the updates' memory. -/
def EnvRel (σ τ : State) (B : MemNames.Births) (x : Var) : Option SymB → Prop
  | none => τ.getEnv x = σ.getEnv x
  | some (.val t) => ∃ v, t.eval σ = .ok v ∧ τ.getEnv x = .ok (.val v)
  | some (.path q) => ∃ r segs, q.eval σ = .ok (.field r :: segs) ∧
      τ.getEnv x = .ok (.spath r segs) ∧ LiveTo (.struct τ.storage) (.field r :: segs)
  | some (.stale q) => ∃ r segs, q.eval σ = .ok (.field r :: segs) ∧
      τ.getEnv x = .ok (.spath r segs)
  | some (.stor s) => ∃ st, s.eval σ = .ok (.struct st) ∧ τ.getEnv x = .ok (.store st)
  | some (.mref i) => ∃ n, LId.evalR B i = .ok n ∧ τ.getEnv x = .ok (.mref n)

/-- The memory `M` runs from `σ` to the heap and the next identity of `τ`. -/
def MemAt (σ : State) (M : LMem) (τ : State) : Prop :=
  ∃ μ B, M.run σ = .ok (μ, B) ∧ μ.HeapEq τ

/-- `MemAt` reads the heap and `nextId` only. -/
theorem MemAt.of_heap {σ τ τ' : State} {M : LMem} (h : MemAt σ M τ) (hh : τ'.heap = τ.heap)
    (hn : τ'.nextId = τ.nextId) : MemAt σ M τ' := by
  obtain ⟨μ, B, hr, h₁, h₂⟩ := h
  exact ⟨μ, B, hr, h₁.trans hh.symm, h₂.trans hn.symm⟩

/-- `τ` is what the updates `ρ` stand for, applied in `σ`: its storage is the
stack of writes read in `σ`, each name holds what its symbol reads in `σ`,
and its heap and next identity are what the memory's run leaves. -/
structure Rel (σ : State) (ρ : Sym) (τ : State) : Prop where
  stor : ρ.stor.eval σ = .ok (.struct τ.storage)
  env : ∀ x, EnvRel σ τ (ρ.mem.births σ) x (lookupBy x ρ.env)
  tx : ∀ k, τ.envVal k = σ.envVal k
  mem : MemAt σ ρ.mem τ

/-- Before any update, the state is itself. -/
theorem Rel.empty (σ : State) : Rel σ Sym.empty σ :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, ⟨memBase σ, [], rfl, rfl, rfl⟩⟩

/-- Binding a name keeps the relation: after `uint y = balances[k];`, `y`
holds what `balances[k]` reads. -/
theorem Rel.bind {σ τ : State} {ρ : Sym} (h : Rel σ ρ τ) (x : Var) (b : SymB) (bd : Binding)
    (hb : EnvRel σ (τ.setEnv x bd) (ρ.mem.births σ) x (some b)) :
    Rel σ { ρ with env := (x, b) :: ρ.env } (τ.setEnv x bd) := by
  refine ⟨h.stor, fun y => ?_, fun k => by rw [← h.tx k]; cases k <;> rfl,
    h.mem.of_heap rfl rfl⟩
  by_cases hy : y = x
  · subst hy; simpa only [lookupBy, ↓reduceIte] using hb
  · have := h.env y
    simp only [lookupBy, hy, if_false]
    revert this
    have hst : (τ.setEnv x bd).storage = τ.storage := rfl
    rcases lookupBy y ρ.env with _ | ⟨t⟩ | ⟨q⟩ | _ <;>
      simp only [EnvRel, State.getEnv_setEnv_ne hy, imp_self, hst]

/-- A symbol the updates bound reads only what the updates read. -/
theorem lookupBy_vars {x y : Var} {b : SymB} : (env : List (Var × SymB)) →
    lookupBy y env = some b → x ∉ env.flatMap (fun b => b.2.vars) → x ∉ b.vars
  | [], h, _ => by simp only [lookupBy, reduceCtorEq] at h
  | (z, c) :: rest, h, hx => by
    simp only [List.flatMap_cons, List.mem_append, not_or] at hx
    by_cases hz : y = z
    · simp only [lookupBy, hz, if_true, Option.some.injEq] at h
      subst h; exact hx.1
    · simp only [lookupBy, hz, if_false] at h
      exact lookupBy_vars rest h hx.2

theorem LMem.births_setEnv {σ : State} {x : Var} {b : Binding} {M : LMem} (hx : x ∉ M.vars) :
    M.births (σ.setEnv x b) = M.births σ := by
  simp only [LMem.births, LMem.run_setEnv M hx]

/-- Rebinding a local the updates do not read keeps the relation, the local
now free: what a quantifier does. -/
theorem Rel.free {σ τ : State} {ρ : Sym} (h : Rel σ ρ τ) {x : Var} (hx : x ∉ ρ.vars)
    (v : Value) : Rel (σ.setEnv x (.val v)) (ρ.free x) (τ.setEnv x (.val v)) := by
  simp only [Sym.vars, List.mem_append, not_or] at hx
  obtain ⟨⟨hx₁, hx₂⟩, hx₃⟩ := hx
  have hB : (ρ.free x).mem.births (σ.setEnv x (.val v)) = ρ.mem.births σ :=
    LMem.births_setEnv hx₃
  refine ⟨?_, fun y => ?_, fun k => by
    rw [State.envVal_setEnv, State.envVal_setEnv, h.tx k], ?_⟩
  · show LStor.eval (σ.setEnv x (.val v)) ρ.stor = _
    rw [LStor.eval_setEnv _ hx₁]; exact h.stor
  · rw [hB]
    by_cases hy : y = x
    · subst hy
      simp only [Sym.free, lookupBy, if_true, EnvRel, LTerm.eval]
      exact ⟨v, by simp only [State.getEnv_setEnv_self]; rfl,
          by simp only [State.getEnv_setEnv_self]⟩
    · have hl : lookupBy y (ρ.free x).env = lookupBy y ρ.env := by
        simp only [Sym.free, lookupBy, hy, ↓reduceIte]
      rw [hl]
      have he := h.env y
      rcases hb : lookupBy y ρ.env with _ | ⟨t⟩ | ⟨q⟩ | ⟨q⟩ | ⟨S⟩ | ⟨k⟩ <;> rw [hb] at he <;>
        simp only [EnvRel] at he ⊢ <;>
        simp only [State.getEnv_setEnv_ne hy]
      · exact he
      · have hv := lookupBy_vars (x := x) ρ.env hb hx₂
        simp only [SymB.vars] at hv
        rw [LTerm.eval_setEnv _ hv]; exact he
      · have hv := lookupBy_vars (x := x) ρ.env hb hx₂
        simp only [SymB.vars] at hv
        rw [LPath.eval_setEnv _ hv]; exact he
      · have hv := lookupBy_vars (x := x) ρ.env hb hx₂
        simp only [SymB.vars] at hv
        rw [LPath.eval_setEnv _ hv]; exact he
      · have hv := lookupBy_vars (x := x) ρ.env hb hx₂
        simp only [SymB.vars] at hv
        rw [LStor.eval_setEnv _ hv]; exact he
      · exact he
  · obtain ⟨μ, B, hr, hh⟩ := h.mem
    exact ⟨μ, B, by rw [show (ρ.free x).mem = ρ.mem from rfl, LMem.run_setEnv _ hx₃]; exact hr,
      hh.1, hh.2⟩

/-! ### Checked paths, slot reads and live reads

The program checks each index of a path against the live length where it
takes the path (`State.checkIndex`), and then reads or writes the slot; the
target language reads and writes the live storage with no check.  Where the
path was checked against the storage it reads, the two agree
(`PTerm.toL_chk`, `live_bridge`). -/

/-- A path with no index evaluates to one. -/
theorem LPath.noAt_eval (σ : State) : ∀ {q : LPath} {qs : List Seg}, q.noAt = true →
    q.eval σ = .ok qs → qs.any Seg.isAt = false
  | .root _, _, _, h => by cases h; rfl
  | .field q f, _, hn, h => by
    obtain ⟨qs', h', he⟩ := Res.bind_eq_ok.1 h; cases he
    simp only [LPath.noAt] at hn
    simp only [List.any_append, LPath.noAt_eval σ hn h', List.any_cons, Seg.isAt, List.any_nil,
        Bool.or_self]
  | .at _ _, _, hn, _ => by simp only [noAt, Bool.false_eq_true] at hn

/-- With no index on the way, the live read is the read: `alice.account`. -/
theorem findLive_eq_find : ∀ (v : SVal) (qs : List Seg), qs.any Seg.isAt = false →
    v.findLive qs = v.find qs
  | v, [], _ => by cases v <;> rfl
  | _, .at _ :: _, h => by simp only [List.any_cons, Seg.isAt, Bool.true_or,
      Bool.true_eq_false] at h
  | v, .field f :: qs, h => by
    have h' : qs.any Seg.isAt = false := by simpa only [List.any_eq_false, Seg.isAt,
        Bool.not_eq_true, List.any_cons, Bool.false_or] using h
    cases v with
    | prim _ => rfl
    | struct fields =>
      simp only [SVal.findLive, SVal.find]
      cases lookupBy f fields with
      | none => rfl
      | some w => exact findLive_eq_find w qs h'
    | array elems shadow fx =>
      by_cases hf : f = "length"
      · subst hf
        simp only [SVal.findLive, SVal.find]
        cases fx
        · exact findLive_eq_find _ qs h'
        · rfl
      · simp only [SVal.findLive, SVal.find]
    | map _ _ => rfl

/-- **One index**: the program's check (`Close.idxOk`) passes exactly where
the live element is there: `values[1]` with two values, `balances[k]`. -/
theorem idx_iff (c : SVal) (k : Int) :
    Close.idxOk k c = .ok () ↔ ∃ c', c.findLive [.at k] = .ok c' := by
  cases c with
  | prim p => simp only [Close.idxOk, reduceCtorEq, SVal.findLive, exists_false]
  | struct _ => simp only [Close.idxOk, reduceCtorEq, SVal.findLive, exists_false]
  | array elems shadow fx =>
    by_cases hk : 0 ≤ k ∧ k.toNat < elems.length
    · simp only [Close.idxOk, hk, and_self, ↓reduceIte, SVal.findLive, ↓reduceDIte,
        List.get_eq_getElem, SVal.findLive_nil, Except.ok.injEq, exists_eq']
    · simp only [Close.idxOk, hk, ↓reduceIte, reduceCtorEq, SVal.findLive, ↓reduceDIte,
        exists_false]
  | map entries dflt =>
    simp only [Close.idxOk, SVal.findLive, true_iff]
    cases lookupBy k entries <;> simp only [Except.ok.injEq, exists_eq']

/-- A live write whose path reads live is the write. -/
theorem saveLive_eq_save : ∀ {v : SVal} {qs : List Seg} {c : SVal} (new : SVal),
    v.findLive qs = .ok c → v.saveLive qs new = v.save qs new
  | v, [], _, _, _ => by cases v <;> rfl
  | .prim _, _ :: _, _, _, h => by simp only [SVal.findLive, reduceCtorEq] at h
  | .struct fields, .field f :: qs, _, new, h => by
    simp only [SVal.findLive] at h
    simp only [SVal.saveLive, SVal.save]
    split at h
    · rename_i o hl
      rw [hl]
      simp only [saveLive_eq_save new h]
    · simp only [reduceCtorEq] at h
  | .struct _, .at _ :: _, _, _, h => by simp only [SVal.findLive, reduceCtorEq] at h
  | .array elems shadow fx, .at i :: qs, _, new, h => by
    simp only [SVal.findLive] at h
    split at h
    · rename_i hi
      have hi' : 0 ≤ i ∧ i.toNat < (elems ++ shadow).length := ⟨hi.1,
          by simp only [List.length_append]; omega⟩
      simp only [SVal.saveLive, SVal.save, dif_pos hi, dif_pos hi', List.get_eq_getElem,
        List.getElem_append_left hi.2]
      rw [List.get_eq_getElem] at h
      rw [saveLive_eq_save new h]
      cases (elems[i.toNat]'hi.2).save qs new with
      | error _ => rfl
      | ok u =>
        simp only [bind, Except.bind]
        rw [List.set_append_left _ _ hi.2]
        simp only [List.length_set, List.take_left', List.drop_left']
    · simp only [reduceCtorEq] at h
  | .array _ _ _, .field _ :: _, _, _, _ => by simp only [SVal.saveLive, SVal.save]
  | .map entries dflt, .at i :: qs, _, new, h => by
    simp only [SVal.findLive] at h
    simp only [SVal.saveLive, SVal.save]
    split at h <;> rename_i hl <;> rw [hl] <;> simp only [saveLive_eq_save new h]
  | .map _ _, .field _ :: _, _, _, _ => by simp only [SVal.saveLive, SVal.save]

/-- A live write returns only where the live read does. -/
theorem findLive_of_saveLive : ∀ {v : SVal} {qs : List Seg} {new u : SVal},
    v.saveLive qs new = .ok u → ∃ c, v.findLive qs = .ok c
  | v, [], _, _, _ => ⟨v, by cases v <;> rfl⟩
  | .prim _, s :: _, _, _, h => by cases s <;> simp only [SVal.saveLive, reduceCtorEq] at h
  | .struct fields, .field f :: qs, _, _, h => by
    simp only [SVal.saveLive] at h
    simp only [SVal.findLive]
    split at h
    · rename_i o hl
      obtain ⟨_, hu, _⟩ := Res.bind_eq_ok.1 h
      rw [hl]
      exact findLive_of_saveLive hu
    · simp only [reduceCtorEq] at h
  | .struct _, .at _ :: _, _, _, h => by simp only [SVal.saveLive, reduceCtorEq] at h
  | .array elems shadow fx, .at i :: qs, _, _, h => by
    simp only [SVal.saveLive] at h
    simp only [SVal.findLive]
    split at h
    · rename_i hi
      obtain ⟨_, hu, _⟩ := Res.bind_eq_ok.1 h
      rw [dif_pos hi]
      exact findLive_of_saveLive hu
    · simp only [reduceCtorEq] at h
  | .array _ _ _, .field _ :: _, _, _, h => by simp only [SVal.saveLive, reduceCtorEq] at h
  | .map entries dflt, .at i :: qs, _, _, h => by
    simp only [SVal.saveLive] at h
    simp only [SVal.findLive]
    split at h <;> rename_i hl <;> rw [hl] <;>
      (obtain ⟨_, hu, _⟩ := Res.bind_eq_ok.1 h; exact findLive_of_saveLive hu)
  | .map _ _, .field _ :: _, _, _, h => by simp only [SVal.saveLive, reduceCtorEq] at h

/-- A write returns only where the read does. -/
theorem find_of_save {v : SVal} {qs : List Seg} {new u : SVal} (h : v.save qs new = .ok u) :
    ∃ c, v.find qs = .ok c := by
  cases hf : v.find qs with
  | ok c => exact ⟨c, rfl⟩
  | error e => rw [Close.save_of_find_error hf] at h; cases h

/-! #### Up to the last index -/

/-- A member after the last index leaves it the last. -/
theorem lastAtSegs_field (qs : List Seg) (f : Name) :
    lastAtSegs (qs ++ [.field f]) = lastAtSegs qs := by
  simp only [lastAtSegs, Seg.isAt, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, Bool.not_false, List.dropWhile_cons_of_pos]

/-- An index is the last one. -/
theorem lastAtSegs_at (qs : List Seg) (k : Int) :
    lastAtSegs (qs ++ [.at k]) = qs ++ [.at k] := by
  simp only [lastAtSegs, Seg.isAt, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, Bool.not_true, Bool.false_eq_true, not_false_eq_true,
          List.dropWhile_cons_of_neg, List.reverse_reverse]

/-- A path is its part up to the last index, then members. -/
theorem lastAtSegs_split (qs : List Seg) :
    ∃ post, qs = lastAtSegs qs ++ post ∧ post.any Seg.isAt = false := by
  refine ⟨(qs.reverse.takeWhile fun s => !Seg.isAt s).reverse, ?_, ?_⟩
  · have := congrArg List.reverse
      (List.takeWhile_append_dropWhile (p := fun s => !Seg.isAt s) (l := qs.reverse))
    simp only [List.reverse_append, List.reverse_reverse] at this
    unfold lastAtSegs
    exact this.symm
  · have hall := List.all_takeWhile (p := fun s => !Seg.isAt s) (l := qs.reverse)
    simp only [List.all_eq_true] at hall
    simp only [List.any_eq_false, List.mem_reverse]
    intro s hs
    simpa only [Bool.not_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] using hall s hs

/-- A path with no index has nothing up to its last one. -/
theorem lastAtSegs_noAt {qs : List Seg} (h : qs.any Seg.isAt = false) : lastAtSegs qs = [] := by
  have hd : ∀ {l : List Seg}, (∀ s ∈ l, Seg.isAt s = false) →
      l.dropWhile (fun s => !Seg.isAt s) = [] := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.dropWhile_cons, hl a List.mem_cons_self, Bool.not_false, if_true]
      exact ih fun s hs => hl s (List.mem_cons_of_mem _ hs)
  simp only [lastAtSegs, List.reverse_eq_nil_iff]
  apply hd
  intro s hs
  simp only [List.any_eq_false] at h
  simpa only [Bool.not_eq_true] using h s (List.mem_reverse.mp hs)

/-- With every index in bounds, the slot read is the live read. -/
theorem LiveTo.find_eq {T : SVal} {qs : List Seg} (h : LiveTo T qs) : T.find qs = T.findLive qs := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨post, hq, hp⟩ := lastAtSegs_split qs
  rw [hq, SVal.find_append, SVal.findLive_append, hc, SVal.find_of_findLive hc, Res.ok_bind,
    Res.ok_bind, findLive_eq_find c post hp]

/-- A path read live has every index in bounds. -/
theorem LiveTo.of_findLive {T c : SVal} {qs : List Seg} (h : T.findLive qs = .ok c) :
    LiveTo T qs := by
  obtain ⟨post, hq, _⟩ := lastAtSegs_split qs
  rw [hq, SVal.findLive_append] at h
  obtain ⟨c₀, hc₀, -⟩ := Res.bind_eq_ok.1 h
  exact ⟨c₀, hc₀⟩

/-- A path with no index has none out of bounds. -/
theorem LiveTo.of_noAt (T : SVal) {qs : List Seg} (h : qs.any Seg.isAt = false) : LiveTo T qs :=
  ⟨T, by rw [lastAtSegs_noAt h]; cases T <;> rfl⟩

/-- The last index of a path, evaluated. -/
theorem LPath.lastAt_eval (σ : State) : ∀ {q : LPath} {qs : List Seg}, q.eval σ = .ok qs →
    (q.lastAt = none → qs.any Seg.isAt = false) ∧
      (∀ q', q.lastAt = some q' → q'.eval σ = .ok (lastAtSegs qs))
  | .root _, _, h => by cases h; exact ⟨fun _ => rfl, fun _ h => by simp only [lastAt,
      reduceCtorEq] at h⟩
  | .field q f, _, h => by
    obtain ⟨qs', h', he⟩ := Res.bind_eq_ok.1 h; cases he
    obtain ⟨h₁, h₂⟩ := LPath.lastAt_eval σ h'
    refine ⟨fun hn => ?_, fun q' hs => ?_⟩
    · simp only [List.any_append, h₁ hn, List.any_cons, Seg.isAt, List.any_nil, Bool.or_self]
    · rw [lastAtSegs_field]; exact h₂ q' hs
  | .at q k, _, h => by
    refine ⟨fun hn => by simp only [lastAt, reduceCtorEq] at hn, fun q' hs => ?_⟩
    simp only [LPath.lastAt, Option.some.injEq] at hs
    subst hs
    obtain ⟨qs', h', h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨i, hi, he⟩ := Res.bind_eq_ok.1 h; cases he
    rw [lastAtSegs_at]
    simp only [LPath.eval, h', hi, Res.ok_bind]

/-- **Binding an alias returns** exactly where its path does and every
index on it is in bounds of the storage `s` leaves. -/
theorem guardPath_ok {σ : State} {s : LStor} {T : SVal} (hs : s.eval σ = .ok T) (q : LPath) :
    (∃ v, (guardPath s q).eval σ = .ok v) ↔ ∃ qs, q.eval σ = .ok qs ∧ LiveTo T qs := by
  unfold guardPath
  cases hl : q.lastAt with
  | none =>
    simp only [LTerm.eval, Res.bind_eq_ok]
    constructor
    · rintro ⟨_, qs, hq, -⟩
      exact ⟨qs, hq, LiveTo.of_noAt T ((LPath.lastAt_eval σ hq).1 hl)⟩
    · rintro ⟨qs, hq, -⟩
      exact ⟨_, qs, hq, rfl⟩
  | some q' =>
    simp only [LTerm.eval, Res.bind_eq_ok, hs, Res.ok_bind]
    constructor
    · rintro ⟨_, _, ⟨qs, hq, -⟩, qs', hq', c, hc, -⟩
      have := (LPath.lastAt_eval σ hq).2 q' hl
      rw [hq'] at this
      cases this
      exact ⟨qs, hq, c, hc⟩
    · rintro ⟨qs, hq, c, hc⟩
      exact ⟨_, _, ⟨qs, hq, rfl⟩, _, (LPath.lastAt_eval σ hq).2 q' hl, c, hc, rfl⟩

/-- **The read of a checked path is the live read**: given what the checks
of a path amount to (`PTerm.toL_chk`), a read returns the same either way. -/
theorem live_bridge {τ : State} {P : Res (Name × List Seg)} {L : Res (List Seg)}
    (hA : ∀ qs, (∃ rs, P = .ok rs ∧ qs = .field rs.1 :: rs.2) ↔
      (L = .ok qs ∧ LiveTo (.struct τ.storage) qs)) (qs : List Seg) (c : SVal) :
    (L = .ok qs ∧ (SVal.struct τ.storage).findLive qs = .ok c) ↔
      ∃ rs, P = .ok rs ∧ qs = .field rs.1 :: rs.2 ∧ τ.findStorage rs.1 rs.2 = .ok c := by
  constructor
  · rintro ⟨hq, hc⟩
    have hl := LiveTo.of_findLive hc
    obtain ⟨rs, hrs, rfl⟩ := (hA _).2 ⟨hq, hl⟩
    refine ⟨rs, hrs, rfl, ?_⟩
    rw [← find_root, hl.find_eq]
    exact hc
  · rintro ⟨rs, hrs, rfl, hc⟩
    obtain ⟨hq, hl⟩ := (hA _).1 ⟨rs, hrs, rfl⟩
    refine ⟨hq, ?_⟩
    rw [← hl.find_eq, find_root]
    exact hc

/-- **A read of the node at a checked path is the live read of it**, the
rest of the run alike: `live_bridge` under a bind. -/
theorem read_bridge {α : Type} {τ : State} {P : Res (Name × List Seg)} {L : Res (List Seg)}
    (hb : ∀ qs c, (L = .ok qs ∧ (SVal.struct τ.storage).findLive qs = .ok c) ↔
      ∃ rs, P = .ok rs ∧ qs = .field rs.1 :: rs.2 ∧ τ.findStorage rs.1 rs.2 = .ok c)
    {G G' : SVal → Res α} (hG : ∀ c, Sim (G c) (G' c)) :
    Sim (L >>= fun qs => (SVal.struct τ.storage).findLive qs >>= G)
      (P >>= fun rs => τ.findStorage rs.1 rs.2 >>= G') := by
  intro a
  simp only [Res.bind_eq_ok]
  constructor
  · rintro ⟨qs, hq, c, hc, ha⟩
    obtain ⟨rs, hrs, rfl, hfs⟩ := (hb qs c).1 ⟨hq, hc⟩
    exact ⟨rs, hrs, c, hfs, (hG c a).1 ha⟩
  · rintro ⟨rs, hrs, c, hfs, ha⟩
    obtain ⟨hq, hc⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hfs⟩
    exact ⟨_, hq, c, hc, (hG c a).2 ha⟩

/-- **A write of the node at a checked path, made of the node there, is the
live write**: `delete`, `push`, `pop` and a copy over it alike. -/
theorem write_bridge {τ : State} {P : Res (Name × List Seg)} {L : Res (List Seg)}
    (hb : ∀ qs c, (L = .ok qs ∧ (SVal.struct τ.storage).findLive qs = .ok c) ↔
      ∃ rs, P = .ok rs ∧ qs = .field rs.1 :: rs.2 ∧ τ.findStorage rs.1 rs.2 = .ok c)
    (F : SVal → Res SVal) :
    Sim (L >>= fun qs => (SVal.struct τ.storage).findLive qs >>= fun c => F c >>= fun c' =>
          (SVal.struct τ.storage).saveLive qs c')
      (P >>= fun rs => τ.findStorage rs.1 rs.2 >>= fun c => F c >>= fun c' =>
          τ.saveStorage rs.1 rs.2 c' >>= fun τ' => .ok (.struct τ'.storage)) := by
  intro a
  simp only [Res.bind_eq_ok]
  constructor
  · rintro ⟨qs, hq, c, hc, c', hF, ha⟩
    obtain ⟨rs, hrs, rfl, hfs⟩ := (hb qs c).1 ⟨hq, hc⟩
    rw [saveLive_eq_save _ hc, save_root] at ha
    obtain ⟨τ'', h'', he⟩ := Res.bind_eq_ok.1 ha
    exact ⟨rs, hrs, c, hfs, c', hF, τ'', h'', he⟩
  · rintro ⟨rs, hrs, c, hfs, c', hF, τ'', h'', he⟩
    obtain ⟨hq, hl⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hfs⟩
    refine ⟨_, hq, c, hl, c', hF, ?_⟩
    rw [saveLive_eq_save _ hl, save_root, h'', Res.ok_bind, he]

/-- `persons.push()` on the node: the slot appended, then written back. -/
theorem pushOn_slot (τ : State) (E : Ty) (r : Name) (segs : List Seg) (w : Value) :
    Close.pushOn τ E r segs pure =
      fun c => (AOp.slot E).apply w c >>= fun c' => τ.saveStorage r segs c' := by
  funext c
  cases c <;> rfl

/-- `values.push(w)` on the node: the word appended, then written back. -/
theorem pushOn_word (τ : State) (r : Name) (segs : List Seg) (x : Value) :
    Close.pushOn τ .uint r segs (fun _ => .ok x.toSVal) =
      fun c => AOp.push.apply x c >>= fun c' => τ.saveStorage r segs c' := by
  funext c
  cases c <;> rfl

/-- `values.pop()` on the node: the last element moved past the end, then
written back. -/
theorem popOn_pop (τ : State) (keep : Bool) (r : Name) (segs : List Seg) (w : Value) :
    Close.popOn τ keep r segs =
      fun c => (AOp.pop keep).apply w c >>= fun c' => τ.saveStorage r segs c' := by
  funext c
  cases c with
  | array elems shadow fx =>
    rcases hr : elems.reverse with _ | ⟨l, rr⟩ <;> simp only [Close.popOn, hr, AOp.apply,
        Res.ok_bind] <;> rfl
  | prim _ | struct _ | map _ _ => rfl

/-- `p = persons.push();` writes what `persons.push();` does. -/
theorem STerm.eval_extend (s : STerm C) (p : PTerm C) (E : Ty) (σ : State) :
    (STerm.extend s p E).eval σ = s.eval σ >>= fun τ => p.eval σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>= Close.pushOn τ E rs.1 rs.2 pure := by
  simp only [Tm.eval, Op2.eval]
  cases s.eval σ with
  | error _ => rfl
  | ok τ =>
    cases p.eval σ with
    | error _ => rfl
    | ok rs =>
      simp only [Res.ok_bind, pushPlaceAt]
      cases τ.findStorage rs.1 rs.2 with
      | error _ => rfl
      | ok c =>
        cases c with
        | array elems shadow fx =>
          simp only [Res.ok_bind, Close.pushOn_array, pure, Except.pure]
          cases τ.saveStorage rs.1 rs.2 _ <;> rfl
        | prim _ | struct _ | map _ _ => rfl

/-- An empty slot copied over is the copy laid on fresh slots. -/
theorem prim_overlay (p : PrimVal) (n : SVal) : (SVal.prim p).overlay n = n.strip := by
  cases n <;> rfl

/-- A write below a location written before is one write of what is
there, written below. -/
theorem saveLive_append {new : SVal} : ∀ {v v' A : SVal} {ps : List Seg} (rest : List Seg),
    v.saveLive ps A = .ok v' →
      v'.saveLive (ps ++ rest) new = A.saveLive rest new >>= fun A' => v.saveLive ps A'
  | v, v', A, [], rest, h => by
    have : v' = A := by cases v <;> simpa only [SVal.saveLive, Except.ok.injEq] using h.symm
    subst this
    simp only [List.nil_append]
    cases v <;> cases v'.saveLive rest new <;> rfl
  | .prim _, _, _, _ :: _, _, h => by cases ‹Seg› <;> simp only [SVal.saveLive, reduceCtorEq] at h
  | .struct fields, v', A, .field f :: ps, rest, h => by
    simp only [SVal.saveLive] at h
    cases hl : lookupBy f fields with
    | none => simp only [hl, reduceCtorEq] at h
    | some old =>
      rw [hl] at h
      obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h
      cases he
      simp only [List.cons_append, SVal.saveLive, lookupBy_setBy_self, saveLive_append rest hu,
        hl, bind_assoc, setBy_setBy_self]
  | .struct _, _, _, .at _ :: _, _, h => by simp only [SVal.saveLive, reduceCtorEq] at h
  | .array _ _ _, _, _, .field _ :: _, _, h => by simp only [SVal.saveLive, reduceCtorEq] at h
  | .map _ _, _, _, .field _ :: _, _, h => by simp only [SVal.saveLive, reduceCtorEq] at h
  | .array elems shadow fx, v', A, .at i :: ps, rest, h => by
    simp only [SVal.saveLive] at h
    split at h
    · rename_i hi
      obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h
      cases he
      have hi' : 0 ≤ i ∧ i.toNat < (elems.set i.toNat upd).length := by
        simpa only [List.length_set] using hi
      simp only [List.cons_append, SVal.saveLive, dif_pos hi', dif_pos hi, List.get_eq_getElem,
        List.getElem_set_self, saveLive_append rest hu, bind_assoc, List.set_set]
    · cases h
  | .map entries dflt, v', A, .at i :: ps, rest, h => by
    simp only [SVal.saveLive] at h
    cases hl : lookupBy i entries with
    | none =>
      rw [hl] at h
      obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h
      cases he
      simp only [List.cons_append, SVal.saveLive, lookupBy_setBy_self, saveLive_append rest hu,
        hl, bind_assoc, setBy_setBy_self]
    | some old =>
      rw [hl] at h
      obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h
      cases he
      simp only [List.cons_append, SVal.saveLive, lookupBy_setBy_self, saveLive_append rest hu,
        hl, bind_assoc, setBy_setBy_self]


/-- Whether a write returns does not depend on what it writes. -/
theorem saveLive_other {x y : SVal} : ∀ {v u : SVal} {ps : List Seg}, v.saveLive ps x = .ok u →
    ∃ u', v.saveLive ps y = .ok u'
  | v, u, [], _ => ⟨y, by cases v <;> rfl⟩
  | .prim _, _, s :: _, h => by cases s <;> simp only [SVal.saveLive, reduceCtorEq] at h
  | .struct fields, u, .field f :: ps, h => by
    simp only [SVal.saveLive] at h ⊢
    split at h
    · rename_i old hl
      obtain ⟨upd, hu, -⟩ := Res.bind_eq_ok.1 h
      obtain ⟨u', hu'⟩ := saveLive_other (y := y) hu
      exact ⟨.struct (setBy f u' fields), by simp only [hu', Res.ok_bind]⟩
    · cases h
  | .struct _, _, .at _ :: _, h => by simp only [SVal.saveLive, reduceCtorEq] at h
  | .array _ _ _, _, .field _ :: _, h => by simp only [SVal.saveLive, reduceCtorEq] at h
  | .map _ _, _, .field _ :: _, h => by simp only [SVal.saveLive, reduceCtorEq] at h
  | .array elems shadow fx, u, .at i :: ps, h => by
    simp only [SVal.saveLive] at h ⊢
    split at h
    · rename_i hi
      obtain ⟨upd, hu, -⟩ := Res.bind_eq_ok.1 h
      obtain ⟨u', hu'⟩ := saveLive_other (y := y) hu
      simp only [List.get_eq_getElem] at hu'
      exact ⟨.array (elems.set i.toNat u') shadow fx, by simp only [hi, and_self, ↓reduceDIte,
          List.get_eq_getElem, hu', Res.ok_bind]⟩
    · cases h
  | .map entries dflt, u, .at i :: ps, h => by
    simp only [SVal.saveLive] at h ⊢
    split at h
    · rename_i old hl
      obtain ⟨upd, hu, -⟩ := Res.bind_eq_ok.1 h
      obtain ⟨u', hu'⟩ := saveLive_other (y := y) hu
      exact ⟨.map (setBy i u' entries) dflt, by simp only [hu', Res.ok_bind]⟩
    · rename_i hl
      obtain ⟨upd, hu, -⟩ := Res.bind_eq_ok.1 h
      obtain ⟨u', hu'⟩ := saveLive_other (y := y) hu
      exact ⟨.map (setBy i u' entries) dflt, by simp only [hu', Res.ok_bind]⟩

/-- Writing the slot one past the old end of a grown array. -/
theorem saveLive_last (es sh : List SVal) (fx : Bool) (x y : SVal) :
    (SVal.array (es ++ [x]) sh fx).saveLive [.at es.length] y = .ok (.array (es ++ [y]) sh fx) := by
  simp only [SVal.saveLive, Int.ofNat_zero_le, Int.toNat_natCast, List.length_append,
      List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, and_self, ↓reduceDIte,
          List.get_eq_getElem, Nat.le_refl, List.getElem_append_right, Nat.sub_self,
          List.getElem_cons_zero, List.set_append_right, List.set_cons_zero, Res.ok_bind]

theorem findLive_last (es sh : List SVal) (fx : Bool) (x : SVal) :
    (SVal.array (es ++ [x]) sh fx).findLive [.at es.length] = .ok x := by
  simp only [SVal.findLive, Int.ofNat_zero_le, Int.toNat_natCast, List.length_append,
      List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, and_self, ↓reduceDIte,
          List.get_eq_getElem, Nat.le_refl, List.getElem_append_right, Nat.sub_self,
          List.getElem_cons_zero, SVal.findLive_nil]

/-- **`tokens.push(tok)`**: a slot appended, the source copied over it. -/
theorem pushCopy_bridge {σ τ : State} {S : LStor} {P SQ : LPath}
    {PE PE' : Res (Name × List Seg)}
    (hS : S.eval σ = .ok (.struct τ.storage))
    (hb : ∀ qs c, (P.eval σ = .ok qs ∧ (SVal.struct τ.storage).findLive qs = .ok c) ↔
      ∃ rs, PE = .ok rs ∧ qs = .field rs.1 :: rs.2 ∧ τ.findStorage rs.1 rs.2 = .ok c)
    (hb' : ∀ qs c, (SQ.eval σ = .ok qs ∧ (SVal.struct τ.storage).findLive qs = .ok c) ↔
      ∃ rs, PE' = .ok rs ∧ qs = .field rs.1 :: rs.2 ∧ τ.findStorage rs.1 rs.2 = .ok c) :
    Sim ((LStor.copy (.arr (.slot .uint) S P (.lit (.bool true))) (.at P (.len S P)) S SQ).eval σ)
      (PE >>= fun rs => τ.findStorage rs.1 rs.2 >>= fun c =>
        Close.pushOn τ .uint rs.1 rs.2
          (fun _ => PE' >>= fun rs' => τ.findStorage rs'.1 rs'.2 >>= fun sv => pure sv.strip) c >>=
        fun τ' => .ok (.struct τ'.storage)) := by
  intro a
  constructor
  · intro h
    simp only [LStor.eval, LTerm.eval, LPath.eval, hS, Res.ok_bind, Res.bind_eq_ok] at h
    obtain ⟨sqs, hsq, n, hn, v', ⟨ps, hp, c, hc, c', hap, hv'⟩, qs', ⟨ps₂, hp₂, i,
      ⟨k, ⟨ps₃, hp₃, c₂, hc₂, hk⟩, hi⟩, hq'⟩, cur, hcur, ha⟩ := h
    rw [hp] at hp₂ hp₃; cases hp₂; cases hp₃
    rw [hc] at hc₂; cases hc₂
    obtain ⟨rs, hrs, rfl, hfs⟩ := (hb _ c).1 ⟨hp, hc⟩
    obtain ⟨rs', hrs', rfl, hfs'⟩ := (hb' _ n).1 ⟨hsq, hn⟩
    cases c with
    | array es sh fx =>
      simp only [AOp.apply] at hap; cases hap
      simp only [Close.arrLen] at hk; cases hk
      simp only [Value.asInt] at hi; cases hi
      cases hq'
      have hslot : (pushSlot (.prim .uint) sh).1 = .prim (.int 0) := by
        cases sh <;> simp only [pushSlot, defaultForTy, Ty.isPrimitive, ↓reduceIte] <;> rfl
      rw [SVal.findLive_append, findLive_saveLive_same hv', Res.ok_bind] at hcur
      rw [hslot, findLive_last] at hcur; cases hcur
      rw [saveLive_append _ hv', hslot, prim_overlay, saveLive_last, Res.ok_bind,
        saveLive_eq_save _ hc, save_root] at ha
      obtain ⟨τ'', h'', he⟩ := Res.bind_eq_ok.1 ha
      simp only [hrs, Res.ok_bind, hfs, Close.pushOn_array, hrs', hfs', pure, Except.pure]
      rw [h'']
      exact he
    | prim _ | struct _ | map _ _ => simp only [AOp.apply, reduceCtorEq] at hap
  · intro h
    obtain ⟨rs, hrs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨c, hfs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨τ'', h, he⟩ := Res.bind_eq_ok.1 h
    cases c with
    | array es sh fx =>
      simp only [Close.pushOn_array] at h
      obtain ⟨n', hval, h⟩ := Res.bind_eq_ok.1 h
      obtain ⟨rs', hrs', hval⟩ := Res.bind_eq_ok.1 hval
      obtain ⟨n, hfs', hval⟩ := Res.bind_eq_ok.1 hval
      simp only [pure, Except.pure, Except.ok.injEq] at hval; subst hval
      obtain ⟨hp, hc⟩ := (hb _ _).2 ⟨rs, hrs, rfl, hfs⟩
      obtain ⟨hsq, hn⟩ := (hb' _ _).2 ⟨rs', hrs', rfl, hfs'⟩
      have hslot : (pushSlot (.prim .uint) sh).1 = .prim (.int 0) := by
        cases sh <;> simp only [pushSlot, defaultForTy, Ty.isPrimitive, ↓reduceIte] <;> rfl
      have hsv : (SVal.struct τ.storage).saveLive (.field rs.1 :: rs.2)
          (.array (es ++ [n.strip]) (pushSlot .uint sh).2 fx) = .ok a := by
        rw [saveLive_eq_save _ hc, save_root, h, Res.ok_bind, he]
      obtain ⟨v', hv'⟩ := saveLive_other (y := .array (es ++ [(pushSlot .uint sh).1])
        (pushSlot .uint sh).2 fx) hsv
      simp only [LStor.eval, LTerm.eval, LPath.eval, hS, Res.ok_bind, Res.bind_eq_ok]
      refine ⟨_, hsq, n, hn, v', ⟨_, hp, _, hc, _, rfl, hv'⟩, _, ⟨_, hp, _,
        ⟨_, ⟨_, hp, _, hc, rfl⟩, rfl⟩, rfl⟩, (pushSlot .uint sh).1, ?_, ?_⟩
      · rw [SVal.findLive_append, findLive_saveLive_same hv', Res.ok_bind, findLive_last]
      · rw [saveLive_append _ hv', hslot, prim_overlay, saveLive_last, Res.ok_bind]
        exact hsv
    | prim _ | struct _ | map _ _ => simp only [Close.pushOn, reduceCtorEq] at h

/-- A write to the storage keeps what the names hold, an alias through an
index made stale. -/
theorem lookupBy_onWrite (y : Var) : ∀ (env : List (Var × SymB)),
    lookupBy y (env.map fun b => (b.1, b.2.onWrite)) = (lookupBy y env).map SymB.onWrite
  | [] => rfl
  | (x, b) :: rest => by
    by_cases hy : y = x <;> simp only [hy, List.map_cons, lookupBy, ↓reduceIte, Option.map_some,
        lookupBy_onWrite y rest]

/-- A write to the storage keeps the relation of each name. -/
theorem EnvRel.onWrite {σ τ τ' : State} {B : MemNames.Births} {y : Var} {o : Option SymB}
    (h : EnvRel σ τ B y o) (he : τ'.getEnv y = τ.getEnv y) :
    EnvRel σ τ' B y (o.map SymB.onWrite) := by
  rcases o with _ | ⟨t⟩ | ⟨q⟩ | _ | ⟨s⟩ | ⟨k⟩
  · simp only [EnvRel, Option.map] at h ⊢; rw [he]; exact h
  · simp only [EnvRel, Option.map, SymB.onWrite] at h ⊢; rw [he]; exact h
  · simp only [EnvRel] at h
    obtain ⟨r, segs, h₁, h₂, -⟩ := h
    by_cases hn : q.noAt = true
    · simp only [Option.map, SymB.onWrite, hn, if_true, EnvRel]
      exact ⟨r, segs, h₁, by rw [he]; exact h₂, LiveTo.of_noAt _ (LPath.noAt_eval σ hn h₁)⟩
    · simp only [Option.map, SymB.onWrite, hn, if_false, EnvRel, Bool.false_eq_true]
      exact ⟨r, segs, h₁, by rw [he]; exact h₂⟩
  · simp only [EnvRel, Option.map, SymB.onWrite] at h ⊢; rw [he]; exact h
  · simp only [EnvRel, Option.map, SymB.onWrite] at h ⊢; rw [he]; exact h
  · simp only [EnvRel, Option.map, SymB.onWrite] at h ⊢; rw [he]; exact h

/-! ### Memory, symbolically and concretely

A memory term pushed in is an `LMem` whose run from the initial state leaves
the heap and the next identity the term leaves (`MemAt`); its births extend
those of the updates' memory, so a name the updates bound denotes the same
object in it (`LId.evalR_prefix`). -/

open MemNames in
/-- A name keeps its object in a run that allocates more. -/
theorem LId.evalR_prefix {B B' : Births} (hp : B <+: B') {j : LId} {n : Nat}
    (h : LId.evalR B j = .ok n) : LId.evalR B' j = .ok n := by
  obtain ⟨D, rfl⟩ := hp
  have hr := evalR_root_lt h
  rw [LId.evalR_ok] at h ⊢
  simpa only [Births.eval, List.getElem?_append_left hr] using h

open MemNames in
/-- A name of an object older than the allocations a run adds denotes it
before them too. -/
theorem LId.evalR_prefix_lt {B B' : Births} (hp : B <+: B') {j : LId} (hj : j.root < B.length)
    {n : Nat} (h : LId.evalR B' j = .ok n) : LId.evalR B j = .ok n := by
  obtain ⟨D, rfl⟩ := hp
  rw [LId.evalR_ok] at h ⊢
  simpa only [Births.eval, List.getElem?_append_left hj] using h

open MemNames in
theorem LMV.eval_prefix {σ : State} {B B' : Births} (hp : B <+: B') {w : LMV} {mv : MVal}
    (h : w.eval σ B = .ok mv) : w.eval σ B' = .ok mv := by
  cases w with
  | word t => exact h
  | ref j =>
    simp only [LMV.eval, Res.bind_eq_ok] at h ⊢
    obtain ⟨n, hn, h⟩ := h
    exact ⟨n, LId.evalR_prefix hp hn, h⟩

open MemNames in
/-- A name's relation holds in a run that allocates more. -/
theorem EnvRel.grow {σ τ : State} {B B' : Births} (hp : B <+: B') {x : Var} {o : Option SymB}
    (h : EnvRel σ τ B x o) : EnvRel σ τ B' x o := by
  rcases o with _ | ⟨t⟩ | ⟨q⟩ | _ | ⟨s⟩ | ⟨j⟩
  · exact h
  · exact h
  · exact h
  · exact h
  · exact h
  · obtain ⟨n, hn, he⟩ := h
    exact ⟨n, LId.evalR_prefix hp hn, he⟩

open MemNames in
/-- A name's relation reads only the name's binding and the storage. -/
theorem EnvRel.congr {σ τ τ' : State} {B : Births} {x : Var} {o : Option SymB}
    (h : EnvRel σ τ B x o) (he : τ'.getEnv x = τ.getEnv x) (hs : τ'.storage = τ.storage) :
    EnvRel σ τ' B x o := by
  rcases o with _ | ⟨t⟩ | ⟨q⟩ | _ | ⟨s⟩ | ⟨j⟩ <;> simp only [EnvRel, he, hs] <;> exact h

/-- The updates' memory has as many births as allocations. -/
theorem Rel.births_length {σ τ : State} {ρ : Sym} (h : Rel σ ρ τ) :
    (ρ.mem.births σ).length = ρ.mem.nAlloc := by
  obtain ⟨μ, B, hr, -⟩ := h.mem
  rw [LMem.births_of_run hr, LMem.run_nAlloc σ _ hr]

open MemNames in
/-- **A memory update keeps the relation**: the memory `M` runs to the heap
the update writes, and the names bound before denote the same objects. -/
theorem Rel.setMem {σ τ μ μ' : State} {ρ : Sym} {M : LMem} {B : Births} (h : Rel σ ρ τ)
    (hr : M.run σ = .ok (μ, B)) (hp : ρ.mem.births σ <+: B) (hh : μ.HeapEq μ') :
    Rel σ { ρ with mem := M } { τ with heap := μ'.heap, nextId := μ'.nextId } := by
  refine ⟨h.stor, fun y => ?_, fun k => h.tx k, μ, B, hr, hh⟩
  show EnvRel σ _ (M.births σ) y (lookupBy y ρ.env)
  rw [LMem.births_of_run hr]
  exact ((h.env y).grow hp).congr rfl rfl

theorem LSel.read_of_addr {σ μ : State} {n : Nat} {a : LSel} {ad : Addr}
    (h : a.addr σ n = .ok ad) : a.read σ μ n = readAddr μ ad >>= MVal.asValue := by
  cases a with
  | fld f => cases h; rfl
  | idx t =>
    show (t.eval σ >>= Value.asInt >>= fun j => readAddr μ (.memoryIndex n j) >>= MVal.asValue) = _
    simp only [LSel.addr] at h
    cases hj : (t.eval σ >>= Value.asInt) with
    | error e => rw [hj] at h; cases h
    | ok j => rw [hj, Res.ok_bind] at h; cases h; rw [Res.ok_bind]
  | size => cases h

theorem LSel.iread_of_addr {σ μ : State} {n : Nat} {a : LSel} {ad : Addr}
    (h : a.addr σ n = .ok ad) : a.iread σ μ n = readAddr μ ad >>= MVal.asRef := by
  simp only [LSel.iread, h, Res.ok_bind]

/-- A default of a type `allocOk` admits is allocated in any state. -/
theorem allocDefault_ok {R : RefTy} (h : allocOk R = true) (σ : State) :
    ∃ τ id, allocDefault σ R = .ok (τ, id) := by
  obtain ⟨⟨τ, mv⟩, hc⟩ := (allocOk_cps h).at σ
  obtain ⟨id, rfl⟩ := copy_ref hc (defaultForTy_ref_ne R)
  exact ⟨τ, id, by unfold allocDefault; rw [defaultForRef, hc]⟩

theorem allocDefault_of_copy {σ τ : State} {R : RefTy} {id : Nat}
    (h : copyStToM σ (defaultForTy (.ref R)) = .ok (τ, .ref id)) :
    allocDefault σ R = .ok (τ, id) := by
  unfold allocDefault; rw [defaultForRef, h]

/-- `new R(nt)` reads to `R`'s array of the length `nt` reads to. -/
theorem newArr_eval_ok {τ : State} {R : RefTy} {nt : Term C} {sv : SVal} :
    (Tm.app1 (Op1.newArr R) nt).eval τ = .ok sv ↔
      ∃ c, nt.eval τ = .ok (.int c) ∧ sv = newArrVal R c := by
  simp only [Tm.eval, Op1.eval]
  cases hn : nt.eval τ with
  | error e => simp only [bind, Except.bind, reduceCtorEq, false_and, exists_false]
  | ok v =>
    cases v with
    | int c =>
      simp only [bind, Except.bind, Value.asInt, pure, Except.pure, Except.ok.injEq,
        PrimVal.int.injEq, exists_eq_left']
      exact eq_comm
    | bool b =>
      simp only [bind, Except.bind, Value.asInt, reduceCtorEq, Except.ok.injEq, false_and,
        exists_false]

/-- The guard of an index returns exactly where the index is an integer. -/
theorem isIntL_ret (σ : State) (t : LTerm) :
    (∃ v, (isIntL t).eval σ = .ok v) ↔ ∃ i, t.eval σ = .ok (.int i) := by
  unfold isIntL
  split
  · rename_i i hi
    exact ⟨fun _ => ⟨i, LTerm.ground?_eval σ t hi⟩, fun _ => ⟨_, rfl⟩⟩
  · constructor
    · rintro ⟨v, hv⟩
      simp only [LTerm.eval] at hv
      cases ht : t.eval σ with
      | error e => rw [ht] at hv; cases hv
      | ok w =>
        cases w with
        | int i => exact ⟨i, rfl⟩
        | bool b => rw [ht] at hv; cases hv
    · rintro ⟨i, hi⟩
      exact ⟨.bool true, by simp only [LTerm.eval, hi, Res.ok_bind, Value.asInt, ite_self]⟩

/-- The symbols of a term, the measure the proofs below recurse on. -/
def _root_.Solidity.Tm.lsize : Tm C s → Nat
  | .app1 _ a => a.lsize + 1
  | .app2 _ a b => a.lsize + b.lsize + 1
  | .app3 _ a b c => a.lsize + b.lsize + c.lsize + 1
  | .pvV _ | .pvP _ | .pvS _ | .pvI _ | .app0 _ => 0

/-- `x.lsize < n` for a direct subterm `x` of a term of size below `n + 1`. -/
macro "lsize_tac" : tactic => `(tactic| (simp only [Solidity.Tm.lsize] at *; omega))

/-! The statements below, one per sort, for the terms of fewer than `n`
symbols: each sort's step is its own declaration, proved from the others at
`n` (`Rel.all_ok` puts them together by induction on `n`). -/

/-- A value term reads, pushed in, what it read after the updates. -/
def TermOK (C : Contract) (σ τ : State) (ρ : Sym) (n : Nat) : Prop :=
  ∀ t : Term C, t.lsize < n → t.inL ρ = true → Sim ((t.toL ρ).eval σ) (t.eval τ)

/-- A path, pushed in, is the path the program took, checked. -/
def PathOK (C : Contract) (σ τ : State) (ρ : Sym) (n : Nat) : Prop :=
  ∀ p : PTerm C, p.lsize < n → p.inL ρ = true → ∀ (qs : List Seg),
    (∃ rs, p.eval τ = .ok rs ∧ qs = .field rs.1 :: rs.2) ↔
      ((p.toL ρ).eval σ = .ok qs ∧ LiveTo (.struct τ.storage) qs)

/-- An identity, pushed in, is a name of the object it denotes, read in the
births of the updates' memory, and a guard that returns exactly where it
does. -/
def IdOK (C : Contract) (σ τ : State) (ρ : Sym) (n : Nat) : Prop :=
  ∀ i : ITerm C, i.lsize < n → i.inL ρ = true → ∃ j g, i.toL ρ = some (j, g) ∧
    (Rets (g.eval σ) → ∃ id, i.eval τ = .ok id) ∧
    ∀ id, i.eval τ = .ok id → Rets (g.eval σ) ∧ LId.evalR (ρ.mem.births σ) j = .ok id

/-- An address, pushed in, is the name of the object and what selects in it. -/
def AddrOK (C : Contract) (σ τ : State) (ρ : Sym) (n : Nat) : Prop :=
  ∀ a : MAddr C, a.lsize < n → a.inL ρ = true → ∃ j sel g, a.toL ρ = some (j, sel, g) ∧
    (Rets (g.eval σ) → ∃ ad, a.eval τ = .ok ad) ∧
    ∀ ad, a.eval τ = .ok ad → Rets (g.eval σ) ∧
      ∃ n, LId.evalR (ρ.mem.births σ) j = .ok n ∧ sel.addr σ n = .ok ad

/-- A memory, pushed in, runs to the heap the term leaves, allocating after
the updates' memory. -/
def MemOK (C : Contract) (σ τ : State) (ρ : Sym) (n : Nat) : Prop :=
  ∀ m : MTerm C, m.lsize < n → m.inL ρ = true → ∃ M g, m.toL ρ = some (M, g) ∧
    (Rets (g.eval σ) → ∃ μ', m.eval τ = .ok μ') ∧
    ∀ μ', m.eval τ = .ok μ' → Rets (g.eval σ) ∧
      ∃ μ B, M.run σ = .ok (μ, B) ∧ μ.HeapEq μ' ∧ ρ.mem.births σ <+: B

/-- A memory value, pushed in, is what the slot it writes holds. -/
def MValOK (C : Contract) (σ τ : State) (ρ : Sym) (n : Nat) : Prop :=
  ∀ v : MValT C, v.lsize < n → v.inL ρ = true → ∃ w g, v.toL ρ = some (w, g) ∧
    (Rets (g.eval σ) → ∃ mv, v.eval τ = .ok mv) ∧
    ∀ mv, v.eval τ = .ok mv → Rets (g.eval σ) ∧ w.eval σ (ρ.mem.births σ) = .ok mv

section
variable {σ τ : State} {ρ : Sym}

/-- **A term reads, pushed in, what it read after the updates.**  Example:
after `balances[k] = 5;`, the local `y` of `uint y = balances[k];` is the
term `find(save(storage, balances[k], 5), balances[k])`, read in the state
before the write. -/
theorem Term.toL_step (h : Rel σ ρ τ) {n : Nat}
    (hT : TermOK C σ τ ρ n) (hP : PathOK C σ τ ρ n) (hI : IdOK C σ τ ρ n)
    (hA : AddrOK C σ τ ρ n) (hM : MemOK C σ τ ρ n) (_hV : MValOK C σ τ ρ n) :
    TermOK C σ τ ρ (n + 1) := fun t hn hf => match t, hn, hf with
  | .lit _, hn, _ => Sim.refl _
  | .env k, hn, _ => by
    rw [Close.Term.eval_env, h.tx k]
    exact Sim.refl _
  | .pv x, hn, _ => by
    have hx := h.env x
    rw [Close.Term.eval_pv]
    apply Sim.of_eq
    rcases hl : lookupBy x ρ.env with _ | ⟨t⟩ | ⟨q⟩ | _ | ⟨S⟩ | ⟨k⟩ <;> rw [hl] at hx <;>
      simp only [EnvRel] at hx <;> simp only [Tm.toL, hl]
    · rw [hx]; rfl
    · obtain ⟨v, h₁, h₂⟩ := hx; rw [h₁, h₂]; rfl
    · obtain ⟨r, segs, _, h₂, _⟩ := hx; rw [h₂]; rfl
    · obtain ⟨r, segs, -, h₂⟩ := hx; rw [h₂]; rfl
    · obtain ⟨st, -, h₂⟩ := hx; rw [h₂]; rfl
    · obtain ⟨n', -, h₂⟩ := hx; rw [h₂]; rfl
  | .binop op p a b, hn, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    rw [Close.Term.eval_binop]
    simp only [Tm.toL, Op2.toLAt, Op2.toL, LTerm.mkBin_eval, LTerm.eval]
    exact Sim.bind (hT a (by lsize_tac) hf.1) fun _ => evalBinop_sim (hT b (by lsize_tac) hf.2)
  | .unop op p a, hn, hf => by
    simp only [Tm.inL, Op1.inL] at hf
    rw [Close.Term.eval_unop]
    simp only [Tm.toL, Op1.toL, LTerm.mkUn_eval, LTerm.eval]
    exact Sim.bind (hT a (by lsize_tac) hf) fun _ => Sim.refl _
  | .find s p, hn, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true, Bool.or_eq_true] at hf
    obtain ⟨hs | hs, hf⟩ := hf
    · obtain rfl := STerm.isStorage_eq hs
      have hb := live_bridge (hP p (by lsize_tac) hf)
      rw [Close.Term.eval_find]
      simp only [Tm.toL, Tm.storLocal?, Op2.toLAt, Op0.toL, LTerm.eval, h.stor, Res.ok_bind]
      intro a
      simp only [Res.bind_eq_ok, Close.STerm.eval_storage, Res.ok_bind]
      constructor
      · rintro ⟨qs, hq, c, hc, ha⟩
        obtain ⟨rs, hrs, rfl, hfs⟩ := (hb qs c).1 ⟨hq, hc⟩
        exact ⟨rs, hrs, c, hfs, ha⟩
      · rintro ⟨rs, hrs, c, hfs, ha⟩
        obtain ⟨hq, hc⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hfs⟩
        exact ⟨_, hq, c, hc, ha⟩
    · -- `find(old, p)`: the path checked against the storage the updates left,
      -- the snapshot read there
      obtain ⟨x, S, rfl, hl⟩ := Tm.storLocal?_isSome hs
      have hx := h.env x
      rw [hl] at hx
      obtain ⟨st, hS, hst⟩ := hx
      have hA := hP p (by lsize_tac) hf
      have hg := guardPath_ok h.stor (p.toL ρ)
      rw [Close.Term.eval_find, Close.STerm.eval_pv, hst]
      simp only [Tm.toL, Tm.storLocal?, hl, Op2.toLAt, LTerm.eval, hS, Res.ok_bind,
        Close.bindingStore_store]
      intro a
      constructor
      · intro H
        obtain ⟨g, hgv, H⟩ := Res.bind_eq_ok.1 H
        obtain ⟨qs, hq, hlive⟩ := hg.1 ⟨g, hgv⟩
        obtain ⟨rs, hrs, rfl⟩ := (hA _).2 ⟨hq, hlive⟩
        rw [hq, Res.ok_bind] at H
        rw [hrs, Res.ok_bind, ← find_root]
        exact H
      · intro H
        obtain ⟨rs, hrs, H⟩ := Res.bind_eq_ok.1 H
        obtain ⟨hq, hlive⟩ := (hA _).1 ⟨rs, hrs, rfl⟩
        obtain ⟨g, hgv⟩ := hg.2 ⟨_, hq, hlive⟩
        rw [hgv, Res.ok_bind, hq, Res.ok_bind]
        rw [← find_root] at H
        exact H
  | .len s p, hn, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨hs, hf⟩ := hf
    obtain rfl := STerm.isStorage_eq hs
    have hb := live_bridge (hP p (by lsize_tac) hf)
    rw [Close.Term.eval_len]
    simp only [Tm.toL, Op0.toL, Op2.toLAt, Op2.toL, LTerm.eval, h.stor, Res.ok_bind]
    intro a
    simp only [Res.bind_eq_ok, Close.STerm.eval_storage, Res.ok_bind]
    constructor
    · rintro ⟨qs, hq, c, hc, ha⟩
      obtain ⟨rs, hrs, rfl, hfs⟩ := (hb qs c).1 ⟨hq, hc⟩
      exact ⟨rs, hrs, c, hfs, ha⟩
    · rintro ⟨rs, hrs, c, hfs, ha⟩
      obtain ⟨hq, hc⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hfs⟩
      exact ⟨_, hq, c, hc, ha⟩
  | .ite c a b, hn, hf => by
    simp only [Tm.inL, Op3.inL, Bool.and_eq_true] at hf
    rw [Close.Term.eval_ite]
    simp only [Tm.toL, Op3.toLAt, Op3.toL, LTerm.eval]
    exact Sim.bind (hT c (by lsize_tac) hf.1.1) fun _ =>
      pickBranch_sim (hT a (by lsize_tac) hf.1.2) (hT b (by lsize_tac) hf.2)
  | .read m a, hn, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨⟨hm, ha⟩, hr⟩ := hf
    obtain ⟨M, g, hM, hmr, hme⟩ := hM m (by lsize_tac) hm
    obtain ⟨j, sel, g', hA, har, hae⟩ := hA a (by lsize_tac) ha
    simp only [hM, hA, readM, Option.isSome_map] at hr
    obtain ⟨r, hrr⟩ := Option.isSome_iff_exists.1 hr
    simp only [Tm.toL, Op2.toLAt, Op2.toL, hM, hA, readM, hrr, Option.map_some, Option.getD_some]
    rw [Close.Term.eval_read]
    intro w
    rw [seqL_eval, seqL_eval]
    constructor
    · intro hw
      obtain ⟨_, hg, hw⟩ := Res.bind_eq_ok.1 hw
      obtain ⟨_, hg', hw⟩ := Res.bind_eq_ok.1 hw
      obtain ⟨μ', hμ'⟩ := hmr ⟨_, hg⟩
      obtain ⟨-, μ, B, hrun, hh, hp⟩ := hme μ' hμ'
      obtain ⟨ad, had⟩ := har ⟨_, hg'⟩
      obtain ⟨-, n0, hn0, hsa⟩ := hae ad had
      have hs := LMem.readT_sim σ M j sel hrun hrr w
      rw [LId.evalR_prefix hp hn0, Res.ok_bind, LSel.read_of_addr hsa, readAddr_of_heap hh.1] at hs
      rw [hμ', Res.ok_bind, had, Res.ok_bind]
      exact hs.1 hw
    · intro hw
      obtain ⟨μ', hμ', hw⟩ := Res.bind_eq_ok.1 hw
      obtain ⟨ad, had, hw⟩ := Res.bind_eq_ok.1 hw
      obtain ⟨⟨_, hg⟩, μ, B, hrun, hh, hp⟩ := hme μ' hμ'
      obtain ⟨⟨_, hg'⟩, n0, hn0, hsa⟩ := hae ad had
      have hs := LMem.readT_sim σ M j sel hrun hrr w
      rw [LId.evalR_prefix hp hn0, Res.ok_bind, LSel.read_of_addr hsa, readAddr_of_heap hh.1] at hs
      rw [hg, Res.ok_bind, hg', Res.ok_bind]
      exact hs.2 hw
  | .app2 .mlen m i, hn, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨⟨hm, hi⟩, hr⟩ := hf
    obtain ⟨M, g, hM, hmr, hme⟩ := hM m (by lsize_tac) hm
    obtain ⟨j, g', hI, hir, hie⟩ := hI i (by lsize_tac) hi
    simp only [hM, hI, lenM, Option.isSome_map] at hr
    obtain ⟨r, hrr⟩ := Option.isSome_iff_exists.1 hr
    simp only [Tm.toL, Op2.toLAt, Op2.toL, hM, hI, lenM, hrr, Option.map_some, Option.getD_some]
    intro w
    rw [seqL_eval, seqL_eval]
    simp only [tm_eval]
    constructor
    · intro hw
      obtain ⟨_, hg, hw⟩ := Res.bind_eq_ok.1 hw
      obtain ⟨_, hg', hw⟩ := Res.bind_eq_ok.1 hw
      obtain ⟨μ', hμ'⟩ := hmr ⟨_, hg⟩
      obtain ⟨-, μ, B, hrun, hh, hp⟩ := hme μ' hμ'
      obtain ⟨id, hid⟩ := hir ⟨_, hg'⟩
      obtain ⟨-, hj⟩ := hie id hid
      have hs := LMem.readT_sim σ M j .size hrun hrr w
      rw [LId.evalR_prefix hp hj, Res.ok_bind] at hs
      simp only [LSel.read, memArrayLen_of_heap hh.1] at hs
      rw [hμ', Res.ok_bind, hid, Res.ok_bind]
      exact hs.1 hw
    · intro hw
      obtain ⟨μ', hμ', hw⟩ := Res.bind_eq_ok.1 hw
      obtain ⟨id, hid, hw⟩ := Res.bind_eq_ok.1 hw
      obtain ⟨⟨_, hg⟩, μ, B, hrun, hh, hp⟩ := hme μ' hμ'
      obtain ⟨⟨_, hg'⟩, hj⟩ := hie id hid
      have hs := LMem.readT_sim σ M j .size hrun hrr w
      rw [LId.evalR_prefix hp hj, Res.ok_bind] at hs
      simp only [LSel.read, memArrayLen_of_heap hh.1] at hs
      rw [hg, Res.ok_bind, hg', Res.ok_bind]
      exact hs.2 hw
  | .net _, _, hf | .netOf _ _, _, hf => by
    simp only [Tm.inL, Bool.false_eq_true, Op1.inL] at hf

/-- **A path, pushed in, is the path the program took**: the program's
path returns exactly where the path pushed in does and every index on it is
in bounds of the storage the updates left (`LiveTo`).  Example: `values[i]`
returns in neither where `i` is past the end. -/
theorem PTerm.toL_step (h : Rel σ ρ τ) {n : Nat}
    (hT : TermOK C σ τ ρ n) (hP : PathOK C σ τ ρ n) (_hI : IdOK C σ τ ρ n)
    (_hA : AddrOK C σ τ ρ n) (_hM : MemOK C σ τ ρ n) (_hV : MValOK C σ τ ρ n) :
    PathOK C σ τ ρ (n + 1) := fun p hn hf qs => match p, hn, hf, qs with
  | .root r, hn, _, qs => by
    simp only [Tm.toL, Op0.toL, LPath.eval, tm_eval]
    constructor
    · rintro ⟨rs, hrs, rfl⟩
      cases hrs
      exact ⟨rfl, LiveTo.of_noAt _ rfl⟩
    · rintro ⟨hq, -⟩
      cases hq
      exact ⟨(r, []), rfl, rfl⟩
  | .pv x, hn, hf, qs => by
    have hx := h.env x
    rw [Close.PTerm.eval_pv]
    simp only [Tm.inL] at hf
    rcases hl : lookupBy x ρ.env with _ | ⟨t⟩ | ⟨q⟩ | _ | ⟨S⟩ | ⟨k⟩ <;> rw [hl] at hx hf <;>
      simp only [EnvRel, Bool.false_eq_true] at hx hf <;>
      simp only [Tm.toL, hl]
    · obtain ⟨v, _, h₂⟩ := hx
      simp only [bind, Except.bind, h₂, Close.bindingPath, reduceCtorEq, false_and, exists_const,
          LPath.stuck, LPath.eval, LTerm.eval]
    · obtain ⟨r, segs, h₁, h₂, hlive⟩ := hx
      simp only [h₂, h₁, Res.ok_bind, Close.bindingPath]
      constructor
      · rintro ⟨rs, hrs, rfl⟩
        cases hrs
        exact ⟨rfl, hlive⟩
      · rintro ⟨hq, -⟩
        cases hq
        exact ⟨(r, segs), rfl, rfl⟩
  | .field p f, hn, hf, qs => by
    simp only [Tm.inL, Op1.inL] at hf
    rw [Close.PTerm.eval_field]
    simp only [Tm.toL, Op1.toL, LPath.eval]
    constructor
    · rintro ⟨rs', hrs', rfl⟩
      obtain ⟨rs, hrs, he⟩ := Res.bind_eq_ok.1 hrs'
      cases he
      obtain ⟨hq, hl⟩ := (hP p (by lsize_tac) hf _).1 ⟨rs, hrs, rfl⟩
      refine ⟨by rw [hq]; rfl, ?_⟩
      show LiveTo _ ((.field rs.1 :: rs.2) ++ [.field f])
      unfold LiveTo
      rw [lastAtSegs_field]
      exact hl
    · rintro ⟨hq, hl⟩
      obtain ⟨qs₀, hq₀, he⟩ := Res.bind_eq_ok.1 hq
      cases he
      have hl₀ : LiveTo (.struct τ.storage) qs₀ := by unfold LiveTo at hl ⊢; rw [lastAtSegs_field] at hl; exact hl
      obtain ⟨rs, hrs, rfl⟩ := (hP p (by lsize_tac) hf qs₀).2 ⟨hq₀, hl₀⟩
      exact ⟨(rs.1, rs.2 ++ [.field f]), by rw [hrs]; rfl, by simp only [List.cons_append]⟩
  | .at p i, hn, hf, qs => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    have hi := hT i (by lsize_tac) hf.2
    rw [Close.PTerm.eval_at]
    simp only [Tm.toL, Op2.toLAt, Op2.toL, LPath.eval]
    constructor
    · rintro ⟨rs', hrs', rfl⟩
      obtain ⟨rs, hrs, hr⟩ := Res.bind_eq_ok.1 hrs'
      obtain ⟨k, hk, hr⟩ := Res.bind_eq_ok.1 hr
      obtain ⟨v, hv, hk⟩ := Res.bind_eq_ok.1 hk
      obtain ⟨u, hu, he⟩ := Res.bind_eq_ok.1 hr
      cases he
      rw [Close.checkIndex_eq] at hu
      obtain ⟨c, hc, hu⟩ := Res.bind_eq_ok.1 hu
      obtain ⟨hq, hl⟩ := (hP p (by lsize_tac) hf.1 _).1 ⟨rs, hrs, rfl⟩
      refine ⟨by rw [hq, Res.ok_bind, (hi v).2 hv, Res.ok_bind, hk]; rfl, ?_⟩
      show LiveTo _ ((.field rs.1 :: rs.2) ++ [.at k])
      unfold LiveTo
      rw [lastAtSegs_at, SVal.findLive_append, ← hl.find_eq, find_root, hc, Res.ok_bind]
      exact (idx_iff c k).1 (by cases u; exact hu)
    · rintro ⟨hq, hl⟩
      obtain ⟨qs₀, hq₀, hq⟩ := Res.bind_eq_ok.1 hq
      obtain ⟨k, hk, he⟩ := Res.bind_eq_ok.1 hq
      cases he
      obtain ⟨v, hv, hk⟩ := Res.bind_eq_ok.1 hk
      obtain ⟨c', hc'⟩ := hl
      rw [lastAtSegs_at, SVal.findLive_append] at hc'
      obtain ⟨c, hc, hck⟩ := Res.bind_eq_ok.1 hc'
      have hl₀ := LiveTo.of_findLive hc
      obtain ⟨rs, hrs, rfl⟩ := (hP p (by lsize_tac) hf.1 qs₀).2 ⟨hq₀, hl₀⟩
      refine ⟨(rs.1, rs.2 ++ [.at k]), ?_, by simp only [List.cons_append]⟩
      have hfs : τ.findStorage rs.1 rs.2 = .ok c := by rw [← find_root, hl₀.find_eq]; exact hc
      rw [hrs, Res.ok_bind, (hi v).1 hv, Res.ok_bind, hk, Res.ok_bind, Close.checkIndex_eq,
        hfs, Res.ok_bind, (idx_iff c k).2 ⟨c', hck⟩, Res.ok_bind]
  | .next _, hn, hf, _ => by simp only [Tm.inL, Op1.inL, Bool.false_eq_true] at hf
  | .nextIn _ _, hn, hf, _ => by simp only [Tm.inL, Op2.inL, Bool.false_eq_true] at hf
  | .atIn _ _ _, hn, hf, _ => by simp only [Tm.inL, Op3.inL, Bool.false_eq_true] at hf

theorem addMOf?_some {m : MTerm C} {R : RefTy} (h : addMOf? m = some R) :
    m = .app1 (.addM R) (.app0 .memory) := by
  unfold addMOf? at h
  split at h
  · cases h; rfl
  · cases h

theorem allocRefOf?_some {v : MValT C} {R : RefTy} (h : allocRefOf? v = some R) :
    v = .app1 .ref (.app1 (.alloc R) (.app0 .memory)) := by
  unfold allocRefOf? at h
  split at h
  · cases h; rfl
  · cases h

/-- The value of a write is its own, or the root a `delete` allocates. -/
theorem freshRef_cases (ρ : Sym) (m : MTerm C) (v : MValT C) :
    (∀ z, freshRef ρ m v z = z) ∨ ∃ R, m = .app1 (.addM R) (.app0 .memory) ∧
      v = .app1 .ref (.app1 (.alloc R) (.app0 .memory)) ∧
      ∀ z, freshRef ρ m v z = some (.ref ⟨ρ.mem.nAlloc, []⟩, .lit (.bool true)) := by
  cases hm : addMOf? m with
  | none => exact Or.inl fun _ => by simp only [freshRef, hm]
  | some R =>
    cases hv : allocRefOf? v with
    | none => exact Or.inl fun _ => by simp only [freshRef, hm, hv]
    | some R' =>
      by_cases hR : R = R'
      · subst hR
        exact Or.inr ⟨R, addMOf?_some hm, allocRefOf?_some hv,
          fun _ => by simp only [freshRef, hm, hv, ↓reduceIte]⟩
      · exact Or.inl fun _ => by simp only [freshRef, hm, hv, hR, ↓reduceIte]

/-- **An identity, pushed in**: a name of the object the term denotes, and
a guard that returns exactly where the term does.  A reference slot read is
the name `LMem.readI` finds, of an object the updates' memory has
(`irOk`). -/
theorem ITerm.toL_step (h : Rel σ ρ τ) {n : Nat}
    (_hT : TermOK C σ τ ρ n) (_hP : PathOK C σ τ ρ n) (_hI : IdOK C σ τ ρ n)
    (hA : AddrOK C σ τ ρ n) (hM : MemOK C σ τ ρ n) (_hV : MValOK C σ τ ρ n) :
    IdOK C σ τ ρ (n + 1) := fun i hn hf => match i, hn, hf with
  | .pvI x, hn, hf => by
    have hx := h.env x
    simp only [Tm.inL] at hf
    split at hf
    · rename_i j hl
      rw [hl] at hx
      obtain ⟨n', hn', he⟩ := hx
      refine ⟨j, .lit (.bool true), by simp only [Tm.toL, hl], fun _ => ⟨n', ?_⟩,
        fun id hid => ?_⟩
      · rw [Close.ITerm.eval_pv, he]; rfl
      · rw [Close.ITerm.eval_pv, he] at hid
        simp only [Res.ok_bind, Close.bindingRef_mref, Except.ok.injEq] at hid
        subst hid
        exact ⟨⟨_, rfl⟩, hn'⟩
    · cases hf
  | .app1 (.alloc _) _, hn, hf => by simp only [Tm.inL, Op1.inL, Bool.false_eq_true] at hf
  | .app2 .copy _ _, hn, hf => by simp only [Tm.inL, Op2.inL, Bool.false_eq_true] at hf
  | .app2 .iread m a, hn, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨⟨hm, ha⟩, hs⟩ := hf
    obtain ⟨M, g, hM, hmr, hme⟩ := hM m (by lsize_tac) hm
    obtain ⟨j, sel, g', hA, har, hae⟩ := hA a (by lsize_tac) ha
    simp only [hM, hA, ireadM] at hs
    cases hj' : M.readI j sel with
    | none => simp only [hj', Option.bind_none, irOk, Bool.false_eq_true] at hs
    | some j' =>
      cases hng : M.nameG j' with
      | none =>
        simp only [hj', hng, Option.bind_some, Option.map_none, irOk, Bool.false_eq_true] at hs
      | some ng =>
        simp only [hj', hng, Option.bind_some, Option.map_some, irOk, decide_eq_true_eq] at hs
        refine ⟨j', seqL g (seqL g' ng), by
          simp only [Tm.toL, Op2.toLAt, Op2.toL, hM, hA, ireadM, hj', hng, Option.bind_some,
            Option.map_some], fun hgg => ?_, fun id hid => ?_⟩
        · obtain ⟨hg, hgg⟩ := (seqL_rets σ _ _).1 hgg
          obtain ⟨hg', hng'⟩ := (seqL_rets σ _ _).1 hgg
          obtain ⟨μ', hμ'⟩ := hmr hg
          obtain ⟨-, μ, B, hrun, hh, hp⟩ := hme μ' hμ'
          obtain ⟨ad, had⟩ := har hg'
          obtain ⟨-, n0, hn0, hsa⟩ := hae ad had
          obtain ⟨id, hid⟩ := (LMem.nameG_sim σ M j' hrun hng).1 hng'
          have hs' := (LMem.readI_sim σ M j sel hrun hj').2 id
          rw [LId.evalR_prefix hp hn0, Res.ok_bind, LSel.iread_of_addr hsa,
            readAddr_of_heap hh.1] at hs'
          refine ⟨id, ?_⟩
          rw [Close.ITerm.eval_read, hμ', Res.ok_bind, had, Res.ok_bind]
          exact hs'.1 hid
        · rw [Close.ITerm.eval_read] at hid
          obtain ⟨μ', hμ', hid⟩ := Res.bind_eq_ok.1 hid
          obtain ⟨ad, had, hid⟩ := Res.bind_eq_ok.1 hid
          obtain ⟨hg, μ, B, hrun, hh, hp⟩ := hme μ' hμ'
          obtain ⟨hg', n0, hn0, hsa⟩ := hae ad had
          have hs' := (LMem.readI_sim σ M j sel hrun hj').2 id
          rw [LId.evalR_prefix hp hn0, Res.ok_bind, LSel.iread_of_addr hsa,
            readAddr_of_heap hh.1] at hs'
          have hB : LId.evalR B j' = .ok id := hs'.2 hid
          refine ⟨(seqL_rets σ _ _).2 ⟨hg, (seqL_rets σ _ _).2
            ⟨hg', (LMem.nameG_sim σ M j' hrun hng).2 ⟨id, hB⟩⟩⟩, ?_⟩
          exact LId.evalR_prefix_lt hp (by rw [h.births_length]; exact hs) hB

/-- **An address, pushed in**: the name and what selects in it. -/
theorem MAddr.toL_step (_h : Rel σ ρ τ) {n : Nat}
    (hT : TermOK C σ τ ρ n) (_hP : PathOK C σ τ ρ n) (hI : IdOK C σ τ ρ n)
    (_hA : AddrOK C σ τ ρ n) (_hM : MemOK C σ τ ρ n) (_hV : MValOK C σ τ ρ n) :
    AddrOK C σ τ ρ (n + 1) := fun a hn hf => match a, hn, hf with
  | .app1 (.mfield f) i, hn, hf => by
    simp only [Tm.inL, Op1.inL] at hf
    obtain ⟨j, g, hI, hir, hie⟩ := hI i (by lsize_tac) hf
    refine ⟨j, .fld f, g, by simp only [Tm.toL, Op1.toL, hI, Option.map_some], fun hg => ?_,
      fun ad had => ?_⟩
    · obtain ⟨id, hid⟩ := hir hg
      exact ⟨_, by rw [Close.MAddr.eval_field, hid, Res.ok_bind]⟩
    · rw [Close.MAddr.eval_field] at had
      obtain ⟨id, hid, had⟩ := Res.bind_eq_ok.1 had
      obtain ⟨hg, hj⟩ := hie id hid
      cases had
      exact ⟨hg, id, hj, rfl⟩
  | .app2 .mat i t, hn, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨j, g, hI, hir, hie⟩ := hI i (by lsize_tac) hf.1
    have ht := hT t (by lsize_tac) hf.2
    refine ⟨j, .idx (t.toL ρ), seqL g (isIntL (t.toL ρ)),
      by simp only [Tm.toL, Op2.toLAt, Op2.toL, hI, Option.map_some], fun hw => ?_,
      fun ad had => ?_⟩
    · obtain ⟨hg, hi⟩ := (seqL_rets σ _ _).1 hw
      obtain ⟨k, hk⟩ := (isIntL_ret σ _).1 hi
      obtain ⟨id, hid⟩ := hir hg
      exact ⟨.memoryIndex id k, by rw [Close.MAddr.eval_at, hid, Res.ok_bind, (ht _).1 hk]; rfl⟩
    · rw [Close.MAddr.eval_at] at had
      obtain ⟨id, hid, had⟩ := Res.bind_eq_ok.1 had
      obtain ⟨hg, hj⟩ := hie id hid
      obtain ⟨k, hk, had⟩ := Res.bind_eq_ok.1 had
      obtain ⟨w, hw, hk⟩ := Res.bind_eq_ok.1 hk
      cases w with
      | bool b => cases hk
      | int k' =>
        cases hk
        cases had
        have hw' := (ht _).2 hw
        refine ⟨(seqL_rets σ _ _).2 ⟨hg, (isIntL_ret σ _).2 ⟨_, hw'⟩⟩, id, hj, ?_⟩
        simp only [LSel.addr, hw', Res.ok_bind, Value.asInt]

/-- The value a write writes, in every run of its memory that allocates
after the updates': a value of the fragment, or the root a `delete`
allocates under the write (`freshRef`). -/
theorem writeVal_ok (h : Rel σ ρ τ) {n : Nat} (hV : MValOK C σ τ ρ n) {m : MTerm C}
    {v : MValT C} (hvn : v.lsize < n) {M : LMem} {g : LTerm} (hM : m.toL ρ = some (M, g))
    (hv : (v.inL ρ || (freshRef ρ m v none).isSome) = true) :
    ∃ w gv, freshRef ρ m v (v.toL ρ) = some (w, gv) ∧
      (Rets (gv.eval σ) → ∃ mv, v.eval τ = .ok mv) ∧
      ∀ mv, v.eval τ = .ok mv → Rets (gv.eval σ) ∧
        ∀ μ B, M.run σ = .ok (μ, B) → ρ.mem.births σ <+: B → w.eval σ B = .ok mv := by
  rcases freshRef_cases ρ m v with hz | ⟨R, rfl, rfl, hfr⟩
  · rw [hz none, Option.isSome_none, Bool.or_false] at hv
    obtain ⟨w, gv, hw, hvr, hve⟩ := hV v hvn hv
    refine ⟨w, gv, by rw [hz, hw], hvr, fun mv hmv => ?_⟩
    obtain ⟨hg, hwe⟩ := hve mv hmv
    exact ⟨hg, fun _ _ _ hp => LMV.eval_prefix hp hwe⟩
  · simp only [Tm.toL, Op1.toL, Op0.toL, Option.bind_some] at hM
    split at hM
    · rename_i hR
      simp only [Option.some.injEq, Prod.mk.injEq] at hM
      obtain ⟨rfl, -⟩ := hM
      have hve : ∀ mv, (MValT.ref (ITerm.alloc .memory R) : MValT C).eval τ = .ok mv ↔
          ∃ τ₁ id, allocDefault τ R = .ok (τ₁, id) ∧ mv = .ref id := by
        intro mv
        rw [Close.MValT.eval_ref, Close.ITerm.eval_alloc, Close.MTerm.eval_memory, Res.ok_bind]
        constructor
        · intro hmv
          obtain ⟨id, hid, hmv⟩ := Res.bind_eq_ok.1 hmv
          obtain ⟨r, hr, hid⟩ := Res.bind_eq_ok.1 hid
          cases hid; cases hmv
          exact ⟨r.1, r.2, hr, rfl⟩
        · rintro ⟨τ₁, id, hr, rfl⟩
          rw [hr]; rfl
      refine ⟨_, _, hfr _, fun _ => ?_, fun mv hmv => ⟨⟨_, rfl⟩, fun μ B hrun _ => ?_⟩⟩
      · obtain ⟨τ₁, id, hr⟩ := allocDefault_ok hR τ
        exact ⟨_, (hve _).2 ⟨τ₁, id, hr, rfl⟩⟩
      · obtain ⟨τ₁, id, hr, rfl⟩ := (hve mv).1 hmv
        obtain ⟨μ₀, B₀, id₀, hr₀, hk, hc, rfl⟩ := LMem.run_addM hrun
        obtain ⟨μ₁, B₁, hr₁, hh⟩ := h.mem
        rw [hr₁, Except.ok.injEq, Prod.mk.injEq] at hr₀
        obtain ⟨rfl, rfl⟩ := hr₀
        rcases (allocDefault_heap hh R).cases with ⟨e, h₁, -⟩ | ⟨t₁, t₂, id', h₁, h₂, -⟩
        · rw [allocDefault_of_copy hc] at h₁; cases h₁
        · rw [allocDefault_of_copy hc, Except.ok.injEq, Prod.mk.injEq] at h₁
          rw [hr, Except.ok.injEq, Prod.mk.injEq] at h₂
          obtain ⟨-, rfl⟩ := h₁
          obtain ⟨-, rfl⟩ := h₂
          simp only [LMV.eval]
          rw [evalR_last _ _ hk]
          rfl
    · cases hM

/-- **A memory, pushed in**: the writes and allocations, run to the heap the
term leaves, and a guard that returns exactly where the term does. -/
theorem MTerm.toL_step (h : Rel σ ρ τ) {n : Nat}
    (hT : TermOK C σ τ ρ n) (_hP : PathOK C σ τ ρ n) (_hI : IdOK C σ τ ρ n)
    (hA : AddrOK C σ τ ρ n) (hM : MemOK C σ τ ρ n) (hV : MValOK C σ τ ρ n) :
    MemOK C σ τ ρ (n + 1) := fun m hn hf => match m, hn, hf with
  | .app0 .memory, hn, _ => by
    obtain ⟨μ, B, hr, hh⟩ := h.mem
    refine ⟨ρ.mem, .lit (.bool true), rfl, fun _ => ⟨τ, rfl⟩, fun μ' hμ' => ?_⟩
    cases hμ'
    exact ⟨⟨_, rfl⟩, μ, B, hr, hh, by rw [LMem.births_of_run hr]; exact List.prefix_refl B⟩
  | .app1 (.addM R) m, hn, hf => by
    simp only [Tm.inL, Op1.inL, Bool.and_eq_true] at hf
    obtain ⟨hm, hs⟩ := hf
    obtain ⟨M, g, hM, hmr, hme⟩ := hM m (by lsize_tac) hm
    simp only [hM, Op1.toL, Option.bind_some] at hs
    have hR : allocOk R = true := by
      cases hR : allocOk R
      · simp only [hR, Bool.false_eq_true, ↓reduceIte, Option.isSome_none] at hs
      · rfl
    refine ⟨.addM M M.nAlloc R, g, by
      simp only [Tm.toL, Op1.toL, hM, Option.bind_some, hR, ↓reduceIte], fun hg => ?_,
      fun μ' hμ' => ?_⟩
    · obtain ⟨μ₀', hμ₀'⟩ := hmr hg
      obtain ⟨τ₁, id, ha⟩ := allocDefault_ok hR μ₀'
      exact ⟨τ₁, by rw [Close.MTerm.eval_addM, hμ₀', Res.ok_bind, ha]; rfl⟩
    · rw [Close.MTerm.eval_addM] at hμ'
      obtain ⟨μ₀', hμ₀', hμ'⟩ := Res.bind_eq_ok.1 hμ'
      obtain ⟨hg, μ, B, hrun, hh, hp⟩ := hme μ₀' hμ₀'
      obtain ⟨r, ha', hμ'⟩ := Res.bind_eq_ok.1 hμ'
      cases hμ'
      rcases (allocDefault_heap hh R).cases with ⟨e, -, h₂⟩ | ⟨t₁, t₂, id, h₁, h₂, ht⟩
      · rw [h₂] at ha'; cases ha'
      · rw [h₂] at ha'; cases ha'
        refine ⟨hg, t₁, B ++ [MemNames.Birth.ofCopy μ t₁ id], ?_, ht,
          hp.trans (List.prefix_append _ _)⟩
        simp only [LMem.run, hrun, Res.ok_bind, LMem.run_nAlloc σ M hrun, ↓reduceIte, h₁]
  | .app2 .copySt m v, hn, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨⟨hm, hv⟩, hs⟩ := hf
    obtain ⟨M, g, hMm, hmr, hme⟩ := hM m (by lsize_tac) hm
    match v, hv, hs with
    | .app1 .sval _, _, hs | .app2 .sfind _ _, _, hs =>
      simp only [Tm.toL, Op1.toL, Op2.toLAt, Op2.toL, hMm, newM, Option.isSome_none,
        Bool.false_eq_true] at hs
    | .app2 .copyMem _ _, _, hs =>
      simp only [Tm.toL, Op2.toLAt, Op2.toL, newM_memL, Option.isSome_none,
        Bool.false_eq_true] at hs
    | .app1 (.newArr R) nt, hv, hs =>
      simp only [Tm.inL, Op1.inL] at hv
      have hnt := hT nt (by lsize_tac) hv
      simp only [Tm.toL, Op1.toL, hMm, newM] at hs
      have hR : allocOk R = true := by
        cases hR : allocOk R
        · simp only [hR, Bool.false_eq_true, ↓reduceIte, Option.isSome_none] at hs
        · rfl
      refine ⟨.newArr M M.nAlloc R (nt.toL ρ), seqL g (isIntL (nt.toL ρ)), by
        simp only [Tm.toL, Op2.toLAt, Op2.toL, Op1.toL, hMm, newM, hR, ↓reduceIte],
        fun hgg => ?_, fun μ' hμ' => ?_⟩
      · obtain ⟨hg, hi⟩ := (seqL_rets σ _ _).1 hgg
        obtain ⟨c, hc⟩ := (isIntL_ret σ _).1 hi
        obtain ⟨μ₀', hμ₀'⟩ := hmr hg
        obtain ⟨⟨τ₁, mv⟩, hcp⟩ := (allocOk_newArr hR c).1.at μ₀'
        refine ⟨τ₁, ?_⟩
        rw [Close.MTerm.eval_copySt, (newArr_eval_ok.2 ⟨c, (hnt _).1 hc, rfl⟩), Res.ok_bind,
          hμ₀', Res.ok_bind, hcp]
        rfl
      · rw [Close.MTerm.eval_copySt] at hμ'
        obtain ⟨sv, hsv, hμ'⟩ := Res.bind_eq_ok.1 hμ'
        obtain ⟨μ₀', hμ₀', hμ'⟩ := Res.bind_eq_ok.1 hμ'
        obtain ⟨r, hcp, hμ'⟩ := Res.bind_eq_ok.1 hμ'
        cases hμ'
        obtain ⟨c, hc, rfl⟩ := newArr_eval_ok.1 hsv
        obtain ⟨hg, μ, B, hrun, hh, hp⟩ := hme μ₀' hμ₀'
        have hc' : (nt.toL ρ).eval σ = .ok (.int c) := (hnt _).2 hc
        rcases (copyStToM_heap hh (newArrVal R c)).cases with ⟨e, -, h₂⟩ |
          ⟨t₁, t₂, mv, h₁, h₂, ht⟩
        · rw [h₂] at hcp; cases hcp
        · rw [h₂] at hcp; cases hcp
          obtain ⟨id, rfl⟩ := copy_ref h₁ (allocOk_newArr hR c).2
          refine ⟨(seqL_rets σ _ _).2 ⟨hg, (isIntL_ret σ _).2 ⟨c, hc'⟩⟩, t₁,
            B ++ [MemNames.Birth.ofCopy μ t₁ id], ?_, ht, hp.trans (List.prefix_append _ _)⟩
          simp only [LMem.run, hc', Res.ok_bind, Value.asInt, hrun, LMem.run_nAlloc σ M hrun,
            ↓reduceIte, h₁, MVal.asRef]
          rfl
  | .app3 .write m a v, hn, hf => by
    simp only [Tm.inL, Op3.inL, Bool.and_eq_true] at hf
    obtain ⟨⟨⟨hm, ha⟩, hv⟩, hs⟩ := hf
    obtain ⟨M, g, hM, hmr, hme⟩ := hM m (by lsize_tac) hm
    obtain ⟨j, sel, g', hA, har, hae⟩ := hA a (by lsize_tac) ha
    obtain ⟨w, gv, hw, hvr, hve⟩ := writeVal_ok h hV (by lsize_tac) hM hv
    simp only [hM, hA, hw, writeM, Option.isSome_map] at hs
    obtain ⟨gw, hgw⟩ := Option.isSome_iff_exists.1 hs
    refine ⟨.write M j sel w, seqL gv (seqL g (seqL g' gw)), by
      simp only [Tm.toL, Op3.toLAt, hM, hA, hw, writeM, hgw, Option.map_some],
      fun hgg => ?_, fun μ' hμ' => ?_⟩
    · obtain ⟨hgv, hgg⟩ := (seqL_rets σ _ _).1 hgg
      obtain ⟨hg, hgg⟩ := (seqL_rets σ _ _).1 hgg
      obtain ⟨hg', hgw'⟩ := (seqL_rets σ _ _).1 hgg
      obtain ⟨mv, hmv⟩ := hvr hgv
      obtain ⟨μ₀', hμ₀'⟩ := hmr hg
      obtain ⟨-, μ, B, hrun, hh, hp⟩ := hme μ₀' hμ₀'
      obtain ⟨ad, had⟩ := har hg'
      obtain ⟨-, n0, hn0, hsa⟩ := hae ad had
      obtain ⟨n1, ad1, μ₁, hn1, hsa1, hwr⟩ := (LMem.writeG_sim σ hrun j sel hgw mv).1 hgw'
      rw [LId.evalR_prefix hp hn0, Except.ok.injEq] at hn1
      subst hn1
      rw [hsa, Except.ok.injEq] at hsa1
      subst hsa1
      rcases Res.memPart_cases (writeAddr_of_heap hh mv ad) with ⟨e, h₁, -⟩ |
        ⟨μ₂, μ₃, -, h₂, -⟩
      · rw [hwr] at h₁; cases h₁
      · exact ⟨μ₃, by rw [Close.MTerm.eval_write, hmv, Res.ok_bind, hμ₀', Res.ok_bind, had,
          Res.ok_bind, h₂]⟩
    · rw [Close.MTerm.eval_write] at hμ'
      obtain ⟨mv, hmv, hμ'⟩ := Res.bind_eq_ok.1 hμ'
      obtain ⟨μ₀', hμ₀', hμ'⟩ := Res.bind_eq_ok.1 hμ'
      obtain ⟨ad, had, hμ'⟩ := Res.bind_eq_ok.1 hμ'
      obtain ⟨hgv, hwv⟩ := hve mv hmv
      obtain ⟨hg, μ, B, hrun, hh, hp⟩ := hme μ₀' hμ₀'
      obtain ⟨hg', n0, hn0, hsa⟩ := hae ad had
      have hn0' := LId.evalR_prefix hp hn0
      rcases Res.memPart_cases (writeAddr_of_heap hh mv ad) with ⟨e, -, h₂⟩ |
        ⟨μ₂, μ₃, h₁, h₂, hh₂⟩
      · rw [h₂] at hμ'; cases hμ'
      · rw [h₂] at hμ'; cases hμ'
        refine ⟨(seqL_rets σ _ _).2 ⟨hgv, (seqL_rets σ _ _).2 ⟨hg, (seqL_rets σ _ _).2
          ⟨hg', (LMem.writeG_sim σ hrun j sel hgw mv).2 ⟨n0, ad, μ₂, hn0', hsa, h₁⟩⟩⟩⟩,
          μ₂, B, ?_, hh₂, hp⟩
        simp only [LMem.run, hrun, Res.ok_bind, hn0', hsa, hwv μ B hrun hp, h₁]

/-- **A memory value, pushed in**: what the slot holds. -/
theorem MValT.toL_step (_h : Rel σ ρ τ) {n : Nat}
    (hT : TermOK C σ τ ρ n) (_hP : PathOK C σ τ ρ n) (hI : IdOK C σ τ ρ n)
    (_hA : AddrOK C σ τ ρ n) (_hM : MemOK C σ τ ρ n) (_hV : MValOK C σ τ ρ n) :
    MValOK C σ τ ρ (n + 1) := fun v hn hf => match v, hn, hf with
  | .app1 .mval t, hn, hf => by
    simp only [Tm.inL, Op1.inL] at hf
    have ht := hT t (by lsize_tac) hf
    refine ⟨.word (t.toL ρ), t.toL ρ, by simp only [Tm.toL, Op1.toL], fun ⟨w, hw⟩ => ?_,
      fun mv hmv => ?_⟩
    · exact ⟨_, by rw [Close.MValT.eval_val, (ht w).1 hw, Res.ok_bind]⟩
    · rw [Close.MValT.eval_val] at hmv
      obtain ⟨w, hw, hmv⟩ := Res.bind_eq_ok.1 hmv
      cases hmv
      have hw' := (ht w).2 hw
      exact ⟨⟨w, hw'⟩, by simp only [LMV.eval, hw', Res.ok_bind]⟩
  | .app1 .ref i, hn, hf => by
    simp only [Tm.inL, Op1.inL] at hf
    obtain ⟨j, g, hI, hir, hie⟩ := hI i (by lsize_tac) hf
    refine ⟨.ref j, g, by simp only [Tm.toL, Op1.toL, hI, Option.map_some], fun hg => ?_,
      fun mv hmv => ?_⟩
    · obtain ⟨id, hid⟩ := hir hg
      exact ⟨_, by rw [Close.MValT.eval_ref, hid, Res.ok_bind]⟩
    · rw [Close.MValT.eval_ref] at hmv
      obtain ⟨id, hid, hmv⟩ := Res.bind_eq_ok.1 hmv
      cases hmv
      obtain ⟨hg, hj⟩ := hie id hid
      exact ⟨hg, by simp only [LMV.eval, hj, Res.ok_bind]⟩

/-- All six at every size. -/
theorem Rel.all_ok (h : Rel σ ρ τ) : (n : Nat) →
    TermOK C σ τ ρ n ∧ PathOK C σ τ ρ n ∧ IdOK C σ τ ρ n ∧ AddrOK C σ τ ρ n ∧
      MemOK C σ τ ρ n ∧ MValOK C σ τ ρ n
  | 0 => ⟨fun _ hn => absurd hn (Nat.not_lt_zero _), fun _ hn => absurd hn (Nat.not_lt_zero _),
      fun _ hn => absurd hn (Nat.not_lt_zero _), fun _ hn => absurd hn (Nat.not_lt_zero _),
      fun _ hn => absurd hn (Nat.not_lt_zero _), fun _ hn => absurd hn (Nat.not_lt_zero _)⟩
  | n + 1 =>
    have ⟨hT, hP, hI, hA, hM, hV⟩ := Rel.all_ok h n
    ⟨Term.toL_step h hT hP hI hA hM hV, PTerm.toL_step h hT hP hI hA hM hV,
      ITerm.toL_step h hT hP hI hA hM hV, MAddr.toL_step h hT hP hI hA hM hV,
      MTerm.toL_step h hT hP hI hA hM hV, MValT.toL_step h hT hP hI hA hM hV⟩

theorem Term.toL_eval (h : Rel σ ρ τ) (t : Term C) (hf : t.inL ρ = true) :
    Sim ((t.toL ρ).eval σ) (t.eval τ) :=
  (h.all_ok _).1 t (Nat.lt_succ_self _) hf

theorem PTerm.toL_chk (h : Rel σ ρ τ) (p : PTerm C) (hf : p.inL ρ = true) (qs : List Seg) :
    (∃ rs, p.eval τ = .ok rs ∧ qs = .field rs.1 :: rs.2) ↔
      ((p.toL ρ).eval σ = .ok qs ∧ LiveTo (.struct τ.storage) qs) :=
  (h.all_ok _).2.1 p (Nat.lt_succ_self _) hf qs

theorem ITerm.toL_eval (h : Rel σ ρ τ) (i : ITerm C) (hf : i.inL ρ = true) :
    ∃ j g, i.toL ρ = some (j, g) ∧ (Rets (g.eval σ) → ∃ id, i.eval τ = .ok id) ∧
      ∀ id, i.eval τ = .ok id → Rets (g.eval σ) ∧ LId.evalR (ρ.mem.births σ) j = .ok id :=
  (h.all_ok _).2.2.1 i (Nat.lt_succ_self _) hf

theorem MTerm.toL_eval (h : Rel σ ρ τ) (m : MTerm C) (hf : m.inL ρ = true) :
    ∃ M g, m.toL ρ = some (M, g) ∧ (Rets (g.eval σ) → ∃ μ', m.eval τ = .ok μ') ∧
      ∀ μ', m.eval τ = .ok μ' → Rets (g.eval σ) ∧
        ∃ μ B, M.run σ = .ok (μ, B) ∧ μ.HeapEq μ' ∧ ρ.mem.births σ <+: B :=
  (h.all_ok _).2.2.2.2.1 m (Nat.lt_succ_self _) hf

/-- A storage term, pushed in, is the write it made.  Example:
`delAt(storage, alice.account)`. -/
theorem STerm.toL_eval (h : Rel σ ρ τ) :
    (s : STerm C) → s.inL ρ = true →
      Sim ((s.toL ρ).eval σ) (s.eval τ >>= fun τ' => .ok (.struct τ'.storage))
  | .app0 .storage, _ => Sim.of_eq (by rw [Tm.toL, Op0.toL, h.stor]; rfl)
  | .app3 .save s p v, hf => by
    simp only [Tm.inL, Op3.inL, Bool.and_eq_true] at hf
    obtain ⟨⟨⟨hs, hp⟩, hv⟩, hz⟩ := hf
    obtain rfl := STerm.isStorage_eq hs
    match v, hv with
    | .app1 .sval t, hv =>
      have hf : p.inL ρ = true ∧ t.inL ρ = true := ⟨hp, hv⟩
      have ht := Term.toL_eval h t hf.2
      have hb := live_bridge (PTerm.toL_chk h p hf.1)
      rw [Close.STerm.eval_save]
      simp only [Tm.toL, Op0.toL, Op1.toL, Op3.toLAt, Op3.toL, LStor.eval, h.stor, Res.ok_bind,
          Close.STerm.eval_storage]
      intro a
      simp only [Res.bind_eq_ok]
      constructor
      · rintro ⟨x, hx, qs, hq, ha⟩
        obtain ⟨c, hc⟩ := findLive_of_saveLive ha
        obtain ⟨rs, hrs, rfl, hfs⟩ := (hb qs c).1 ⟨hq, hc⟩
        rw [saveLive_eq_save _ hc, save_root] at ha
        obtain ⟨τ'', h'', he⟩ := Res.bind_eq_ok.1 ha
        exact ⟨τ'', ⟨x, (ht x).1 hx, rs, hrs, h''⟩, he⟩
      · rintro ⟨τ'', ⟨x, hx, rs, hrs, h''⟩, he⟩
        have hsv : (SVal.struct τ.storage).save (.field rs.1 :: rs.2) x.toSVal = .ok a := by
          rw [save_root, h'', Res.ok_bind, he]
        obtain ⟨c, hc⟩ := find_of_save hsv
        rw [find_root] at hc
        obtain ⟨hq, hl⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hc⟩
        exact ⟨x, (ht x).2 hx, _, hq, by rw [saveLive_eq_save _ hl]; exact hsv⟩
    | .app2 .sfind s' p', hv =>
      simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hv
      obtain ⟨hs', hp'⟩ := hv
      obtain rfl := STerm.isStorage_eq hs'
      have hb := live_bridge (PTerm.toL_chk h p hp)
      have hb' := live_bridge (PTerm.toL_chk h p' hp')
      rw [Close.STerm.eval_save_find, Close.SValT.eval_find]
      simp only [Tm.toL, Op0.toL, Op2.toLAt, Op2.toL, Op3.toLAt, Op3.toL, LStor.eval, h.stor,
        Res.ok_bind, Close.STerm.eval_storage, bind_assoc]
      exact read_bridge hb' fun n => write_bridge hb fun c => .ok (c.overlay n)
    | .app1 (.newArr _) _, _ =>
      simp only [Tm.toL, Op1.toL, LVal.storable, Bool.false_eq_true] at hz
    | .app2 .copyMem m i, hv =>
      simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hv
      obtain ⟨⟨hm, hi⟩, hl⟩ := hv
      obtain ⟨M, g, hMm, hmr, hme⟩ := MTerm.toL_eval h m hm
      obtain ⟨j, g', hIi, hir, hie⟩ := ITerm.toL_eval h i hi
      rw [hMm, hIi] at hl
      obtain ⟨⟨c, rfl⟩, c', rfl⟩ := memL_some hl
      have hb := live_bridge (PTerm.toL_chk h p hp)
      have hsrc : Sim (LMem.run σ M >>= fun r => LId.evalR r.2 j >>= fun n => copyMem r.1 (.ref n))
          ((SValT.copyMem m i).eval τ) := by
        rw [Close.SValT.eval_copyMem]
        obtain ⟨μ', hm'⟩ := hmr ⟨c, rfl⟩
        obtain ⟨id, hi'⟩ := hir ⟨c', rfl⟩
        obtain ⟨-, μ, B, hr, hheq, hpre⟩ := hme μ' hm'
        have hj : LId.evalR B j = .ok id := LId.evalR_prefix hpre (hie id hi').2
        simp only [hr, hm', hi', hj, Res.ok_bind, copyMem_of_heap hheq.1]
        exact Sim.refl _
      rw [Close.STerm.eval_save_copyMem]
      simp only [Tm.toL, Op0.toL, Op2.toLAt, Op2.toL, Op3.toLAt, Op3.toL, hMm, hIi, memL,
        Option.getD_some, LStor.eval, h.stor, Res.ok_bind, Close.STerm.eval_storage, LPath.eval]
      simp only [bind_assoc, Res.ok_bind, view_findLive, SVal.findLive_nil]
      have key := Sim.bind hsrc fun n => write_bridge hb fun c => .ok (c.overlay n)
      simp only [bind_assoc, Res.ok_bind] at key
      exact key
  | .app2 .delAt s p, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨hs, hf⟩ := hf
    obtain rfl := STerm.isStorage_eq hs
    have hb := live_bridge (PTerm.toL_chk h p hf)
    rw [Close.STerm.eval_delAt]
    simp only [Tm.toL, Op0.toL, Op2.toLAt, Op2.toL, LStor.eval, h.stor, Res.ok_bind,
        Close.STerm.eval_storage]
    intro a
    simp only [Res.bind_eq_ok]
    constructor
    · rintro ⟨qs, hq, c, hc, ha⟩
      obtain ⟨rs, hrs, rfl, hfs⟩ := (hb qs c).1 ⟨hq, hc⟩
      rw [saveLive_eq_save _ hc, save_root] at ha
      obtain ⟨τ'', h'', he⟩ := Res.bind_eq_ok.1 ha
      exact ⟨τ'', ⟨rs, hrs, c, hfs, h''⟩, he⟩
    · rintro ⟨τ'', ⟨rs, hrs, c, hfs, h''⟩, he⟩
      obtain ⟨hq, hl⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hfs⟩
      refine ⟨_, hq, c, hl, ?_⟩
      rw [saveLive_eq_save _ hl, save_root, h'', Res.ok_bind, he]
  | .pvS _, hf => by simp only [Tm.inL, Bool.false_eq_true] at hf
  | .app3 .push s p v, hf => by
    match v, hf with
    | .app1 .sval t, hf =>
      simp only [Tm.inL, Op3.inL, Op1.inL, Bool.and_eq_true] at hf
      obtain ⟨⟨hs, hp⟩, ht⟩ := hf
      obtain rfl := STerm.isStorage_eq hs
      have hb := live_bridge (PTerm.toL_chk h p hp)
      have htt := Term.toL_eval h t ht
      rw [Close.STerm.eval_push, Close.SValT.eval_val]
      simp only [Tm.toL, Op0.toL, Op1.toL, Op3.toLAt, Op3.toL, LStor.eval, h.stor, Res.ok_bind,
        Close.STerm.eval_storage, bind_assoc]
      cases hx : t.eval τ with
      | ok x =>
        rw [(htt x).2 hx, Res.ok_bind]
        have hval : (fun _ : SVal => (Except.ok x : Res Value) >>= fun x =>
            (Except.ok x.toSVal : Res SVal) >>= fun sv => pure sv.strip) =
            fun _ => .ok x.toSVal := by
          funext _; cases x <;> rfl
        simp only [Res.ok_bind] at hval ⊢
        rw [hval]
        simp only [pushOn_word, bind_assoc]
        exact write_bridge hb _
      | error e =>
        refine Sim.halt (fun a ha => ?_) (fun a ha => ?_)
        · obtain ⟨y, hy, -⟩ := Res.bind_eq_ok.1 ha
          have := (htt y).1 hy
          rw [hx] at this; cases this
        · obtain ⟨rs, -, ha⟩ := Res.bind_eq_ok.1 ha
          obtain ⟨c, -, ha⟩ := Res.bind_eq_ok.1 ha
          obtain ⟨τ', hτ', -⟩ := Res.bind_eq_ok.1 ha
          cases c with
          | array es sh fx =>
            simp only [Close.pushOn_array, Res.error_bind] at hτ'
            cases hτ'
          | prim _ | struct _ | map _ _ => cases hτ'
    | .app2 .sfind s' p', hf =>
      simp only [Tm.inL, Op3.inL, Op2.inL, Bool.and_eq_true] at hf
      obtain ⟨⟨hs, hp⟩, hs', hp'⟩ := hf
      obtain rfl := STerm.isStorage_eq hs
      obtain rfl := STerm.isStorage_eq hs'
      rw [Close.STerm.eval_push, Close.SValT.eval_find]
      simp only [Tm.toL, Op0.toL, Op2.toLAt, Op2.toL, Op3.toLAt, Op3.toL, Close.STerm.eval_storage,
          Res.ok_bind,
        bind_assoc]
      exact pushCopy_bridge h.stor (live_bridge (PTerm.toL_chk h p hp))
        (live_bridge (PTerm.toL_chk h p' hp'))
    | .app1 (.newArr _) _, hf | .app2 .copyMem _ _, hf =>
      simp only [Tm.inL, Op3.inL, Bool.false_eq_true] at hf
  | .app1 (.select _) _, hf => by simp only [Tm.inL, Op1.inL, Bool.false_eq_true] at hf
  | .app2 (.pushSlot E) s p, hf | .app2 (.extend E) s p, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨hs, hp⟩ := hf
    obtain rfl := STerm.isStorage_eq hs
    have hb := live_bridge (PTerm.toL_chk h p hp)
    first
      | rw [Close.STerm.eval_pushSlot]
      | rw [STerm.eval_extend]
    simp only [Tm.toL, Op0.toL, Op2.toLAt, Op2.toL, LStor.eval, LTerm.eval, h.stor, Res.ok_bind,
      Close.STerm.eval_storage, pushOn_slot _ E _ _ (.bool true), bind_assoc]
    exact write_bridge hb _
  | .app2 .pop s p, hf | .app2 .shrink s p, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨hs, hp⟩ := hf
    obtain rfl := STerm.isStorage_eq hs
    have hb := live_bridge (PTerm.toL_chk h p hp)
    first
      | rw [Close.STerm.eval_pop]
      | rw [Close.STerm.eval_shrink]
    simp only [Tm.toL, Op0.toL, Op2.toLAt, Op2.toL, LStor.eval, LTerm.eval, h.stor, Res.ok_bind,
      Close.STerm.eval_storage, popOn_pop _ _ _ _ (.bool true), bind_assoc]
    exact write_bridge hb _

/-- A stale alias's slot-level path reads as the path the alias holds, and
so do its members. -/
theorem PTerm.slotPath?_eval (h : Rel σ ρ τ) : (p : PTerm C) → (q : LPath) →
    p.slotPath? ρ = some q → ∃ r segs, q.eval σ = .ok (.field r :: segs) ∧ p.eval τ = .ok (r, segs)
  | .pvP x, q, hq => by
    have hx := h.env x
    simp only [Tm.slotPath?] at hq
    split at hq
    · rename_i q' hl
      cases hq
      rw [hl] at hx
      obtain ⟨r, segs, h₁, h₂⟩ := hx
      refine ⟨r, segs, h₁, ?_⟩
      rw [Close.PTerm.eval_pv, h₂]
      rfl
    · cases hq
  | .app1 (.field f) p, q, hq => by
    simp only [Tm.slotPath?, Option.map_eq_some_iff] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    obtain ⟨r, segs, h₁, h₂⟩ := PTerm.slotPath?_eval h p q' hq'
    refine ⟨r, segs ++ [.field f], ?_, ?_⟩
    · simp only [LPath.eval, h₁, Res.ok_bind, List.cons_append]
    · rw [Close.PTerm.eval_field, h₂]
      rfl
  | .app0 (.root _), _, hq | .app1 .next _, _, hq | .app2 .at _ _, _, hq
  | .app2 .nextIn _ _, _, hq | .app3 .atIn _ _ _, _, hq => by
    simp only [Tm.slotPath?, reduceCtorEq] at hq

/-- What `STerm.staleWrite?` recognises: a word written or pushed at an
alias's slot-level path. -/
theorem STerm.staleWrite?_some {s : STerm C} {op : Option AOp} {q : LPath} {t : Term C}
    (hw : s.staleWrite? ρ = some (op, q, t)) : ∃ p : PTerm C, p.slotPath? ρ = some q ∧
      ((op = none ∧ s = .app3 .save (.app0 .storage) p (.app1 .sval t)) ∨
        (op = some .push ∧ s = .app3 .push (.app0 .storage) p (.app1 .sval t))) := by
  unfold STerm.staleWrite? at hw
  split at hw
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hw
    obtain ⟨q', hq, rfl, rfl, rfl⟩ := hw
    exact ⟨_, hq, .inl ⟨rfl, rfl⟩⟩
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hw
    obtain ⟨q', hq, rfl, rfl, rfl⟩ := hw
    exact ⟨_, hq, .inr ⟨rfl, rfl⟩⟩
  · cases hw

/-- **A write through a stale alias** (`storageFieldWriteSave` with `sp` the
alias): the slot-level write at the path it holds, live or not. -/
theorem stale_write_bridge (h : Rel σ ρ τ) {p : PTerm C} {q : LPath}
    (hq : p.slotPath? ρ = some q) (t : Term C) (ht : t.inL ρ = true) :
    Sim ((LStor.stale none ρ.stor q (t.toL ρ)).eval σ)
      ((Tm.app3 .save (.app0 .storage) p (.app1 .sval t) : STerm C).eval τ >>= fun τ' =>
        .ok (.struct τ'.storage)) := by
  obtain ⟨r, segs, h₁, h₂⟩ := PTerm.slotPath?_eval h p q hq
  rw [Close.STerm.eval_save]
  simp only [LStor.eval, h.stor, h₁, Res.ok_bind, staleSave, Close.STerm.eval_storage, h₂,
    bind_assoc, save_root]
  exact Sim.bind (Term.toL_eval h t ht) fun _ => Sim.refl _

/-- **A push through a stale alias** (`storagePushValueSave` with `sp` the
alias): the array at the path it holds, one longer, written back. -/
theorem stale_push_bridge (h : Rel σ ρ τ) {p : PTerm C} {q : LPath}
    (hq : p.slotPath? ρ = some q) (t : Term C) (ht : t.inL ρ = true) :
    Sim ((LStor.stale (some .push) ρ.stor q (t.toL ρ)).eval σ)
      ((Tm.app3 .push (.app0 .storage) p (.app1 .sval t) : STerm C).eval τ >>= fun τ' =>
        .ok (.struct τ'.storage)) := by
  obtain ⟨r, segs, h₁, h₂⟩ := PTerm.slotPath?_eval h p q hq
  have htt := Term.toL_eval h t ht
  rw [Close.STerm.eval_push, Close.SValT.eval_val]
  simp only [LStor.eval, h.stor, h₁, Res.ok_bind, staleSave, Close.STerm.eval_storage, h₂,
    bind_assoc]
  cases hx : t.eval τ with
  | ok x =>
    rw [(htt x).2 hx, Res.ok_bind]
    have hval : (fun _ : SVal => (Except.ok x : Res Value) >>= fun x =>
        (Except.ok x.toSVal : Res SVal) >>= fun sv => pure sv.strip) =
        fun _ => .ok x.toSVal := by
      funext _; cases x <;> rfl
    simp only [Res.ok_bind] at hval ⊢
    rw [hval]
    simp only [pushOn_word, bind_assoc, find_root, save_root]
    exact Sim.refl _
  | error e =>
    refine Sim.halt (fun a ha => ?_) (fun a ha => ?_)
    · obtain ⟨y, hy, -⟩ := Res.bind_eq_ok.1 ha
      have := (htt y).1 hy
      rw [hx] at this; cases this
    · obtain ⟨c, -, ha⟩ := Res.bind_eq_ok.1 ha
      obtain ⟨τ', hτ', -⟩ := Res.bind_eq_ok.1 ha
      cases c with
      | array es sh fx =>
        simp only [Close.pushOn_array, Res.error_bind] at hτ'
        cases hτ'
      | prim _ | struct _ | map _ _ => cases hτ'

/-- A storage update, pushed in by `toLS`, is the write it made: through a
stale alias at the slot level, otherwise as `STerm.toL_eval` says. -/
theorem STerm.toLS_eval (h : Rel σ ρ τ) (s : STerm C) (hf : s.inLS ρ = true) :
    Sim ((s.toLS ρ).eval σ) (s.eval τ >>= fun τ' => .ok (.struct τ'.storage)) := by
  unfold STerm.toLS
  unfold STerm.inLS at hf
  cases hw : s.staleWrite? ρ with
  | none =>
    simp only [hw] at hf ⊢
    exact STerm.toL_eval h s hf
  | some w =>
    obtain ⟨op, q, t⟩ := w
    simp only [hw] at hf ⊢
    obtain ⟨p, hq, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := STerm.staleWrite?_some hw
    · exact stale_write_bridge h hq t hf
    · exact stale_push_bridge h hq t hf
end

/-- `Tm.sameL` is equality. -/
theorem Tm.sameL_eq {a b : Tm C s} (h : a.sameL b = true) : a = b := by
  simp only [Tm.sameL, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem Term.sameL_eq (a b : Term C) (h : a.sameL b = true) : a = b := Tm.sameL_eq h
theorem PTerm.sameL_eq (p q : PTerm C) (h : p.sameL q = true) : p = q := Tm.sameL_eq h

/-- What `Fml.eqDView` recognises is `eqD a b`. -/
theorem Fml.eqDView_some {φ ψ : Fml C} {a b : Term C} (h : Fml.eqDView φ ψ = some (a, b)) :
    φ = .defined a ∧ ψ = .and (.defined b) (.eq a b) := by
  unfold Fml.eqDView at h
  split at h
  · rename_i a₀ b₀ a' b'
    split at h
    · rename_i hs
      simp only [Bool.and_eq_true] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [← Term.sameL_eq _ _ hs.1, ← Term.sameL_eq _ _ hs.2]
      exact ⟨rfl, rfl⟩
    · cases h
  · cases h

theorem Term.eqLit_cases {a b : Term C} (h : a.eqLit b = true) :
    (a.isLitLike = true ∧ b.isAtom = true) ∨ (b.isLitLike = true ∧ a.isAtom = true) := by
  simpa only [Term.eqLit, Bool.or_eq_true, Bool.and_eq_true] using h

/-- A literal or `msg.sender` denotes the value it returns, pushed in or not. -/
theorem Term.litLike_val {σ τ : State} {ρ : Sym} (h : Rel σ ρ τ) {a : Term C}
    (ha : a.isLitLike = true) : ∃ w, a.denote τ = .prim w ∧ (a.toL ρ).eval σ = .ok w := by
  unfold Term.isLitLike at ha
  split at ha
  · exact ⟨_, rfl, rfl⟩
  · rename_i k
    exact ⟨.int (τ.envVal k), rfl, by simp only [Tm.toL, Op0.toL, LTerm.eval, h.tx k]⟩
  · cases ha

theorem Term.inL_of_isAtom {t : Term C} {ρ : Sym} (h : t.isAtom = true) : t.inL ρ = true := by
  unfold Term.isAtom at h
  split at h
  · rfl
  · rfl
  · cases h

/-- A literal or a local is `≐` a primitive exactly when it returns it: a
local bound to no value denotes the empty struct, no primitive. -/
theorem Term.atom_equiv_prim {τ : State} {t : Term C} (h : t.isAtom = true) (v : Value) :
    Theory.StValue.Equiv (t.denote τ) (.prim v) ↔ t.eval τ = .ok v := by
  rw [Theory.StValue.Equiv.prim_iff]
  unfold Term.isAtom at h
  split at h
  · simp only [Close.Term.denote_lit, Close.Term.eval_lit, Theory.StValue.prim.injEq,
      Except.ok.injEq]
  · rename_i x
    rw [Close.Term.denote_pv, Close.Term.eval_pv]
    cases τ.getEnv x with
    | ok b => cases b <;> simp only [Theory.StValue.prim.injEq, reduceCtorEq, bind, Except.bind,
        Close.bindingVal, Except.ok.injEq]
    | error e => simp only [reduceCtorEq, bind, Except.bind]
  · cases h

/-- An equation of the target language holds when both sides return, with
one value. -/
theorem LFml.holds_eq_iff (σ : State) (a b : LTerm) :
    (LFml.eq a b).holds σ ↔ ∃ x, a.eval σ = .ok x ∧ b.eval σ = .ok x := by
  simp only [LFml.holds]
  cases a.eval σ with
  | ok x =>
    cases b.eval σ with
    | ok y => exact ⟨fun h => ⟨x, rfl, h ▸ rfl⟩, fun ⟨_, h₁, h₂⟩ => by cases h₁; cases h₂; rfl⟩
    | error _ => exact ⟨False.elim, fun ⟨_, _, h⟩ => nomatch h⟩
  | error _ => exact ⟨False.elim, fun ⟨_, h, _⟩ => nomatch h⟩

/-- An update's term returns, as a formula: `eq g g`. -/
theorem holds_eq_self (σ : State) (g : LTerm) :
    (LFml.eq g g).holds σ ↔ ∃ v, g.eval σ = .ok v := by
  simp only [LFml.holds]
  cases g.eval σ <;> simp only [reduceCtorEq, exists_false, Except.ok.injEq, exists_eq']

/-- The guard of an update under the box: `[ x = e; ] φ` holds when `e`
halts. -/
theorem guardM_box (σ : State) (g : LTerm) (φ : LFml) :
    (guardM .box g φ).holds σ ↔ ((∃ v, g.eval σ = .ok v) → φ.holds σ) := by
  simp only [guardM, LFml.holds, ← holds_eq_self]

/-- Under the diamond: `⟨ x = e; ⟩ φ` does not hold when `e` halts. -/
theorem guardM_diamond (σ : State) (g : LTerm) (φ : LFml) :
    (guardM .diamond g φ).holds σ ↔ ((∃ v, g.eval σ = .ok v) ∧ φ.holds σ) := by
  simp only [guardM, LFml.holds, ← holds_eq_self]

/-- An update and its guard agree: the update runs exactly when its term
returns, and what follows agrees in the state it leaves. -/
theorem after_guardM {σ : State} {m : Modality} {x : Res State} {P : State → Prop} {g : LTerm}
    {ψ : LFml} (hg : (∃ v, g.eval σ = .ok v) ↔ ∃ τ', x = .ok τ')
    (hψ : ∀ τ', x = .ok τ' → (P τ' ↔ ψ.holds σ)) :
    m.after P x ↔ (guardM m g ψ).holds σ := by
  cases x with
  | error e =>
    have : ¬ ∃ v, g.eval σ = .ok v := by simp only [hg, reduceCtorEq, exists_false,
        not_false_eq_true]
    cases m <;> simp only [Modality.after, Modality.onHalt, guardM_diamond, this, false_and,
        guardM_box, false_implies]
  | ok τ' =>
    have : ∃ v, g.eval σ = .ok v := by simp only [hg, Except.ok.injEq, exists_eq']
    cases m <;> simp only [Modality.after, hψ τ' rfl, guardM_diamond, this, true_and, guardM_box,
        forall_const]

theorem allocPair?_cases {i : ITerm C} {mm : MTerm C} (h : allocPair? i mm = true) :
    (∃ R, i = .app1 (.alloc R) (.app0 .memory) ∧ mm = .app1 (.addM R) (.app0 .memory)) ∨
      ∃ v, i = .app2 .copy (.app0 .memory) v ∧ mm = .app2 .copySt (.app0 .memory) v := by
  unfold allocPair? at h
  split at h
  · simp only [decide_eq_true_eq] at h
    subst h
    exact Or.inl ⟨_, rfl, rfl⟩
  · simp only [decide_eq_true_eq] at h
    subst h
    exact Or.inr ⟨_, rfl, rfl⟩
  · cases h

theorem newM_some {M₀ M : LMem} {g₀ g : LTerm} {lv : LVal}
    (h : newM (some (M₀, g₀)) lv = some (M, g)) :
    ∃ R n, lv = .arr R n ∧ allocOk R = true ∧ M = .newArr M₀ M₀.nAlloc R n ∧
      g = seqL g₀ (isIntL n) := by
  match lv, h with
  | .arr R n, h =>
    simp only [newM] at h
    split at h
    · rename_i hR
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨R, n, rfl, hR, rfl, rfl⟩
    · cases h
  | .word _, h | .sub _ _, h | .mem _ _, h => simp only [newM, reduceCtorEq] at h

/-- A stored value pushed in as `new R(n)` reads to `R`'s array of the
length `n` returns. -/
theorem SValT.arr_eval {σ τ : State} {ρ : Sym} (h : Rel σ ρ τ) : (v : SValT C) →
    v.inL ρ = true → ∀ {R : RefTy} {n : LTerm}, v.toL ρ = .arr R n → ∀ sv,
      v.eval τ = .ok sv ↔ ∃ c, n.eval σ = .ok (.int c) ∧ sv = newArrVal R c
  | .app1 (.newArr R) nt, hv, R', n, hvt, sv => by
    simp only [Tm.toL, Op1.toL, LVal.arr.injEq] at hvt
    obtain ⟨rfl, rfl⟩ := hvt
    simp only [Tm.inL, Op1.inL] at hv
    have hnt := Term.toL_eval h nt hv
    rw [newArr_eval_ok]
    exact exists_congr fun c => and_congr (hnt _).symm Iff.rfl
  | .app1 .sval _, _, _, _, hvt, _ => by simp only [Tm.toL, Op1.toL, reduceCtorEq] at hvt
  | .app2 .sfind _ _, _, _, _, hvt, _ => by
    simp only [Tm.toL, Op2.toLAt, Op2.toL, reduceCtorEq] at hvt
  | .app2 .copyMem a b, _, _, _, hvt, _ => by
    simp only [Tm.toL, Op2.toLAt, Op2.toL] at hvt
    rcases memL_getD (a.toL ρ) (b.toL ρ) with he | ⟨_, _, he⟩ <;>
      rw [he] at hvt <;> cases hvt

/-- The pair's last step: where its guard returns exactly when both the
identity and the memory do, and the memory's run names the identity at the
next ordinal, the pair keeps the relation. -/
theorem pair_tail {σ τ : State} {ρ : Sym} {x : Var} {i : ITerm C} {mm : MTerm C} {M : LMem}
    {g : LTerm} (h : Rel σ ρ τ)
    (H1 : Rets (g.eval σ) ↔ ∃ id μ', i.eval τ = .ok id ∧ mm.eval τ = .ok μ')
    (H2 : ∀ id μ', i.eval τ = .ok id → mm.eval τ = .ok μ' → ∃ μ B, M.run σ = .ok (μ, B) ∧
      μ.HeapEq μ' ∧ ρ.mem.births σ <+: B ∧ LId.evalR B ⟨ρ.mem.nAlloc, []⟩ = .ok id) :
    (Rets (g.eval σ) ↔ ∃ τ', Upd.apply [.mref x i, .memory mm] τ = .ok τ') ∧
      ∀ τ', Upd.apply [.mref x i, .memory mm] τ = .ok τ' →
        Rel σ { ρ with env := (x, .mref ⟨ρ.mem.nAlloc, []⟩) :: ρ.env, mem := M } τ' := by
  have hU : Upd.apply [.mref x i, .memory mm] τ = i.eval τ >>= fun id => mm.eval τ >>=
      fun μ => .ok { τ.setEnv x (.mref id) with heap := μ.heap, nextId := μ.nextId } := by
    simp only [Upd.apply, List.foldlM_cons, List.foldlM_nil, bind_pure,
      Close.UpdElem.write_mref, Close.UpdElem.write_memory, bind_assoc, Res.ok_bind]
  rw [hU, H1]
  refine ⟨⟨fun ⟨id, μ', hid, hμ'⟩ => ⟨_, by rw [hid, Res.ok_bind, hμ', Res.ok_bind]⟩,
    fun ⟨τ', hτ'⟩ => ?_⟩, fun τ' hτ' => ?_⟩
  · obtain ⟨id, hid, hτ'⟩ := Res.bind_eq_ok.1 hτ'
    obtain ⟨μ', hμ', -⟩ := Res.bind_eq_ok.1 hτ'
    exact ⟨id, μ', hid, hμ'⟩
  · obtain ⟨id, hid, hτ'⟩ := Res.bind_eq_ok.1 hτ'
    obtain ⟨μ', hμ', he⟩ := Res.bind_eq_ok.1 hτ'
    cases he
    obtain ⟨μ, B, hrun, hh, hp, hB⟩ := H2 id μ' hid hμ'
    exact (h.setMem hrun hp hh).bind x (.mref ⟨ρ.mem.nAlloc, []⟩) (.mref id)
      ⟨id, by rw [LMem.births_of_run hrun]; exact hB, by simp only [State.getEnv_setEnv_self]⟩

open MemNames in
/-- **A copy from storage's pair** (`memoryStorageCopy`): `copyG` returns
exactly where the identity and the memory do, and the node `LMem.copySt`
at the next ordinal runs to the interpreter's heap, its root the identity
(`readFromCopyToStorage` then reads the subtree in the storage of the
copy).  The path is checked (`live_bridge`), so the live read is the
interpreter's. -/
theorem pairCopy_key {σ τ : State} {ρ : Sym} {p : PTerm C} (h : Rel σ ρ τ)
    (hp : p.inL ρ = true) :
    (Rets ((copyG ρ.stor (p.toL ρ)).eval σ) ↔
      ∃ id μ', (Tm.app2 .copy (.app0 .memory) (.app2 .sfind (.app0 .storage) p)).eval τ = .ok id ∧
        (Tm.app2 .copySt (.app0 .memory) (.app2 .sfind (.app0 .storage) p)).eval τ = .ok μ') ∧
    ∀ id μ', (Tm.app2 .copy (.app0 .memory) (.app2 .sfind (.app0 .storage) p)).eval τ = .ok id →
      (Tm.app2 .copySt (.app0 .memory) (.app2 .sfind (.app0 .storage) p)).eval τ = .ok μ' →
      ∃ μ B, (LMem.copySt ρ.mem ρ.mem.nAlloc ρ.stor (p.toL ρ)).run σ = .ok (μ, B) ∧
        μ.HeapEq μ' ∧ ρ.mem.births σ <+: B ∧ LId.evalR B ⟨ρ.mem.nAlloc, []⟩ = .ok id := by
  have hb := live_bridge (PTerm.toL_chk h p hp)
  have hv : ∀ c, (Tm.app2 (C := C) .sfind (.app0 .storage) p).eval τ = .ok c ↔
      ∃ qs, (p.toL ρ).eval σ = .ok qs ∧ (SVal.struct τ.storage).findLive qs = .ok c := by
    intro c
    rw [Close.SValT.eval_find, Close.STerm.eval_storage, Res.ok_bind]
    constructor
    · intro hc
      obtain ⟨rs, hrs, hc⟩ := Res.bind_eq_ok.1 hc
      obtain ⟨hq, hl⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hc⟩
      exact ⟨_, hq, hl⟩
    · rintro ⟨qs, hq, hl⟩
      obtain ⟨rs, hrs, rfl, hc⟩ := (hb qs c).1 ⟨hq, hl⟩
      rw [hrs, Res.ok_bind]
      exact hc
  have hi : (Tm.app2 (C := C) .copy (.app0 .memory) (.app2 .sfind (.app0 .storage) p)).eval τ =
      (Tm.app2 (C := C) .sfind (.app0 .storage) p).eval τ >>= fun sv =>
        copyStToM τ sv >>= fun r => r.2.asRef := by
    rw [Close.ITerm.eval_copy, Close.MTerm.eval_memory]
    rfl
  have hmm : (Tm.app2 (C := C) .copySt (.app0 .memory) (.app2 .sfind (.app0 .storage) p)).eval τ =
      (Tm.app2 (C := C) .sfind (.app0 .storage) p).eval τ >>= fun sv =>
        copyStToM τ sv >>= fun r => .ok r.1 := by
    rw [Close.MTerm.eval_copySt, Close.MTerm.eval_memory]
    rfl
  have hG : Rets ((copyG ρ.stor (p.toL ρ)).eval σ) ↔
      ∃ c, (Tm.app2 (C := C) .sfind (.app0 .storage) p).eval τ = .ok c ∧ Cps c ∧
        ∀ pv, c ≠ .prim pv := by
    unfold copyG
    rw [seq_rets, ite_isT_rets]
    simp only [lit_rets, and_true]
    constructor
    · rintro ⟨⟨a, ha⟩, hf⟩
      simp only [LTerm.eval, h.stor, Res.ok_bind] at ha
      obtain ⟨qs, hq, ha⟩ := Res.bind_eq_ok.1 ha
      obtain ⟨c, hc, ha⟩ := Res.bind_eq_ok.1 ha
      obtain ⟨r, hr, -⟩ := Res.bind_eq_ok.1 ha
      refine ⟨c, (hv c).2 ⟨qs, hq, hc⟩, ⟨_, r, hr⟩, ?_⟩
      rintro pv rfl
      obtain ⟨a', ha'⟩ : ∃ a', (SVal.prim pv).asValue = .ok a' := by
        cases pv <;> exact ⟨_, rfl⟩
      exact hf ⟨a', by simp only [LTerm.eval, h.stor, hq, hc, Res.ok_bind, ha']⟩
    · rintro ⟨c, hc, hcp, hnp⟩
      obtain ⟨qs, hq, hl⟩ := (hv c).1 hc
      obtain ⟨r, hr⟩ := hcp.at (memBase σ)
      refine ⟨⟨.bool true, by simp only [LTerm.eval, h.stor, hq, hl, Res.ok_bind, hr]⟩, ?_⟩
      rintro ⟨a, ha⟩
      simp only [LTerm.eval, h.stor, hq, hl, Res.ok_bind] at ha
      cases c with
      | prim pv => exact hnp pv rfl
      | struct _ | array _ _ _ | map _ _ => simp only [SVal.asValue, reduceCtorEq] at ha
  refine ⟨hG.trans ⟨fun ⟨c, hc, hcp, hnp⟩ => ?_, fun ⟨id, μ', hid, _⟩ => ?_⟩,
    fun id μ' hid hμ' => ?_⟩
  · obtain ⟨⟨τ₁, mv⟩, hcopy⟩ := hcp.at τ
    obtain ⟨id, rfl⟩ := copy_ref hcopy hnp
    exact ⟨id, τ₁, by rw [hi, hc, Res.ok_bind, hcopy]; rfl,
      by rw [hmm, hc, Res.ok_bind, hcopy]; rfl⟩
  · rw [hi] at hid
    obtain ⟨c, hc, hid⟩ := Res.bind_eq_ok.1 hid
    obtain ⟨r, hr, hid⟩ := Res.bind_eq_ok.1 hid
    refine ⟨c, hc, ⟨τ, r, hr⟩, ?_⟩
    rintro pv rfl
    cases pv <;> simp only [copyStToM, Except.ok.injEq] at hr <;> subst hr <;> cases hid
  · rw [hmm] at hμ'
    obtain ⟨c, hc, hμ'⟩ := Res.bind_eq_ok.1 hμ'
    obtain ⟨r, hr, hμ'⟩ := Res.bind_eq_ok.1 hμ'
    cases hμ'
    rw [hi, hc, Res.ok_bind, hr, Res.ok_bind] at hid
    obtain ⟨qs, hq, hl⟩ := (hv c).1 hc
    obtain ⟨μ₁, B₁, hr₁, hh⟩ := h.mem
    have hk : B₁.length = ρ.mem.nAlloc := LMem.run_nAlloc σ ρ.mem hr₁
    rcases (copyStToM_heap hh c).cases with ⟨e, -, h₂⟩ | ⟨t₁, t₂, mv, h₁, h₂, ht⟩
    · rw [hr] at h₂
      cases h₂
    · rw [hr, Except.ok.injEq] at h₂
      subst h₂
      obtain rfl : mv = .ref id := by
        cases mv <;> simp only [MVal.asRef, reduceCtorEq] at hid
        cases hid
        rfl
      refine ⟨t₁, B₁ ++ [Birth.ofCopy μ₁ t₁ id], ?_, ht, ?_, ?_⟩
      · simp only [LMem.run, h.stor, hq, hl, hr₁, Res.ok_bind, hk, ↓reduceIte, h₁, MVal.asRef]
        rfl
      · rw [LMem.births_of_run hr₁]
        exact List.prefix_append _ _
      · rw [evalR_last _ _ hk.symm]
        rfl

open MemNames in
/-- **An allocation's pair, pushed in**: it runs exactly where the memory's
guard returns, and binds `x` to the root of the next ordinal, which is the
identity the interpreter's allocation takes. -/
theorem pair_sound {σ τ : State} {ρ ρ' : Sym} {x : Var} {i : ITerm C} {mm : MTerm C}
    {g : LTerm} (h : Rel σ ρ τ) (hq : pairL ρ x i mm = some (g, ρ')) (hm : pairIn ρ mm = true) :
    (Rets (g.eval σ) ↔ ∃ τ', Upd.apply [.mref x i, .memory mm] τ = .ok τ') ∧
      ∀ τ', Upd.apply [.mref x i, .memory mm] τ = .ok τ' → Rel σ ρ' τ' := by
  unfold pairL at hq
  split at hq
  · rename_i hap
    cases hc : copyOf? mm with
    | some p =>
      obtain rfl := copyOf?_some hc
      simp only [pairIn, hc] at hm
      simp only [pairMem, hc, Option.bind_some] at hq
      split at hq
      case isFalse => cases hq
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      rcases allocPair?_cases hap with ⟨R, -, hmm⟩ | ⟨v, rfl, hmm⟩
      · cases hmm
      · cases hmm
        exact pair_tail h (pairCopy_key h hm).1 (pairCopy_key h hm).2
    | none =>
      simp only [pairIn, hc] at hm
      simp only [pairMem, hc] at hq
      obtain ⟨M, g', hM, hmr, hme⟩ := MTerm.toL_eval h mm hm
      rw [hM, Option.bind_some] at hq
      split at hq
      case isFalse => cases hq
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      have hkey : (∀ id, i.eval τ = .ok id → ∃ μ', mm.eval τ = .ok μ') ∧
          ∀ μ', mm.eval τ = .ok μ' → ∃ id, i.eval τ = .ok id ∧
            LId.evalR (M.births σ) ⟨ρ.mem.nAlloc, []⟩ = .ok id := by
        rcases allocPair?_cases hap with ⟨R, rfl, rfl⟩ | ⟨v, rfl, rfl⟩
        · simp only [Tm.toL, Op1.toL, Op0.toL, Option.bind_some] at hM
          split at hM
          · simp only [Option.some.injEq, Prod.mk.injEq] at hM
            obtain ⟨rfl, -⟩ := hM
            have hi : (Tm.app1 (C := C) (.alloc R) (.app0 .memory)).eval τ =
                allocDefault τ R >>= fun r => .ok r.2 := rfl
            have hmm : (Tm.app1 (C := C) (.addM R) (.app0 .memory)).eval τ =
                allocDefault τ R >>= fun r => .ok r.1 := rfl
            refine ⟨fun id hid => ?_, fun μ' hμ' => ?_⟩
            · rw [hi] at hid
              obtain ⟨r, hr, -⟩ := Res.bind_eq_ok.1 hid
              exact ⟨r.1, by rw [hmm, hr]; rfl⟩
            · obtain ⟨-, μ, B, hrun, -, -⟩ := hme μ' hμ'
              rw [hmm] at hμ'
              obtain ⟨r, hr, -⟩ := Res.bind_eq_ok.1 hμ'
              obtain ⟨μ₀, B₀, id₀, hr₀, hk, hc, rfl⟩ := LMem.run_addM hrun
              obtain ⟨μ₁, B₁, hr₁, hh⟩ := h.mem
              rw [hr₁, Except.ok.injEq, Prod.mk.injEq] at hr₀
              obtain ⟨rfl, rfl⟩ := hr₀
              rcases (allocDefault_heap hh R).cases with ⟨e, h₁, -⟩ | ⟨t₁, t₂, id', h₁, h₂, -⟩
              · rw [allocDefault_of_copy hc] at h₁; cases h₁
              · rw [allocDefault_of_copy hc, Except.ok.injEq, Prod.mk.injEq] at h₁
                obtain ⟨-, rfl⟩ := h₁
                rw [hr, Except.ok.injEq] at h₂
                subst h₂
                refine ⟨id₀, by rw [hi, hr]; rfl, ?_⟩
                rw [LMem.births_of_run hrun, evalR_last _ _ hk]
                rfl
          · cases hM
        · have hvi : v.inL ρ = true := by
            simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hm
            exact hm.1.2
          obtain ⟨R, n', hvt, hR, rfl, -⟩ := newM_some (by
            simpa only [Tm.toL, Op2.toLAt, Op2.toL, Op0.toL] using hM)
          have hva := SValT.arr_eval h v hvi hvt
          have hi : (Tm.app2 (C := C) .copy (.app0 .memory) v).eval τ =
              v.eval τ >>= fun sv => copyStToM τ sv >>= fun r => r.2.asRef := by
            rw [Close.ITerm.eval_copy, Close.MTerm.eval_memory]
            rfl
          have hmm : (Tm.app2 (C := C) .copySt (.app0 .memory) v).eval τ =
              v.eval τ >>= fun sv => copyStToM τ sv >>= fun r => .ok r.1 := by
            rw [Close.MTerm.eval_copySt, Close.MTerm.eval_memory]
            rfl
          refine ⟨fun id hid => ?_, fun μ' hμ' => ?_⟩
          · rw [hi] at hid
            obtain ⟨sv, hsv, hid⟩ := Res.bind_eq_ok.1 hid
            obtain ⟨r, hr, -⟩ := Res.bind_eq_ok.1 hid
            exact ⟨r.1, by rw [hmm, hsv, Res.ok_bind, hr]; rfl⟩
          · obtain ⟨-, μ, B, hrun, -, -⟩ := hme μ' hμ'
            rw [hmm] at hμ'
            obtain ⟨sv, hsv, hμ'⟩ := Res.bind_eq_ok.1 hμ'
            obtain ⟨r, hr, -⟩ := Res.bind_eq_ok.1 hμ'
            obtain ⟨c, hc, rfl⟩ := (hva sv).1 hsv
            obtain ⟨μ₀, B₀, id₀, c', hr₀, hk, hc', hcp, rfl⟩ := LMem.run_newArr hrun
            rw [hc, Except.ok.injEq, PrimVal.int.injEq] at hc'
            subst hc'
            obtain ⟨μ₁, B₁, hr₁, hh⟩ := h.mem
            rw [hr₁, Except.ok.injEq, Prod.mk.injEq] at hr₀
            obtain ⟨rfl, rfl⟩ := hr₀
            rcases (copyStToM_heap hh (newArrVal R c)).cases with ⟨e, h₁, -⟩ |
              ⟨t₁, t₂, mv, h₁, h₂, -⟩
            · rw [hcp] at h₁; cases h₁
            · rw [hcp, Except.ok.injEq, Prod.mk.injEq] at h₁
              obtain ⟨-, rfl⟩ := h₁
              rw [hr, Except.ok.injEq] at h₂
              subst h₂
              refine ⟨id₀, by rw [hi, hsv, Res.ok_bind, hr]; rfl, ?_⟩
              rw [LMem.births_of_run hrun, evalR_last _ _ hk]
              rfl
      refine pair_tail h ⟨fun hg => ?_, fun ⟨_, μ', _, hμ'⟩ => (hme μ' hμ').1⟩
        fun id μ' hid hμ' => ?_
      · obtain ⟨μ', hμ'⟩ := hmr hg
        obtain ⟨id, hid, -⟩ := hkey.2 μ' hμ'
        exact ⟨id, μ', hid, hμ'⟩
      · obtain ⟨-, μ, B, hrun, hh, hp⟩ := hme μ' hμ'
        obtain ⟨id', hid', hB⟩ := hkey.2 μ' hμ'
        rw [hid, Except.ok.injEq] at hid'
        subst hid'
        exact ⟨μ, B, hrun, hh, hp, by rw [← LMem.births_of_run hrun]; exact hB⟩
  · cases hq


/-- **Pushing the updates in keeps the meaning**, halts included.

Example: `{ storage := save(storage, balances[k], 5) } find(storage, balances[k]) = 5`
holds exactly when `sok(save(init, balances[k], 5)) = sok(…) → find(save(init,
balances[k], 5), balances[k]) = 5` does, both read in the state before the
write. -/
theorem Fml.toL_holds :
    (φ : Fml C) → ∀ {σ τ : State} {ρ : Sym}, Rel σ ρ τ → φ.inL ρ = true →
      (holds τ φ ↔ (φ.toL ρ).holds σ)
  | .tt, _, _, _, _, _ => Iff.rfl
  | .eq a b, _, τ, _, h, hf => by
    simp only [Fml.inL] at hf
    simp only [holds, Fml.toL]
    rw [LFml.holds_eq_iff]
    rcases Term.eqLit_cases hf with ⟨hla, hb⟩ | ⟨hlb, ha⟩
    · obtain ⟨w, hd, hl⟩ := Term.litLike_val h hla
      have hs : Sim ((b.toL _).eval _) (b.eval τ) := Term.toL_eval h b (Term.inL_of_isAtom hb)
      rw [hd, Close.equiv_prim_left_iff, eq_comm, ← Theory.StValue.Equiv.prim_iff,
        Term.atom_equiv_prim hb]
      simp only [hl, Except.ok.injEq, exists_eq_left']
      exact (hs w).symm
    · obtain ⟨w, hd, hl⟩ := Term.litLike_val h hlb
      have hs : Sim ((a.toL _).eval _) (a.eval τ) := Term.toL_eval h a (Term.inL_of_isAtom ha)
      rw [hd, Term.atom_equiv_prim ha]
      simp only [hl, Except.ok.injEq, exists_eq_right']
      exact (hs w).symm
  | .defined t, _, _, _, h, hf => by
    have ht := Term.toL_eval h t hf
    simp only [holds, Fml.toL, LFml.holds]
    cases hx : (t.toL _).eval _ with
    | ok x => exact ⟨fun _ => rfl, fun _ => ⟨x, (ht x).1 hx⟩⟩
    | error _ =>
      refine ⟨fun ⟨v, hv⟩ => ?_, False.elim⟩
      have := (ht v).2 hv
      simp_all only [reduceCtorEq]
  | .not φ, _, _, _, h, hf => by
    simp only [Fml.inL] at hf
    simp only [holds, Fml.toL, LFml.holds, Fml.toL_holds φ h hf]
  | .and φ ψ, _, _, _, h, hf => by
    cases hv : Fml.eqDView φ ψ with
    | none =>
      simp only [Fml.inL, hv, Bool.and_eq_true] at hf
      simp only [holds, Fml.toL, hv, LFml.holds, Fml.toL_holds φ h hf.1, Fml.toL_holds ψ h hf.2]
    | some ab =>
      obtain ⟨a, b⟩ := ab
      simp only [Fml.inL, hv, Bool.and_eq_true] at hf
      simp only [Fml.toL, hv]
      obtain ⟨rfl, rfl⟩ := Fml.eqDView_some hv
      have ha : Sim ((a.toL _).eval _) (a.eval _) := Term.toL_eval h a hf.1
      have hb : Sim ((b.toL _).eval _) (b.eval _) := Term.toL_eval h b hf.2
      refine holds_eqD_iff.trans ?_
      rw [LFml.holds_eq_iff]
      exact exists_congr fun x => and_congr (ha x).symm (hb x).symm
  | .imp φ ψ, _, _, _, h, hf => by
    simp only [Fml.inL, Bool.and_eq_true] at hf
    simp only [holds, Fml.toL, LFml.holds, Fml.toL_holds φ h hf.1, Fml.toL_holds ψ h hf.2]
  | .upd m [] φ, _, τ, _, h, hf => by
    simp only [Fml.inL] at hf
    simp only [holds, Fml.toL, Upd.apply, List.foldlM_nil]
    exact Fml.toL_holds φ h hf
  | .upd m [e] φ, σ, τ, ρ, h, hf => by
    simp only [Fml.inL, Bool.and_eq_true] at hf
    simp only [holds, Fml.toL, Upd.apply, List.foldlM_cons, List.foldlM_nil, bind_pure]
    cases e with
    | val x t =>
      have ht := Term.toL_eval h t hf.1
      rw [Close.UpdElem.write_val]
      refine after_guardM (by
        simp only [UpdElem.toL, Res.bind_eq_ok]
        exact ⟨fun ⟨v, hv⟩ => ⟨_, v, (ht v).1 hv, rfl⟩, fun ⟨_, v, hv, _⟩ => ⟨v, (ht v).2 hv⟩⟩)
        fun τ' hτ => ?_
      obtain ⟨v, hv, he⟩ := Res.bind_eq_ok.1 hτ
      cases he
      refine Fml.toL_holds φ (h.bind x _ _ ?_) hf.2
      exact ⟨v, (ht v).2 hv, by simp only [State.getEnv_setEnv_self]⟩
    | path x p =>
      have hA := PTerm.toL_chk h p hf.1
      rw [Close.UpdElem.write_path]
      refine after_guardM (by
        simp only [UpdElem.toL]
        rw [guardPath_ok h.stor]
        simp only [Res.bind_eq_ok]
        constructor
        · rintro ⟨qs, hq, hl⟩
          obtain ⟨rs, hrs, -⟩ := (hA qs).2 ⟨hq, hl⟩
          exact ⟨_, rs, hrs, rfl⟩
        · rintro ⟨_, rs, hrs, -⟩
          obtain ⟨hq, hl⟩ := (hA _).1 ⟨rs, hrs, rfl⟩
          exact ⟨_, hq, hl⟩) fun τ' hτ => ?_
      obtain ⟨rs, hr, he⟩ := Res.bind_eq_ok.1 hτ
      cases he
      refine Fml.toL_holds φ (h.bind x _ _ ?_) hf.2
      obtain ⟨hq, hl⟩ := (hA _).1 ⟨rs, hr, rfl⟩
      exact ⟨rs.1, rs.2, hq, by simp only [State.getEnv_setEnv_self], hl⟩
    | storage s =>
      have hs := STerm.toLS_eval h s hf.1
      rw [Close.UpdElem.write_storage]
      refine after_guardM (by
        simp only [UpdElem.toL, LTerm.eval, Res.bind_eq_ok]
        constructor
        · rintro ⟨_, v, hv, -⟩
          obtain ⟨τ₁, h₁, -⟩ := Res.bind_eq_ok.1 ((hs v).1 hv)
          exact ⟨_, τ₁, h₁, rfl⟩
        · rintro ⟨_, τ₁, h₁, -⟩
          exact ⟨_, _, (hs _).2 (by rw [h₁]; rfl), rfl⟩) fun τ' hτ => ?_
      obtain ⟨τ₁, h₁, he⟩ := Res.bind_eq_ok.1 hτ
      cases he
      refine Fml.toL_holds φ ⟨(hs _).2 (by rw [h₁]; rfl), fun y => ?_,
        fun k => by rw [← h.tx k]; cases k <;> rfl, h.mem.of_heap rfl rfl⟩ hf.2
      simp only [UpdElem.toL, lookupBy_onWrite]
      exact (h.env y).onWrite rfl
    | store x s =>
      have hs := STerm.toL_eval h s hf.1
      rw [Close.UpdElem.write_store]
      refine after_guardM (by
        simp only [UpdElem.toL, LTerm.eval, Res.bind_eq_ok]
        constructor
        · rintro ⟨_, v, hv, -⟩
          obtain ⟨τ₁, h₁, -⟩ := Res.bind_eq_ok.1 ((hs v).1 hv)
          exact ⟨_, τ₁, h₁, rfl⟩
        · rintro ⟨_, τ₁, h₁, -⟩
          exact ⟨_, _, (hs _).2 (by rw [h₁]; rfl), rfl⟩) fun τ' hτ => ?_
      obtain ⟨τ₁, h₁, he⟩ := Res.bind_eq_ok.1 hτ
      cases he
      refine Fml.toL_holds φ (h.bind x _ _ ?_) hf.2
      exact ⟨τ₁.storage, (hs _).2 (by rw [h₁]; rfl), by simp only [State.getEnv_setEnv_self]⟩
    | net r op a =>
      have hra : r.inL ρ = true ∧ a.inL ρ = true := by simpa only [UpdElem.inL,
          Bool.and_eq_true] using hf.1
      have hr := Term.toL_eval h r hra.1
      have ha := Term.toL_eval h a hra.2
      rw [Close.UpdElem.write_net]
      refine after_guardM ?_ fun τ' hτ => ?_
      · simp only [UpdElem.toL, LTerm.eval]
        constructor
        · rintro ⟨_, hv⟩
          obtain ⟨i, hi, hv⟩ := Res.bind_eq_ok.1 hv
          obtain ⟨x, hx, hi⟩ := Res.bind_eq_ok.1 hi
          obtain ⟨j, hj, -⟩ := Res.bind_eq_ok.1 hv
          obtain ⟨y, hy, hj⟩ := Res.bind_eq_ok.1 hj
          exact ⟨_, by simp only [(hr x).1 hx, (ha y).1 hy, Res.ok_bind, hi, hj]; rfl⟩
        · rintro ⟨τ', hτ⟩
          obtain ⟨i, hi, hτ⟩ := Res.bind_eq_ok.1 hτ
          obtain ⟨x, hx, hi⟩ := Res.bind_eq_ok.1 hi
          obtain ⟨j, hj, -⟩ := Res.bind_eq_ok.1 hτ
          obtain ⟨y, hy, hj⟩ := Res.bind_eq_ok.1 hj
          refine ⟨.bool true, ?_⟩
          simp only [(hr x).2 hx, (ha y).2 hy, Res.ok_bind, hi, hj]
          split <;> rfl
      · obtain ⟨i, -, hτ⟩ := Res.bind_eq_ok.1 hτ
        obtain ⟨j, -, hτ⟩ := Res.bind_eq_ok.1 hτ
        cases hτ
        exact Fml.toL_holds φ ⟨h.stor, fun y => h.env y, fun k => h.tx k,
          h.mem.of_heap rfl rfl⟩ hf.2
    | pay r a =>
      have hra : r.inL ρ = true ∧ a.inL ρ = true := by simpa only [UpdElem.inL,
          Bool.and_eq_true] using hf.1
      have hr := Term.toL_eval h r hra.1
      have ha := Term.toL_eval h a hra.2
      rw [Close.UpdElem.write_pay]
      refine after_guardM ?_ fun τ' hτ => ?_
      · simp only [UpdElem.toL, LTerm.eval]
        constructor
        · rintro ⟨_, hv⟩
          obtain ⟨i, hi, hv⟩ := Res.bind_eq_ok.1 hv
          obtain ⟨x, hx, hi⟩ := Res.bind_eq_ok.1 hi
          obtain ⟨j, hj, hv⟩ := Res.bind_eq_ok.1 hv
          obtain ⟨y, hy, hj⟩ := Res.bind_eq_ok.1 hj
          have hn : ¬ j < 0 := by
            intro hn
            rw [payGuard_eval σ _ hy hj, if_pos hn] at hv
            split at hv <;> cases hv
          exact ⟨_, by simp only [(hr x).1 hx, (ha y).1 hy, Res.ok_bind, hi, hj, if_neg hn]; rfl⟩
        · rintro ⟨τ', hτ⟩
          obtain ⟨i, hi, hτ⟩ := Res.bind_eq_ok.1 hτ
          obtain ⟨x, hx, hi⟩ := Res.bind_eq_ok.1 hi
          obtain ⟨j, hj, hτ⟩ := Res.bind_eq_ok.1 hτ
          obtain ⟨y, hy, hj⟩ := Res.bind_eq_ok.1 hj
          have hn : ¬ j < 0 := by intro hn; rw [if_pos hn] at hτ; cases hτ
          refine ⟨.bool true, ?_⟩
          simp only [(hr x).2 hx, (ha y).2 hy, Res.ok_bind, hi, hj]
          split <;> rw [payGuard_eval σ _ ((ha y).2 hy) hj, if_neg hn]
      · obtain ⟨i, -, hτ⟩ := Res.bind_eq_ok.1 hτ
        obtain ⟨j, -, hτ⟩ := Res.bind_eq_ok.1 hτ
        split at hτ
        · cases hτ
        · cases hτ
          exact Fml.toL_holds φ ⟨h.stor, fun y => h.env y, fun k => h.tx k,
          h.mem.of_heap rfl rfl⟩ hf.2
    | mref x i =>
      obtain ⟨j, g, hI, hir, hie⟩ := ITerm.toL_eval h i hf.1
      have hf2 := hf.2
      simp only [UpdElem.toL, hI] at hf2 ⊢
      rw [Close.UpdElem.write_mref]
      refine after_guardM ?_ fun τ' hτ => ?_
      · simp only [Res.bind_eq_ok]
        constructor
        · intro hg
          obtain ⟨id, hid⟩ := hir hg
          exact ⟨_, id, hid, rfl⟩
        · rintro ⟨_, id, hid, -⟩
          exact (hie id hid).1
      · obtain ⟨id, hid, he⟩ := Res.bind_eq_ok.1 hτ
        cases he
        refine Fml.toL_holds φ (h.bind x _ _ ?_) hf2
        exact ⟨id, (hie id hid).2, by simp only [State.getEnv_setEnv_self]⟩
    | memory mm =>
      have hmm : mm.inL ρ = true ∧ memWithin (mm.toL ρ) = true := by
        simpa only [UpdElem.inL, Bool.and_eq_true] using hf.1
      obtain ⟨M, g, hM, hmr, hme⟩ := MTerm.toL_eval h mm hmm.1
      have hf2 := hf.2
      have hw : M.within memSize = true := by simpa only [memWithin, hM] using hmm.2
      simp only [UpdElem.toL, hM, hw, ↓reduceIte] at hf2 ⊢
      rw [Close.UpdElem.write_memory]
      refine after_guardM ?_ fun τ' hτ => ?_
      · constructor
        · intro hg
          obtain ⟨μ, hμ⟩ := hmr hg
          exact ⟨_, by rw [hμ, Res.ok_bind]⟩
        · rintro ⟨_, hτ⟩
          obtain ⟨μ, hμ, -⟩ := Res.bind_eq_ok.1 hτ
          exact (hme μ hμ).1
      · obtain ⟨μ', hμ', he⟩ := Res.bind_eq_ok.1 hτ
        cases he
        obtain ⟨-, μ, B, hrun, hh, hp⟩ := hme μ' hμ'
        exact Fml.toL_holds φ (h.setMem hrun hp hh) hf2
    | selfBalance _ _ | saveNet _ =>
      simp only [UpdElem.inL, Bool.false_eq_true, false_and] at hf
  | .modal m P φ, _, _, _, _, hf => by
    obtain ⟨ω, rfl⟩ := Prog.reverts_eq hf
    cases m <;> simp only [holds, Prog.run, Stmt.run, bind, Except.bind, Modality.afterRun,
      Modality.after, Modality.onHalt, Fml.toL, LFml.holds, not_true_eq_false, ne_eq,
      Except.error.injEq, reduceCtorEq, not_false_eq_true, and_true]
  | .all x p φ, σ, τ, ρ, h, hf => by
    simp only [Fml.inL, Bool.and_eq_true, Bool.not_eq_true'] at hf
    have hx : x ∉ ρ.vars := by simpa only [List.contains_eq_mem, decide_eq_false_iff_not] using hf.1
    simp only [holds, Fml.toL, LFml.holds]
    exact forall_congr' fun v => imp_congr_right fun _ => Fml.toL_holds φ (h.free hx v) hf.2
  | .upd md (e₁ :: e₂ :: rest) φ, σ, τ, ρ, h, hf => by
    cases hv : pairView e₁ e₂ rest with
    | none => simp only [Fml.inL, hv, Bool.false_eq_true] at hf
    | some p =>
      obtain ⟨x, i, mm⟩ := p
      cases hq : pairL ρ x i mm with
      | none => simp only [Fml.inL, hv, hq, Bool.false_eq_true] at hf
      | some q =>
        obtain ⟨g, ρ'⟩ := q
        simp only [Fml.inL, hv, hq, Bool.and_eq_true] at hf
        obtain ⟨rfl, rfl, rfl⟩ := pairView_some hv
        have hs := pair_sound h hq hf.1.1
        show md.after (fun τ' => holds τ' φ) (Upd.apply [.mref x i, .memory mm] τ) ↔ _
        simp only [Fml.toL, pairView, hq]
        exact after_guardM hs.1 fun τ' hτ => Fml.toL_holds φ (hs.2 τ' hτ) hf.2
  | .havoc _, _, _, _, _, hf | .anon .., _, _, _, _, hf => by
    simp only [Fml.inL, Bool.false_eq_true] at hf

/-- `⊨ φ` is the formula with its updates pushed in, true in every state. -/
theorem Fml.valid_iff_toL (φ : Fml C) (hf : φ.inL Sym.empty = true) :
    (⊨ φ) ↔ ∀ σ, (φ.toL Sym.empty).holds σ :=
  forall_congr' fun σ => Fml.toL_holds φ (Rel.empty σ) hf

/-! ## What the storage reads after a write

`ReadWrite.lean` has the read at a written path and apart from it
(`find_save_diverge`).  Deciding needs the other two of mini-solkey's four
cases, and the `delete`: a read *above* a write finds a struct, a mapping or
an array, which is no word; a read *below* a written word finds nothing; a
read at or below a deleted location, before any key, finds the default of
what was there. -/

/-- A write at a nonempty path keeps the shape of what it writes into: a
struct stays a struct, an array an array of the same length and kind, a
mapping a mapping with the same default.  After `alice.age = 3;`, `alice` is
still a struct. -/
theorem saveLive_cons_shape {v new u : SVal} {s : Seg} {r : List Seg}
    (h : v.saveLive (s :: r) new = .ok u) :
    (∃ fs fs', v = .struct fs ∧ u = .struct fs') ∨
    (∃ es es' sh fx, v = .array es sh fx ∧ u = .array es' sh fx ∧ es'.length = es.length) ∨
    (∃ es es' d, v = .map es d ∧ u = .map es' d) := by
  cases v with
  | prim p => cases s <;> simp only [SVal.saveLive, reduceCtorEq] at h
  | struct fields =>
    cases s with
    | «at» _ => simp only [SVal.saveLive, reduceCtorEq] at h
    | field n =>
      simp only [SVal.saveLive] at h
      split at h
      · obtain ⟨_, _, he⟩ := Res.bind_eq_ok.1 h; cases he; exact .inl ⟨_, _, rfl, rfl⟩
      · simp only [reduceCtorEq] at h
  | array elems shadow fx =>
    cases s with
    | field _ => simp only [SVal.saveLive, reduceCtorEq] at h
    | «at» i =>
      simp only [SVal.saveLive] at h
      split at h
      · obtain ⟨_, _, he⟩ := Res.bind_eq_ok.1 h; cases he
        exact .inr (.inl ⟨_, _, _, _, rfl, rfl, List.length_set⟩)
      · simp only [reduceCtorEq] at h
  | map entries dflt =>
    cases s with
    | field _ => simp only [SVal.saveLive, reduceCtorEq] at h
    | «at» i =>
      simp only [SVal.saveLive] at h
      split at h <;>
        (obtain ⟨_, _, he⟩ := Res.bind_eq_ok.1 h; cases he; exact .inr (.inr ⟨_, _, _, rfl, rfl⟩))

/-- A write at a nonempty path returns a struct, an array or a mapping,
which reads as no word: after `alice.age = 3;`, `alice` is not a `uint`. -/
theorem save_cons_asValue {v new u : SVal} {s : Seg} {r : List Seg}
    (h : v.saveLive (s :: r) new = .ok u) : ∃ e, u.asValue = .error e := by
  rcases saveLive_cons_shape h with ⟨_, _, -, rfl⟩ | ⟨_, _, _, _, -, rfl, -⟩ | ⟨_, _, _, -, rfl⟩ <;>
    exact ⟨_, rfl⟩

/-- **A write passes through every location above it**: a write at `Q ++ R`
finds a location at `Q`, writes at `R` below it, and leaves that location
readable at `Q`.  Example: `alice.account.balance = 7;` passes through
`alice` and `alice.account`. -/
theorem save_through : ∀ {v new u : SVal} (Q R : List Seg),
    v.saveLive (Q ++ R) new = .ok u →
      ∃ w w', v.findLive Q = .ok w ∧ w.saveLive R new = .ok w' ∧ u.findLive Q = .ok w'
  | v, _, u, [], R, h => ⟨v, u, by cases v <;> rfl, h, by cases u <;> rfl⟩
  | v, new, u, s :: Q, R, h => by
    cases v with
    | prim p => cases s <;> simp only [List.cons_append, SVal.saveLive, reduceCtorEq] at h
    | struct fields =>
      cases s with
      | «at» _ => simp only [List.cons_append, SVal.saveLive, reduceCtorEq] at h
      | field n =>
        simp only [List.cons_append, SVal.saveLive] at h
        split at h
        · rename_i old hl
          obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h; cases he
          obtain ⟨w, w', h₁, h₂, h₃⟩ := save_through Q R hu
          exact ⟨w, w', by simp only [SVal.findLive, hl, h₁], h₂, by simp only [SVal.findLive,
              lookupBy_setBy_self, h₃]⟩
        · simp only [reduceCtorEq] at h
    | array elems shadow fx =>
      cases s with
      | field _ => simp only [List.cons_append, SVal.saveLive, reduceCtorEq] at h
      | «at» i =>
        simp only [List.cons_append, SVal.saveLive] at h
        split at h
        · rename_i hi
          obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h; cases he
          obtain ⟨w, w', h₁, h₂, h₃⟩ := save_through Q R hu
          refine ⟨w, w', by simp only [SVal.findLive, hi, and_self, ↓reduceDIte,
              List.get_eq_getElem, ← h₁], h₂, ?_⟩
          simp only [SVal.findLive, hi, List.length_set, and_self, ↓reduceDIte,
              List.get_eq_getElem, List.getElem_set_self, h₃]
        · simp only [reduceCtorEq] at h
    | map entries dflt =>
      cases s with
      | field _ => simp only [List.cons_append, SVal.saveLive, reduceCtorEq] at h
      | «at» i =>
        simp only [List.cons_append, SVal.saveLive] at h
        split at h <;> rename_i hl
        · obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h; cases he
          obtain ⟨w, w', h₁, h₂, h₃⟩ := save_through Q R hu
          exact ⟨w, w', by simp only [SVal.findLive, hl, h₁], h₂, by simp only [SVal.findLive,
              lookupBy_setBy_self, h₃]⟩
        · obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h; cases he
          obtain ⟨w, w', h₁, h₂, h₃⟩ := save_through Q R hu
          exact ⟨w, w', by simp only [SVal.findLive, hl, h₁], h₂, by simp only [SVal.findLive,
              lookupBy_setBy_self, h₃]⟩

/-- No segment is a `length`: the one field an array answers to, and the
one a program never writes. -/
def NoLen (ps : List Seg) : Prop := ∀ s ∈ ps, s ≠ .field "length"

/-- A run followed by a return returns when the run does. -/
theorem ex_ok_bind {α β : Type} {x : Res α} {f : α → β} :
    (∃ u, (x >>= fun a => .ok (f a)) = .ok u) ↔ ∃ a, x = .ok a := by
  cases x <;> simp only [bind, Except.bind, reduceCtorEq, exists_false, Except.ok.injEq, exists_eq']

/-- **A write succeeds where a read does**, `length` aside: `alice.age = 3;`
runs exactly where `alice.age` names a location. -/
theorem save_ok_iff_find_ok {new : SVal} : ∀ {v : SVal} {ps : List Seg}, NoLen ps →
    ((∃ u, v.saveLive ps new = .ok u) ↔ ∃ w, v.findLive ps = .ok w)
  | v, [], _ => by cases v <;> simp only [SVal.saveLive, Except.ok.injEq, exists_eq', SVal.findLive]
  | v, s :: ps, hn => by
    have hn' : NoLen ps := fun t ht => hn t (.tail _ ht)
    have hs : s ≠ .field "length" := hn s (.head _)
    cases v with
    | prim p => cases s <;> simp only [SVal.saveLive, reduceCtorEq, exists_false, SVal.findLive]
    | struct fields =>
      cases s with
      | «at» _ => simp only [SVal.saveLive, reduceCtorEq, exists_false, SVal.findLive]
      | field n =>
        simp only [SVal.saveLive, SVal.findLive]
        cases lookupBy n fields with
        | none => simp only [reduceCtorEq, exists_false]
        | some old => simp only [ex_ok_bind]; exact save_ok_iff_find_ok hn'
    | array elems shadow fx =>
      cases s with
      | field n =>
        have : n ≠ "length" := fun h => hs (by rw [h])
        simp only [SVal.saveLive, reduceCtorEq, exists_false, SVal.findLive]
      | «at» i =>
        simp only [SVal.saveLive, SVal.findLive]
        split
        · simp only [ex_ok_bind]; exact save_ok_iff_find_ok hn'
        · simp only [reduceCtorEq, exists_false]
    | map entries dflt =>
      cases s with
      | field _ => simp only [SVal.saveLive, reduceCtorEq, exists_false, SVal.findLive]
      | «at» i =>
        simp only [SVal.saveLive, SVal.findLive]
        cases lookupBy i entries <;> (simp only [ex_ok_bind]; exact save_ok_iff_find_ok hn')

/-- **Below a delete, at a member**: the member of the deleted value is the
deleted member.  After `delete alice;`, `alice.account` is the default of the
old `alice.account`; after `delete values;`, `values.length` is the default of
the old length, `0`; a fixed-size array has no `length` member before or
after. -/
theorem defaultOf_field (N : SVal) (f : Name) (more : List Seg) :
    N.defaultOf.findLive (.field f :: more) =
      N.findLive [.field f] >>= fun e => e.defaultOf.findLive more := by
  cases N with
  | prim p => cases p <;> rfl
  | struct fields =>
    simp only [SVal.defaultOf, SVal.findLive, lookupBy_defaultOfFields]
    cases lookupBy f fields <;> simp only [Option.map_none, bind, Except.bind, Option.map_some]
  | array elems shadow fx =>
    by_cases hf : f = "length"
    · subst hf
      cases fx <;> simp only [SVal.defaultOf, SVal.findLive, Bool.false_eq_true, ↓reduceIte,
          List.length_nil, Int.cast_ofNat_Int, bind, Except.bind]
    · cases fx <;> simp only [SVal.defaultOf, SVal.findLive, bind, Except.bind]
  | map _ _ => rfl

/-- **Below a delete, at a key**: a mapping keeps its entries; a fixed-size
array keeps its elements, each deleted in place; anything else has no key to
read (a dynamic array is emptied). -/
theorem defaultOf_key (N : SVal) (k : Int) (more : List Seg) (a : SVal) :
    N.defaultOf.findLive (.at k :: more) = .ok a ↔
      (isMapV N = true ∧ N.findLive (.at k :: more) = .ok a) ∨
      (isFixV N = true ∧ ∃ e, N.findLive [.at k] = .ok e ∧ e.defaultOf.findLive more = .ok a) := by
  cases N with
  | prim p => cases p <;> simp only [SVal.defaultOf, SVal.findLive, reduceCtorEq, isMapV,
      Bool.false_eq_true, and_self, isFixV, false_and, exists_false, or_self]
  | struct _ => simp only [SVal.defaultOf, SVal.findLive, reduceCtorEq, isMapV,
      Bool.false_eq_true, and_self, isFixV, false_and, exists_false, or_self]
  | array elems shadow fx =>
    cases fx
    · simp only [SVal.defaultOf, SVal.findLive, List.length_nil, Nat.not_lt_zero, and_false,
        ↓reduceDIte, reduceCtorEq, isMapV, Bool.false_eq_true, List.get_eq_getElem, false_and,
            isFixV, SVal.findLive_nil, or_self]
    · simp only [SVal.defaultOf, SVal.findLive, isMapV, isFixV, defaultOfElems_eq_map,
        List.length_map, List.get_eq_getElem, List.getElem_map, SVal.findLive_nil]
      by_cases hb : 0 ≤ k ∧ k.toNat < elems.length
      · simp only [hb, and_self, ↓reduceDIte, Bool.false_eq_true, false_and, Except.ok.injEq,
          exists_eq_left', true_and, false_or]
      · simp only [hb, ↓reduceDIte, reduceCtorEq, Bool.false_eq_true, and_self, false_and,
          exists_false, and_false, or_self]
  | map _ _ => simp only [SVal.defaultOf, isMapV, true_and, isFixV, Bool.false_eq_true, false_and,
      or_false]

/-- The default of a word reads as the word's default: `delete total;` then
`total` is `0`.  A struct, an array or a mapping reads as no word, before
and after. -/
theorem asValue_defaultOf (c : SVal) :
    c.defaultOf.asValue = c.asValue >>= fun x => .ok (zeroV x) := by
  cases c with
  | prim p => cases p <;> rfl
  | struct _ => rfl
  | array _ _ fx => cases fx <;> rfl
  | map _ _ => rfl

/-- **Below a delete, before any key**, a path reads the default of what it
read: after `delete alice.account;`, `alice.account.balance` is the default
of the old balance, and an array's `length` is `0`. -/
theorem find_defaultOf : ∀ (c : SVal) (rest : List Seg), rest.any Seg.isAt = false →
    c.defaultOf.findLive rest = c.findLive rest >>= fun w => .ok w.defaultOf
  | c, [], _ => by simp only [SVal.findLive_nil]; rfl
  | c, .at _ :: _, h => by simp only [List.any_cons, Seg.isAt, Bool.true_or,
      Bool.true_eq_false] at h
  | c, .field n :: r, h => by
    have hr : r.any Seg.isAt = false := by simpa only [List.any_eq_false, Seg.isAt,
        Bool.not_eq_true, List.any_cons, Bool.false_or] using h
    rw [defaultOf_field, show Seg.field n :: r = [Seg.field n] ++ r from rfl,
      SVal.findLive_append c [.field n] r, bind_assoc]
    congr 1; funext e
    exact find_defaultOf e r hr

/-! ## Comparing a write with a read

A write at `P` and a read at `Q` are compared segment by segment from the
root, mini-solkey's `LPath.cmp`: two members at once, two keys by a case on
their equality. -/

/-- A segment of a path, its key a term. -/
inductive SSeg where
  | field (f : Name)
  | key (k : LTerm)
  deriving Inhabited

/-- The segments of a path, root first. -/
def LPath.segs : LPath → List SSeg
  | .root r => [.field r]
  | .field q f => q.segs ++ [.field f]
  | .at q k => q.segs ++ [.key k]

/-- The segment is a key: the `[k]` of `balances[k]`. -/
def SSeg.isKey : SSeg → Bool
  | .field _ => false
  | .key _ => true

/-- Segments evaluated from the root. -/
def segsEval (σ : State) : List SSeg → Res (List Seg)
  | [] => .ok []
  | .field f :: r => segsEval σ r >>= fun rs => .ok (.field f :: rs)
  | .key k :: r => (k.eval σ >>= Value.asInt) >>= fun i => segsEval σ r >>= fun rs => .ok (.at i :: rs)

/-- Segments evaluate piece by piece: `alice.account` then `.balance`. -/
theorem segsEval_append (σ : State) : ∀ {xs ys : List SSeg} {a b : List Seg},
    segsEval σ xs = .ok a → segsEval σ ys = .ok b → segsEval σ (xs ++ ys) = .ok (a ++ b)
  | [], _, a, _, ha, hb => by cases ha; exact hb
  | .field f :: xs, _, a, _, ha, hb => by
    obtain ⟨a', ha', he⟩ := Res.bind_eq_ok.1 ha; cases he
    simp only [List.cons_append, segsEval, bind, Except.bind, segsEval_append σ ha' hb]
  | .key k :: xs, _, a, _, ha, hb => by
    obtain ⟨i, hi, ha⟩ := Res.bind_eq_ok.1 ha
    obtain ⟨a', ha', he⟩ := Res.bind_eq_ok.1 ha; cases he
    simp only [segsEval, hi, Res.ok_bind, segsEval_append σ ha' hb, List.cons_append]

/-- A path that evaluates has segments that do, to the same list. -/
theorem LPath.segs_eval (σ : State) : ∀ {q : LPath} {qs : List Seg},
    q.eval σ = .ok qs → segsEval σ q.segs = .ok qs
  | .root r, qs, h => by cases h; rfl
  | .field q f, qs, h => by
    obtain ⟨qs', h', he⟩ := Res.bind_eq_ok.1 h; cases he
    exact segsEval_append σ (LPath.segs_eval σ h') rfl
  | .at q k, qs, h => by
    obtain ⟨qs', h', h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨i, hi, he⟩ := Res.bind_eq_ok.1 h; cases he
    exact segsEval_append σ (LPath.segs_eval σ h') (by simp only [segsEval, hi, Res.ok_bind])

/-- Evaluated segments have a key exactly where the terms do. -/
theorem segsEval_any (σ : State) : ∀ {xs : List SSeg} {a : List Seg},
    segsEval σ xs = .ok a → a.any Seg.isAt = xs.any SSeg.isKey
  | [], a, h => by cases h; rfl
  | .field f :: xs, a, h => by
    obtain ⟨a', h', he⟩ := Res.bind_eq_ok.1 h; cases he
    simp only [List.any_cons, Seg.isAt, segsEval_any σ h', Bool.false_or, SSeg.isKey]
  | .key k :: xs, a, h => by
    obtain ⟨i, _, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨a', _, he⟩ := Res.bind_eq_ok.1 h; cases he
    simp only [List.any_cons, Seg.isAt, Bool.true_or, SSeg.isKey]

/-- How a read path `Q` stands to a written path `P`. -/
inductive PathRel where
  | eq
  | above
  /-- `Q` is below `P`, by the segments `rest`. -/
  | below (rest : List SSeg)
  | diverge
  deriving Inhabited

/-- What each relation says of the two paths. -/
def PathRel.Holds (σ : State) : PathRel → List Seg → List Seg → Prop
  | .eq, P, Q => Q = P
  | .above, P, Q => ∃ f r, P = Q ++ f :: r
  | .below rest, P, Q => ∃ f r, Q = P ++ f :: r ∧ segsEval σ rest = .ok (f :: r)
  | .diverge, P, Q => Close.Diverge P Q

/-- A value that depends on key equalities. -/
inductive CaseTree (α : Type) where
  | leaf (a : α)
  | ite (a b : LTerm) (t e : CaseTree α)

/-- The leaf a state selects. -/
def CaseTree.get {α : Type} (σ : State) : CaseTree α → α
  | .leaf a => a
  | .ite a b t e =>
    if keyEq (a.eval σ >>= Value.asInt) (b.eval σ >>= Value.asInt) then t.get σ else e.get σ

/-- A tree of terms as one term, its tests `kite`s. -/
def CaseTree.toTerm {α : Type} (f : α → LTerm) : CaseTree α → LTerm
  | .leaf a => f a
  | .ite a b t e => key{ if(a = b) then ‹t.toTerm f› else ‹e.toTerm f› }   -- \if(a1 = a2)

/-- Every test of the tree compares two integers. -/
def CaseTree.TestsOk {α : Type} (σ : State) : CaseTree α → Prop
  | .leaf _ => True
  | .ite a b t e => (∃ i, (a.eval σ >>= Value.asInt) = .ok i) ∧
      (∃ j, (b.eval σ >>= Value.asInt) = .ok j) ∧ t.TestsOk σ ∧ e.TestsOk σ

/-- The term of a tree reads what the selected leaf does, where its tests
compare integers. -/
theorem CaseTree.toTerm_eval {α : Type} (σ : State) (f : α → LTerm) :
    (t : CaseTree α) → t.TestsOk σ → (t.toTerm f).eval σ = (f (t.get σ)).eval σ
  | .leaf _, _ => rfl
  | .ite a b t e, ⟨⟨i, hi⟩, ⟨j, hj⟩, ht, he⟩ => by
    simp only [CaseTree.toTerm, LTerm.eval, CaseTree.get, hi, hj, keyEq, Res.ok_bind,
      decide_eq_true_eq]
    split
    · exact CaseTree.toTerm_eval σ f t ht
    · exact CaseTree.toTerm_eval σ f e he

/-- Two keys the terms alone compare, as KeY's `select(store(…))` does
before it splits: the same local, literal or value of the transaction is
the same key (`some true`),
two different integer literals are different ones (`some false`); anything
else is for the state to settle (`none`).  Not recursive, so the kernel
re-checking a reduction pays one comparison of names. -/
def keyCmp : LTerm → LTerm → Option Bool
  | key{ var(x) }, key{ var(y) } => if x = y then some true else none
  | key{ env(k) }, key{ env(k') } => if k = k' then some true else none
  | key{ lit(‹.int a›) }, key{ lit(‹.int b›) } => some (decide (a = b))
  | _, _ => none

/-- What `keyCmp` settles holds in every state where both keys are integers. -/
theorem keyCmp_spec {σ : State} {i j : LTerm} {c : Bool} {a b : Int}
    (hk : keyCmp i j = some c) (ha : (i.eval σ >>= Value.asInt) = .ok a)
    (hb : (j.eval σ >>= Value.asInt) = .ok b) : decide (a = b) = c := by
  unfold keyCmp at hk
  split at hk
  · split at hk
    · cases hk
      subst_vars
      rw [ha] at hb
      cases hb
      simp only [decide_true]
    · cases hk
  · split at hk
    · cases hk
      subst_vars
      rw [ha] at hb
      cases hb
      simp only [decide_true]
    · cases hk
  · cases hk
    simp only [LTerm.eval, Res.ok_bind, Value.asInt] at ha hb
    cases ha
    cases hb
    rfl
  · cases hk

/-- `cmpSegs P Q`: how the read `Q` stands to the write `P`.

Example: `balances[j]` against `balances[k]` is `ite j k eq diverge`, and
`balances[k]` against `balances[k]` is `eq` (`keyCmp`). -/
def cmpSegs : List SSeg → List SSeg → CaseTree PathRel
  | [], [] => .leaf .eq
  | [], q => .leaf (.below q)
  | _, [] => .leaf .above
  | .field f :: p, .field g :: q => if f = g then cmpSegs p q else .leaf .diverge
  | .key i :: p, .key j :: q => match keyCmp i j with
    | some true => cmpSegs p q
    | some false => .leaf .diverge
    | none => .ite i j (cmpSegs p q) (.leaf .diverge)
  | .field _ :: _, .key _ :: _ | .key _ :: _, .field _ :: _ => .leaf .diverge

/-- A common first segment keeps the relation. -/
theorem PathRel.Holds.cons {σ : State} {r : PathRel} {P Q : List Seg} (x : Seg)
    (h : r.Holds σ P Q) : r.Holds σ (x :: P) (x :: Q) := by
  cases r with
  | eq => simp_all only [Holds]
  | above => obtain ⟨f, t, h⟩ := h; exact ⟨f, t, by simp only [h, List.cons_append]⟩
  | below k => obtain ⟨f, t, h, hk⟩ := h; exact ⟨f, t, by simp only [h, List.cons_append], hk⟩
  | diverge => exact .inr h

/-- **The comparison is right**: in a state where both paths evaluate, it
selects the relation they are in.  Example: for the write
`balances[j] = 6;` and the read `balances[k]`, `eq` where `k = j`, `diverge`
elsewhere. -/
theorem cmpSegs_holds (σ : State) : ∀ (P Q : List SSeg) {ps qs : List Seg},
    segsEval σ P = .ok ps → segsEval σ Q = .ok qs → ((cmpSegs P Q).get σ).Holds σ ps qs
  | [], [], _, _, hp, hq => by cases hp; cases hq; rfl
  | [], y :: ys, ps, qs, hp, hq => by
    cases hp
    have hq₀ := hq
    revert hq hq₀
    cases y with
    | field g =>
      intro hq hq₀
      obtain ⟨a, _, he⟩ := Res.bind_eq_ok.1 hq; cases he
      exact ⟨_, _, rfl, hq₀⟩
    | key j =>
      intro hq hq₀
      obtain ⟨i, _, hq⟩ := Res.bind_eq_ok.1 hq
      obtain ⟨a, _, he⟩ := Res.bind_eq_ok.1 hq; cases he
      exact ⟨_, _, rfl, hq₀⟩
  | x :: xs, [], ps, qs, hp, hq => by
    cases hq
    cases x with
    | field g =>
      obtain ⟨a, _, he⟩ := Res.bind_eq_ok.1 hp; cases he
      exact ⟨_, _, rfl⟩
    | key j =>
      obtain ⟨i, _, hp⟩ := Res.bind_eq_ok.1 hp
      obtain ⟨a, _, he⟩ := Res.bind_eq_ok.1 hp; cases he
      exact ⟨_, _, rfl⟩
  | .field f :: xs, .field g :: ys, ps, qs, hp, hq => by
    obtain ⟨a, ha, he⟩ := Res.bind_eq_ok.1 hp; cases he
    obtain ⟨b, hb, he⟩ := Res.bind_eq_ok.1 hq; cases he
    by_cases hfg : f = g
    · subst hfg
      simpa only [cmpSegs, ↓reduceIte] using (cmpSegs_holds σ xs ys ha hb).cons (.field f)
    · simp only [cmpSegs, hfg, if_false, CaseTree.get]
      exact .inl (by simpa only [ne_eq, Seg.field.injEq] using hfg)
  | .key i :: xs, .key j :: ys, ps, qs, hp, hq => by
    obtain ⟨a, ha, hp⟩ := Res.bind_eq_ok.1 hp
    obtain ⟨as, has, he⟩ := Res.bind_eq_ok.1 hp; cases he
    obtain ⟨b, hb, hq⟩ := Res.bind_eq_ok.1 hq
    obtain ⟨bs, hbs, he⟩ := Res.bind_eq_ok.1 hq; cases he
    rcases hk : keyCmp i j with _ | _ | _
    · simp only [cmpSegs, hk, CaseTree.get, ha, hb, keyEq]
      by_cases hab : a = b
      · subst hab
        simpa only [decide_true, ↓reduceIte] using (cmpSegs_holds σ xs ys has hbs).cons (.at a)
      · simp only [hab, decide_false, Bool.false_eq_true, if_false]
        exact .inl (by simpa only [ne_eq, Seg.at.injEq] using hab)
    · have hab : a ≠ b := by simpa only [ne_eq, decide_eq_false_iff_not] using keyCmp_spec hk ha hb
      simp only [cmpSegs, hk, CaseTree.get]
      exact .inl (by simpa only [ne_eq, Seg.at.injEq] using hab)
    · have hab : a = b := by simpa only [decide_eq_true_eq] using keyCmp_spec hk ha hb
      subst hab
      simpa only [cmpSegs, hk] using (cmpSegs_holds σ xs ys has hbs).cons (.at a)
  | .field f :: xs, .key j :: ys, ps, qs, hp, hq => by
    obtain ⟨a, ha, he⟩ := Res.bind_eq_ok.1 hp; cases he
    obtain ⟨b, hb, hq⟩ := Res.bind_eq_ok.1 hq
    obtain ⟨bs, hbs, he⟩ := Res.bind_eq_ok.1 hq; cases he
    exact .inl (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
  | .key i :: xs, .field g :: ys, ps, qs, hp, hq => by
    obtain ⟨a, ha, hp⟩ := Res.bind_eq_ok.1 hp
    obtain ⟨as, has, he⟩ := Res.bind_eq_ok.1 hp; cases he
    obtain ⟨b, hb, he⟩ := Res.bind_eq_ok.1 hq; cases he
    exact .inl (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])

/-- The comparison of two paths that evaluate compares integers only. -/
theorem cmpSegs_testsOk (σ : State) : ∀ (P Q : List SSeg) {ps qs : List Seg},
    segsEval σ P = .ok ps → segsEval σ Q = .ok qs → (cmpSegs P Q).TestsOk σ
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, _, _, _ => trivial
  | .field _ :: _, [], _, _, _, _ | .key _ :: _, [], _, _, _, _ => trivial
  | .field f :: xs, .field g :: ys, _, _, hp, hq => by
    obtain ⟨_, ha, -⟩ := Res.bind_eq_ok.1 hp
    obtain ⟨_, hb, -⟩ := Res.bind_eq_ok.1 hq
    simp only [cmpSegs]
    split
    · exact cmpSegs_testsOk σ xs ys ha hb
    · trivial
  | .key i :: xs, .key j :: ys, _, _, hp, hq => by
    obtain ⟨a, ha, hp⟩ := Res.bind_eq_ok.1 hp
    obtain ⟨_, has, -⟩ := Res.bind_eq_ok.1 hp
    obtain ⟨b, hb, hq⟩ := Res.bind_eq_ok.1 hq
    obtain ⟨_, hbs, -⟩ := Res.bind_eq_ok.1 hq
    simp only [cmpSegs]
    split
    · exact cmpSegs_testsOk σ xs ys has hbs
    · trivial
    · exact ⟨⟨a, ha⟩, ⟨b, hb⟩, cmpSegs_testsOk σ xs ys has hbs, trivial⟩
  | .field _ :: _, .key _ :: _, _, _, _, _ => trivial
  | .key _ :: _, .field _ :: _, _, _, _, _ => trivial

/-! ## Eliminating the reads of writes

`find(s, Q)` with writes in `s` becomes a case tree whose leaves read the
initial storage only.  Each read is guarded by what makes it return: the
writes below it succeed (`LStor.okE`) and its path evaluates.  Under the
guard, `readU` and `hasU` peel off one write at a time, comparing paths. -/

/-- The path has no `length` segment. -/
def LPath.noLen : LPath → Bool
  | .root r => r != "length"
  | .field q f => q.noLen && f != "length"
  | .at q _ => q.noLen

/-- The leaf of a read after a write of `w`: the value at the written path,
none above it (a struct is no word) or below it (a word has no members), the
old read apart from it. -/
def saveLeaf (w old : LTerm) : PathRel → LTerm
  | .eq => w                                    -- selectOnSaveCons \then, saveOnEmptyPrim
  | .above | .below _ => key{ err }             -- Lean only: a word is not a struct
  | .diverge => old                             -- selectOnSaveCons \else

/-- A read below a deleted location, `rest` below `q`, from the root down:
through a member, what the member of the deleted value has; at a key, the old
read (`atMap`) where the location above the key is a mapping, which `delete`
leaves alone (`guard .map`); the same one key further down where it is a
fixed-size array, whose elements `delete` resets in place (`guard .fixed`);
nothing where it is anything else (a dynamic array is emptied).  With every
key passed, the default of the old read (`atEnd`).  After `delete ledger;`,
`ledger.balances[k]` is the old entry; after `delete grid;` (`uint[2][3]`),
`grid[i][j]` is `0`. -/
def delBelow (atMap atEnd : LTerm) (guard : KShape → LPath → LTerm) : LPath → List SSeg → LTerm
  | q, .field f :: r => delBelow atMap atEnd guard (q.field f) r      -- selectStDelNodeRef
  -- selectStDelNodeMap: a mapping keeps its entries; selectStDelNodeFixedElement
  | q, .key k :: r => key{ orElse((‹guard .map q›; atMap),
      (‹guard .fixed q›; ‹delBelow atMap atEnd guard (q.at k) r›)) }
  | _, [] => atEnd                                                  -- selectStDelNodeDefault

/-- The leaf of a read after a `delete` of `P`: the default of the old word
at the path, and below it as `delBelow` walks it. -/
def delLeaf (old : LTerm) (P : LPath) (guard : KShape → LPath → LTerm) : PathRel → LTerm
  | .eq => key{ delValue(old) }               -- selectOnDelAtCons \then, delFieldDefault
  | .below rest => delBelow old key{ delValue(old) } guard P rest   -- delField*, selectStDelNode*
  | .above => key{ err }                      -- Lean only: a word is not a struct
  | .diverge => old                           -- selectOnDelAtCons \else

/-- Whether a location is there after a write. -/
def saveHas (old : LTerm) : PathRel → LTerm
  | .eq | .above => key{ true }
  | .below _ => key{ err }
  | .diverge => old

/-- Whether a location is there after a `delete`: through members as before,
through keys as `delBelow` says. -/
def delHas (old : LTerm) (P : LPath) (guard : KShape → LPath → LTerm) : PathRel → LTerm
  | .eq | .above => key{ true }
  | .below rest => delBelow old old guard P rest
  | .diverge => old

/-- Whether a mapping is there after a write: a write keeps the shape of
every location above it. -/
def saveMap (old : LTerm) : PathRel → LTerm
  | .eq | .below _ => key{ err }
  | .above | .diverge => old

/-- Whether a mapping (a fixed-size array) is there after a `delete`: the
default of a value has its shape. -/
def delMap (old : LTerm) (P : LPath) (guard : KShape → LPath → LTerm) : PathRel → LTerm
  | .eq | .above | .diverge => old
  | .below rest => delBelow old old guard P rest

/-- The length of an array's default: a fixed-size array keeps it (`fixed`
returns where it is one), a dynamic one is emptied.  `delete values;` leaves
`values.length` at `0`, `delete fixedValues;` at `3`. -/
def lenEnd (old fixed : LTerm) : LTerm :=
  key{ orElse((fixed; old), (old; 0)) }   -- selectStDelNodeFixedSize, selectStDelNodeDefault

/-- The length at `Q` after a `delete` of `P`: its default's where `Q` is
`P`, as `delBelow` walks it below `P`, the old one above or apart. -/
def delLen (old atEnd : LTerm) (P : LPath) (guard : KShape → LPath → LTerm) : PathRel → LTerm
  | .eq => atEnd
  | .above | .diverge => old
  | .below rest => delBelow old atEnd guard P rest

/-- The length after a `push`, unchecked (`bool` arithmetic is not
range-checked): a storage array's length has no bound. -/
def lenSucc (L : LTerm) : LTerm := key{ binop(‹.add›, bool, L, 1) }

/-- The length after a `pop`, unchecked as `lenSucc`. -/
def lenPred (L : LTerm) : LTerm := key{ binop(‹.sub›, bool, L, 1) }

/-- The default word of a primitive type: what `values.push();` appends. -/
def dfltV : PrimTy → Value
  | .bool => .bool false
  | .uint | .int => .int 0

/-- Returns where the operation on an array of length `L` does: a push
wherever there is an array, a `pop` where it is not empty. -/
def arrOk : AOp → LTerm → LTerm
  | .push, L | .slot _, L => key{ (L; true) }
  -- storagePopSave: "nonEmpty" where 0 < find(storage, consr(sp, size)), "empty" reverts
  | .pop _, L => key{ if(0 < L) then true else err }

/-- The slot an operation appends, at an index `k` against the old length
`L`: the word `w` or a primitive default at `k = L` (`atNew`, nothing below a
word), the old element elsewhere.  A `pop` leaves nothing at `L - 1`.  Below
a `push()` of a struct or an array the read itself (`opq`): the closer types
it whole, the slot and the elements alike (`Facts.slotTy`). -/
def arrKey (op : AOp) (L k old opq : LTerm) (atNew : LTerm) : LTerm :=
  match op with
  | .push | .slot (.prim _) => key{ if(k = L) then atNew else old }  -- selectOnSaveCons at at(L)
  | .slot (.ref _) => opq
  | .pop _ => key{ if(k = ‹lenPred L›) then err else old }   -- storagePopSave's delAt(at(L - 1))

/-- The leaf of a read after an operation on the array at `P`: no word at or
above the array; below it, by `arrKey`; the old read apart from it. -/
def arrRead (op : AOp) (w L old opq : LTerm) (slot : List SSeg → LTerm) : PathRel → LTerm
  | .eq | .above => key{ err }
  | .diverge => old
  | .below (.key k :: rest) =>
    match op with
    | .slot (.ref _) => key{ if(k = L) then ‹slot rest› else old }
    | _ => arrKey op L k old opq (match op with
      | .push => if rest.isEmpty then w else key{ err }
      | .slot (.prim p) => if rest.isEmpty then key{ lit(‹dfltV p›) } else key{ err }
      | _ => key{ err })
  | .below _ => opq

/-- `true` where `0 ≤ k ≤ L`, halting elsewhere: an index of an array of
length `L + 1`. -/
def inRange (k L : LTerm) : LTerm :=
  key{ if(0 <= k && k <= L) then true else err }

/-- Whether a location is there after an operation on an array: an element
of a pushed struct or array at an index up to the old length. -/
def arrHas (op : AOp) (L old opq : LTerm) : PathRel → LTerm
  | .eq | .above => key{ true }
  | .diverge => old
  | .below (.key k :: rest) =>
    match op with
    | .slot (.ref _) => if rest.isEmpty then inRange k L else opq
    | _ => arrKey op L k old opq (if rest.isEmpty then key{ true } else key{ err })
  | .below _ => opq

/-- `o` where the operation is a `push()` of a reference, the one operation
whose length `arrLength` reads the slot for, else `none`: `macro_inline`, so
compiled code builds `o` only there. -/
@[macro_inline] def AOp.gateSlot {α : Type} (op : AOp) (o : Option α) : Option α :=
  match op with
  | .slot (.ref _) => o
  | _ => none

/-- The length at `Q` after an operation on the array at `P`: one more or
one less at `P`, the old one above or apart.  Below a `push()` of an array,
the length the recycled slot has (`slot`, `findDefinitionSize` then
`selectOnSaveCons` on `size`) where it is given, the read itself otherwise. -/
def arrLength (op : AOp) (L old opq : LTerm) (slot : Option (List SSeg → LTerm)) :
    PathRel → LTerm
  | .eq => match op with
    | .push | .slot _ => lenSucc L
    | .pop _ => lenPred L
  | .above | .diverge => old
  | .below (.key k :: rest) =>
    match op, slot with
    | .slot (.ref _), some f => key{ if(k = L) then ‹f rest› else old }
    | _, _ => arrKey op L k old opq key{ err }
  | .below _ => opq

/-- Whether a mapping (a fixed-size array) is at `Q` after an operation on
an array: the shapes at and above it stay. -/
def arrMap (op : AOp) (L old opq : LTerm) : PathRel → LTerm
  | .eq | .above | .diverge => old
  | .below (.key k :: _) => arrKey op L k old opq key{ err }
  | .below _ => opq

/-- A read below a copy, the segments `pre` walked: at a key, the read
itself (`opq`) where the source has a mapping there (a mapping met in both
keeps the target's entries; a copy of a well-typed program has none); with
no key left, what the source has (`F`). -/
def copyKeys (srcMap : List SSeg → LTerm) (opq : LTerm) (F : List SSeg → LTerm) :
    List SSeg → List SSeg → LTerm
  | pre, [] => F pre
  | pre, .field f :: r => copyKeys srcMap opq F (pre ++ [.field f]) r
  | pre, .key k :: r =>
    key{ if(‹isT (srcMap pre)›) then opq else ‹copyKeys srcMap opq F (pre ++ [.key k]) r› }

/-- The leaf of a read after a copy over `P`: at and below `P`, what the
source has there (`copyKeys`); the old read apart. -/
def copyLeaf (atEq aboveV old opq : LTerm) (srcMap F : List SSeg → LTerm) : PathRel → LTerm
  | .eq => atEq
  | .above => aboveV
  | .diverge => old
  | .below rest => copyKeys srcMap opq F [] rest

/-- The path extended by the segments `rest`. -/
def LPath.addSegs : LPath → List SSeg → LPath
  | q, [] => q
  | q, .field f :: r => LPath.addSegs (q.field f) r
  | q, .key k :: r => LPath.addSegs (q.at k) r

/-- The path extended by the members `rest` starts with, up to its first
key: `alice` and `[account, balances, k]` make `alice.account.balances`. -/
def LPath.addFields : LPath → List SSeg → LPath
  | q, .field f :: r => LPath.addFields (q.field f) r
  | q, _ => q

/-! ### The run guard of a memory (Lean only)

KeY's memory operations are total; the interpreter's halt: an allocation of
a type with a mapping, a copy of a word or of a subtree with a mapping, a
write outside a struct or past the length, a name that denotes nothing.  The
guard `LMem.okU` returns exactly where the run does, from tests the closer
reads off the layout and the memory; it says nothing (`none`) where an
allocation's ordinal or type is not one it can check statically. -/


/-- The guard of a write's slot from the memory below it: a member in a
struct (`S`), an element at the index `t` below the length (`L`). -/
def wrGuard (S L : Unit → Option LTerm) (t : LTerm) : LSel → Option LTerm
  | .fld _ => S ()
  | .idx _ => (L ()).map (ltR t)
  | .size => none

/-- The name a memory value refers to. -/
def LMV.refId? : LMV → Option LId
  | .word _ => none
  | .ref j => some j

/-- The guard of a write's value: the word returns (`W`), the name denotes (`N`). -/
def valGuard (W : LTerm) (N : Unit → Option LTerm) : LMV → Option LTerm
  | .word _ => some W
  | .ref _ => N ()

/-- The memory below runs (`G`), and so do the slot's and the value's guards. -/
def okWrite (G : Option LTerm) (W V : Unit → Option LTerm) : Option LTerm :=
  G.bind fun g => (W ()).bind fun w => (V ()).map fun x =>
    key{ (g; (w; (x; true))) }

/-- The root a view puts its object at: a view that returns has it. -/
def isViewRoot : LPath → Bool
  | .root r => r == viewRoot
  | _ => false

/-- A view's guard: the memory runs and the name denotes; `d` where either
is not known. -/
def okView (G N : Option LTerm) (d : LTerm) : LTerm :=
  match G, N with
  | some g, some n => key{ (g; (n; true)) }
  | _, _ => d

/-! ### Writes through a dangling alias

A write through a stale alias (`LStor.stale none`) is KeY's plain `save` at
a slot: a read compared with it sees the word where the paths meet, nothing
below or above it, the old read apart (`selectOnSaveCons`).  Unlike a live
write, the read at its path is live only where the path is: the word is
guarded by the old location's presence (`staleRead`, `staleHas`). -/

/-- The leaf of a read after a stale write of `w`: the word where the old
location is live (`hasQ`), nothing above or below it, the old read apart. -/
def staleRead (w hasQ old : LTerm) : PathRel → LTerm
  | .eq => key{ (hasQ; w) }                     -- selectOnSaveCons \then, guarded
  | .above | .below _ => key{ err }
  | .diverge => old                             -- selectOnSaveCons \else

/-- Whether a location is there after a stale write: as before, but below
the written word. -/
def staleHas (old : LTerm) : PathRel → LTerm
  | .below _ => key{ err }
  | .eq | .above | .diverge => old

/-- The array of a path's last index, the index, and the members after it:
`tokens[0].value` splits as `tokens`, `0`, `[value]`. -/
def LPath.splitLast : LPath → Option (LPath × LTerm × List SSeg)
  | .root _ => none
  | .field q f => q.splitLast.map fun x => (x.1, x.2.1, x.2.2 ++ [.field f])
  | .at q k => some (q, k, [])

/-- **The run guard of a stale write** (Lean only: KeY's `save` is total,
the interpreter's halts where the slot is not there).  Where `has`, the live
location, returns, or the index is the array's length (`k = L`) and the
first slot past the end has the location (`S`), the write returns;
elsewhere the guard is the write itself (`opq`). -/
def staleOk (has : LTerm) (slot : Option (LTerm × LTerm × LTerm)) (opq : LTerm) : LTerm :=
  .orElse (.orElse has (match slot with
    | some (k, L, S) => key{ if(k = L) then S else err }
    | none => key{ err })) opq

/-- The leaf of a slot reader through a write through a dangling alias, the
written location compared with the slot: `atEq` where it is the slot,
`atDiv` where it is apart, the read itself (`opq`) elsewhere. -/
def slotLeaf (atEq atDiv opq : LTerm) : PathRel → LTerm
  | .eq => atEq
  | .diverge => atDiv
  | .above | .below _ => opq

/-- The index a read below an array starts with (`.err` where it starts
with none). -/
def headKey : List SSeg → LTerm
  | .key k :: _ => k
  | _ => key{ err }

/-- The word `w` where the read is the element at one index, `.err`
otherwise (a word has nothing below it). -/
def wordAtKey (w : LTerm) : List SSeg → LTerm
  | [.key _] => w
  | _ => key{ err }


/-- Whether `s` holds a write through a stale alias (`SymB.stale`: one a
`pop` left dangling, or one still live but bound before the storage last
changed).  Lean only, a cost and regression guard: the slot readers look past
a `delete` of an empty array, past a copy, and below a recycled array's
length only then (`LStor.slotU`, `LStor.lenU`), so every other storage's
reduction is as before. -/
def LStor.dangles : LStor → Bool
  | .stale .. => true
  | .save s .. | .delAt s _ | .arr _ s .. => s.dangles
  | .copy s _ src _ => s.dangles || src.dangles
  | .init | .view .. => false
termination_by structural s => s

mutual

/-- Every read of a write eliminated. -/
def LTerm.elim : LTerm → LTerm
  | key{ lit(v) } => key{ lit(v) }
  | key{ var(x) } => key{ var(x) }
  | key{ binop(op, p, a, b) } => .binop op p a.elim b.elim
  | key{ unop(op, p, a) } => .unop op p a.elim
  | key{ if(c) then a else b } => .ite c.elim a.elim b.elim
  | key{ find(st, q) } => .seq st.okE (.seq (.pok q.elim) (st.readU q.elim))
  | key{ has(st, q) } => .seq st.okE (.seq (.pok q.elim) (st.hasU q.elim))
  | key{ kmap(sh, st, q) } => .seq st.okE (.seq (.pok q.elim) (st.mapU sh q.elim))
  | key{ find(st, q.length) } => .seq st.okE (.seq (.pok q.elim) (st.lenU q.elim))
  | key{ okSt(st) } => st.okE
  | key{ okPath(q) } => .pok q.elim
  | key{ (d; a) } => .seq d.elim a.elim
  | key{ orElse(a, b) } => .orElse a.elim b.elim
  | key{ if(a = b) then t else e } => .kite a.elim b.elim t.elim e.elim
  | key{ delValue(a) } => .zero a.elim
  | key{ err } => key{ err }
  | key{ env(k) } => key{ env(k) }
  | key{ findP(st, q) } => .findP st q.elim
  | key{ copyOk(st, q) } => .seq st.okE (.seq (.pok q.elim) (st.cpokU q.elim))
termination_by structural t => t

/-- A path with the reads in its keys eliminated: `people[balances[a]]`. -/
def LPath.elim : LPath → LPath
  | .root r => .root r
  | key{ q.f } => .field q.elim f
  | key{ q[k] } => .at q.elim k.elim
termination_by structural q => q

/-- Returns exactly when the writes of `s` succeed.  A copy within one
storage (`tokens = bucket.tokens;`) checks it once where it holds a stale
write (`LStor.dangles`): the guard is repeated at every read, and twice it
would put those leaves past `Derive.elimSize`. -/
def LStor.okE : LStor → LTerm
  -- Lean only: KeY's save and delAt are total, the interpreter's halt
  | key{ storage } => key{ true }
  | key{ save(st, q, w) } =>
    if q.noLen then .seq st.okE (.seq w.elim (.seq (.pok q.elim) (st.hasU q.elim)))
    else key{ ok(save(st, q, w)) }
  | key{ delAt(st, q) } =>
    if q.noLen then .seq st.okE (.seq (.pok q.elim) (st.hasU q.elim))
    else key{ ok(delAt(st, q)) }
  | key{ arr(op, st, q, w) } =>
    if q.noLen then .seq st.okE (.seq w.elim (.seq (.pok q.elim) (arrOk op (st.lenU q.elim))))
    else key{ ok(arr(op, st, q, w)) }
  | key{ staleSave(st, q, w) } =>
    if q.noLen then .seq st.okE (.seq w.elim (.seq (.pok q.elim)
      (staleOk (st.hasU q.elim) (match q.elim.splitLast with
        | some (A, k, rest) => some (k, st.lenU A, st.slotHasU A rest .err)
        | none => none) key{ ok(staleSave(st, q, w)) })))
    else key{ ok(staleSave(st, q, w)) }
  | key{ stale(op, st, q, w) } =>
    if q.noLen then .seq st.okE (.seq w.elim (.seq (.pok q.elim)
      (staleOk (arrOk op (st.lenU q.elim)) (match q.elim.splitLast with
        | some (A, k, rest) => some (k, st.lenU A, arrOk op (st.slotLenU A rest .err))
        | none => none) key{ ok(stale(op, st, q, w)) })))
    else key{ ok(stale(op, st, q, w)) }
  | key{ save(st, q, find(src, sq)) } =>
    if q.noLen then
      if st.dangles && src == st then .seq st.okE (.seq (.pok sq.elim) (.seq (st.hasU sq.elim)
        (.seq (.pok q.elim) (st.hasU q.elim))))
      else .seq src.okE (.seq (.pok sq.elim) (.seq (src.hasU sq.elim)
        (.seq st.okE (.seq (.pok q.elim) (st.hasU q.elim)))))
    else key{ ok(save(st, q, find(src, sq))) }
  | key{ copyMem(mtSt, m, i) } =>
    if m.refDesc then okView m.okU (m.objU false i) key{ ok(copyMem(mtSt, m, i)) }
    else key{ ok(copyMem(mtSt, m, i)) }
termination_by structural s => s

/-- The word at `Q` in `s`, where `s` and `Q` return. -/
def LStor.readU : LStor → LPath → LTerm
  | key{ storage }, Q => key{ find(storage, Q) }    -- the initial storage, for the facts
  -- findDefinition*, then selectOnSaveCons per segment (cmpSegs); saveLeaf: .eq is \then
  -- and saveOnEmptyPrim, .diverge \else, .above/.below Lean's err
  | key{ save(st, P, w) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm (saveLeaf w.elim (st.readU Q))
  -- selectOnDelAtCons, then delField* / selectStDelNode* (by a shape test, not a sort)
  | key{ delAt(st, P) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (delLeaf (st.readU Q) P.elim fun sh q => st.mapU sh q)
  -- selectOnSaveCons on the slot and the size a push or a pop writes (arrRead)
  | key{ arr(op, st, P, w) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (arrRead op w.elim (st.lenU P.elim) (st.readU Q) key{ find(arr(op, st, P, w), Q) }
        fun rest => st.slotU P.elim rest key{ find(arr(op, st, P, w), Q) })
  -- selectOnSaveCons, the word guarded by the old location (staleRead)
  | key{ staleSave(st, P, w) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (staleRead w.elim (st.hasU Q) (st.readU Q))
  | key{ stale(op, st, P, w) }, Q => key{ find(stale(op, st, P, w), Q) }
  -- selectOnSaveEmpty{Ref,Fixed,IndexStruct,Default}: below the copy, the source (copyLeaf)
  | key{ save(st, P, find(src, SQ)) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (copyLeaf (src.readU SQ.elim) key{ err } (st.readU Q)
        key{ find(save(st, P, find(src, SQ)), Q) }
        (fun pre => src.mapU .map (SQ.elim.addSegs pre)) fun rest => src.readU (SQ.elim.addSegs rest))
  -- findOnCopy, selectOnCopyMemPrim: the memory read through the view
  | key{ copyMem(mtSt, m, i) }, Q =>
    match viewPath Q with
    | some (p, a) =>
      match m.walk i p with
      | some j => (m.readU j a).getD key{ find(copyMem(mtSt, m, i), Q) }
      | none => key{ find(copyMem(mtSt, m, i), Q) }
    | none => key{ find(copyMem(mtSt, m, i), Q) }
termination_by structural s => s

/-- What the slot a `push()` of a struct or an array takes holds at `rest`,
the array at `P` in `s` (`pushSlot`: the first slot past the end, recycled):
after a `pop` at `P`, the element it popped, cleared (as below a `delete`)
or kept; after a `delete` of a dynamic array at `P`, its old first element,
cleared, where it had one; through a stale write, the word where it is at
the slot.  Where `s` holds a stale write (`LStor.dangles`) it also reads
past a `delete` of an empty array (the slot as it was,
`selectStDelNodeIndexStruct`) and past a copy over `P` (below the old
length the old element there, cleared; at it the old slot;
`selectOnSaveEmptyIndexStruct`).  Elsewhere the read itself (`opq`). -/
def LStor.slotU : LStor → LPath → List SSeg → LTerm → LTerm
  -- storagePopSave's delAt(at(n - 1)), then selectOnDelAtCons, delFieldIndexStruct
  | key{ arr(pop(keep), st, P', _) }, P, rest, opq =>
    if P'.elim == P then
      if keep then st.readU ((P.at (lenPred (st.lenU P))).addSegs rest)
      else delLeaf (st.readU ((P.at (lenPred (st.lenU P))).addSegs rest)) (P.at (lenPred (st.lenU P)))
        (fun sh q => st.mapU sh q) (if rest.isEmpty then .eq else .below rest)
    else opq
  -- selectStDelNodeIndexStruct: the old first element, cleared; past the end, the slot
  | key{ delAt(st, P') }, P, rest, opq =>
    if P'.elim == P then
      key{ if(‹isT (st.mapU .fixed P)›) then opq
        else if(‹st.lenU P› = 0) then ‹if st.dangles then st.slotU P rest opq else opq›
        else ‹delLeaf (st.readU ((P.at key{ 0 }).addSegs rest)) (P.at key{ 0 })
          (fun sh q => st.mapU sh q) (if rest.isEmpty then .eq else .below rest)› }
    else opq
  | key{ staleSave(st, P', w) }, P, rest, opq =>
    (cmpSegs P'.elim.segs ((P.at (st.lenU P)).addSegs rest).segs).toTerm
      (saveLeaf (if rest.any SSeg.isKey then opq else w.elim) (st.slotU P rest opq))
  -- a copy over the array, where the storage holds a stale write
  | key{ save(st, P', find(src, SQ)) }, P, rest, opq =>
    if st.dangles && P'.elim == P then
      let L' := src.lenU SQ.elim
      let L := st.lenU P
      -- selectOnSaveEmptyIndexStruct, branches 2 and 3
      key{ if(‹isT key{ (L'; L) }›) then
          (if(L' = L) then ‹st.slotU P rest opq›
           else if(L' < L) then ‹delLeaf (st.readU ((P.at L').addSegs rest)) (P.at L')
             (fun sh q => st.mapU sh q) (if rest.isEmpty then .eq else .below rest)› else opq)
        else opq }
    else opq
  | key{ stale(push, st, P', w) }, P, rest, opq =>
    (cmpSegs P'.elim.segs (P.at (st.lenU P)).segs).toTerm
      (slotLeaf key{ orElse(if(‹headKey rest› = ‹st.slotLenU P [] .err›)
          then ‹wordAtKey w.elim rest› else opq, opq) } opq opq)
  | .init, _, _, opq | .save .., _, _, opq | .arr .push .., _, _, opq
  | .arr (.slot _) .., _, _, opq | .stale (some (.pop _)) .., _, _, opq
  | .stale (some (.slot _)) .., _, _, opq | .view .., _, _, opq => opq
termination_by structural s => s

/-- Whether the slot a `push()` of a struct or an array takes has the
location `rest`, the array at `P` in `s` (`slotU`'s guard): after a `pop` at
`P`, what the popped element has; through a stale write, what it had,
nothing below the written word.  Elsewhere `opq`. -/
def LStor.slotHasU : LStor → LPath → List SSeg → LTerm → LTerm
  | key{ arr(pop(keep), st, P', _) }, P, rest, opq =>
    if P'.elim == P then
      if keep then st.hasU ((P.at (lenPred (st.lenU P))).addSegs rest)
      else delHas (st.hasU ((P.at (lenPred (st.lenU P))).addSegs rest)) (P.at (lenPred (st.lenU P)))
        (fun sh q => st.mapU sh q) (if rest.isEmpty then .eq else .below rest)
    else opq
  | key{ staleSave(st, P', _) }, P, rest, opq =>
    (cmpSegs P'.elim.segs ((P.at (st.lenU P)).addSegs rest).segs).toTerm
      (staleHas (st.slotHasU P rest opq))
  | .init, _, _, opq | .save .., _, _, opq | .delAt .., _, _, opq | .arr .push .., _, _, opq
  | .arr (.slot _) .., _, _, opq | .stale (some _) .., _, _, opq | .copy .., _, _, opq
  | .view .., _, _, opq => opq
termination_by structural s => s

/-- The length the slot a `push()` of an array takes has at `rest`, the
array at `P` in `s` (`slotU`'s length, `arrLength`'s slot): after a `pop` at
`P`, the popped element's, cleared (as below a `delete`) or kept; through a
write through a dangling alias apart from the slot, the old one; through a
`push` through one at the slot, one more.  Elsewhere `opq`.  Only sound
(`LStor.slotLenU_sound`): its users keep `opq` beside it or need no more. -/
def LStor.slotLenU : LStor → LPath → List SSeg → LTerm → LTerm
  | key{ arr(pop(keep), st, P', _) }, P, rest, opq =>
    if P'.elim == P then
      if keep then st.lenU ((P.at (lenPred (st.lenU P))).addSegs rest)
      else delLen (st.lenU ((P.at (lenPred (st.lenU P))).addSegs rest))
        (lenEnd (st.lenU ((P.at (lenPred (st.lenU P))).addSegs rest))
          (st.mapU .fixed ((P.at (lenPred (st.lenU P))).addSegs rest)))
        (P.at (lenPred (st.lenU P))) (fun sh q => st.mapU sh q)
        (if rest.isEmpty then .eq else .below rest)
    else opq
  | key{ staleSave(st, P', _) }, P, rest, opq =>
    (cmpSegs P'.elim.segs (P.at (st.lenU P)).segs).toTerm
      (slotLeaf opq (st.slotLenU P rest opq) opq)
  | key{ stale(push, st, P', _) }, P, rest, opq =>
    (cmpSegs P'.elim.segs (P.at (st.lenU P)).segs).toTerm
      (slotLeaf (if rest.isEmpty then lenSucc (st.slotLenU P rest .err) else opq) opq opq)
  | .init, _, _, opq | .save .., _, _, opq | .delAt .., _, _, opq | .arr .push .., _, _, opq
  | .arr (.slot _) .., _, _, opq | .stale (some (.pop _)) .., _, _, opq
  | .stale (some (.slot _)) .., _, _, opq | .copy .., _, _, opq | .view .., _, _, opq => opq
termination_by structural s => s

/-- Whether `Q` names a location of `s`, where `s` and `Q` return. -/
def LStor.hasU : LStor → LPath → LTerm
  | key{ storage }, Q => key{ has(storage, Q) }
  -- Lean only: a write leaves its path and every location above it (saveHas)
  | key{ save(st, P, _) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm (saveHas (st.hasU Q))
  | key{ delAt(st, P) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (delHas (st.hasU Q) P.elim fun sh q => st.mapU sh q)
  | key{ arr(op, st, P, w) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (arrHas op (st.lenU P.elim) (st.hasU Q) key{ has(arr(op, st, P, w), Q) })
  | key{ staleSave(st, P, _) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm (staleHas (st.hasU Q))
  | key{ stale(op, st, P, w) }, Q => key{ has(stale(op, st, P, w), Q) }
  | key{ save(st, P, find(src, SQ)) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (copyLeaf key{ true } key{ true } (st.hasU Q) key{ has(save(st, P, find(src, SQ)), Q) }
        (fun pre => src.mapU .map (SQ.elim.addSegs pre)) fun rest => src.hasU (SQ.elim.addSegs rest))
  -- selectOnCopyMemRef: the memory's name and slot through the view
  | key{ copyMem(mtSt, m, i) }, Q =>
    match viewPath Q with
    | some (p, a) =>
      match m.walk i p with
      | some j =>
        match m.readU j a, (m.readI j a).bind fun j' => m.objU false j' with
        | some W, some N => key{ orElse((W; true), (N; true)) }
        | _, _ => key{ has(copyMem(mtSt, m, i), Q) }
      | none => key{ has(copyMem(mtSt, m, i), Q) }
    | none => if isViewRoot Q then key{ true } else key{ has(copyMem(mtSt, m, i), Q) }
termination_by structural s => s

/-- The length of the array at `Q` in `s`, where `s` and `Q` return: a
write keeps the length of every array above it, as it keeps its shape. -/
def LStor.lenU : LStor → LPath → LTerm
  | key{ storage }, Q => key{ find(storage, Q.length) }
  -- selectOnSaveCons on size: a write keeps the length of every array above it
  | key{ save(st, P, _) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm (saveMap (st.lenU Q))
  -- selectOnDelAtCons; selectStDelNodeFixedSize, selectStDelNodeDefault at the path (lenEnd)
  | key{ delAt(st, P) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (delLen (st.lenU Q) (lenEnd (st.lenU Q) (st.mapU .fixed Q)) P.elim fun sh q => st.mapU sh q)
  -- the size a push or a pop writes (arrLength); findDefinitionSize below a recycled slot
  | key{ arr(op, st, P, w) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (arrLength op (st.lenU P.elim) (st.lenU Q) key{ find(arr(op, st, P, w), Q.length) }
        (if st.dangles then some fun rest =>
          key{ orElse(‹st.slotLenU P.elim rest .err›, find(arr(op, st, P, w), Q.length)) }
          else none))
  | key{ staleSave(st, P, _) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm (saveMap (st.lenU Q))
  | key{ stale(op, st, P, w) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (arrLength op (st.lenU P.elim) (st.lenU Q) key{ find(stale(op, st, P, w), Q.length) } none)
  | key{ save(st, P, find(src, SQ)) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (copyLeaf (src.lenU SQ.elim) (st.lenU Q) (st.lenU Q)
        key{ find(save(st, P, find(src, SQ)), Q.length) }
        (fun pre => src.mapU .map (SQ.elim.addSegs pre)) fun rest => src.lenU (SQ.elim.addSegs rest))
  -- selectOnCopyMemPrim on size
  | key{ copyMem(mtSt, m, i) }, Q =>
    match viewObj Q with
    | some p =>
      match m.walk i p with
      | some j => (m.readU j key{ size }).getD key{ find(copyMem(mtSt, m, i), Q.length) }
      | none => key{ find(copyMem(mtSt, m, i), Q.length) }
    | none => key{ find(copyMem(mtSt, m, i), Q.length) }
termination_by structural s => s

/-- Whether `Q` names a mapping (`sh = .map`) or a fixed-size array
(`.fixed`) of `s`, where `s` and `Q` return. -/
def LStor.mapU (sh : KShape) : LStor → LPath → LTerm
  | key{ storage }, Q => key{ kmap(sh, storage, Q) }
  -- Lean only (KeY reads the shape off the field's sort): a write keeps every shape above it
  | key{ save(st, P, _) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm (saveMap (st.mapU sh Q))
  | key{ delAt(st, P) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (delMap (st.mapU sh Q) P.elim fun sh' q => st.mapU sh' q)
  | key{ arr(op, st, P, w) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (arrMap op (st.lenU P.elim) (st.mapU sh Q) key{ kmap(sh, arr(op, st, P, w), Q) })
  | key{ staleSave(st, P, _) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm (saveMap (st.mapU sh Q))
  | key{ stale(op, st, P, w) }, Q => key{ kmap(sh, stale(op, st, P, w), Q) }
  | key{ save(st, P, find(src, SQ)) }, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (copyLeaf (src.mapU sh SQ.elim) (st.mapU sh Q) (st.mapU sh Q)
        key{ kmap(sh, save(st, P, find(src, SQ)), Q) }
        (fun pre => src.mapU .map (SQ.elim.addSegs pre)) fun rest => src.mapU sh (SQ.elim.addSegs rest))
  | key{ copyMem(mtSt, m, i) }, Q =>
    match sh with
    | .map => key{ err }                        -- Lean only: memory holds no mapping
    | .fixed => key{ kmap(sh, copyMem(mtSt, m, i), Q) }
termination_by structural s => s

/-- Whether the subtree at `Q` of `s` copies into memory, where `s` and `Q`
return (Lean only: `copyStToM` halts on a mapping).  A word written over a
word keeps the shape, so the test passes the write (`save_cpok_sim`); it
reaches `cpok init Q` for the closer's `wt` clause.  Any other write keeps
the test whole. -/
def LStor.cpokU : LStor → LPath → LTerm
  | key{ storage }, Q => key{ copyOk(storage, Q) }
  | key{ save(st, P, w) }, Q =>
    key{ if(‹isT (st.readU P.elim)›) then ‹st.cpokU Q› else copyOk(save(st, P, w), Q) }
  | s@(.delAt ..), Q | s@(.arr ..), Q | s@(.stale ..), Q | s@(.copy ..), Q | s@(.view ..), Q =>
    key{ copyOk(s, Q) }
termination_by structural s => s

/-- The index a selector writes at, its reads eliminated. -/
def LSel.idxU : LSel → LTerm
  | key{ at(w) } => w.elim
  | .fld _ | key{ size } => key{ err }
termination_by structural a => a

/-- A word written to memory, its reads eliminated; a reference is no word. -/
def LMV.wordU : LMV → LTerm
  | .word t => t.elim
  | .ref _ => .err
termination_by structural v => v

/-- **`LMem.readT` in the elimination** (`readOnWrite`, `readOnAddM`,
`readFromCopyToStorage`): the same walk, the words written and the storage a
copy read eliminated. -/
def LMem.readU : LMem → LId → LSel → Option LTerm
  -- readFromEmptyMemory: refused
  | key{ memory }, _, _ => none
  -- readOnAddM: \if(idp1 = idp2) \then init(idC(idp2, flds), a2) \else read(mem, id2, a2)
  | key{ addM(mem, shaped(idp1, R)) }, id2, a2 =>
    if id2.root = idp1 then some (dfltSel ((Ty.ref R).memberTy id2.path) a2) else mem.readU id2 a2
  -- memoryArrayFreshAlloc
  | key{ write(addM(mem, shaped(idp1, R)), idC(idp1, nil), size, n) }, id2, a2 =>
    if id2.root = idp1 then some (newSel R n.elim id2.path a2) else mem.readU id2 a2
  -- readFromCopyToStorage: \then find(st, consr(fxs, a2)), under the storage's guards
  | key{ copySt(mem, idp1, find(st, q)) }, id2, a2 =>
    if id2.root = idp1 then
      copySelG (fun Q => key{ (‹st.okE›; (okPath(Q); ‹st.readU Q›)) })
        (fun Q => key{ (‹st.okE›; (okPath(Q); ‹st.lenU Q›)) }) q.elim id2.path a2
    else mem.readU id2 a2
  -- readOnWrite: \if(id1 = id2 & a1 = a2) \then cast(v) \else read(mem, id2, a2)
  | key{ write(mem, id1, a1, v) }, id2, a2 =>
    if id2 = id1 then
      match selRel a1 a2 with
      | .same => some v.wordU
      | .apart => mem.readU id2 a2
      -- if(r = w) then cast(v) else read(mem, id2, a2), `a1` = at(w)
      | .key r _ => (mem.readU id2 a2).map (.kite r a1.idxU v.wordU)
    else mem.readU id2 a2
termination_by structural m => m

/-- `LMem.nameG` (`str = false`) and `LMem.structG` (`true`) in the
elimination. -/
def LMem.objU (str : Bool) : LMem → LId → Option LTerm
  | key{ memory }, _ => none
  | key{ addM(mem, shaped(idp1, R)) }, id2 =>
    if id2.root = idp1 then
      some (if str then dfltStruct ((Ty.ref R).memberTy id2.path)
        else dfltRef ((Ty.ref R).memberTy id2.path))
    else mem.objU str id2
  | key{ write(addM(mem, shaped(idp1, R)), idC(idp1, nil), size, n) }, id2 =>
    if id2.root = idp1 then some (newObj (if str then dfltStruct else dfltRef) R n.elim id2.path)
    else mem.objU str id2
  -- readFromCopyToStorageIdentity: there where the storage holds no word
  | key{ copySt(mem, idp1, find(st, q)) }, id2 =>
    if id2.root = idp1 then
      if noLen id2.path then
        let Q := q.elim.ext id2.path
        let H : LTerm := key{ if(‹isT (st.readU Q)›) then err else ‹st.hasU Q› }
        some key{ (‹st.okE›; (okPath(Q);
          ‹if str then key{ if(‹isT (st.lenU Q)›) then err else H } else H›)) }
      else none
    else mem.objU str id2
  -- newFromWrite: a write allocates nothing
  | key{ write(mem, _, _, _) }, id2 => mem.objU str id2
termination_by structural m => m

/-- **The run guard of a memory** (Lean only): it returns exactly where the
run does.  An allocation at its ordinal, of a type `allocOk` admits (a
`new T[](n)` with an integer `n`); a copy from storage of a subtree that
copies and is no word; a write whose slot and value pass `writeG`'s and
`nameG`'s tests.  The guards' reads are the elimination's. -/
def LMem.okU : LMem → Option LTerm
  | key{ memory } => some key{ true }
  | key{ addM(mem, shaped(idp1, R)) } =>
    if idp1 = mem.nAlloc ∧ allocOk R = true then mem.okU else none
  | key{ write(addM(mem, shaped(idp1, R)), idC(idp1, nil), size, n) } =>
    if idp1 = mem.nAlloc ∧ allocOk R = true then mem.okU.map fun G => key{ (G; ‹isIntL n.elim›) }
    else none
  | key{ copySt(mem, idp1, find(st, q)) } =>
    if idp1 = mem.nAlloc then
      let Q := q.elim
      mem.okU.map fun G => key{ (G; (‹st.okE›; (okPath(Q); (‹st.cpokU Q›;
        if(‹isT (st.readU Q)›) then err else true)))) }
    else none
  | key{ write(mem, id1, a1, v) } =>
    okWrite mem.okU
      (fun _ => wrGuard (fun _ => mem.objU true id1) (fun _ => mem.readU id1 key{ size })
        a1.idxU a1)
      fun _ => valGuard key{ (‹v.wordU›; true) }
        (fun _ => v.refId?.bind fun j' => mem.objU false j') v
termination_by structural m => m

end

/-! ### The elimination as compiled code

The elimination's `.arr` cases pass the old length and the old value to
their leaf as strict arguments: two recursive calls on the same storage, so
compiled code (`Derive.leafFits`, run through `evalExpr`, which heeds no
heartbeats) does `2^k` calls for `k` operations on arrays where the term it
builds is small; twelve pushes alternating between two arrays took 106 s.
The `F` copies below differ only there (`CaseTree.toTermLazy`): a leaf
computes what it reads, 7 ms on the same leaf.  `@[csimp]` makes compiled
code run them; the kernel and every proof see the definitions above. -/

/-- The relations at which an operation on an array reads the old length
(`arrKey`'s `L`). -/
def PathRel.needsLen : PathRel → Bool
  | .eq | .below _ => true
  | .above | .diverge => false

/-- The relations at which the leaf of an operation on an array reads the
old value: all but the array itself. -/
def PathRel.needsOld : PathRel → Bool
  | .eq => false
  | .above | .below _ | .diverge => true

/-- `t.toTerm (f L old)`, where a tree that is one leaf `r` computes `L`
and `old` only where `r` reads them (`needsLen`, `nO`): compiled code
evaluates arguments strictly, and the two are recursive calls on the same
storage. -/
@[inline] def CaseTree.toTermLazy (nO : PathRel → Bool) (t : CaseTree PathRel)
    (L old : Unit → LTerm) (f : LTerm → LTerm → PathRel → LTerm) : LTerm :=
  match t with
  | .leaf r => f (if r.needsLen then L () else .err) (if nO r then old () else .err) r
  | t => t.toTerm (f (L ()) (old ()))

/-- The lazy tree is the tree, where the leaf function ignores what it
is not given. -/
theorem CaseTree.toTermLazy_eq (nO : PathRel → Bool) (t : CaseTree PathRel) (L old : LTerm)
    (f : LTerm → LTerm → PathRel → LTerm)
    (hf : ∀ r, f (if r.needsLen then L else .err) (if nO r then old else .err) r = f L old r) :
    t.toTermLazy nO (fun _ => L) (fun _ => old) f = t.toTerm (f L old) := by
  cases t with
  | leaf r => exact hf r
  | ite => rfl

/-- `CaseTree.toTermLazy` with the first argument's gate given too (`nL`),
for a leaf that reads less than an operation on an array (`staleRead`). -/
@[inline] def CaseTree.toTermLazyBy (nL nO : PathRel → Bool) (t : CaseTree PathRel)
    (L old : Unit → LTerm) (f : LTerm → LTerm → PathRel → LTerm) : LTerm :=
  match t with
  | .leaf r => f (if nL r then L () else .err) (if nO r then old () else .err) r
  | t => t.toTerm (f (L ()) (old ()))

theorem CaseTree.toTermLazyBy_eq (nL nO : PathRel → Bool) (t : CaseTree PathRel)
    (L old : LTerm) (f : LTerm → LTerm → PathRel → LTerm)
    (hf : ∀ r, f (if nL r then L else .err) (if nO r then old else .err) r = f L old r) :
    t.toTermLazyBy nL nO (fun _ => L) (fun _ => old) f = t.toTerm (f L old) := by
  cases t with
  | leaf r => exact hf r
  | ite => rfl

mutual

/-- `LTerm.elim` as compiled code runs it (`LTerm.elim_csimp`). -/
def LTerm.elimF : LTerm → LTerm
  | key{ lit(v) } => key{ lit(v) }
  | key{ var(x) } => key{ var(x) }
  | key{ binop(op, p, a, b) } => .binop op p a.elimF b.elimF
  | key{ unop(op, p, a) } => .unop op p a.elimF
  | key{ if(c) then a else b } => .ite c.elimF a.elimF b.elimF
  | key{ find(st, q) } => .seq st.okEF (.seq (.pok q.elimF) (st.readUF q.elimF))
  | key{ has(st, q) } => .seq st.okEF (.seq (.pok q.elimF) (st.hasUF q.elimF))
  | key{ kmap(sh, st, q) } => .seq st.okEF (.seq (.pok q.elimF) (st.mapUF sh q.elimF))
  | key{ find(st, q.length) } => .seq st.okEF (.seq (.pok q.elimF) (st.lenUF q.elimF))
  | key{ okSt(st) } => st.okEF
  | key{ okPath(q) } => .pok q.elimF
  | key{ (d; a) } => .seq d.elimF a.elimF
  | key{ orElse(a, b) } => .orElse a.elimF b.elimF
  | key{ if(a = b) then t else e } => .kite a.elimF b.elimF t.elimF e.elimF
  | key{ delValue(a) } => .zero a.elimF
  | key{ err } => key{ err }
  | key{ env(k) } => key{ env(k) }
  | key{ findP(st, q) } => .findP st q.elimF
  | key{ copyOk(st, q) } => .seq st.okEF (.seq (.pok q.elimF) (st.cpokUF q.elimF))
termination_by structural t => t

/-- `LPath.elim` as compiled code runs it. -/
def LPath.elimF : LPath → LPath
  | .root r => .root r
  | key{ q.f } => .field q.elimF f
  | key{ q[k] } => .at q.elimF k.elimF
termination_by structural q => q

/-- `LStor.okE` as compiled code runs it. -/
def LStor.okEF : LStor → LTerm
  | key{ storage } => key{ true }
  | key{ save(st, q, w) } =>
    if q.noLen then .seq st.okEF (.seq w.elimF (.seq (.pok q.elimF) (st.hasUF q.elimF)))
    else key{ ok(save(st, q, w)) }
  | key{ delAt(st, q) } =>
    if q.noLen then .seq st.okEF (.seq (.pok q.elimF) (st.hasUF q.elimF))
    else key{ ok(delAt(st, q)) }
  | key{ arr(op, st, q, w) } =>
    if q.noLen then .seq st.okEF (.seq w.elimF (.seq (.pok q.elimF) (arrOk op (st.lenUF q.elimF))))
    else key{ ok(arr(op, st, q, w)) }
  | key{ staleSave(st, q, w) } =>
    if q.noLen then
      let Q := q.elimF
      .seq st.okEF (.seq w.elimF (.seq (.pok Q)
        (staleOk (st.hasUF Q) (match Q.splitLast with
          | some (A, k, rest) => some (k, st.lenUF A, st.slotHasUF A rest .err)
          | none => none) key{ ok(staleSave(st, q, w)) })))
    else key{ ok(staleSave(st, q, w)) }
  | key{ stale(op, st, q, w) } =>
    if q.noLen then
      let Q := q.elimF
      .seq st.okEF (.seq w.elimF (.seq (.pok Q)
        (staleOk (arrOk op (st.lenUF Q)) (match Q.splitLast with
          | some (A, k, rest) => some (k, st.lenUF A, arrOk op (st.slotLenUF A rest .err))
          | none => none) key{ ok(stale(op, st, q, w)) })))
    else key{ ok(stale(op, st, q, w)) }
  | key{ save(st, q, find(src, sq)) } =>
    if q.noLen then
      if st.dangles && src == st then .seq st.okEF (.seq (.pok sq.elimF) (.seq (st.hasUF sq.elimF)
        (.seq (.pok q.elimF) (st.hasUF q.elimF))))
      else .seq src.okEF (.seq (.pok sq.elimF) (.seq (src.hasUF sq.elimF)
        (.seq st.okEF (.seq (.pok q.elimF) (st.hasUF q.elimF)))))
    else key{ ok(save(st, q, find(src, sq))) }
  | key{ copyMem(mtSt, m, i) } =>
    if m.refDesc then okView m.okUF (m.objUF false i) key{ ok(copyMem(mtSt, m, i)) }
    else key{ ok(copyMem(mtSt, m, i)) }
termination_by structural s => s

/-- `LStor.readU` as compiled code runs it: an operation on an array reads
the old length and value only where the relation needs them. -/
def LStor.readUF : LStor → LPath → LTerm
  | key{ storage }, Q => key{ find(storage, Q) }
  | key{ save(st, P, w) }, Q => (cmpSegs P.elimF.segs Q.segs).toTerm (saveLeaf w.elimF (st.readUF Q))
  | key{ delAt(st, P) }, Q => (cmpSegs P.elimF.segs Q.segs).toTerm
      (delLeaf (st.readUF Q) P.elimF fun sh q => st.mapUF sh q)
  | key{ arr(op, st, P, w) }, Q =>
    let Pe := P.elimF
    (cmpSegs Pe.segs Q.segs).toTermLazy PathRel.needsOld (fun _ => st.lenUF Pe) (fun _ => st.readUF Q)
      fun L old => arrRead op w.elimF L old key{ find(arr(op, st, P, w), Q) }
        fun rest => st.slotUF Pe rest key{ find(arr(op, st, P, w), Q) }
  | key{ staleSave(st, P, w) }, Q => (cmpSegs P.elimF.segs Q.segs).toTermLazyBy (· matches .eq)
      (· matches .diverge) (fun _ => st.hasUF Q) (fun _ => st.readUF Q)
      fun H old => staleRead w.elimF H old
  | key{ stale(op, st, P, w) }, Q => key{ find(stale(op, st, P, w), Q) }
  | key{ save(st, P, find(src, SQ)) }, Q => (cmpSegs P.elimF.segs Q.segs).toTerm
      (copyLeaf (src.readUF SQ.elimF) key{ err } (st.readUF Q)
        key{ find(save(st, P, find(src, SQ)), Q) }
        (fun pre => src.mapUF .map (SQ.elimF.addSegs pre))
        fun rest => src.readUF (SQ.elimF.addSegs rest))
  | key{ copyMem(mtSt, m, i) }, Q =>
    match viewPath Q with
    | some (p, a) =>
      match m.walk i p with
      | some j => (m.readUF j a).getD key{ find(copyMem(mtSt, m, i), Q) }
      | none => key{ find(copyMem(mtSt, m, i), Q) }
    | none => key{ find(copyMem(mtSt, m, i), Q) }
termination_by structural s => s

/-- `LStor.slotU` as compiled code runs it. -/
def LStor.slotUF : LStor → LPath → List SSeg → LTerm → LTerm
  -- storagePopSave's delAt(at(n - 1)), then selectOnDelAtCons, delFieldIndexStruct
  | key{ arr(pop(keep), st, P', _) }, P, rest, opq =>
    if P'.elimF == P then
      if keep then st.readUF ((P.at (lenPred (st.lenUF P))).addSegs rest)
      else delLeaf (st.readUF ((P.at (lenPred (st.lenUF P))).addSegs rest))
        (P.at (lenPred (st.lenUF P)))
        (fun sh q => st.mapUF sh q) (if rest.isEmpty then .eq else .below rest)
    else opq
  -- selectStDelNodeIndexStruct: the old first element, cleared; past the end, the slot
  | key{ delAt(st, P') }, P, rest, opq =>
    if P'.elimF == P then
      key{ if(‹isT (st.mapUF .fixed P)›) then opq
        else if(‹st.lenUF P› = 0) then ‹if st.dangles then st.slotUF P rest opq else opq›
        else ‹delLeaf (st.readUF ((P.at key{ 0 }).addSegs rest)) (P.at key{ 0 })
          (fun sh q => st.mapUF sh q) (if rest.isEmpty then .eq else .below rest)› }
    else opq
  | key{ staleSave(st, P', w) }, P, rest, opq =>
    let L := st.lenUF P
    (cmpSegs P'.elimF.segs ((P.at L).addSegs rest).segs).toTerm
      (saveLeaf (if rest.any SSeg.isKey then opq else w.elimF) (st.slotUF P rest opq))
  -- a copy over the array, where the storage holds a stale write
  | key{ save(st, P', find(src, SQ)) }, P, rest, opq =>
    if st.dangles && P'.elimF == P then
      let L' := src.lenUF SQ.elimF
      let L := st.lenUF P
      -- selectOnSaveEmptyIndexStruct, branches 2 and 3
      key{ if(‹isT key{ (L'; L) }›) then
          (if(L' = L) then ‹st.slotUF P rest opq›
           else if(L' < L) then ‹delLeaf (st.readUF ((P.at L').addSegs rest)) (P.at L')
             (fun sh q => st.mapUF sh q) (if rest.isEmpty then .eq else .below rest)› else opq)
        else opq }
    else opq
  | key{ stale(push, st, P', w) }, P, rest, opq =>
    (cmpSegs P'.elimF.segs (P.at (st.lenUF P)).segs).toTerm
      (slotLeaf key{ orElse(if(‹headKey rest› = ‹st.slotLenUF P [] .err›)
          then ‹wordAtKey w.elimF rest› else opq, opq) } opq opq)
  | .init, _, _, opq | .save .., _, _, opq | .arr .push .., _, _, opq
  | .arr (.slot _) .., _, _, opq | .stale (some (.pop _)) .., _, _, opq
  | .stale (some (.slot _)) .., _, _, opq | .view .., _, _, opq => opq
termination_by structural s => s

/-- `LStor.slotHasU` as compiled code runs it. -/
def LStor.slotHasUF : LStor → LPath → List SSeg → LTerm → LTerm
  | key{ arr(pop(keep), st, P', _) }, P, rest, opq =>
    if P'.elimF == P then
      let E := P.at (lenPred (st.lenUF P))
      if keep then st.hasUF (E.addSegs rest)
      else delHas (st.hasUF (E.addSegs rest)) E
        (fun sh q => st.mapUF sh q) (if rest.isEmpty then .eq else .below rest)
    else opq
  | key{ staleSave(st, P', _) }, P, rest, opq =>
    let L := st.lenUF P
    (cmpSegs P'.elimF.segs ((P.at L).addSegs rest).segs).toTerm
      (staleHas (st.slotHasUF P rest opq))
  | .init, _, _, opq | .save .., _, _, opq | .delAt .., _, _, opq | .arr .push .., _, _, opq
  | .arr (.slot _) .., _, _, opq | .stale (some _) .., _, _, opq | .copy .., _, _, opq
  | .view .., _, _, opq => opq
termination_by structural s => s

/-- `LStor.slotLenU` as compiled code runs it. -/
def LStor.slotLenUF : LStor → LPath → List SSeg → LTerm → LTerm
  | key{ arr(pop(keep), st, P', _) }, P, rest, opq =>
    if P'.elimF == P then
      let E := P.at (lenPred (st.lenUF P))
      let Q := E.addSegs rest
      if keep then st.lenUF Q
      else
        let LQ := st.lenUF Q
        delLen LQ (lenEnd LQ (st.mapUF .fixed Q)) E (fun sh q => st.mapUF sh q)
          (if rest.isEmpty then .eq else .below rest)
    else opq
  | key{ staleSave(st, P', _) }, P, rest, opq =>
    let L := st.lenUF P
    (cmpSegs P'.elimF.segs (P.at L).segs).toTerm
      (slotLeaf opq (st.slotLenUF P rest opq) opq)
  | key{ stale(push, st, P', _) }, P, rest, opq =>
    let L := st.lenUF P
    (cmpSegs P'.elimF.segs (P.at L).segs).toTerm
      (slotLeaf (if rest.isEmpty then lenSucc (st.slotLenUF P rest .err) else opq) opq opq)
  | .init, _, _, opq | .save .., _, _, opq | .delAt .., _, _, opq | .arr .push .., _, _, opq
  | .arr (.slot _) .., _, _, opq | .stale (some (.pop _)) .., _, _, opq
  | .stale (some (.slot _)) .., _, _, opq | .copy .., _, _, opq | .view .., _, _, opq => opq
termination_by structural s => s

/-- `LStor.hasU` as compiled code runs it. -/
def LStor.hasUF : LStor → LPath → LTerm
  | key{ storage }, Q => key{ has(storage, Q) }
  | key{ save(st, P, _) }, Q => (cmpSegs P.elimF.segs Q.segs).toTerm (saveHas (st.hasUF Q))
  | key{ delAt(st, P) }, Q => (cmpSegs P.elimF.segs Q.segs).toTerm
      (delHas (st.hasUF Q) P.elimF fun sh q => st.mapUF sh q)
  | key{ arr(op, st, P, w) }, Q =>
    let Pe := P.elimF
    (cmpSegs Pe.segs Q.segs).toTermLazy PathRel.needsOld (fun _ => st.lenUF Pe) (fun _ => st.hasUF Q)
      fun L old => arrHas op L old key{ has(arr(op, st, P, w), Q) }
  | key{ staleSave(st, P, _) }, Q => (cmpSegs P.elimF.segs Q.segs).toTerm (staleHas (st.hasUF Q))
  | key{ stale(op, st, P, w) }, Q => key{ has(stale(op, st, P, w), Q) }
  | key{ save(st, P, find(src, SQ)) }, Q => (cmpSegs P.elimF.segs Q.segs).toTerm
      (copyLeaf key{ true } key{ true } (st.hasUF Q) key{ has(save(st, P, find(src, SQ)), Q) }
        (fun pre => src.mapUF .map (SQ.elimF.addSegs pre))
        fun rest => src.hasUF (SQ.elimF.addSegs rest))
  | key{ copyMem(mtSt, m, i) }, Q =>
    match viewPath Q with
    | some (p, a) =>
      match m.walk i p with
      | some j =>
        match m.readUF j a, (m.readI j a).bind fun j' => m.objUF false j' with
        | some W, some N => key{ orElse((W; true), (N; true)) }
        | _, _ => key{ has(copyMem(mtSt, m, i), Q) }
      | none => key{ has(copyMem(mtSt, m, i), Q) }
    | none => if isViewRoot Q then key{ true } else key{ has(copyMem(mtSt, m, i), Q) }
termination_by structural s => s

/-- `LStor.lenU` as compiled code runs it. -/
def LStor.lenUF : LStor → LPath → LTerm
  | key{ storage }, Q => key{ find(storage, Q.length) }
  | key{ save(st, P, _) }, Q => (cmpSegs P.elimF.segs Q.segs).toTerm (saveMap (st.lenUF Q))
  | key{ delAt(st, P) }, Q => (cmpSegs P.elimF.segs Q.segs).toTerm
      (delLen (st.lenUF Q) (lenEnd (st.lenUF Q) (st.mapUF .fixed Q)) P.elimF fun sh q => st.mapUF sh q)
  | key{ arr(op, st, P, w) }, Q =>
    let Pe := P.elimF
    (cmpSegs Pe.segs Q.segs).toTermLazy PathRel.needsOld (fun _ => st.lenUF Pe) (fun _ => st.lenUF Q)
      fun L old => arrLength op L old key{ find(arr(op, st, P, w), Q.length) }
        (op.gateSlot (if st.dangles then some fun rest =>
          key{ orElse(‹st.slotLenUF Pe rest .err›, find(arr(op, st, P, w), Q.length)) }
          else none))
  | key{ staleSave(st, P, _) }, Q => (cmpSegs P.elimF.segs Q.segs).toTerm (saveMap (st.lenUF Q))
  | key{ stale(op, st, P, w) }, Q =>
    let Pe := P.elimF
    (cmpSegs Pe.segs Q.segs).toTermLazy PathRel.needsOld (fun _ => st.lenUF Pe) (fun _ => st.lenUF Q)
      fun L old => arrLength op L old key{ find(stale(op, st, P, w), Q.length) } none
  | key{ save(st, P, find(src, SQ)) }, Q => (cmpSegs P.elimF.segs Q.segs).toTerm
      (copyLeaf (src.lenUF SQ.elimF) (st.lenUF Q) (st.lenUF Q)
        key{ find(save(st, P, find(src, SQ)), Q.length) }
        (fun pre => src.mapUF .map (SQ.elimF.addSegs pre))
        fun rest => src.lenUF (SQ.elimF.addSegs rest))
  | key{ copyMem(mtSt, m, i) }, Q =>
    match viewObj Q with
    | some p =>
      match m.walk i p with
      | some j => (m.readUF j key{ size }).getD key{ find(copyMem(mtSt, m, i), Q.length) }
      | none => key{ find(copyMem(mtSt, m, i), Q.length) }
    | none => key{ find(copyMem(mtSt, m, i), Q.length) }
termination_by structural s => s

/-- `LStor.mapU` as compiled code runs it. -/
def LStor.mapUF (sh : KShape) : LStor → LPath → LTerm
  | key{ storage }, Q => key{ kmap(sh, storage, Q) }
  | key{ save(st, P, _) }, Q => (cmpSegs P.elimF.segs Q.segs).toTerm (saveMap (st.mapUF sh Q))
  | key{ delAt(st, P) }, Q => (cmpSegs P.elimF.segs Q.segs).toTerm
      (delMap (st.mapUF sh Q) P.elimF fun sh' q => st.mapUF sh' q)
  | key{ arr(op, st, P, w) }, Q =>
    let Pe := P.elimF
    (cmpSegs Pe.segs Q.segs).toTermLazy (fun _ => true) (fun _ => st.lenUF Pe)
      (fun _ => st.mapUF sh Q)
      fun L old => arrMap op L old key{ kmap(sh, arr(op, st, P, w), Q) }
  | key{ staleSave(st, P, _) }, Q => (cmpSegs P.elimF.segs Q.segs).toTerm (saveMap (st.mapUF sh Q))
  | key{ stale(op, st, P, w) }, Q => key{ kmap(sh, stale(op, st, P, w), Q) }
  | key{ save(st, P, find(src, SQ)) }, Q => (cmpSegs P.elimF.segs Q.segs).toTerm
      (copyLeaf (src.mapUF sh SQ.elimF) (st.mapUF sh Q) (st.mapUF sh Q)
        key{ kmap(sh, save(st, P, find(src, SQ)), Q) }
        (fun pre => src.mapUF .map (SQ.elimF.addSegs pre))
        fun rest => src.mapUF sh (SQ.elimF.addSegs rest))
  | key{ copyMem(mtSt, m, i) }, Q =>
    match sh with
    | .map => key{ err }
    | .fixed => key{ kmap(sh, copyMem(mtSt, m, i), Q) }
termination_by structural s => s

/-- `LStor.cpokU` as compiled code runs it. -/
def LStor.cpokUF : LStor → LPath → LTerm
  | key{ storage }, Q => key{ copyOk(storage, Q) }
  | key{ save(st, P, w) }, Q =>
    key{ if(‹isT (st.readUF P.elimF)›) then ‹st.cpokUF Q› else copyOk(save(st, P, w), Q) }
  | s@(.delAt ..), Q | s@(.arr ..), Q | s@(.stale ..), Q | s@(.copy ..), Q | s@(.view ..), Q =>
    key{ copyOk(s, Q) }
termination_by structural s => s

/-- `LSel.idxU` as compiled code runs it. -/
def LSel.idxUF : LSel → LTerm
  | key{ at(w) } => w.elimF
  | .fld _ | key{ size } => key{ err }
termination_by structural a => a

/-- `LMV.wordU` as compiled code runs it. -/
def LMV.wordUF : LMV → LTerm
  | .word t => t.elimF
  | .ref _ => .err
termination_by structural v => v

/-- `LMem.readU` as compiled code runs it. -/
def LMem.readUF : LMem → LId → LSel → Option LTerm
  -- readFromEmptyMemory: refused
  | key{ memory }, _, _ => none
  -- readOnAddM: \if(idp1 = idp2) \then init(idC(idp2, flds), a2) \else read(mem, id2, a2)
  | key{ addM(mem, shaped(idp1, R)) }, id2, a2 =>
    if id2.root = idp1 then some (dfltSel ((Ty.ref R).memberTy id2.path) a2) else mem.readUF id2 a2
  -- memoryArrayFreshAlloc
  | key{ write(addM(mem, shaped(idp1, R)), idC(idp1, nil), size, n) }, id2, a2 =>
    if id2.root = idp1 then some (newSel R n.elimF id2.path a2) else mem.readUF id2 a2
  -- readFromCopyToStorage: \then find(st, consr(fxs, a2)), under the storage's guards
  | key{ copySt(mem, idp1, find(st, q)) }, id2, a2 =>
    if id2.root = idp1 then
      copySelG (fun Q => key{ (‹st.okEF›; (okPath(Q); ‹st.readUF Q›)) })
        (fun Q => key{ (‹st.okEF›; (okPath(Q); ‹st.lenUF Q›)) }) q.elimF id2.path a2
    else mem.readUF id2 a2
  -- readOnWrite: \if(id1 = id2 & a1 = a2) \then cast(v) \else read(mem, id2, a2)
  | key{ write(mem, id1, a1, v) }, id2, a2 =>
    if id2 = id1 then
      match selRel a1 a2 with
      | .same => some v.wordUF
      | .apart => mem.readUF id2 a2
      -- if(r = w) then cast(v) else read(mem, id2, a2), `a1` = at(w)
      | .key r _ => (mem.readUF id2 a2).map (.kite r a1.idxUF v.wordUF)
    else mem.readUF id2 a2
termination_by structural m => m

/-- `LMem.objU` as compiled code runs it. -/
def LMem.objUF (str : Bool) : LMem → LId → Option LTerm
  | key{ memory }, _ => none
  | key{ addM(mem, shaped(idp1, R)) }, id2 =>
    if id2.root = idp1 then
      some (if str then dfltStruct ((Ty.ref R).memberTy id2.path)
        else dfltRef ((Ty.ref R).memberTy id2.path))
    else mem.objUF str id2
  | key{ write(addM(mem, shaped(idp1, R)), idC(idp1, nil), size, n) }, id2 =>
    if id2.root = idp1 then some (newObj (if str then dfltStruct else dfltRef) R n.elimF id2.path)
    else mem.objUF str id2
  -- readFromCopyToStorageIdentity: there where the storage holds no word
  | key{ copySt(mem, idp1, find(st, q)) }, id2 =>
    if id2.root = idp1 then
      if noLen id2.path then
        let Q := q.elimF.ext id2.path
        let H : LTerm := key{ if(‹isT (st.readUF Q)›) then err else ‹st.hasUF Q› }
        some key{ (‹st.okEF›; (okPath(Q);
          ‹if str then key{ if(‹isT (st.lenUF Q)›) then err else H } else H›)) }
      else none
    else mem.objUF str id2
  -- newFromWrite: a write allocates nothing
  | key{ write(mem, _, _, _) }, id2 => mem.objUF str id2
termination_by structural m => m

/-- `LMem.okU` as compiled code runs it. -/
def LMem.okUF : LMem → Option LTerm
  | key{ memory } => some key{ true }
  | key{ addM(mem, shaped(idp1, R)) } =>
    if idp1 = mem.nAlloc ∧ allocOk R = true then mem.okUF else none
  | key{ write(addM(mem, shaped(idp1, R)), idC(idp1, nil), size, n) } =>
    if idp1 = mem.nAlloc ∧ allocOk R = true then mem.okUF.map fun G => key{ (G; ‹isIntL n.elimF›) }
    else none
  | key{ copySt(mem, idp1, find(st, q)) } =>
    if idp1 = mem.nAlloc then
      let Q := q.elimF
      mem.okUF.map fun G => key{ (G; (‹st.okEF›; (okPath(Q); (‹st.cpokUF Q›;
        if(‹isT (st.readUF Q)›) then err else true)))) }
    else none
  | key{ write(mem, id1, a1, v) } =>
    okWrite mem.okUF
      (fun _ => wrGuard (fun _ => mem.objUF true id1) (fun _ => mem.readUF id1 key{ size })
        a1.idxUF a1)
      fun _ => valGuard key{ (‹v.wordUF›; true) }
        (fun _ => v.refId?.bind fun j' => mem.objUF false j') v
termination_by structural m => m

end

/-- `arrRead` ignores the old length and value where it does not read them. -/
theorem arrRead_lazy (op : AOp) (w L old opq : LTerm) (slot : List SSeg → LTerm) (r : PathRel) :
    arrRead op w (if r.needsLen then L else .err) (if r.needsOld then old else .err) opq slot r =
      arrRead op w L old opq slot r := by
  cases r <;> rfl

/-- `arrHas` ignores what it does not read. -/
theorem arrHas_lazy (op : AOp) (L old opq : LTerm) (r : PathRel) :
    arrHas op (if r.needsLen then L else .err) (if r.needsOld then old else .err) opq r =
      arrHas op L old opq r := by
  cases r <;> rfl

/-- `arrLength` ignores what it does not read. -/
theorem arrLength_lazy (op : AOp) (L old opq : LTerm) (slot : Option (List SSeg → LTerm))
    (r : PathRel) :
    arrLength op (if r.needsLen then L else .err) (if r.needsOld then old else .err) opq slot r =
      arrLength op L old opq slot r := by
  cases r <;> rfl

/-- `staleRead` ignores what it does not read. -/
theorem staleRead_lazy (w H old : LTerm) (r : PathRel) :
    staleRead w (if r matches .eq then H else .err) (if r matches .diverge then old else .err) r =
      staleRead w H old r := by
  cases r <;> rfl

/-- `arrLength` reads its slot only for `.slot (.ref _)`. -/
theorem arrLength_gateSlot (op : AOp) (L old opq : LTerm) (slot : Option (List SSeg → LTerm)) :
    arrLength op L old opq (op.gateSlot slot) = arrLength op L old opq slot := by
  funext r
  cases op with
  | slot E => cases E with
    | ref _ => rfl
    | _ => cases r with
      | below rest => rcases rest with _ | ⟨_ | _, _⟩ <;> first | rfl | (cases slot <;> rfl)
      | _ => rfl
  | _ => cases r with
    | below rest => rcases rest with _ | ⟨_ | _, _⟩ <;> first | rfl | (cases slot <;> rfl)
    | _ => rfl

/-- `arrMap` ignores the old length where it does not read it. -/
theorem arrMap_lazy (op : AOp) (L old opq : LTerm) (r : PathRel) :
    arrMap op (if r.needsLen then L else .err) (if true then old else .err) opq r =
      arrMap op L old opq r := by
  cases r <;> rfl

mutual

/-- The compiled elimination is the elimination. -/
theorem LTerm.elimF_eq : (t : LTerm) → t.elimF = t.elim
  | .lit _ | .var _ | .err | .env _ => rfl
  | .binop _ _ a b => by simp only [LTerm.elimF, LTerm.elim, LTerm.elimF_eq a, LTerm.elimF_eq b]
  | .unop _ _ a | .zero a => by simp only [LTerm.elimF, LTerm.elim, LTerm.elimF_eq a]
  | .ite c a b => by
    simp only [LTerm.elimF, LTerm.elim, LTerm.elimF_eq c, LTerm.elimF_eq a, LTerm.elimF_eq b]
  | .kite a b t e => by
    simp only [LTerm.elimF, LTerm.elim, LTerm.elimF_eq a, LTerm.elimF_eq b, LTerm.elimF_eq t,
      LTerm.elimF_eq e]
  | .seq a b | .orElse a b => by simp only [LTerm.elimF, LTerm.elim, LTerm.elimF_eq a,
      LTerm.elimF_eq b]
  | .find s q => by
    simp only [LTerm.elimF, LTerm.elim, LStor.okEF_eq s, LPath.elimF_eq q, LStor.readUF_eq s]
  | .has s q => by
    simp only [LTerm.elimF, LTerm.elim, LStor.okEF_eq s, LPath.elimF_eq q, LStor.hasUF_eq s]
  | .kmap sh s q => by
    simp only [LTerm.elimF, LTerm.elim, LStor.okEF_eq s, LPath.elimF_eq q, LStor.mapUF_eq sh s]
  | .len s q => by
    simp only [LTerm.elimF, LTerm.elim, LStor.okEF_eq s, LPath.elimF_eq q, LStor.lenUF_eq s]
  | .sok s => by simp only [LTerm.elimF, LTerm.elim, LStor.okEF_eq s]
  | .pok q => by simp only [LTerm.elimF, LTerm.elim, LPath.elimF_eq q]
  | .findP _ q => by simp only [LTerm.elimF, LTerm.elim, LPath.elimF_eq q]
  | .cpok s q => by
    simp only [LTerm.elimF, LTerm.elim, LStor.okEF_eq s, LPath.elimF_eq q, LStor.cpokUF_eq s]
termination_by structural t => t

theorem LPath.elimF_eq : (q : LPath) → q.elimF = q.elim
  | .root _ => rfl
  | .field q _ => by simp only [LPath.elimF, LPath.elim, LPath.elimF_eq q]
  | .at q k => by simp only [LPath.elimF, LPath.elim, LPath.elimF_eq q, LTerm.elimF_eq k]
termination_by structural q => q

theorem LStor.okEF_eq : (s : LStor) → s.okEF = s.okE
  | .init => rfl
  | .save s q w => by
    simp only [LStor.okEF, LStor.okE, LStor.okEF_eq s, LTerm.elimF_eq w, LPath.elimF_eq q,
      LStor.hasUF_eq s]
  | .delAt s q => by
    simp only [LStor.okEF, LStor.okE, LStor.okEF_eq s, LPath.elimF_eq q, LStor.hasUF_eq s]
  | .arr _ s q w => by
    simp only [LStor.okEF, LStor.okE, LStor.okEF_eq s, LTerm.elimF_eq w, LPath.elimF_eq q,
      LStor.lenUF_eq s]
  | .stale none s q w => by
    simp only [LStor.okEF, LStor.okE, LStor.okEF_eq s, LTerm.elimF_eq w, LPath.elimF_eq q,
      LStor.hasUF_eq s, LStor.lenUF_eq s, LStor.slotHasUF_eq s]
  | .stale (some _) s q w => by
    simp only [LStor.okEF, LStor.okE, LStor.okEF_eq s, LTerm.elimF_eq w, LPath.elimF_eq q,
      LStor.lenUF_eq s, LStor.slotLenUF_eq s]
  | .copy s q src sq => by
    simp only [LStor.okEF, LStor.okE, LStor.okEF_eq s, LStor.okEF_eq src, LPath.elimF_eq q,
      LPath.elimF_eq sq, LStor.hasUF_eq s, LStor.hasUF_eq src]
  | .view m _ => by simp only [LStor.okEF, LStor.okE, LMem.okUF_eq m, LMem.objUF_eq _ m]
termination_by structural s => s

theorem LStor.readUF_eq : (s : LStor) → ∀ Q, s.readUF Q = s.readU Q
  | .init, _ => rfl
  | .save s P w, Q => by
    simp only [LStor.readUF, LStor.readU, LPath.elimF_eq P, LTerm.elimF_eq w, LStor.readUF_eq s]
  | .delAt s P, Q => by
    simp only [LStor.readUF, LStor.readU, LPath.elimF_eq P, LStor.readUF_eq s, LStor.mapUF_eq _ s]
  | .arr op s P w, Q => by
    simp only [LStor.readUF, LStor.readU, LPath.elimF_eq P, LTerm.elimF_eq w, LStor.readUF_eq s,
      LStor.lenUF_eq s, LStor.slotUF_eq s]
    exact CaseTree.toTermLazy_eq _ _ _ _ _ (arrRead_lazy op _ _ _ _ _)
  | .stale none s P w, Q => by
    simp only [LStor.readUF, LStor.readU, LPath.elimF_eq P, LTerm.elimF_eq w, LStor.readUF_eq s,
      LStor.hasUF_eq s]
    exact CaseTree.toTermLazyBy_eq _ _ _ _ _ _ (staleRead_lazy _ _ _)
  | .stale (some _) .., _ => rfl
  | .copy s P src SQ, Q => by
    simp only [LStor.readUF, LStor.readU, LPath.elimF_eq P, LPath.elimF_eq SQ, LStor.readUF_eq s,
      LStor.readUF_eq src, LStor.mapUF_eq _ src]
  | .view m _, _ => by simp only [LStor.readUF, LStor.readU, LMem.readUF_eq m]
termination_by structural s => s

theorem LStor.slotUF_eq : (s : LStor) → ∀ P rest opq, s.slotUF P rest opq = s.slotU P rest opq
  | .arr (.pop _) s P' _, P, rest, opq => by
    simp only [LStor.slotUF, LStor.slotU, LPath.elimF_eq P', LStor.readUF_eq s, LStor.lenUF_eq s,
      LStor.mapUF_eq _ s]
  | .delAt s P', P, rest, opq => by
    simp only [LStor.slotUF, LStor.slotU, LPath.elimF_eq P', LStor.readUF_eq s, LStor.lenUF_eq s,
      LStor.mapUF_eq _ s, LStor.slotUF_eq s]
  | .stale none s P' w, P, rest, opq => by
    simp only [LStor.slotUF, LStor.slotU, LPath.elimF_eq P', LTerm.elimF_eq w, LStor.lenUF_eq s,
      LStor.slotUF_eq s]
  | .copy s P' src SQ, P, rest, opq => by
    simp only [LStor.slotUF, LStor.slotU, LPath.elimF_eq P', LPath.elimF_eq SQ, LStor.lenUF_eq s,
      LStor.lenUF_eq src, LStor.readUF_eq s, LStor.mapUF_eq _ s, LStor.slotUF_eq s]
  | .stale (some .push) s P' w, P, rest, opq => by
    simp only [LStor.slotUF, LStor.slotU, LPath.elimF_eq P', LTerm.elimF_eq w, LStor.lenUF_eq s,
      LStor.slotLenUF_eq s]
  | .init, _, _, _ | .save .., _, _, _ | .arr .push .., _, _, _
  | .arr (.slot _) .., _, _, _ | .stale (some (.pop _)) .., _, _, _
  | .stale (some (.slot _)) .., _, _, _ | .view .., _, _, _ => rfl
termination_by structural s => s

theorem LStor.slotLenUF_eq : (s : LStor) → ∀ P rest opq,
    s.slotLenUF P rest opq = s.slotLenU P rest opq
  | .arr (.pop _) s P' _, P, rest, opq => by
    simp only [LStor.slotLenUF, LStor.slotLenU, LPath.elimF_eq P', LStor.lenUF_eq s,
      LStor.mapUF_eq _ s]
  | .stale none s P' _, P, rest, opq => by
    simp only [LStor.slotLenUF, LStor.slotLenU, LPath.elimF_eq P', LStor.lenUF_eq s,
      LStor.slotLenUF_eq s]
  | .stale (some .push) s P' _, P, rest, opq => by
    simp only [LStor.slotLenUF, LStor.slotLenU, LPath.elimF_eq P', LStor.lenUF_eq s,
      LStor.slotLenUF_eq s]
  | .init, _, _, _ | .save .., _, _, _ | .delAt .., _, _, _ | .arr .push .., _, _, _
  | .arr (.slot _) .., _, _, _ | .stale (some (.pop _)) .., _, _, _
  | .stale (some (.slot _)) .., _, _, _ | .copy .., _, _, _ | .view .., _, _, _ => rfl
termination_by structural s => s

theorem LStor.slotHasUF_eq : (s : LStor) → ∀ P rest opq,
    s.slotHasUF P rest opq = s.slotHasU P rest opq
  | .arr (.pop _) s P' _, P, rest, opq => by
    simp only [LStor.slotHasUF, LStor.slotHasU, LPath.elimF_eq P', LStor.hasUF_eq s,
      LStor.lenUF_eq s, LStor.mapUF_eq _ s]
  | .stale none s P' _, P, rest, opq => by
    simp only [LStor.slotHasUF, LStor.slotHasU, LPath.elimF_eq P', LStor.lenUF_eq s,
      LStor.slotHasUF_eq s]
  | .init, _, _, _ | .save .., _, _, _ | .delAt .., _, _, _ | .arr .push .., _, _, _
  | .arr (.slot _) .., _, _, _ | .stale (some _) .., _, _, _ | .copy .., _, _, _
  | .view .., _, _, _ => rfl
termination_by structural s => s

theorem LStor.hasUF_eq : (s : LStor) → ∀ Q, s.hasUF Q = s.hasU Q
  | .init, _ => rfl
  | .save s P _, Q => by
    simp only [LStor.hasUF, LStor.hasU, LPath.elimF_eq P, LStor.hasUF_eq s]
  | .delAt s P, Q => by
    simp only [LStor.hasUF, LStor.hasU, LPath.elimF_eq P, LStor.hasUF_eq s, LStor.mapUF_eq _ s]
  | .arr op s P _, Q => by
    simp only [LStor.hasUF, LStor.hasU, LPath.elimF_eq P, LStor.hasUF_eq s, LStor.lenUF_eq s]
    exact CaseTree.toTermLazy_eq _ _ _ _ _ (arrHas_lazy op _ _ _)
  | .stale none s P _, Q => by
    simp only [LStor.hasUF, LStor.hasU, LPath.elimF_eq P, LStor.hasUF_eq s]
  | .stale (some _) .., _ => rfl
  | .copy s P src SQ, Q => by
    simp only [LStor.hasUF, LStor.hasU, LPath.elimF_eq P, LPath.elimF_eq SQ, LStor.hasUF_eq s,
      LStor.hasUF_eq src, LStor.mapUF_eq _ src]
  | .view m _, _ => by simp only [LStor.hasUF, LStor.hasU, LMem.readUF_eq m, LMem.objUF_eq _ m]
termination_by structural s => s

theorem LStor.lenUF_eq : (s : LStor) → ∀ Q, s.lenUF Q = s.lenU Q
  | .init, _ => rfl
  | .save s P _, Q => by
    simp only [LStor.lenUF, LStor.lenU, LPath.elimF_eq P, LStor.lenUF_eq s]
  | .delAt s P, Q => by
    simp only [LStor.lenUF, LStor.lenU, LPath.elimF_eq P, LStor.lenUF_eq s, LStor.mapUF_eq _ s]
  | .arr op s P _, Q => by
    simp only [LStor.lenUF, LStor.lenU, LPath.elimF_eq P, LStor.lenUF_eq s, LStor.slotLenUF_eq s,
      arrLength_gateSlot]
    exact CaseTree.toTermLazy_eq _ _ _ _ _ (arrLength_lazy op _ _ _ _)
  | .stale none s P _, Q => by
    simp only [LStor.lenUF, LStor.lenU, LPath.elimF_eq P, LStor.lenUF_eq s]
  | .stale (some op) s P _, Q => by
    simp only [LStor.lenUF, LStor.lenU, LPath.elimF_eq P, LStor.lenUF_eq s]
    exact CaseTree.toTermLazy_eq _ _ _ _ _ (arrLength_lazy op _ _ _ _)
  | .copy s P src SQ, Q => by
    simp only [LStor.lenUF, LStor.lenU, LPath.elimF_eq P, LPath.elimF_eq SQ, LStor.lenUF_eq s,
      LStor.lenUF_eq src, LStor.mapUF_eq _ src]
  | .view m _, _ => by simp only [LStor.lenUF, LStor.lenU, LMem.readUF_eq m]
termination_by structural s => s

theorem LStor.mapUF_eq (sh : KShape) : (s : LStor) → ∀ Q, s.mapUF sh Q = s.mapU sh Q
  | .init, _ => rfl
  | .save s P _, Q => by
    simp only [LStor.mapUF, LStor.mapU, LPath.elimF_eq P, LStor.mapUF_eq sh s]
  | .delAt s P, Q => by
    simp only [LStor.mapUF, LStor.mapU, LPath.elimF_eq P, LStor.mapUF_eq _ s]
  | .arr op s P _, Q => by
    simp only [LStor.mapUF, LStor.mapU, LPath.elimF_eq P, LStor.mapUF_eq sh s, LStor.lenUF_eq s]
    exact CaseTree.toTermLazy_eq _ _ _ _ _ (arrMap_lazy op _ _ _)
  | .stale none s P _, Q => by
    simp only [LStor.mapUF, LStor.mapU, LPath.elimF_eq P, LStor.mapUF_eq sh s]
  | .stale (some _) .., _ => rfl
  | .copy s P src SQ, Q => by
    simp only [LStor.mapUF, LStor.mapU, LPath.elimF_eq P, LPath.elimF_eq SQ, LStor.mapUF_eq sh s,
      LStor.mapUF_eq _ src]
  | .view _ _, _ => rfl
termination_by structural s => s

theorem LStor.cpokUF_eq : (s : LStor) → ∀ Q, s.cpokUF Q = s.cpokU Q
  | .init, _ => rfl
  | .save s P _, Q => by
    simp only [LStor.cpokUF, LStor.cpokU, LPath.elimF_eq P, LStor.readUF_eq s, LStor.cpokUF_eq s]
  | .delAt .., _ | .arr .., _ | .stale .., _ | .copy .., _ | .view .., _ => rfl
termination_by structural s => s

theorem LSel.idxUF_eq : (a : LSel) → a.idxUF = a.idxU
  | .idx w => by simp only [LSel.idxUF, LSel.idxU, LTerm.elimF_eq w]
  | .fld _ | .size => rfl
termination_by structural a => a

theorem LMV.wordUF_eq : (v : LMV) → v.wordUF = v.wordU
  | .word t => by simp only [LMV.wordUF, LMV.wordU, LTerm.elimF_eq t]
  | .ref _ => rfl
termination_by structural v => v

theorem LMem.readUF_eq : (m : LMem) → ∀ i a, m.readUF i a = m.readU i a
  | .init, _, _ => rfl
  | .addM m _ _, i, a => by simp only [LMem.readUF, LMem.readU, LMem.readUF_eq m]
  | .newArr m _ _ n, i, a => by
    simp only [LMem.readUF, LMem.readU, LMem.readUF_eq m, LTerm.elimF_eq n]
  | .copySt m _ s q, i, a => by
    simp only [LMem.readUF, LMem.readU, LMem.readUF_eq m, LPath.elimF_eq q, LStor.okEF_eq s,
      LStor.readUF_eq s, LStor.lenUF_eq s]
  | .write m _ b v, i, a => by
    simp only [LMem.readUF, LMem.readU, LMem.readUF_eq m, LMV.wordUF_eq v, LSel.idxUF_eq b]
termination_by structural m => m

theorem LMem.objUF_eq (str : Bool) : (m : LMem) → ∀ i, m.objUF str i = m.objU str i
  | .init, _ => rfl
  | .addM m _ _, i => by simp only [LMem.objUF, LMem.objU, LMem.objUF_eq str m]
  | .newArr m _ _ n, i => by
    simp only [LMem.objUF, LMem.objU, LMem.objUF_eq str m, LTerm.elimF_eq n]
  | .copySt m _ s q, i => by
    simp only [LMem.objUF, LMem.objU, LMem.objUF_eq str m, LPath.elimF_eq q, LStor.okEF_eq s,
      LStor.readUF_eq s, LStor.lenUF_eq s, LStor.hasUF_eq s]
  | .write m _ _ _, i => by simp only [LMem.objUF, LMem.objU, LMem.objUF_eq str m]
termination_by structural m => m

theorem LMem.okUF_eq : (m : LMem) → m.okUF = m.okU
  | .init => rfl
  | .addM m _ _ => by simp only [LMem.okUF, LMem.okU, LMem.okUF_eq m]
  | .newArr m _ _ n => by simp only [LMem.okUF, LMem.okU, LMem.okUF_eq m, LTerm.elimF_eq n]
  | .copySt m _ s q => by
    simp only [LMem.okUF, LMem.okU, LMem.okUF_eq m, LPath.elimF_eq q, LStor.okEF_eq s,
      LStor.cpokUF_eq s, LStor.readUF_eq s]
  | .write m _ b v => by
    simp only [LMem.okUF, LMem.okU, LMem.okUF_eq m, LMem.objUF_eq _ m, LMem.readUF_eq m,
      LSel.idxUF_eq b, LMV.wordUF_eq v]
termination_by structural m => m

end

@[csimp] theorem LSel.idxU_csimp : @LSel.idxU = @LSel.idxUF :=
  funext fun a => (LSel.idxUF_eq a).symm

@[csimp] theorem LMV.wordU_csimp : @LMV.wordU = @LMV.wordUF :=
  funext fun v => (LMV.wordUF_eq v).symm

@[csimp] theorem LMem.readU_csimp : @LMem.readU = @LMem.readUF :=
  funext fun m => funext fun i => funext fun a => (LMem.readUF_eq m i a).symm

@[csimp] theorem LMem.okU_csimp : @LMem.okU = @LMem.okUF :=
  funext fun m => (LMem.okUF_eq m).symm

@[csimp] theorem LMem.objU_csimp : @LMem.objU = @LMem.objUF :=
  funext fun str => funext fun m => funext fun i => (LMem.objUF_eq str m i).symm

@[csimp] theorem LTerm.elim_csimp : @LTerm.elim = @LTerm.elimF :=
  funext fun t => (LTerm.elimF_eq t).symm

@[csimp] theorem LPath.elim_csimp : @LPath.elim = @LPath.elimF :=
  funext fun q => (LPath.elimF_eq q).symm

@[csimp] theorem LStor.okE_csimp : @LStor.okE = @LStor.okEF :=
  funext fun s => (LStor.okEF_eq s).symm

@[csimp] theorem LStor.readU_csimp : @LStor.readU = @LStor.readUF :=
  funext fun s => funext fun Q => (LStor.readUF_eq s Q).symm

@[csimp] theorem LStor.slotU_csimp : @LStor.slotU = @LStor.slotUF :=
  funext fun s => funext fun P => funext fun rest => funext fun opq =>
    (LStor.slotUF_eq s P rest opq).symm

@[csimp] theorem LStor.slotHasU_csimp : @LStor.slotHasU = @LStor.slotHasUF :=
  funext fun s => funext fun P => funext fun rest => funext fun opq =>
    (LStor.slotHasUF_eq s P rest opq).symm

@[csimp] theorem LStor.slotLenU_csimp : @LStor.slotLenU = @LStor.slotLenUF :=
  funext fun s => funext fun P => funext fun rest => funext fun opq =>
    (LStor.slotLenUF_eq s P rest opq).symm

@[csimp] theorem LStor.hasU_csimp : @LStor.hasU = @LStor.hasUF :=
  funext fun s => funext fun Q => (LStor.hasUF_eq s Q).symm

@[csimp] theorem LStor.lenU_csimp : @LStor.lenU = @LStor.lenUF :=
  funext fun s => funext fun Q => (LStor.lenUF_eq s Q).symm

@[csimp] theorem LStor.cpokU_csimp : @LStor.cpokU = @LStor.cpokUF :=
  funext fun s => funext fun Q => (LStor.cpokUF_eq s Q).symm

@[csimp] theorem LStor.mapU_csimp : @LStor.mapU = @LStor.mapUF :=
  funext fun sh => funext fun s => funext fun Q => (LStor.mapUF_eq sh s Q).symm

/-- A formula with every read of a write eliminated. -/
def LFml.elim : LFml → LFml
  | .tt => .tt
  | .eq a b => .eq a.elim b.elim
  | .not φ => .not φ.elim
  | .and φ ψ => .and φ.elim ψ.elim
  | .imp φ ψ => .imp φ.elim ψ.elim
  | .all x p φ => .all x p φ.elim

/-! ### Eliminating keeps what returns -/


/-- A path without a `length` segment evaluates to one. -/
theorem LPath.noLen_eval (σ : State) : ∀ {q : LPath} {qs : List Seg},
    q.noLen = true → q.eval σ = .ok qs → NoLen qs
  | .root r, qs, hn, h => by
    cases h
    intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    simp only [LPath.noLen, bne_iff_ne, ne_eq] at hn
    intro he; exact hn (by injection he)
  | .field q f, qs, hn, h => by
    simp only [LPath.noLen, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
    obtain ⟨qs', h', he⟩ := Res.bind_eq_ok.1 h; cases he
    intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · exact LPath.noLen_eval σ hn.1 h' s hs
    · simp only [List.mem_singleton] at hs
      subst hs; intro he; exact hn.2 (by injection he)
  | .at q k, qs, hn, h => by
    simp only [LPath.noLen] at hn
    obtain ⟨qs', h', h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨i, _, he⟩ := Res.bind_eq_ok.1 h; cases he
    intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · exact LPath.noLen_eval σ hn h' s hs
    · simp only [List.mem_singleton] at hs
      subst hs; simp only [ne_eq, reduceCtorEq, not_false_eq_true]

/-- A read guarded by its storage and its path agrees with the read. -/
theorem guard_sim {σ : State} {s : LStor} {q q' : LPath} {X : LTerm} {F : SVal → List Seg → Res Value}
    (hs : Sim (s.okE.eval σ) (s.eval σ >>= fun _ => .ok (.bool true)))
    (hq : Sim (q'.eval σ) (q.eval σ))
    (hX : ∀ v qs, s.eval σ = .ok v → q'.eval σ = .ok qs → Sim (X.eval σ) (F v qs)) :
    Sim ((LTerm.seq s.okE (.seq (.pok q') X)).eval σ)
      (s.eval σ >>= fun v => q.eval σ >>= fun qs => F v qs) := by
  intro a
  simp only [LTerm.eval, Res.bind_eq_ok]
  constructor
  · rintro ⟨_, h₁, _, ⟨qs, h₂, -⟩, h₃⟩
    obtain ⟨v, hv, -⟩ := Res.bind_eq_ok.1 ((hs _).1 h₁)
    exact ⟨v, hv, qs, (hq _).1 h₂, (hX v qs hv h₂ a).1 h₃⟩
  · rintro ⟨v, hv, qs, hq', h₃⟩
    have h₂ := (hq qs).2 hq'
    exact ⟨.bool true, (hs _).2 (by simp only [hv, Res.ok_bind]), .bool true, ⟨qs, h₂, rfl⟩,
      (hX v qs hv h₂ a).2 h₃⟩

/-- A `delete` keeps the shape: the default of a mapping is a mapping, of a
fixed-size array a fixed-size array. -/
theorem KShape.test_defaultOf (sh : KShape) (c : SVal) : sh.test c.defaultOf = sh.test c := by
  cases c with
  | prim p => cases p <;> cases sh <;> rfl
  | struct _ => cases sh <;> rfl
  | array _ _ fx => cases fx <;> cases sh <;> rfl
  | map _ _ => cases sh <;> rfl

/-- A write below a location keeps its shape: after `ledger.balances[1] = 5;`,
`ledger.balances` is the mapping it was. -/
theorem save_cons_kmapF {sh : KShape} {v new u : SVal} {s : Seg} {r : List Seg}
    (h : v.saveLive (s :: r) new = .ok u) : sh.test u = sh.test v := by
  rcases saveLive_cons_shape h with ⟨_, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl, rfl, -⟩ | ⟨_, _, _, rfl, rfl⟩ <;>
    cases sh <;> rfl

/-- A write below an array keeps its length: after `values[2] = 5;`,
`values.length` is what it was. -/
theorem save_cons_arrLen {v new u : SVal} {s : Seg} {r : List Seg}
    (h : v.saveLive (s :: r) new = .ok u) : Close.arrLen u = Close.arrLen v := by
  rcases saveLive_cons_shape h with ⟨_, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl, rfl, hl⟩ | ⟨_, _, _, rfl, rfl⟩
  · rfl
  · simp only [Close.arrLen, hl]
  · rfl

/-- The members a list of segments starts with, up to its first key. -/
def leadFields : List SSeg → List Seg
  | .field f :: r => .field f :: leadFields r
  | _ => []

/-- Leading members have no key: `account.balance` of `account.balance[k]`. -/
theorem leadFields_noAt : (xs : List SSeg) → (leadFields xs).any Seg.isAt = false
  | .field _ :: r => by simp only [leadFields, List.any_cons, Seg.isAt, leadFields_noAt r,
      Bool.or_self]
  | [] => rfl
  | .key _ :: _ => rfl

/-- Segments with a key evaluate to their leading members, then a key. -/
theorem segsEval_leadFields (σ : State) : ∀ {xs : List SSeg} {ys : List Seg},
    segsEval σ xs = .ok ys → xs.any SSeg.isKey = true →
      ∃ k more, ys = leadFields xs ++ .at k :: more
  | [], _, _, hk => by simp only [List.any_nil, Bool.false_eq_true] at hk
  | .field f :: r, ys, h, hk => by
    obtain ⟨ys', h', he⟩ := Res.bind_eq_ok.1 h; cases he
    obtain ⟨k, more, rfl⟩ := segsEval_leadFields σ h' (by simpa only [List.any_eq_true,
        SSeg.isKey, List.any_cons, Bool.false_or] using hk)
    exact ⟨k, more, rfl⟩
  | .key k :: r, ys, h, _ => by
    obtain ⟨i, _, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨ys', _, he⟩ := Res.bind_eq_ok.1 h; cases he
    exact ⟨i, ys', rfl⟩

/-- Extending a path by members appends them. -/
theorem LPath.addFields_eval (σ : State) : ∀ (xs : List SSeg) (q : LPath),
    (q.addFields xs).eval σ = q.eval σ >>= fun qs => .ok (qs ++ leadFields xs)
  | .field f :: r, q => by
    simp only [LPath.addFields, LPath.addFields_eval σ r, LPath.eval, bind_assoc, Res.ok_bind,
      leadFields, List.append_assoc, List.singleton_append]
  | [], q => by simp only [addFields, leadFields, List.append_nil, Close.bind_ok_right]
  | .key _ :: _, q => by simp only [addFields, leadFields, List.append_nil, Close.bind_ok_right]

/-- Agreeing runs, each with an agreeing fallback, agree. -/
theorem Sim.orElse {a a' b b' : Res Value} (ha : Sim a a') (hb : Sim b b') :
    Sim (orElseR a b) (orElseR a' b') := by
  intro x
  cases a with
  | ok v =>
    have h := (ha v).1 rfl
    rw [h]; rfl
  | error e =>
    cases a' with
    | ok v' => exact absurd ((ha v').2 rfl) (by simp only [reduceCtorEq, not_false_eq_true])
    | error _ => exact hb x

/-- A run that returns when a test does, and otherwise falls back. -/
theorem orElseR_eq_ok {a b : Res Value} {x : Value} :
    orElseR a b = .ok x ↔ a = .ok x ∨ ((∀ y, a ≠ .ok y) ∧ b = .ok x) := by
  cases a <;> simp only [orElseR, reduceCtorEq, ne_eq, not_false_eq_true, implies_true, true_and,
      false_or, Except.ok.injEq, forall_eq', false_and, or_false]

/-- The length of a default: a fixed-size array keeps its length, a dynamic
one has none left. -/
theorem lenEnd_sim {σ : State} {old fixed : LTerm} {x : Res SVal}
    (ho : Sim (old.eval σ) (x >>= Close.arrLen)) (hf : Sim (fixed.eval σ) (x >>= KShape.fixed.test)) :
    Sim ((lenEnd old fixed).eval σ) (x >>= fun w => Close.arrLen w.defaultOf) := by
  refine (Sim.orElse (Sim.bind hf fun _ => ho) (Sim.bind ho fun _ => Sim.refl _)).trans
    (Sim.of_eq ?_)
  rcases x with e | ⟨(i | b) | fs | ⟨es, sh, _ | _⟩ | ⟨es, d⟩⟩ <;>
    simp only [orElseR, bind, Except.bind, KShape.test, isFixV, Bool.false_eq_true, ↓reduceIte,
        Close.arrLen, SVal.defaultOf, LTerm.eval, defaultOfElems_eq_map, List.length_nil,
            Int.cast_ofNat_Int, List.length_map]

/-- **`delBelow` reads what the deleted value has below it.**  `v` is the
storage before the delete, `guard sh q` tests the location `q` names in it for
the shape `sh`, `atMap` is the old read of the whole path `full` and `atEnd`
its default; then the walk from `q` (at `qs`) down `rest` returns what the
default of the location at `qs` has at `rest`.  Example: `delete fixedMaps;`
then `fixedMaps[1][2]`: `fixedMaps` is a fixed-size array (its element `1` is
deleted in place), `fixedMaps[1]` a mapping (its entry `2` is the old one). -/
theorem delBelow_sim {σ : State} {v : SVal} {G : SVal → Res Value} {atMap atEnd : LTerm}
    {guard : KShape → LPath → LTerm} {full : List Seg}
    (hg : ∀ sh q qs, q.eval σ = .ok qs → Sim ((guard sh q).eval σ) (v.findLive qs >>= sh.test))
    (hMap : Sim (atMap.eval σ) (v.findLive full >>= G))
    (hEnd : Sim (atEnd.eval σ) (v.findLive full >>= fun w => G w.defaultOf)) :
    ∀ (rest : List SSeg) (q : LPath) (qs R : List Seg), q.eval σ = .ok qs →
      segsEval σ rest = .ok R → qs ++ R = full →
      Sim ((delBelow atMap atEnd guard q rest).eval σ)
        (v.findLive qs >>= fun N => N.defaultOf.findLive R >>= G)
  | [], q, qs, R, hq, hR, hf => by
    cases hR
    simp only [delBelow, List.append_nil] at hf ⊢
    subst hf
    refine hEnd.trans (Sim.of_eq ?_)
    congr 1; funext N
    simp only [SVal.findLive_nil, Res.ok_bind]
  | .field f :: r, q, qs, R, hq, hR, hf => by
    obtain ⟨R', hR', he⟩ := Res.bind_eq_ok.1 hR; cases he
    have hq' : (q.field f).eval σ = .ok (qs ++ [.field f]) := by
      simp only [LPath.eval, hq, Res.ok_bind]
    have ih := delBelow_sim hg hMap hEnd r (q.field f) (qs ++ [.field f]) R' hq' hR'
      (by rw [← hf]; simp only [List.append_assoc, List.cons_append, List.nil_append])
    simp only [delBelow]
    refine ih.trans (Sim.of_eq ?_)
    rw [SVal.findLive_append, bind_assoc]
    congr 1; funext N
    rw [defaultOf_field, bind_assoc]
  | .key k :: r, q, qs, R, hq, hR, hf => by
    obtain ⟨i, hi, hR⟩ := Res.bind_eq_ok.1 hR
    obtain ⟨R', hR', he⟩ := Res.bind_eq_ok.1 hR; cases he
    have hq' : (q.at k).eval σ = .ok (qs ++ [.at i]) := by
      simp only [LPath.eval, hq, Res.ok_bind, hi]
    have ih := delBelow_sim hg hMap hEnd r (q.at k) (qs ++ [.at i]) R' hq' hR'
      (by rw [← hf]; simp only [List.append_assoc, List.cons_append, List.nil_append])
    have hgm := hg .map q qs hq
    have hgf := hg .fixed q qs hq
    simp only [delBelow]
    intro a
    simp only [LTerm.eval, orElseR_eq_ok, Res.bind_eq_ok]
    constructor
    · rintro (⟨x, h₁, h₂⟩ | ⟨hA, x, h₁, h₂⟩)
      · -- a mapping: the old read
        obtain ⟨N, hN, hm⟩ := Res.bind_eq_ok.1 ((hgm x).1 h₁)
        have hmap : isMapV N = true := by
          simp only [KShape.test, kmapF] at hm; split at hm
          · assumption
          · simp only [reduceCtorEq] at hm
        obtain ⟨N', hN', hr⟩ := Res.bind_eq_ok.1 (by
          have := (hMap a).1 h₂; rw [← hf, SVal.findLive_append] at this; rw [bind_assoc] at this
          exact this)
        rw [hN] at hN'; cases hN'
        obtain ⟨b, hb, hG⟩ := Res.bind_eq_ok.1 hr
        exact ⟨N, hN, b, (defaultOf_key N i R' b).2 (.inl ⟨hmap, hb⟩), hG⟩
      · -- a fixed-size array: the element, one key down
        obtain ⟨N, hN, hx⟩ := Res.bind_eq_ok.1 ((hgf x).1 h₁)
        have hfix : isFixV N = true := by
          simp only [KShape.test] at hx; split at hx
          · assumption
          · simp only [reduceCtorEq] at hx
        obtain ⟨e, he, hr⟩ := Res.bind_eq_ok.1 (by
          have := (ih a).1 h₂; rw [SVal.findLive_append, bind_assoc, hN, Res.ok_bind] at this
          exact this)
        obtain ⟨b, hb, hG⟩ := Res.bind_eq_ok.1 hr
        exact ⟨N, hN, b, (defaultOf_key N i R' b).2 (.inr ⟨hfix, e, he, hb⟩), hG⟩
    · rintro ⟨N, hN, b, hb, hG⟩
      rcases (defaultOf_key N i R' b).1 hb with ⟨hmap, hb'⟩ | ⟨hfix, e, he, hb'⟩
      · refine .inl ⟨.bool true, (hgm _).2 ?_, (hMap a).2 ?_⟩
        · simp only [hN, Res.ok_bind, KShape.test, kmapF, hmap, ↓reduceIte]
        · rw [← hf, SVal.findLive_append, bind_assoc, hN, Res.ok_bind, hb', Res.ok_bind, hG]
      · have hnm : isMapV N = false := by
          cases N <;> simp_all only [isFixV, Bool.false_eq_true, isMapV]
        refine .inr ⟨fun y hy => ?_, .bool true, (hgf _).2 ?_, (ih a).2 ?_⟩
        · obtain ⟨z, hz, _⟩ := Res.bind_eq_ok.1 hy
          obtain ⟨N', hN', hm⟩ := Res.bind_eq_ok.1 ((hgm z).1 hz)
          rw [hN] at hN'; cases hN'
          simp only [KShape.test, kmapF, hnm, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hm
        · simp only [hN, Res.ok_bind, KShape.test, hfix, ↓reduceIte]
        · rw [SVal.findLive_append, bind_assoc, hN, Res.ok_bind, he, Res.ok_bind, hb',
            Res.ok_bind, hG]

/-- A word has nothing below it. -/
theorem find_prim_cons (p : PrimVal) (f : Seg) (t : List Seg) :
    (SVal.prim p).findLive (f :: t) = .error .stuck := by
  cases f <;> rfl

/-- The case tree comparing a write at `P` with a read at `Q` agrees with a
run when every leaf whose relation holds of the two paths does. -/
theorem cmp_sim {σ : State} {P Q : LPath} {ps qs : List Seg} (hp : P.eval σ = .ok ps)
    (hq : Q.eval σ = .ok qs) {leaf : PathRel → LTerm} {y : Res Value}
    (h : ∀ r : PathRel, r.Holds σ ps qs → Sim ((leaf r).eval σ) y) :
    Sim (((cmpSegs P.segs Q.segs).toTerm leaf).eval σ) y := by
  have hp' := LPath.segs_eval σ hp
  have hq' := LPath.segs_eval σ hq
  rw [CaseTree.toTerm_eval σ _ _ (cmpSegs_testsOk σ _ _ hp' hq')]
  exact h _ (cmpSegs_holds σ _ _ hp' hq')

theorem LPath.addSegs_eval (σ : State) : ∀ (xs : List SSeg) (q : LPath),
    (q.addSegs xs).eval σ = q.eval σ >>= fun qs => segsEval σ xs >>= fun r => .ok (qs ++ r)
  | [], q => by
    simp only [LPath.addSegs, segsEval, Res.ok_bind, List.append_nil]
    cases q.eval σ <;> rfl
  | .field f :: xs, q => by
    rw [LPath.addSegs, LPath.addSegs_eval σ xs]
    simp only [LPath.eval, segsEval, bind_assoc, Res.ok_bind, List.append_assoc,
      List.singleton_append]
  | .key k :: xs, q => by
    rw [LPath.addSegs, LPath.addSegs_eval σ xs]
    simp only [LPath.eval, segsEval, bind_assoc, Res.ok_bind, List.append_assoc,
      List.singleton_append]

/-! ### Arrays and copies

An operation on an array changes the node at its path alone (`AOp.apply`):
below it a read compares its index with the old length (`arrKey`); a copy
reads the source through members (`overlay_findLive_fields`), and below a
key of a copy the read is kept whole, since a mapping met in both keeps the
target's entries. -/

theorem findLive_grow (es sh sh' : List SVal) (fx : Bool) (x : SVal) (i : Int) (r : List Seg) :
    (SVal.array (es ++ [x]) sh' fx).findLive (.at i :: r) =
      if i = es.length then x.findLive r else (SVal.array es sh fx).findLive (.at i :: r) := by
  simp only [SVal.findLive, List.length_append, List.length_singleton, List.get_eq_getElem]
  by_cases hi : i = es.length
  · subst hi
    simp only [Int.ofNat_zero_le, Int.toNat_natCast, Nat.lt_add_one, and_self, ↓reduceDIte,
        Nat.le_refl, List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero, ↓reduceIte]
  · rw [if_neg hi]
    by_cases hb : 0 ≤ i ∧ i.toNat < es.length
    · rw [dif_pos hb, dif_pos (by omega)]
      rw [List.getElem_append_left]
    · rw [dif_neg hb, dif_neg (by omega)]

theorem findLive_shrink (es sh sh' : List SVal) (fx : Bool) (x : SVal) (i : Int) (r : List Seg) :
    (SVal.array es sh' fx).findLive (.at i :: r) =
      if i = es.length then .error .revert else (SVal.array (es ++ [x]) sh fx).findLive (.at i :: r) := by
  rw [findLive_grow es sh' sh fx x i r]
  by_cases hi : i = es.length
  · subst hi
    simp only [SVal.findLive, Int.ofNat_zero_le, Int.toNat_natCast, Nat.lt_irrefl, and_false,
        ↓reduceDIte, ↓reduceIte]
  · simp only [hi, ↓reduceIte]

theorem layAt_overlay : ∀ (old : SVal) (q : List Seg) (v : SVal), ∃ c : SVal, Close.layAt old q v = c.overlay v
  | old, [], v => ⟨old, by cases old <;> simp only [Close.layAt]⟩
  | .struct ofs, .field f :: q, v => by
    simp only [Close.layAt]
    split
    · exact layAt_overlay _ q v
    · exact ⟨.prim (.int 0), (prim_overlay _ v).symm⟩
  | .prim _, _ :: _, v | .array .., _ :: _, v | .map .., _ :: _, v | .struct _, .at _ :: _, v =>
    ⟨.prim (.int 0), (prim_overlay _ v).symm⟩

theorem overlayElems_length : ∀ (os nel : List SVal), (SVal.overlay.overlayElems os nel).length = nel.length
  | o :: os, _ :: nel => by simp only [SVal.overlay.overlayElems, List.length_cons,
      overlayElems_length os nel]
  | [], nel => by simp only [SVal.overlay.overlayElems, Close.stripElems_length]
  | _ :: _, [] => rfl

theorem overlay_asValue (c y : SVal) : (c.overlay y).asValue = y.asValue := by
  cases y with
  | prim p => cases c <;> simp only [SVal.overlay, SVal.strip]
  | struct _ => cases c <;> simp only [SVal.asValue, SVal.overlay, SVal.strip]
  | array _ _ _ => cases c <;> simp only [SVal.asValue, SVal.overlay, SVal.strip]
  | map _ _ => cases c <;> simp only [SVal.asValue, SVal.overlay, SVal.strip]

theorem overlay_arrLen (c y : SVal) : Close.arrLen (c.overlay y) = Close.arrLen y := by
  cases y with
  | array nel nsh nfx =>
    cases c <;> simp only [Close.arrLen, SVal.overlay, SVal.strip, Close.stripElems_length,
        overlayElems_length]
  | prim p => cases c <;> simp only [SVal.overlay, SVal.strip]
  | struct _ => cases c <;> simp only [Close.arrLen, SVal.overlay, SVal.strip]
  | map _ _ => cases c <;> simp only [Close.arrLen, SVal.overlay, SVal.strip]


theorem overlay_test (sh : KShape) (c y : SVal) : sh.test (c.overlay y) = sh.test y := by
  cases y with
  | array nel nsh nfx =>
    cases c <;> cases sh <;> simp only [KShape.test, kmapF, isMapV, SVal.overlay, SVal.strip,
        Bool.false_eq_true, ↓reduceIte, isFixV]
  | prim p => cases c <;> simp only [SVal.overlay, SVal.strip]
  | struct _ => cases c <;> cases sh <;> simp only [KShape.test, kmapF, isMapV, SVal.overlay,
      SVal.strip, Bool.false_eq_true, ↓reduceIte, isFixV]
  | map _ _ => cases c <;> cases sh <;> simp only [KShape.test, kmapF, isMapV, SVal.overlay,
      SVal.strip, ↓reduceIte, isFixV, Bool.false_eq_true]

theorem fieldPath_of_any : ∀ (fs : List Seg), fs.any Seg.isAt = false → Close.fieldPath fs = true
  | [], _ => rfl
  | .field _ :: fs, h => by
    simpa only [Close.fieldPath_field] using fieldPath_of_any fs (by
      simpa only [List.any_eq_false, Seg.isAt, Bool.not_eq_true, List.any_cons, Bool.false_or]
        using h)
  | .at _ :: _, h => by simp only [List.any_cons, Seg.isAt, Bool.true_or, Bool.true_eq_false] at h

/-- **A copy read along members reads the source**, up to what a read of a
word, a location, a length or a shape sees (`hG`). -/
theorem overlay_findLive_fields {G : SVal → Res Value} (hG : ∀ c y : SVal, G (c.overlay y) = G y)
    (cur n : SVal) (fs : List Seg) (hf : fs.any Seg.isAt = false) :
    ((cur.overlay n).findLive fs >>= G) = (n.findLive fs >>= G) := by
  rw [findLive_eq_find _ _ hf, findLive_eq_find _ _ hf,
    Close.find_overlay_fields cur n fs (fieldPath_of_any fs hf)]
  cases n.find fs with
  | error _ => rfl
  | ok v =>
    obtain ⟨c, hc⟩ := layAt_overlay cur fs v
    simp only [Res.ok_bind, hc, hG]

theorem AOp.apply_pop {keep : Bool} {wv : Value} {c c' : SVal}
    (h : (AOp.pop keep).apply wv c = .ok c') :
    ∃ es last sh fx sh', c = .array (es ++ [last]) sh fx ∧ c' = .array es sh' fx := by
  cases c with
  | array elems shadow fx =>
    simp only [AOp.apply] at h
    rcases hr : elems.reverse with _ | ⟨l, rr⟩ <;> simp only [hr] at h
    · cases h
    · cases h
      refine ⟨rr.reverse, l, shadow, fx, _, ?_, rfl⟩
      have he : elems = (l :: rr).reverse := by rw [← hr, List.reverse_reverse]
      simp only [he, List.reverse_cons]
  | prim _ | struct _ | map _ _ => simp only [apply, reduceCtorEq] at h

/-- The array an operation leaves, against the one it found. -/
theorem AOp.apply_ok {op : AOp} {wv : Value} {c c' : SVal} (h : op.apply wv c = .ok c') :
    ∃ es sh fx es' sh', c = .array es sh fx ∧ c' = .array es' sh' fx ∧
      (es'.length : Int) = (match op with | .pop _ => (es.length : Int) - 1 | _ => es.length + 1) := by
  cases op with
  | push =>
    cases c with
    | array es sh fx => simp only [AOp.apply] at h; cases h; exact ⟨es, sh, fx, _, _, rfl, rfl,
        by simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
            Int.natCast_add, Int.cast_ofNat_Int]⟩
    | prim _ | struct _ | map _ _ => simp only [apply, reduceCtorEq] at h
  | slot E =>
    cases c with
    | array es sh fx => simp only [AOp.apply] at h; cases h; exact ⟨es, sh, fx, _, _, rfl, rfl,
        by simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
            Int.natCast_add, Int.cast_ofNat_Int]⟩
    | prim _ | struct _ | map _ _ => simp only [apply, reduceCtorEq] at h
  | pop keep =>
    obtain ⟨es, last, sh, fx, sh', rfl, rfl⟩ := AOp.apply_pop h
    exact ⟨_, sh, fx, es, sh', rfl, rfl, by simp only [List.length_append, List.length_cons,
        List.length_nil, Nat.zero_add, Int.natCast_add, Int.cast_ofNat_Int, Int.add_sub_cancel]⟩

theorem pushSlot_prim (p : PrimTy) (sh : List SVal) :
    (pushSlot (.prim p) sh).1 = .prim (dfltV p) := by
  cases sh <;> cases p <;> simp only [pushSlot, defaultForTy, dfltV, Ty.isPrimitive,
      ↓reduceIte] <;> rfl

theorem kite_eval {σ : State} {k L t e : LTerm} {i n : Int}
    (hk : (k.eval σ >>= Value.asInt) = .ok i) (hL : L.eval σ = .ok (.int n)) :
    (LTerm.kite k L t e).eval σ = if i = n then t.eval σ else e.eval σ := by
  simp only [LTerm.eval, hk, hL, Res.ok_bind, Value.asInt]

theorem lenPred_eval {σ : State} {L : LTerm} {n : Int} (h : L.eval σ = .ok (.int n)) :
    (lenPred L).eval σ = .ok (.int (n - 1)) := by
  simp only [lenPred, LTerm.eval, bind, Except.bind, h, evalBinop, applyBinOp, Value.asInt,
      checkArith, BinOp.retTy, BinOp.isArith, ↓reduceIte]

theorem lenSucc_eval {σ : State} {L : LTerm} {n : Int} (h : L.eval σ = .ok (.int n)) :
    (lenSucc L).eval σ = .ok (.int (n + 1)) := by
  simp only [lenSucc, LTerm.eval, bind, Except.bind, h, evalBinop, applyBinOp, Value.asInt,
      checkArith, BinOp.retTy, BinOp.isArith, ↓reduceIte]

/-- **What is at an index after an operation on the array.** -/
theorem arrKey_sim {σ : State} {op : AOp} {wv : Value} {c c' : SVal} {k L old opq atNew : LTerm}
    {i : Int} {r : List Seg} {G : SVal → Res Value}
    (hap : op.apply wv c = .ok c') (hk : (k.eval σ >>= Value.asInt) = .ok i)
    (hL : Sim (L.eval σ) (Close.arrLen c))
    (hold : Sim (old.eval σ) (c.findLive (.at i :: r) >>= G))
    (hopq : Sim (opq.eval σ) (c'.findLive (.at i :: r) >>= G))
    (hnew : ∀ pv : PrimVal, (op = .push → SVal.prim pv = wv.toSVal) →
      (∀ p, op = .slot (.prim p) → SVal.prim pv = .prim (dfltV p)) →
      (op = .push ∨ ∃ p, op = .slot (.prim p)) → Sim (atNew.eval σ) ((SVal.prim pv).findLive r >>= G)) :
    Sim ((arrKey op L k old opq atNew).eval σ) (c'.findLive (.at i :: r) >>= G) := by
  cases op with
  | push =>
    cases c with
    | array es sh fx =>
      simp only [AOp.apply] at hap; cases hap
      have hL' : L.eval σ = .ok (.int es.length) := (hL _).2 rfl
      simp only [arrKey, kite_eval hk hL', findLive_grow es sh _ fx _ i r]
      split
      · cases wv with
        | int n => exact hnew (.int n) (fun _ => rfl) (fun _ h => by cases h) (.inl rfl)
        | bool b => exact hnew (.bool b) (fun _ => rfl) (fun _ h => by cases h) (.inl rfl)
      · exact hold
    | prim _ | struct _ | map _ _ => simp only [AOp.apply, reduceCtorEq] at hap
  | slot E =>
    cases c with
    | array es sh fx =>
      simp only [AOp.apply] at hap; cases hap
      have hL' : L.eval σ = .ok (.int es.length) := (hL _).2 rfl
      cases E with
      | prim p =>
        simp only [arrKey, kite_eval hk hL', findLive_grow es sh _ fx _ i r, pushSlot_prim]
        split
        · exact hnew (dfltV p) (fun h => by cases h) (fun _ h => by cases h; rfl) (.inr ⟨p, rfl⟩)
        · exact hold
      | ref R =>
        simp only [arrKey]
        exact hopq
    | prim _ | struct _ | map _ _ => simp only [AOp.apply, reduceCtorEq] at hap
  | pop keep =>
    obtain ⟨es, last, sh, fx, sh', rfl, rfl⟩ := AOp.apply_pop hap
    have hL' : L.eval σ = .ok (.int (es ++ [last]).length) := (hL _).2 rfl
    have hP : (lenPred L).eval σ = .ok (.int es.length) := by
      rw [lenPred_eval hL']; simp only [List.length_append, List.length_cons, List.length_nil,
          Nat.zero_add, Int.natCast_add, Int.cast_ofNat_Int, Int.add_sub_cancel]
    simp only [arrKey, kite_eval hk hP, findLive_shrink es sh sh' fx last i r]
    split
    · exact Sim.halt (by simp only [LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
        implies_true]) (by simp only [Res.error_bind, ne_eq, reduceCtorEq, not_false_eq_true,
            implies_true])
    · exact hold

theorem below_cases {σ : State} {rest : List SSeg} {f : Seg} {r : List Seg}
    (h : segsEval σ rest = .ok (f :: r)) :
    (∃ g rest', rest = .field g :: rest') ∨
      ∃ k rest' i, rest = .key k :: rest' ∧ (k.eval σ >>= Value.asInt) = .ok i ∧ f = .at i ∧
        segsEval σ rest' = .ok r := by
  cases rest with
  | nil => simp only [segsEval, Except.ok.injEq, List.nil_eq, reduceCtorEq] at h
  | cons x rest' =>
    cases x with
    | field g => exact .inl ⟨g, rest', rfl⟩
    | key k =>
      obtain ⟨i, hi, h⟩ := Res.bind_eq_ok.1 h
      obtain ⟨r', hr', he⟩ := Res.bind_eq_ok.1 h
      cases he
      exact .inr ⟨k, rest', i, rfl, hi, rfl, hr'⟩

theorem segsEval_isEmpty {σ : State} : ∀ {xs : List SSeg} {ys : List Seg},
    segsEval σ xs = .ok ys → (xs.isEmpty = true ↔ ys = [])
  | [], ys, h => by cases h; simp only [List.isEmpty_nil]
  | .field f :: xs, ys, h => by
    obtain ⟨_, _, he⟩ := Res.bind_eq_ok.1 h; cases he; simp only [List.isEmpty_cons,
        Bool.false_eq_true, reduceCtorEq]
  | .key k :: xs, ys, h => by
    obtain ⟨_, _, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨_, _, he⟩ := Res.bind_eq_ok.1 h; cases he; simp only [List.isEmpty_cons,
        Bool.false_eq_true, reduceCtorEq]

theorem segsEval_lead {σ : State} : ∀ {xs : List SSeg} {ys : List Seg},
    segsEval σ xs = .ok ys → xs.any SSeg.isKey = false → ys = leadFields xs
  | [], ys, h, _ => by cases h; rfl
  | .field f :: xs, ys, h, hk => by
    obtain ⟨ys', h', he⟩ := Res.bind_eq_ok.1 h; cases he
    simp only [segsEval_lead h' (by simpa only [List.any_eq_false, SSeg.isKey, Bool.not_eq_true,
        List.any_cons, Bool.false_or] using hk), leadFields]
  | .key _ :: _, _, _, hk => by simp only [List.any_cons, SSeg.isKey, Bool.true_or,
      Bool.true_eq_false] at hk

/-- Below a word: what a read finds at its end, nothing past it. -/
theorem prim_leaf_sim {σ : State} {pv : PrimVal} {t : List Seg} {rest : List SSeg}
    {G : SVal → Res Value} {a : LTerm} (hemp : rest.isEmpty = true ↔ t = [])
    (ha : Sim (a.eval σ) (G (.prim pv))) :
    Sim ((if rest.isEmpty then a else .err).eval σ) ((SVal.prim pv).findLive t >>= G) := by
  by_cases ht : t = []
  · subst ht
    rw [if_pos (hemp.2 rfl)]
    simpa only [SVal.findLive] using ha
  · rw [if_neg (fun h => ht (hemp.1 h))]
    obtain ⟨f, t', rfl⟩ := List.exists_cons_of_ne_nil ht
    exact Sim.halt (by simp only [LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
        implies_true]) (by simp only [find_prim_cons, Res.error_bind, ne_eq, reduceCtorEq,
            not_false_eq_true, implies_true])

/-- Below a word, where only a location would do. -/
theorem prim_err_sim {σ : State} {pv : PrimVal} {t : List Seg} {G : SVal → Res Value}
    (hG : ∀ p x, G (.prim p) ≠ .ok x) :
    Sim (LTerm.err.eval σ) ((SVal.prim pv).findLive t >>= G) := by
  refine Sim.halt (by simp only [LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
      implies_true]) fun x hx => ?_
  cases t with
  | nil => exact hG pv x (by simpa only [SVal.findLive] using hx)
  | cons f t' => simp only [find_prim_cons, Res.error_bind, reduceCtorEq] at hx

theorem arrRead_sim {σ : State} {op : AOp} {wv : Value} {w L old opq : LTerm}
    {slot : List SSeg → LTerm} {v c c' u : SVal} {ps qs : List Seg}
    (hc : v.findLive ps = .ok c) (hap : op.apply wv c = .ok c') (hu : v.saveLive ps c' = .ok u)
    (hw : w.eval σ = .ok wv) (hL : Sim (L.eval σ) (Close.arrLen c))
    (hold : Sim (old.eval σ) (v.findLive qs >>= SVal.asValue))
    (hopq : Sim (opq.eval σ) (u.findLive qs >>= SVal.asValue))
    (hslot : ∀ es sh fx R, c = .array es sh fx → op = .slot (.ref R) → ∀ rest r,
      segsEval σ rest = .ok r →
      Sim (opq.eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue) →
      Sim ((slot rest).eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue))
    (r : PathRel) (hr : r.Holds σ ps qs) :
    Sim ((arrRead op w L old opq slot r).eval σ) (u.findLive qs >>= SVal.asValue) := by
  cases r with
  | eq =>
    simp only [PathRel.Holds] at hr; subst hr
    obtain ⟨es, sh, fx, es', sh', -, rfl, -⟩ := AOp.apply_ok hap
    refine Sim.halt (by simp only [arrRead, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
        implies_true]) ?_
    simp only [findLive_saveLive_same hu, Res.ok_bind, SVal.asValue, ne_eq, reduceCtorEq,
        not_false_eq_true, implies_true]
  | above =>
    obtain ⟨f, t, rfl⟩ := hr
    obtain ⟨_, w', _, hs', hf⟩ := save_through qs (f :: t) hu
    obtain ⟨e, he⟩ := save_cons_asValue hs'
    refine Sim.halt (by simp only [arrRead, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
        implies_true]) ?_
    simp only [hf, Res.ok_bind, he, ne_eq, reduceCtorEq, not_false_eq_true, implies_true]
  | diverge => rw [findLive_saveLive_diverge hr hu]; exact hold
  | below rest =>
    obtain ⟨f, t, rfl, hrest⟩ := hr
    rcases below_cases hrest with ⟨g, rest', rfl⟩ | ⟨k, rest', i, rfl, hk, rfl, hr'⟩
    · exact hopq
    · simp only [arrRead]
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind] at hopq ⊢
      rw [SVal.findLive_append, hc, Res.ok_bind] at hold
      by_cases hop : ∃ R, op = .slot (.ref R)
      · obtain ⟨R, rfl⟩ := hop
        cases c with
        | array es sh fx =>
          simp only [AOp.apply] at hap; cases hap
          have hL' : L.eval σ = .ok (.int es.length) := (hL _).2 rfl
          simp only [kite_eval hk hL']
          rw [findLive_grow es sh _ fx _ i t] at hopq ⊢
          by_cases hi : i = es.length
          · rw [if_pos hi] at hopq
            rw [if_pos hi, if_pos hi]
            exact hslot es sh fx R rfl rfl rest' t hr' hopq
          · rw [if_neg hi, if_neg hi]
            exact hold
        | prim _ | struct _ | map _ _ => simp only [AOp.apply, reduceCtorEq] at hap
      · split
        · rename_i R; exact absurd ⟨R, rfl⟩ hop
        refine arrKey_sim hap hk hL hold hopq fun pv h1 h2 h3 => ?_
        have hemp := segsEval_isEmpty hr'
        rcases h3 with rfl | ⟨p, rfl⟩
        · refine prim_leaf_sim hemp (Sim.of_eq ?_)
          rw [h1 rfl, Close.asValue_toSVal, hw]
        · refine prim_leaf_sim hemp (Sim.of_eq ?_)
          rw [h2 p rfl]
          cases p <;> rfl

theorem arrHas_sim {σ : State} {op : AOp} {wv : Value} {L old opq : LTerm} {v c c' u : SVal}
    {ps qs : List Seg}
    (hc : v.findLive ps = .ok c) (hap : op.apply wv c = .ok c') (hu : v.saveLive ps c' = .ok u)
    (hL : Sim (L.eval σ) (Close.arrLen c))
    (hold : Sim (old.eval σ) (v.findLive qs >>= fun _ => .ok (.bool true)))
    (hopq : Sim (opq.eval σ) (u.findLive qs >>= fun _ => .ok (.bool true)))
    (r : PathRel) (hr : r.Holds σ ps qs) :
    Sim ((arrHas op L old opq r).eval σ) (u.findLive qs >>= fun _ => .ok (.bool true)) := by
  cases r with
  | eq =>
    simp only [PathRel.Holds] at hr; subst hr
    exact Sim.of_eq (by simp only [arrHas, LTerm.eval, findLive_saveLive_same hu, Res.ok_bind])
  | above =>
    obtain ⟨f, t, rfl⟩ := hr
    obtain ⟨_, w', _, _, hf⟩ := save_through qs (f :: t) hu
    exact Sim.of_eq (by simp only [arrHas, LTerm.eval, hf, Res.ok_bind])
  | diverge => rw [findLive_saveLive_diverge hr hu]; exact hold
  | below rest =>
    obtain ⟨f, t, rfl, hrest⟩ := hr
    rcases below_cases hrest with ⟨g, rest', rfl⟩ | ⟨k, rest', i, rfl, hk, rfl, hr'⟩
    · exact hopq
    · simp only [arrHas]
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind] at hopq ⊢
      rw [SVal.findLive_append, hc, Res.ok_bind] at hold
      by_cases hop : ∃ R, op = .slot (.ref R)
      · obtain ⟨R, rfl⟩ := hop
        simp only
        split
        · rename_i hemp
          have ht : t = [] := (segsEval_isEmpty hr').1 hemp
          subst ht
          cases c with
          | array es sh fx =>
            simp only [AOp.apply] at hap; cases hap
            have hL' : L.eval σ = .ok (.int es.length) := (hL _).2 rfl
            obtain ⟨x, hx, hxi⟩ := Res.bind_eq_ok.1 hk
            cases x with
            | bool b => simp only [Value.asInt, reduceCtorEq] at hxi
            | int j =>
              simp only [Value.asInt, Except.ok.injEq] at hxi
              subst hxi
              have hT : (inRange k L).eval σ =
                  (if 0 ≤ j ∧ j ≤ es.length then (.ok (.bool true) : Res Value) else .error .stuck) := by
                simp only [inRange, LTerm.eval, hx, hL', evalBinop, applyBinOp, Value.asInt,
                  Value.asBool, checkArith, pickBranch, bind, Except.bind, pure, Except.pure]
                by_cases h0 : 0 ≤ j <;> by_cases h1 : j ≤ (es.length : Int) <;>
                  simp only [h0, decide_true, h1, Bool.and_self, and_self, ↓reduceIte,
                      decide_false, Bool.and_false, and_false, and_true]
              have hR : ((SVal.array (es ++ [(pushSlot (Ty.ref R) sh).1]) (pushSlot (Ty.ref R) sh).2
                  fx).findLive [.at j] >>= fun _ => .ok (.bool true)) =
                  (if 0 ≤ j ∧ j ≤ es.length then (.ok (.bool true) : Res Value) else .error .revert) := by
                simp only [SVal.findLive, List.length_append, List.length_singleton]
                by_cases hj : 0 ≤ j ∧ j ≤ es.length
                · have hj' : 0 ≤ j ∧ j.toNat < es.length + 1 := ⟨hj.1, by omega⟩
                  simp only [hj', and_self, ↓reduceDIte, List.get_eq_getElem, Res.ok_bind, hj,
                      ↓reduceIte]
                · have hj' : ¬(0 ≤ j ∧ j.toNat < es.length + 1) := by omega
                  rw [dif_neg hj', if_neg hj]; rfl
              rw [hT, hR]
              split
              · exact Sim.refl _
              · exact Sim.halt (by simp only [ne_eq, reduceCtorEq, not_false_eq_true,
                  implies_true]) (by simp only [ne_eq, reduceCtorEq, not_false_eq_true,
                      implies_true])
          | prim _ | struct _ | map _ _ => simp only [AOp.apply, reduceCtorEq] at hap
        · exact hopq
      · split
        · rename_i R; exact absurd ⟨R, rfl⟩ hop
        exact arrKey_sim hap hk hL hold hopq fun pv _ _ _ =>
          prim_leaf_sim (segsEval_isEmpty hr') (Sim.of_eq rfl)

theorem arrLength_sim {σ : State} {op : AOp} {wv : Value} {L old opq : LTerm} {v c c' u : SVal}
    {ps qs : List Seg}
    (hc : v.findLive ps = .ok c) (hap : op.apply wv c = .ok c') (hu : v.saveLive ps c' = .ok u)
    (hL : Sim (L.eval σ) (Close.arrLen c))
    (hold : Sim (old.eval σ) (v.findLive qs >>= Close.arrLen))
    (hopq : Sim (opq.eval σ) (u.findLive qs >>= Close.arrLen))
    {slot : Option (List SSeg → LTerm)}
    (hslot : ∀ f, slot = some f → ∀ es sh fx R, c = .array es sh fx → op = .slot (.ref R) →
      ∀ rest r, segsEval σ rest = .ok r →
      Sim (opq.eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= Close.arrLen) →
      Sim ((f rest).eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= Close.arrLen))
    (r : PathRel) (hr : r.Holds σ ps qs) :
    Sim ((arrLength op L old opq slot r).eval σ) (u.findLive qs >>= Close.arrLen) := by
  cases r with
  | eq =>
    simp only [PathRel.Holds] at hr; subst hr
    obtain ⟨es, sh, fx, es', sh', rfl, rfl, hlen⟩ := AOp.apply_ok hap
    have hL' : L.eval σ = .ok (.int es.length) := (hL _).2 rfl
    simp only [findLive_saveLive_same hu, Res.ok_bind, Close.arrLen]
    cases op with
    | push | slot _ =>
      simp only [arrLength, lenSucc_eval hL']
      exact Sim.of_eq (by rw [hlen])
    | pop _ =>
      simp only [arrLength, lenPred_eval hL']
      exact Sim.of_eq (by rw [hlen])
  | above =>
    obtain ⟨f, t, rfl⟩ := hr
    obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu
    simp only [arrLength, hf, Res.ok_bind, save_cons_arrLen hs']
    rw [hw₀, Res.ok_bind] at hold
    exact hold
  | diverge => rw [findLive_saveLive_diverge hr hu]; exact hold
  | below rest =>
    obtain ⟨f, t, rfl, hrest⟩ := hr
    rcases below_cases hrest with ⟨g, rest', rfl⟩ | ⟨k, rest', i, rfl, hk, rfl, hr'⟩
    · exact hopq
    · simp only [arrLength]
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind] at hopq ⊢
      rw [SVal.findLive_append, hc, Res.ok_bind] at hold
      by_cases hop : ∃ R f, op = .slot (.ref R) ∧ slot = some f
      · obtain ⟨R, f, rfl, rfl⟩ := hop
        cases c with
        | array es sh fx =>
          simp only [AOp.apply] at hap; cases hap
          have hL' : L.eval σ = .ok (.int es.length) := (hL _).2 rfl
          simp only [kite_eval hk hL']
          rw [findLive_grow es sh _ fx _ i t] at hopq ⊢
          by_cases hi : i = es.length
          · rw [if_pos hi] at hopq
            rw [if_pos hi, if_pos hi]
            exact hslot f rfl es sh fx R rfl rfl rest' t hr' hopq
          · rw [if_neg hi, if_neg hi]
            exact hold
        | prim _ | struct _ | map _ _ => simp only [AOp.apply, reduceCtorEq] at hap
      · split
        · rename_i R f; exact absurd ⟨R, f, rfl, rfl⟩ hop
        exact arrKey_sim hap hk hL hold hopq fun pv _ _ _ =>
          prim_err_sim fun p x h => by simp only [Close.arrLen, reduceCtorEq] at h

theorem arrMap_sim {σ : State} {op : AOp} {wv : Value} {sh : KShape} {L old opq : LTerm}
    {v c c' u : SVal} {ps qs : List Seg}
    (hc : v.findLive ps = .ok c) (hap : op.apply wv c = .ok c') (hu : v.saveLive ps c' = .ok u)
    (hL : Sim (L.eval σ) (Close.arrLen c))
    (hold : Sim (old.eval σ) (v.findLive qs >>= sh.test))
    (hopq : Sim (opq.eval σ) (u.findLive qs >>= sh.test))
    (r : PathRel) (hr : r.Holds σ ps qs) :
    Sim ((arrMap op L old opq r).eval σ) (u.findLive qs >>= sh.test) := by
  cases r with
  | eq =>
    simp only [PathRel.Holds] at hr; subst hr
    obtain ⟨es, sh₀, fx, es', sh', rfl, rfl, -⟩ := AOp.apply_ok hap
    simp only [arrMap, findLive_saveLive_same hu, Res.ok_bind]
    rw [hc, Res.ok_bind] at hold
    cases sh <;> exact hold
  | above =>
    obtain ⟨f, t, rfl⟩ := hr
    obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu
    simp only [arrMap, hf, Res.ok_bind, save_cons_kmapF hs']
    rw [hw₀, Res.ok_bind] at hold
    exact hold
  | diverge => rw [findLive_saveLive_diverge hr hu]; exact hold
  | below rest =>
    obtain ⟨f, t, rfl, hrest⟩ := hr
    rcases below_cases hrest with ⟨g, rest', rfl⟩ | ⟨k, rest', i, rfl, hk, rfl, hr'⟩
    · exact hopq
    · simp only [arrMap]
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind] at hopq ⊢
      rw [SVal.findLive_append, hc, Res.ok_bind] at hold
      exact arrKey_sim hap hk hL hold hopq fun pv _ _ _ =>
        prim_err_sim fun p x h => by cases sh <;> simp only [KShape.test, kmapF, isMapV,
            Bool.false_eq_true, ↓reduceIte, reduceCtorEq, isFixV] at h

/-- No location the read passes an index at is a mapping: what a copy's read
below a key needs to read the source (a mapping met keeps the target's
entries). -/
def NoMapAlong (y : SVal) (segs : List Seg) : Prop :=
  ∀ pre i rest, segs = pre ++ .at i :: rest → ∀ w, y.findLive pre = .ok w → isMapV w = false

theorem overlay_prim_eq (c : SVal) (p : PrimVal) : c.overlay (.prim p) = .prim p := by
  cases c <;> rfl

theorem lookupBy_overlayFields' (ofs : List (Name × SVal)) (f : Name) :
    ∀ ns : List (Name × SVal), lookupBy f (SVal.overlay.overlayFields ofs ns) =
      (lookupBy f ns).map (fun v => match lookupBy f ofs with
        | some o => o.overlay v
        | none => v.strip)
  | [] => rfl
  | (n, w) :: tl => by
    simp only [SVal.overlay.overlayFields, lookupBy]
    split
    · rename_i h; subst h; rfl
    · exact lookupBy_overlayFields' ofs f tl

theorem lookupBy_stripFields (f : Name) : ∀ ns : List (Name × SVal),
    lookupBy f (SVal.strip.stripFields ns) = (lookupBy f ns).map SVal.strip
  | [] => rfl
  | (n, w) :: tl => by
    simp only [SVal.strip.stripFields, lookupBy]
    split
    · rfl
    · exact lookupBy_stripFields f tl

theorem overlayElems_getElem : ∀ (os ns : List SVal) (i : Nat) (h : i < ns.length)
    (h' : i < (SVal.overlay.overlayElems os ns).length),
    ∃ c : SVal, (SVal.overlay.overlayElems os ns)[i] = c.overlay ns[i]
  | o :: os, n :: ns, 0, _, _ => ⟨o, rfl⟩
  | o :: os, n :: ns, i + 1, h, h' => by
    simp only [SVal.overlay.overlayElems, List.getElem_cons_succ]
    exact overlayElems_getElem os ns i (by simpa only [List.length_cons,
        Nat.add_lt_add_iff_right] using h) (by simpa only [SVal.overlay.overlayElems,
            List.length_cons, Nat.add_lt_add_iff_right] using h')
  | [], ns, i, h, h' => by
    simp only [SVal.overlay.overlayElems]
    exact ⟨.prim (.int 0), by rw [prim_overlay]; exact stripElems_getElem ns i h⟩
  | _ :: _, [], i, h, _ => absurd h (by simp only [List.length_nil, Nat.not_lt_zero,
      not_false_eq_true])
where
  stripElems_getElem : ∀ (ns : List SVal) (i : Nat) (h : i < ns.length),
      (SVal.strip.stripElems ns)[i]'(by rw [Close.stripElems_length]; exact h) = ns[i].strip
    | n :: ns, 0, _ => rfl
    | n :: ns, i + 1, h => by
      simp only [SVal.strip.stripElems, List.getElem_cons_succ]
      exact stripElems_getElem ns i (by simpa only [List.length_cons,
          Nat.add_lt_add_iff_right] using h)

theorem NoMapAlong.field {y w : SVal} {f : Name} {r : List Seg} (h : NoMapAlong y (.field f :: r))
    (hw : y.findLive [.field f] = .ok w) : NoMapAlong w r := by
  intro pre i rest he w' hw'
  apply h (.field f :: pre) i rest (by simp only [he, List.cons_append])
  rw [show Seg.field f :: pre = [Seg.field f] ++ pre from rfl, SVal.findLive_append, hw,
    Res.ok_bind, hw']

theorem NoMapAlong.at {y w : SVal} {i : Int} {r : List Seg} (h : NoMapAlong y (.at i :: r))
    (hw : y.findLive [.at i] = .ok w) : NoMapAlong w r := by
  intro pre j rest he w' hw'
  apply h (.at i :: pre) j rest (by simp only [he, List.cons_append])
  rw [show Seg.at i :: pre = [Seg.at i] ++ pre from rfl, SVal.findLive_append, hw,
    Res.ok_bind, hw']

/-- **A copy read below keys reads the source**, where no location the
read passes a key at is a mapping. -/
theorem overlay_findLive_nomap {G : SVal → Res Value} (hG : ∀ c y : SVal, G (c.overlay y) = G y) :
    ∀ (segs : List Seg) (c y : SVal), NoMapAlong y segs →
      ((c.overlay y).findLive segs >>= G) = (y.findLive segs >>= G)
  | [], c, y, _ => by simp only [SVal.findLive_nil, Res.ok_bind, hG]
  | .field f :: r, c, y, hy => by
    cases y with
    | prim p => rw [overlay_prim_eq]
    | map ne nd => cases c <;> simp only [SVal.overlay, SVal.strip, SVal.findLive]
    | struct nfs =>
      cases hl : lookupBy f nfs with
      | none =>
        cases c <;> simp only [SVal.overlay, SVal.strip, SVal.findLive, lookupBy_stripFields, hl,
            Option.map_none, lookupBy_overlayFields']
      | some w =>
        have hw : (SVal.struct nfs).findLive [.field f] = .ok w := by
          simp only [SVal.findLive, hl, SVal.findLive_nil]
        have hy' := hy.field hw
        have hyr : (SVal.struct nfs).findLive (.field f :: r) = w.findLive r := by
          simp only [SVal.findLive, hl]
        rw [hyr]
        cases c with
        | struct ofs =>
          simp only [SVal.overlay, SVal.findLive, lookupBy_overlayFields', hl, Option.map_some]
          split
          · exact overlay_findLive_nomap hG r _ w hy'
          · rw [← prim_overlay (.int 0)]; exact overlay_findLive_nomap hG r _ w hy'
        | prim _ | array _ _ _ | map _ _ =>
          simp only [SVal.overlay, SVal.strip, SVal.findLive, lookupBy_stripFields, hl,
            Option.map_some]
          rw [← prim_overlay (.int 0)]; exact overlay_findLive_nomap hG r _ w hy'
    | array nel nsh nfx =>
      by_cases hf : f = "length"
      · subst hf
        cases c <;> simp only [SVal.overlay, SVal.strip, SVal.findLive, Close.stripElems_length,
            overlayElems_length]
      · cases c <;> simp only [SVal.overlay, SVal.strip, SVal.findLive]
  | .at i :: r, c, y, hy => by
    have hm := hy [] i r rfl y (by cases y <;> rfl)
    cases y with
    | prim p => rw [overlay_prim_eq]
    | map ne nd => simp only [isMapV, Bool.true_eq_false] at hm
    | struct nfs => cases c <;> simp only [SVal.overlay, SVal.strip, SVal.findLive]
    | array nel nsh nfx =>
      have hlen : ∀ os, (SVal.overlay.overlayElems os nel).length = nel.length :=
        fun os => overlayElems_length os nel
      by_cases hi : 0 ≤ i ∧ i.toNat < nel.length
      · have hw : (SVal.array nel nsh nfx).findLive [.at i] = .ok nel[i.toNat] := by
          simp only [SVal.findLive, hi, and_self, ↓reduceDIte, List.get_eq_getElem,
              SVal.findLive_nil]
        have hy' := hy.at hw
        have hyr : (SVal.array nel nsh nfx).findLive (.at i :: r) = nel[i.toNat].findLive r := by
          simp only [SVal.findLive, hi, and_self, ↓reduceDIte, List.get_eq_getElem]
        rw [hyr]
        cases c with
        | array oel osh ofx =>
          have hi' : 0 ≤ i ∧ i.toNat < (SVal.overlay.overlayElems (oel ++ osh) nel).length := by
            rw [hlen]; exact hi
          obtain ⟨c', hc'⟩ := overlayElems_getElem (oel ++ osh) nel i.toNat hi.2 hi'.2
          simp only [SVal.overlay, SVal.findLive, dif_pos hi', List.get_eq_getElem, hc']
          exact overlay_findLive_nomap hG r c' _ hy'
        | prim _ | struct _ | map _ _ =>
          have hi' : 0 ≤ i ∧ i.toNat < (SVal.strip.stripElems nel).length := by
            rw [Close.stripElems_length]; exact hi
          simp only [SVal.overlay, SVal.strip, SVal.findLive, dif_pos hi', List.get_eq_getElem,
            overlayElems_getElem.stripElems_getElem nel i.toNat hi.2]
          rw [← prim_overlay (.int 0)]; exact overlay_findLive_nomap hG r _ _ hy'
      · have hyr : (SVal.array nel nsh nfx).findLive (.at i :: r) = .error .revert := by
          simp only [SVal.findLive, hi, ↓reduceDIte]
        rw [hyr]
        cases c with
        | array oel osh ofx =>
          have hi' : ¬(0 ≤ i ∧ i.toNat < (SVal.overlay.overlayElems (oel ++ osh) nel).length) := by
            rw [hlen]; exact hi
          simp only [SVal.overlay, SVal.findLive, hi', ↓reduceDIte]
        | prim _ | struct _ | map _ _ =>
          have hi' : ¬(0 ≤ i ∧ i.toNat < (SVal.strip.stripElems nel).length) := by
            rw [Close.stripElems_length]; exact hi
          simp only [SVal.overlay, SVal.strip, SVal.findLive, hi', ↓reduceDIte]

theorem NoMapAlong.nil (y : SVal) : NoMapAlong y [] := by
  intro pre i rest he
  cases pre <;> simp only [List.nil_append, List.nil_eq, reduceCtorEq, List.cons_append] at he

theorem NoMapAlong.snoc_field {y : SVal} {p : List Seg} (f : Name) (h : NoMapAlong y p) :
    NoMapAlong y (p ++ [.field f]) := by
  intro pre i rest he w hw
  obtain ⟨rest', rfl⟩ : ∃ rest', p = pre ++ .at i :: rest' := by
    rcases List.eq_nil_or_concat rest with rfl | ⟨r', x, rfl⟩
    · have := congrArg List.getLast? he
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq,
          reduceCtorEq] at this
    · refine ⟨r', ?_⟩
      have := he
      simp only [List.concat_eq_append] at this
      rw [show pre ++ Seg.at i :: (r' ++ [x]) = (pre ++ Seg.at i :: r') ++ [x] by
        simp only [List.append_assoc, List.cons_append]] at this
      exact (List.append_inj' this rfl).1
  exact h pre i rest' rfl w hw

theorem NoMapAlong.snoc_at {y : SVal} {p : List Seg} (i : Int) (h : NoMapAlong y p)
    (hp : ∀ w, y.findLive p = .ok w → isMapV w = false) : NoMapAlong y (p ++ [.at i]) := by
  intro pre j rest he w hw
  rcases List.eq_nil_or_concat rest with rfl | ⟨r', x, rfl⟩
  · have := List.append_inj' he rfl
    obtain ⟨rfl, -⟩ := this
    exact hp w hw
  · have h' := he
    simp only [List.concat_eq_append] at h'
    rw [show pre ++ Seg.at j :: (r' ++ [x]) = (pre ++ Seg.at j :: r') ++ [x] by
      simp only [List.append_assoc, List.cons_append]] at h'
    exact h pre j r' (List.append_inj' h' rfl).1 w hw

/-- **A read below a copy reads the source**, key by key: where the
source has a mapping at a key, the read is kept whole. -/
theorem copyKeys_sim {σ : State} {G : SVal → Res Value} (hG : ∀ c y : SVal, G (c.overlay y) = G y)
    {sv n cur u : SVal} {ps sqs full : List Seg} {srcMap F : List SSeg → LTerm} {opq : LTerm}
    (hn : sv.findLive sqs = .ok n) (hu : u.findLive ps = .ok (cur.overlay n))
    (hM : ∀ pre rs, segsEval σ pre = .ok rs →
      Sim ((srcMap pre).eval σ) (sv.findLive (sqs ++ rs) >>= KShape.map.test))
    (hF : ∀ rest rs, segsEval σ rest = .ok rs → Sim ((F rest).eval σ) (sv.findLive (sqs ++ rs) >>= G))
    (hopq : Sim (opq.eval σ) (u.findLive (ps ++ full) >>= G)) :
    ∀ (r pre : List SSeg) (preS rS : List Seg), segsEval σ pre = .ok preS →
      segsEval σ r = .ok rS → full = preS ++ rS → NoMapAlong n preS →
        Sim ((copyKeys srcMap opq F pre r).eval σ) (u.findLive (ps ++ full) >>= G)
  | [], pre, preS, rS, hpre, hr, hfull, hnm => by
    cases hr
    simp only [List.append_nil] at hfull
    rw [hfull]
    simp only [copyKeys]
    have h := hF pre preS hpre
    rw [SVal.findLive_append, hn, Res.ok_bind, ← overlay_findLive_nomap hG preS cur n hnm] at h
    rw [SVal.findLive_append, hu, Res.ok_bind]
    exact h
  | .field f :: r, pre, preS, rS, hpre, hr, hfull, hnm => by
    obtain ⟨rS', hr', he⟩ := Res.bind_eq_ok.1 hr
    cases he
    simp only [copyKeys]
    exact copyKeys_sim hG hn hu hM hF hopq r (pre ++ [.field f]) (preS ++ [.field f]) rS'
      (segsEval_append σ hpre rfl) hr' (by simp only [hfull, List.append_assoc, List.cons_append,
          List.nil_append]) (hnm.snoc_field f)
  | .key k :: r, pre, preS, rS, hpre, hr, hfull, hnm => by
    obtain ⟨i, hi, hr⟩ := Res.bind_eq_ok.1 hr
    obtain ⟨rS', hr', he⟩ := Res.bind_eq_ok.1 hr
    cases he
    simp only [copyKeys]
    have hm := hM pre preS hpre
    rw [SVal.findLive_append, hn, Res.ok_bind] at hm
    by_cases hmap : ∃ w, n.findLive preS = .ok w ∧ isMapV w = true
    · obtain ⟨w, hw, hwm⟩ := hmap
      have hmt : (srcMap pre).eval σ = .ok (.bool true) := by
        apply (hm _).2
        rw [hw, Res.ok_bind]
        simp only [KShape.test, kmapF, hwm, ↓reduceIte]
      simp only [LTerm.eval, isT_eval, hmt, Res.ok_bind, pickBranch]
      exact hopq
    · have hmt : ∀ x, (srcMap pre).eval σ ≠ .ok x := by
        intro x hx
        have := (hm x).1 hx
        obtain ⟨w, hw, ht⟩ := Res.bind_eq_ok.1 this
        simp only [KShape.test, kmapF] at ht
        split at ht
        · exact hmap ⟨w, hw, ‹_›⟩
        · cases ht
      have hfalse : (isT (srcMap pre)).eval σ = .ok (.bool false) := by
        rw [isT_eval]
        cases hh : (srcMap pre).eval σ with
        | ok x => exact absurd hh (hmt x)
        | error _ => rfl
      simp only [LTerm.eval, hfalse, Res.ok_bind, pickBranch]
      refine copyKeys_sim hG hn hu hM hF hopq r (pre ++ [.key k]) (preS ++ [.at i]) rS'
        (segsEval_append σ hpre (by simp only [segsEval, hi, Res.ok_bind])) hr'
        (by simp only [hfull, List.append_assoc, List.cons_append,
            List.nil_append]) (hnm.snoc_at i fun w hw => ?_)
      cases hb : isMapV w with
      | false => rfl
      | true => exact absurd ⟨w, hw, hb⟩ hmap

theorem copyLeaf_sim {σ : State} {G : SVal → Res Value} (hG : ∀ c y : SVal, G (c.overlay y) = G y)
    {v sv cur n u : SVal} {ps qs sqs : List Seg} {SQ : LPath} {atEq aboveV old opq : LTerm}
    {srcMap F : List SSeg → LTerm}
    (hn : sv.findLive sqs = .ok n) (hsq : SQ.eval σ = .ok sqs)
    (hu : v.saveLive ps (cur.overlay n) = .ok u)
    (heq : Sim (atEq.eval σ) (G n))
    (habove : ∀ f t, ps = qs ++ f :: t → Sim (aboveV.eval σ) (u.findLive qs >>= G))
    (hold : Sim (old.eval σ) (v.findLive qs >>= G))
    (hopq : Sim (opq.eval σ) (u.findLive qs >>= G))
    (hM : ∀ pre q', (SQ.addSegs pre).eval σ = .ok q' →
      Sim ((srcMap pre).eval σ) (sv.findLive q' >>= KShape.map.test))
    (hF : ∀ rest q', (SQ.addSegs rest).eval σ = .ok q' →
      Sim ((F rest).eval σ) (sv.findLive q' >>= G))
    (r : PathRel) (hr : r.Holds σ ps qs) :
    Sim ((copyLeaf atEq aboveV old opq srcMap F r).eval σ) (u.findLive qs >>= G) := by
  cases r with
  | eq =>
    simp only [PathRel.Holds] at hr; subst hr
    simp only [copyLeaf, findLive_saveLive_same hu, Res.ok_bind, hG]
    exact heq
  | above =>
    obtain ⟨f, t, rfl⟩ := hr
    exact habove f t rfl
  | diverge => rw [findLive_saveLive_diverge hr hu]; exact hold
  | below rest =>
    obtain ⟨f, t, rfl, hrest⟩ := hr
    simp only [copyLeaf]
    have hseg : ∀ xs rs, segsEval σ xs = .ok rs → (SQ.addSegs xs).eval σ = .ok (sqs ++ rs) := by
      intro xs rs h; rw [LPath.addSegs_eval, hsq, Res.ok_bind, h, Res.ok_bind]
    exact copyKeys_sim hG hn (findLive_saveLive_same hu)
      (fun pre rs h => hM pre _ (hseg pre rs h)) (fun rest rs h => hF rest _ (hseg rest rs h))
      hopq rest [] [] (f :: t) rfl hrest rfl (NoMapAlong.nil n)

theorem copy_eval_ok {σ : State} {s src : LStor} {P SQ : LPath} {u : SVal}
    (hu : (LStor.copy s P src SQ).eval σ = .ok u) :
    ∃ sv sqs n v ps cur, src.eval σ = .ok sv ∧ SQ.eval σ = .ok sqs ∧ sv.findLive sqs = .ok n ∧
      s.eval σ = .ok v ∧ P.eval σ = .ok ps ∧ v.findLive ps = .ok cur ∧
      v.saveLive ps (cur.overlay n) = .ok u := by
  simp only [LStor.eval, Res.bind_eq_ok] at hu
  obtain ⟨sv, h1, sqs, h2, n, h3, v, h4, ps, h5, cur, h6, h7⟩ := hu
  exact ⟨sv, sqs, n, v, ps, cur, h1, h2, h3, h4, h5, h6, h7⟩

theorem arr_eval_ok {σ : State} {op : AOp} {s : LStor} {P : LPath} {w : LTerm} {u : SVal}
    (hu : (LStor.arr op s P w).eval σ = .ok u) :
    ∃ wv v ps c c', w.eval σ = .ok wv ∧ s.eval σ = .ok v ∧ P.eval σ = .ok ps ∧
      v.findLive ps = .ok c ∧ op.apply wv c = .ok c' ∧ v.saveLive ps c' = .ok u := by
  simp only [LStor.eval, Res.bind_eq_ok] at hu
  obtain ⟨wv, h1, v, h2, ps, h3, c, h4, c', h5, h6⟩ := hu
  exact ⟨wv, v, ps, c, c', h1, h2, h3, h4, h5, h6⟩

/-- A term that is only sound, kept by an exact one beside it (`orElse`). -/
theorem orElse_sound_sim {a b y : Res Value} (ha : ∀ x, a = .ok x → y = .ok x) (hb : Sim b y) :
    Sim (orElseR a b) y := by
  intro z
  cases a with
  | ok x =>
    simp only [orElseR_ok]
    constructor
    · intro hz; cases hz; exact ha _ rfl
    · intro hz
      have h := ha x rfl
      rw [hz] at h
      cases h
      rfl
  | error e => simp only [orElseR_error]; exact hb z

theorem headR_ok {sh : List SVal} {c : SVal} (h : headR sh = .ok c) : ∃ t, sh = c :: t := by
  cases sh with
  | nil => cases h
  | cons c' t => cases h; exact ⟨t, rfl⟩

/-- The slot past the end, its length at `r`, as a run: strict, no slot no
length (`slotLenU`'s specification). -/
def slotLen (sh : List SVal) (r : List Seg) : Res Value :=
  headR sh >>= fun c => c.findLive r >>= Close.arrLen

/-- Where the slot has a length, a `push()` of an array recycles it. -/
theorem slotLen_pushSlot {sh : List SVal} {r : List Seg} {x : Value} (R : RefTy)
    (h : slotLen sh r = .ok x) : ((pushSlot (.ref R) sh).1.findLive r >>= Close.arrLen) = .ok x := by
  cases sh with
  | nil => simp only [slotLen, headR, Res.error_bind, reduceCtorEq] at h
  | cons c t =>
    simpa only [slotLen, headR, Res.ok_bind, pushSlot, Ty.isPrimitive, Bool.false_eq_true,
      ↓reduceIte] using h

section Wrappers

variable {σ : State} {s src : LStor} {P SQ Q : LPath} {u : SVal} {qs : List Seg}

theorem copy_readU_sim (hu : (LStor.copy s P src SQ).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ)) (hSQ : Sim (SQ.elim.eval σ) (SQ.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue))
    (ihS : ∀ (Q' : LPath) {v qs}, src.eval σ = .ok v → Q'.eval σ = .ok qs →
      Sim ((src.readU Q').eval σ) (v.findLive qs >>= SVal.asValue))
    (ihSM : ∀ (Q' : LPath) {v qs}, src.eval σ = .ok v → Q'.eval σ = .ok qs →
      Sim ((src.mapU .map Q').eval σ) (v.findLive qs >>= KShape.map.test)) :
    Sim (((LStor.copy s P src SQ).readU Q).eval σ) (u.findLive qs >>= SVal.asValue) := by
  obtain ⟨sv, sqs, n, v, ps, cur, hsv, hsq, hn, hv, hp, hc, hu'⟩ := copy_eval_ok hu
  have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
  have hsq' : SQ.elim.eval σ = .ok sqs := (hSQ sqs).2 hsq
  rw [LStor.readU]
  refine cmp_sim hp' hq fun r hr => copyLeaf_sim (G := SVal.asValue) overlay_asValue hn hsq' hu'
    ?_ ?_ (ihR hv hq) ?_ (fun pre q' hq' => ihSM _ hsv hq') (fun rest q' hq' => ihS _ hsv hq') r hr
  · have := ihS SQ.elim hsv hsq'; rwa [hn, Res.ok_bind] at this
  · intro f t he; subst he
    obtain ⟨_, w', _, hs', hf⟩ := save_through qs (f :: t) hu'
    obtain ⟨e, he⟩ := save_cons_asValue hs'
    exact Sim.halt (by simp only [LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
        implies_true]) (by simp only [hf, Res.ok_bind, he, ne_eq, reduceCtorEq, not_false_eq_true,
            implies_true])
  · exact Sim.of_eq (by simp only [LTerm.eval, hu, hq, Res.ok_bind])

theorem copy_hasU_sim (hu : (LStor.copy s P src SQ).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ)) (hSQ : Sim (SQ.elim.eval σ) (SQ.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.hasU Q).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true)))
    (ihS : ∀ (Q' : LPath) {v qs}, src.eval σ = .ok v → Q'.eval σ = .ok qs →
      Sim ((src.hasU Q').eval σ) (v.findLive qs >>= fun _ => .ok (.bool true)))
    (ihSM : ∀ (Q' : LPath) {v qs}, src.eval σ = .ok v → Q'.eval σ = .ok qs →
      Sim ((src.mapU .map Q').eval σ) (v.findLive qs >>= KShape.map.test)) :
    Sim (((LStor.copy s P src SQ).hasU Q).eval σ) (u.findLive qs >>= fun _ => .ok (.bool true)) := by
  obtain ⟨sv, sqs, n, v, ps, cur, hsv, hsq, hn, hv, hp, hc, hu'⟩ := copy_eval_ok hu
  have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
  have hsq' : SQ.elim.eval σ = .ok sqs := (hSQ sqs).2 hsq
  rw [LStor.hasU]
  refine cmp_sim hp' hq fun r hr => copyLeaf_sim (G := fun _ => .ok (.bool true))
    (fun _ _ => rfl) hn hsq' hu' (Sim.of_eq rfl) ?_ (ihR hv hq) ?_
    (fun pre q' hq' => ihSM _ hsv hq') (fun rest q' hq' => ihS _ hsv hq') r hr
  · intro f t he; subst he
    obtain ⟨_, w', _, _, hf⟩ := save_through qs (f :: t) hu'
    exact Sim.of_eq (by simp only [LTerm.eval, hf, Res.ok_bind])
  · exact Sim.of_eq (by simp only [LTerm.eval, hu, hq, Res.ok_bind])

theorem copy_lenU_sim (hu : (LStor.copy s P src SQ).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ)) (hSQ : Sim (SQ.elim.eval σ) (SQ.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.lenU Q).eval σ) (v.findLive qs >>= Close.arrLen))
    (ihS : ∀ (Q' : LPath) {v qs}, src.eval σ = .ok v → Q'.eval σ = .ok qs →
      Sim ((src.lenU Q').eval σ) (v.findLive qs >>= Close.arrLen))
    (ihSM : ∀ (Q' : LPath) {v qs}, src.eval σ = .ok v → Q'.eval σ = .ok qs →
      Sim ((src.mapU .map Q').eval σ) (v.findLive qs >>= KShape.map.test)) :
    Sim (((LStor.copy s P src SQ).lenU Q).eval σ) (u.findLive qs >>= Close.arrLen) := by
  obtain ⟨sv, sqs, n, v, ps, cur, hsv, hsq, hn, hv, hp, hc, hu'⟩ := copy_eval_ok hu
  have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
  have hsq' : SQ.elim.eval σ = .ok sqs := (hSQ sqs).2 hsq
  rw [LStor.lenU]
  refine cmp_sim hp' hq fun r hr => copyLeaf_sim (G := Close.arrLen) overlay_arrLen hn hsq' hu'
    ?_ ?_ (ihR hv hq) ?_ (fun pre q' hq' => ihSM _ hsv hq') (fun rest q' hq' => ihS _ hsv hq') r hr
  · have := ihS SQ.elim hsv hsq'; rwa [hn, Res.ok_bind] at this
  · intro f t he; subst he
    obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu'
    have hold := ihR hv hq
    rw [hw₀, Res.ok_bind] at hold
    rw [hf, Res.ok_bind, save_cons_arrLen hs']
    exact hold
  · exact Sim.of_eq (by simp only [LTerm.eval, hu, hq, Res.ok_bind])

theorem copy_mapU_sim {sh : KShape} (hu : (LStor.copy s P src SQ).eval σ = .ok u)
    (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ)) (hSQ : Sim (SQ.elim.eval σ) (SQ.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test))
    (ihS : ∀ (Q' : LPath) {v qs}, src.eval σ = .ok v → Q'.eval σ = .ok qs →
      Sim ((src.mapU sh Q').eval σ) (v.findLive qs >>= sh.test))
    (ihSM : ∀ (Q' : LPath) {v qs}, src.eval σ = .ok v → Q'.eval σ = .ok qs →
      Sim ((src.mapU .map Q').eval σ) (v.findLive qs >>= KShape.map.test)) :
    Sim (((LStor.copy s P src SQ).mapU sh Q).eval σ) (u.findLive qs >>= sh.test) := by
  obtain ⟨sv, sqs, n, v, ps, cur, hsv, hsq, hn, hv, hp, hc, hu'⟩ := copy_eval_ok hu
  have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
  have hsq' : SQ.elim.eval σ = .ok sqs := (hSQ sqs).2 hsq
  rw [LStor.mapU]
  refine cmp_sim hp' hq fun r hr => copyLeaf_sim (G := sh.test) (overlay_test sh) hn hsq' hu'
    ?_ ?_ (ihR hv hq) ?_ (fun pre q' hq' => ihSM _ hsv hq') (fun rest q' hq' => ihS _ hsv hq') r hr
  · have := ihS SQ.elim hsv hsq'; rwa [hn, Res.ok_bind] at this
  · intro f t he; subst he
    obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu'
    have hold := ihR hv hq
    rw [hw₀, Res.ok_bind] at hold
    rw [hf, Res.ok_bind, save_cons_kmapF hs']
    exact hold
  · exact Sim.of_eq (by simp only [LTerm.eval, hu, hq, Res.ok_bind])

variable {op : AOp} {w : LTerm}

theorem arr_readU_sim (hu : (LStor.arr op s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ)) (hw : Sim (w.elim.eval σ) (w.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue))
    (ihL : ∀ {v ps}, s.eval σ = .ok v → P.elim.eval σ = .ok ps →
      Sim ((s.lenU P.elim).eval σ) (v.findLive ps >>= Close.arrLen))
    (ihS : ∀ (rest : List SSeg) (opq : LTerm) {v : SVal} {ps : List Seg} {es sh : List SVal}
      {fx : Bool} {R : RefTy} {r : List Seg}, s.eval σ = .ok v → P.elim.eval σ = .ok ps →
      v.findLive ps = .ok (.array es sh fx) → segsEval σ rest = .ok r →
      Sim (opq.eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue) →
      Sim ((s.slotU P.elim rest opq).eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue)) :
    Sim (((LStor.arr op s P w).readU Q).eval σ) (u.findLive qs >>= SVal.asValue) := by
  obtain ⟨wv, v, ps, c, c', hw₀, hv, hp, hc, hap, hu'⟩ := arr_eval_ok hu
  have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
  have hL := ihL hv hp'
  rw [hc, Res.ok_bind] at hL
  rw [LStor.readU]
  exact cmp_sim hp' hq fun r hr => arrRead_sim hc hap hu' ((hw wv).2 hw₀) hL (ihR hv hq)
    (Sim.of_eq (by simp only [LTerm.eval, hu, hq, Res.ok_bind]))
    (fun es sh fx R hce _ rest r hr hopq => ihS rest _ hv hp' (hce ▸ hc) hr hopq) r hr

theorem arr_hasU_sim (hu : (LStor.arr op s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.hasU Q).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true)))
    (ihL : ∀ {v ps}, s.eval σ = .ok v → P.elim.eval σ = .ok ps →
      Sim ((s.lenU P.elim).eval σ) (v.findLive ps >>= Close.arrLen)) :
    Sim (((LStor.arr op s P w).hasU Q).eval σ) (u.findLive qs >>= fun _ => .ok (.bool true)) := by
  obtain ⟨wv, v, ps, c, c', hw₀, hv, hp, hc, hap, hu'⟩ := arr_eval_ok hu
  have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
  have hL := ihL hv hp'
  rw [hc, Res.ok_bind] at hL
  rw [LStor.hasU]
  exact cmp_sim hp' hq fun r hr => arrHas_sim hc hap hu' hL (ihR hv hq)
    (Sim.of_eq (by simp only [LTerm.eval, hu, hq, Res.ok_bind])) r hr

theorem arr_lenU_sim (hu : (LStor.arr op s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.lenU Q).eval σ) (v.findLive qs >>= Close.arrLen))
    (ihL : ∀ {v ps}, s.eval σ = .ok v → P.elim.eval σ = .ok ps →
      Sim ((s.lenU P.elim).eval σ) (v.findLive ps >>= Close.arrLen))
    (ihSL : ∀ (rest : List SSeg) {v : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool}
      {r : List Seg}, s.eval σ = .ok v → P.elim.eval σ = .ok ps →
      v.findLive ps = .ok (.array es sh fx) → segsEval σ rest = .ok r →
      ∀ x, (s.slotLenU P.elim rest .err).eval σ = .ok x → slotLen sh r = .ok x) :
    Sim (((LStor.arr op s P w).lenU Q).eval σ) (u.findLive qs >>= Close.arrLen) := by
  obtain ⟨wv, v, ps, c, c', hw₀, hv, hp, hc, hap, hu'⟩ := arr_eval_ok hu
  have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
  have hL := ihL hv hp'
  rw [hc, Res.ok_bind] at hL
  rw [LStor.lenU]
  refine cmp_sim hp' hq fun r hr => arrLength_sim hc hap hu' hL (ihR hv hq)
    (Sim.of_eq (by simp only [LTerm.eval, hu, hq, Res.ok_bind])) ?_ r hr
  intro f hf es sh fx R hce _ rest r' hr' hopq
  split at hf
  · cases hf
    simp only [LTerm.eval]
    exact orElse_sound_sim (fun x hx => slotLen_pushSlot R (ihSL rest hv hp' (hce ▸ hc) hr' x hx))
      hopq
  · cases hf

theorem arr_mapU_sim {sh : KShape} (hu : (LStor.arr op s P w).eval σ = .ok u)
    (hq : Q.eval σ = .ok qs) (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test))
    (ihL : ∀ {v ps}, s.eval σ = .ok v → P.elim.eval σ = .ok ps →
      Sim ((s.lenU P.elim).eval σ) (v.findLive ps >>= Close.arrLen)) :
    Sim (((LStor.arr op s P w).mapU sh Q).eval σ) (u.findLive qs >>= sh.test) := by
  obtain ⟨wv, v, ps, c, c', hw₀, hv, hp, hc, hap, hu'⟩ := arr_eval_ok hu
  have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
  have hL := ihL hv hp'
  rw [hc, Res.ok_bind] at hL
  rw [LStor.mapU]
  exact cmp_sim hp' hq fun r hr => arrMap_sim hc hap hu' hL (ihR hv hq)
    (Sim.of_eq (by simp only [LTerm.eval, hu, hq, Res.ok_bind])) r hr

end Wrappers

theorem arrOk_sim {σ : State} {op : AOp} {wv : Value} {L : LTerm} {x : Res SVal}
    (hL : Sim (L.eval σ) (x >>= Close.arrLen)) :
    Sim ((arrOk op L).eval σ) (x >>= fun c => op.apply wv c >>= fun _ => .ok (.bool true)) := by
  have hno : (∀ y, x >>= Close.arrLen ≠ .ok y) → Sim ((arrOk op L).eval σ)
      (x >>= fun c => op.apply wv c >>= fun _ => .ok (.bool true)) := by
    intro hx
    have hLn : ∀ y, L.eval σ ≠ .ok y := fun y h => hx y ((hL y).1 h)
    refine Sim.halt ?_ ?_
    · intro a ha
      obtain ⟨e, he⟩ : ∃ e, L.eval σ = .error e := by
        cases h : L.eval σ with
        | ok y => exact absurd h (hLn y)
        | error e => exact ⟨e, rfl⟩
      cases op <;> simp only [arrOk, LTerm.eval, bind, Except.bind, he, reduceCtorEq,
          evalBinop] at ha
    · intro a ha
      obtain ⟨c, hc, ha⟩ := Res.bind_eq_ok.1 ha
      obtain ⟨c', hap, -⟩ := Res.bind_eq_ok.1 ha
      obtain ⟨es, sh, fx, _, _, rfl, -⟩ := AOp.apply_ok hap
      exact hx _ (by rw [hc, Res.ok_bind]; rfl)
  cases x with
  | error e => exact hno fun y h => by simp only [Res.error_bind, reduceCtorEq] at h
  | ok c =>
    cases c with
    | array es sh fx =>
      have hL' : L.eval σ = .ok (.int es.length) := (hL _).2 rfl
      cases op with
      | push | slot _ => exact Sim.of_eq (by simp only [arrOk, LTerm.eval, hL', Res.ok_bind,
          AOp.apply])
      | pop keep =>
        rcases hr : es.reverse with _ | ⟨l, rr⟩
        · have : es = [] := List.reverse_eq_nil_iff.1 hr
          subst this
          refine Sim.halt ?_ ?_ <;>
            simp only [arrOk, LTerm.eval, bind, Except.bind, evalBinop, hL', List.length_nil,
                Int.cast_ofNat_Int, applyBinOp, Value.asInt, Int.lt_irrefl, decide_false,
                    checkArith, pickBranch, ne_eq, reduceCtorEq, not_false_eq_true, implies_true,
                    AOp.apply, List.reverse_nil]
        · have hlen : es.length = rr.length + 1 := by
            rw [← List.length_reverse, hr]; rfl
          refine Sim.of_eq ?_
          simp only [arrOk, LTerm.eval, bind, Except.bind, evalBinop, hL', hlen, Int.natCast_add,
              Int.cast_ofNat_Int, applyBinOp, Value.asInt, Int.succ_ofNat_pos, decide_true,
                  checkArith, pickBranch, AOp.apply, hr]
    | prim _ | struct _ | map _ _ => exact hno fun y h => by simp only [Res.ok_bind, Close.arrLen,
        reduceCtorEq] at h

theorem arr_okE_sim {σ : State} {op : AOp} {s : LStor} {P : LPath} {w : LTerm}
    (hs : Sim (s.okE.eval σ) (s.eval σ >>= fun _ => .ok (.bool true)))
    (hw : Sim (w.elim.eval σ) (w.eval σ)) (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihL : ∀ {v ps}, s.eval σ = .ok v → P.elim.eval σ = .ok ps →
      Sim ((s.lenU P.elim).eval σ) (v.findLive ps >>= Close.arrLen)) :
    Sim ((LStor.arr op s P w).okE.eval σ)
      ((LStor.arr op s P w).eval σ >>= fun _ => .ok (.bool true)) := by
  simp only [LStor.okE]
  split
  · rename_i hn
    intro a
    simp only [LTerm.eval, LStor.eval, Res.bind_eq_ok]
    constructor
    · rintro ⟨_, h₁, wv, h₂, _, ⟨ps, h₃, -⟩, h₄⟩
      obtain ⟨v, hv, -⟩ := Res.bind_eq_ok.1 ((hs _).1 h₁)
      have hok := ((arrOk_sim (op := op) (wv := wv) (ihL hv h₃)) a).1 h₄
      obtain ⟨c, hc, h₅⟩ := Res.bind_eq_ok.1 hok
      obtain ⟨c', hap, h₆⟩ := Res.bind_eq_ok.1 h₅
      have hq := (hP ps).1 h₃
      obtain ⟨u, hu⟩ := (save_ok_iff_find_ok (new := c') (LPath.noLen_eval σ hn hq)).2 ⟨_, hc⟩
      exact ⟨u, ⟨wv, (hw wv).1 h₂, v, hv, ps, hq, c, hc, c', hap, hu⟩, h₆⟩
    · rintro ⟨u, ⟨wv, h₂, v, hv, ps, hq, c, hc, c', hap, hu⟩, h₆⟩
      have h₃ := (hP ps).2 hq
      refine ⟨.bool true, (hs _).2 (by simp only [hv, Res.ok_bind]), wv, (hw wv).2 h₂, .bool true,
        ⟨ps, h₃, rfl⟩, ?_⟩
      exact ((arrOk_sim (wv := wv) (ihL hv h₃)) _).2 (by simpa only [hc, Res.ok_bind, hap,
          Except.ok.injEq] using h₆)
  · exact Sim.refl _

theorem copy_okE_sim {σ : State} {s src : LStor} {P SQ : LPath}
    (hs : Sim (s.okE.eval σ) (s.eval σ >>= fun _ => .ok (.bool true)))
    (hsrc : Sim (src.okE.eval σ) (src.eval σ >>= fun _ => .ok (.bool true)))
    (hP : Sim (P.elim.eval σ) (P.eval σ)) (hSQ : Sim (SQ.elim.eval σ) (SQ.eval σ))
    (ihH : ∀ {v ps}, s.eval σ = .ok v → P.elim.eval σ = .ok ps →
      Sim ((s.hasU P.elim).eval σ) (v.findLive ps >>= fun _ => .ok (.bool true)))
    (ihS : ∀ {v ps}, src.eval σ = .ok v → SQ.elim.eval σ = .ok ps →
      Sim ((src.hasU SQ.elim).eval σ) (v.findLive ps >>= fun _ => .ok (.bool true))) :
    Sim ((LStor.copy s P src SQ).okE.eval σ)
      ((LStor.copy s P src SQ).eval σ >>= fun _ => .ok (.bool true)) := by
  simp only [LStor.okE]
  split
  · rename_i hn
    have hold : Sim ((LTerm.seq src.okE (.seq (.pok SQ.elim) (.seq (src.hasU SQ.elim)
        (.seq s.okE (.seq (.pok P.elim) (s.hasU P.elim)))))).eval σ)
        ((LStor.copy s P src SQ).eval σ >>= fun _ => .ok (.bool true)) := by
      intro a
      simp only [LTerm.eval, LStor.eval, Res.bind_eq_ok]
      constructor
      · rintro ⟨_, h₁, _, ⟨sqs, h₂, -⟩, _, h₃, _, h₄, _, ⟨ps, h₅, -⟩, h₆⟩
        obtain ⟨sv, hsv, -⟩ := Res.bind_eq_ok.1 ((hsrc _).1 h₁)
        obtain ⟨n, hn', -⟩ := Res.bind_eq_ok.1 ((ihS hsv h₂ _).1 h₃)
        obtain ⟨v, hv, -⟩ := Res.bind_eq_ok.1 ((hs _).1 h₄)
        obtain ⟨cur, hc, he⟩ := Res.bind_eq_ok.1 ((ihH hv h₅ _).1 h₆)
        cases he
        have hq := (hP ps).1 h₅
        obtain ⟨u, hu⟩ := (save_ok_iff_find_ok (new := cur.overlay n)
          (LPath.noLen_eval σ hn hq)).2 ⟨_, hc⟩
        exact ⟨u, ⟨sv, hsv, sqs, (hSQ sqs).1 h₂, n, hn', v, hv, ps, hq, cur, hc, hu⟩, rfl⟩
      · rintro ⟨u, ⟨sv, hsv, sqs, hsq, n, hn', v, hv, ps, hq, cur, hc, hu⟩, he⟩
        cases he
        have h₂ := (hSQ sqs).2 hsq
        have h₅ := (hP ps).2 hq
        exact ⟨.bool true, (hsrc _).2 (by simp only [hsv, Res.ok_bind]), .bool true, ⟨sqs, h₂, rfl⟩,
          .bool true, (ihS hsv h₂ _).2 (by simp only [hn', Res.ok_bind]), .bool true,
          (hs _).2 (by simp only [hv, Res.ok_bind]), .bool true, ⟨ps, h₅, rfl⟩,
          (ihH hv h₅ _).2 (by simp only [hc, Res.ok_bind])⟩
    split
    · rename_i hd
      have he : src = s := by simp only [Bool.and_eq_true, beq_iff_eq] at hd; exact hd.2
      subst he
      refine Sim.trans (Sim.of_eq ?_) hold
      simp only [LTerm.eval]
      cases src.okE.eval σ <;> rfl
    · exact hold
  · exact Sim.refl _

/-! ### The slot a `push()` recycles -/

theorem pushSlot_ref_cons (R : RefTy) (c : SVal) (t : List SVal) :
    (pushSlot (.ref R) (c :: t)).1 = c := by
  simp only [pushSlot, Ty.isPrimitive, Bool.false_eq_true, ↓reduceIte]

theorem AOp.apply_pop_eq {keep : Bool} {wv : Value} {c c' : SVal}
    (h : (AOp.pop keep).apply wv c = .ok c') :
    ∃ es last sh fx, c = .array (es ++ [last]) sh fx ∧
      c' = .array es ((if keep then last else last.defaultOf) :: sh) fx := by
  cases c with
  | array elems shadow fx =>
    simp only [AOp.apply] at h
    rcases hr : elems.reverse with _ | ⟨l, rr⟩ <;> simp only [hr] at h
    · cases h
    · cases h
      refine ⟨rr.reverse, l, shadow, fx, ?_, rfl⟩
      have he : elems = (l :: rr).reverse := by rw [← hr, List.reverse_reverse]
      simp only [he, List.reverse_cons]
  | prim _ | struct _ | map _ _ => simp only [apply, reduceCtorEq] at h

/-- **The default of an element, read below it**: the leaf a `delete` of
the element at `E` leaves, at `rest`. -/
theorem delSlot_sim {σ : State} {s : LStor} {v e : SVal} {E : LPath} {eps : List Seg}
    {rest : List SSeg} {r : List Seg}
    (hE : E.eval σ = .ok eps) (he : v.findLive eps = .ok e) (hr : segsEval σ rest = .ok r)
    (ihR : ∀ (Q : LPath) {qs}, Q.eval σ = .ok qs →
      Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue))
    (ihM : ∀ (sh : KShape) (Q : LPath) {qs}, Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)) :
    Sim ((delLeaf (s.readU (E.addSegs rest)) E (fun sh q => s.mapU sh q)
      (if rest.isEmpty then .eq else .below rest)).eval σ)
      (e.defaultOf.findLive r >>= SVal.asValue) := by
  have hQ : (E.addSegs rest).eval σ = .ok (eps ++ r) := by
    rw [LPath.addSegs_eval, hE, Res.ok_bind, hr, Res.ok_bind]
  have hold := ihR _ hQ
  by_cases hemp : rest.isEmpty = true
  · have hr0 : r = [] := (segsEval_isEmpty hr).1 hemp
    subst hr0
    rw [if_pos hemp]
    simp only [delLeaf, LTerm.eval, SVal.findLive_nil, Res.ok_bind, asValue_defaultOf]
    rw [List.append_nil, he, Res.ok_bind] at hold
    exact Sim.bind hold fun _ => Sim.refl _
  · rw [if_neg hemp]
    simp only [delLeaf]
    have hEnd : Sim ((LTerm.zero (s.readU (E.addSegs rest))).eval σ)
        (v.findLive (eps ++ r) >>= fun w => w.defaultOf.asValue) := by
      simp only [LTerm.eval]
      refine (Sim.bind hold (fun _ => Sim.refl _)).trans (Sim.of_eq ?_)
      rw [bind_assoc]; congr 1; funext w; rw [asValue_defaultOf]
    have h := delBelow_sim (v := v) (G := SVal.asValue)
      (fun sh q qs hq' => ihM sh q hq') hold hEnd rest E eps r hE hr rfl
    rw [he, Res.ok_bind] at h
    exact h

theorem pop_slotU_sim {σ : State} {keep : Bool} {s : LStor} {P' P : LPath} {w' opq : LTerm}
    {rest : List SSeg} {v : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool} {R : RefTy}
    {r : List Seg}
    (hu : (LStor.arr (.pop keep) s P' w').eval σ = .ok v) (hP' : Sim (P'.elim.eval σ) (P'.eval σ))
    (hp : P.eval σ = .ok ps) (hn : v.findLive ps = .ok (.array es sh fx))
    (hr : segsEval σ rest = .ok r)
    (hopq : Sim (opq.eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue))
    (ihR : ∀ (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue))
    (ihM : ∀ (sh : KShape) (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test))
    (ihL : ∀ {v qs}, s.eval σ = .ok v → P.eval σ = .ok qs →
      Sim ((s.lenU P).eval σ) (v.findLive qs >>= Close.arrLen)) :
    Sim (((LStor.arr (.pop keep) s P' w').slotU P rest opq).eval σ)
      ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue) := by
  rw [LStor.slotU]
  split
  · rename_i heq
    have hPe : P'.elim = P := by simpa only [beq_iff_eq] using heq
    obtain ⟨wv, v', ps', c0, c1, -, hv', hp', hc0, hap, hu'⟩ := arr_eval_ok hu
    have hpp : ps' = ps := by
      have := (hP' ps').2 hp'
      rw [hPe, hp] at this
      cases this; rfl
    subst hpp
    rw [findLive_saveLive_same hu'] at hn
    obtain ⟨es0, last, sh0, fx0, rfl, rfl⟩ := AOp.apply_pop_eq hap
    simp only [Except.ok.injEq, SVal.array.injEq] at hn
    obtain ⟨rfl, rfl, rfl⟩ := hn
    rw [pushSlot_ref_cons] at hopq ⊢
    have hL := ihL hv' hp
    rw [hc0, Res.ok_bind] at hL
    have hL' : (s.lenU P).eval σ = .ok (.int (es0 ++ [last]).length) := (hL _).2 rfl
    have hE : (P.at (lenPred (s.lenU P))).eval σ = .ok (ps' ++ [.at es0.length]) := by
      simp only [LPath.eval, hp, Res.ok_bind, lenPred_eval hL', Value.asInt]
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
          Int.natCast_add, Int.cast_ofNat_Int, Int.add_sub_cancel]
    have he : v'.findLive (ps' ++ [.at es0.length]) = .ok last := by
      rw [SVal.findLive_append, hc0, Res.ok_bind, findLive_last]
    cases keep
    · simp only [Bool.false_eq_true, if_false]
      exact delSlot_sim hE he hr (fun Q _ hq => ihR Q hv' hq) (fun sh Q _ hq => ihM sh Q hv' hq)
    · simp only [if_true]
      have hQ : ((P.at (lenPred (s.lenU P))).addSegs rest).eval σ =
          .ok ((ps' ++ [.at es0.length]) ++ r) := by
        rw [LPath.addSegs_eval, hE, Res.ok_bind, hr, Res.ok_bind]
      have := ihR _ hv' hQ
      rw [SVal.findLive_append, he, Res.ok_bind] at this
      exact this
  · exact hopq

theorem del_slotU_sim {σ : State} {s : LStor} {P' P : LPath} {opq : LTerm}
    {rest : List SSeg} {v : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool} {R : RefTy}
    {r : List Seg}
    (hu : (LStor.delAt s P').eval σ = .ok v) (hP' : Sim (P'.elim.eval σ) (P'.eval σ))
    (hp : P.eval σ = .ok ps) (hn : v.findLive ps = .ok (.array es sh fx))
    (hr : segsEval σ rest = .ok r)
    (hopq : Sim (opq.eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue))
    (ihR : ∀ (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue))
    (ihM : ∀ (sh : KShape) (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test))
    (ihL : ∀ {v qs}, s.eval σ = .ok v → P.eval σ = .ok qs →
      Sim ((s.lenU P).eval σ) (v.findLive qs >>= Close.arrLen))
    (ihS : ∀ {v : SVal} {es sh : List SVal} {fx : Bool}, s.eval σ = .ok v →
      v.findLive ps = .ok (.array es sh fx) →
      Sim (opq.eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue) →
      Sim ((s.slotU P rest opq).eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue)) :
    Sim (((LStor.delAt s P').slotU P rest opq).eval σ)
      ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue) := by
  rw [LStor.slotU]
  split
  · rename_i heq
    have hPe : P'.elim = P := by simpa only [beq_iff_eq] using heq
    obtain ⟨v', hv', hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps', hp', hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨c0, hc0, hu'⟩ := Res.bind_eq_ok.1 hu
    have hpp : ps' = ps := by
      have := (hP' ps').2 hp'
      rw [hPe, hp] at this
      cases this; rfl
    subst hpp
    rw [findLive_saveLive_same hu'] at hn
    have hM := ihM .fixed P hv' hp
    rw [hc0, Res.ok_bind] at hM
    have hL := ihL hv' hp
    rw [hc0, Res.ok_bind] at hL
    cases c0 with
    | array es0 sh0 fx0 =>
      cases fx0 with
      | true =>
        have hm : (s.mapU .fixed P).eval σ = .ok (.bool true) := (hM _).2 rfl
        simp only [LTerm.eval, isT_eval, hm, Res.ok_bind, pickBranch]
        exact hopq
      | false =>
        have hm : ∀ x, (s.mapU .fixed P).eval σ ≠ .ok x := fun x h => by
          have := (hM x).1 h
          simp only [KShape.test, isFixV, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at this
        have hmT : (isT (s.mapU .fixed P)).eval σ = .ok (.bool false) := by
          rw [isT_eval]
          cases hh : (s.mapU .fixed P).eval σ with
          | ok x => exact absurd hh (hm x)
          | error _ => rfl
        have hL' : (s.lenU P).eval σ = .ok (.int es0.length) := (hL _).2 rfl
        simp only [LTerm.eval, hmT, Res.ok_bind, pickBranch, hL', Value.asInt]
        simp only [SVal.defaultOf, Except.ok.injEq, SVal.array.injEq] at hn
        obtain ⟨rfl, rfl, rfl⟩ := hn
        cases es0 with
        | nil =>
          simp only [List.length_nil, Int.natCast_zero, if_true]
          simp only [SVal.defaultOf.defaultOfElems, List.nil_append] at hopq ⊢
          split
          · exact ihS hv' hc0 hopq
          · exact hopq
        | cons e et =>
          have hne : ((e :: et).length : Int) ≠ 0 := by simp only [List.length_cons,
              Int.natCast_add, Int.cast_ofNat_Int, ne_eq]; omega
          rw [if_neg hne]
          simp only [SVal.defaultOf.defaultOfElems, List.cons_append] at hopq ⊢
          rw [pushSlot_ref_cons]
          have hE : (P.at (.lit (.int 0))).eval σ = .ok (ps' ++ [.at 0]) := by
            simp only [LPath.eval, hp, LTerm.eval, Res.ok_bind, Value.asInt]
          have he : v'.findLive (ps' ++ [.at 0]) = .ok e := by
            rw [SVal.findLive_append, hc0, Res.ok_bind]
            simp only [SVal.findLive, Int.le_refl, Int.toNat_zero, List.length_cons,
                Nat.zero_lt_succ, and_self, ↓reduceDIte, Fin.zero_eta, List.get_eq_getElem,
                    Fin.val_zero, List.getElem_cons_zero, SVal.findLive_nil]
          exact delSlot_sim hE he hr (fun Q _ hq => ihR Q hv' hq) (fun sh Q _ hq => ihM sh Q hv' hq)
    | prim p => cases p <;> simp only [SVal.defaultOf, Except.ok.injEq, reduceCtorEq] at hn
    | struct _ => simp only [SVal.defaultOf, Except.ok.injEq, reduceCtorEq] at hn
    | map _ _ => simp only [SVal.defaultOf, Except.ok.injEq, reduceCtorEq] at hn
  · exact hopq

/-! ### Writes and deletes, one lemma per case

The cases of the elimination's soundness, each with what it needs of the
storage below it as hypotheses, so that the mutual proof only dispatches. -/

theorem save_okE_sim {σ : State} {s : LStor} {q : LPath} {w : LTerm}
    (hs : Sim (s.okE.eval σ) (s.eval σ >>= fun _ => .ok (.bool true)))
    (hW : Sim (w.elim.eval σ) (w.eval σ))
    (hP : Sim (q.elim.eval σ) (q.eval σ))
    (ihH : ∀ {v qs}, s.eval σ = .ok v → q.elim.eval σ = .ok qs →
      Sim ((s.hasU q.elim).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true))) :
    Sim ((LStor.save s q w).okE.eval σ) ((LStor.save s q w).eval σ >>= fun _ => .ok (.bool true)) := by
    simp only [LStor.okE]
    split
    · rename_i hn
      intro a
      simp only [LTerm.eval, LStor.eval, Res.bind_eq_ok]
      constructor
      · rintro ⟨_, h₁, wv, h₂, _, ⟨qs, h₃, -⟩, h₄⟩
        obtain ⟨v, hv, -⟩ := Res.bind_eq_ok.1 ((hs _).1 h₁)
        have hq := (hP qs).1 h₃
        obtain ⟨_, hf, he⟩ := Res.bind_eq_ok.1 ((ihH hv h₃ a).1 h₄)
        cases he
        obtain ⟨u, hu⟩ := (save_ok_iff_find_ok (new := wv.toSVal) (LPath.noLen_eval σ hn hq)).2
          ⟨_, hf⟩
        exact ⟨u, ⟨wv, (hW wv).1 h₂, v, hv, qs, hq, hu⟩, rfl⟩
      · rintro ⟨u, ⟨wv, h₂, v, hv, qs, hq, hu⟩, he⟩
        cases he
        have h₃ := (hP qs).2 hq
        obtain ⟨c, hc⟩ := (save_ok_iff_find_ok (LPath.noLen_eval σ hn hq)).1 ⟨u, hu⟩
        refine ⟨.bool true, (hs _).2 (by simp only [hv, Res.ok_bind]), wv,
          (hW wv).2 h₂, .bool true, ⟨qs, h₃, rfl⟩, ?_⟩
        exact (ihH hv h₃ _).2 (by simp only [hc, Res.ok_bind])
    · exact Sim.refl _

theorem del_okE_sim {σ : State} {s : LStor} {q : LPath}
    (hs : Sim (s.okE.eval σ) (s.eval σ >>= fun _ => .ok (.bool true)))
    (hP : Sim (q.elim.eval σ) (q.eval σ))
    (ihH : ∀ {v qs}, s.eval σ = .ok v → q.elim.eval σ = .ok qs →
      Sim ((s.hasU q.elim).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true))) :
    Sim ((LStor.delAt s q).okE.eval σ) ((LStor.delAt s q).eval σ >>= fun _ => .ok (.bool true)) := by
    simp only [LStor.okE]
    split
    · rename_i hn
      intro a
      simp only [LTerm.eval, LStor.eval, Res.bind_eq_ok]
      constructor
      · rintro ⟨_, h₁, _, ⟨qs, h₃, -⟩, h₄⟩
        obtain ⟨v, hv, -⟩ := Res.bind_eq_ok.1 ((hs _).1 h₁)
        have hq := (hP qs).1 h₃
        obtain ⟨c, hf, he⟩ := Res.bind_eq_ok.1 ((ihH hv h₃ a).1 h₄)
        cases he
        obtain ⟨u, hu⟩ := (save_ok_iff_find_ok (new := c.defaultOf) (LPath.noLen_eval σ hn hq)).2
          ⟨_, hf⟩
        exact ⟨u, ⟨v, hv, qs, hq, c, hf, hu⟩, rfl⟩
      · rintro ⟨u, ⟨v, hv, qs, hq, c, hc, hu⟩, he⟩
        cases he
        have h₃ := (hP qs).2 hq
        refine ⟨.bool true, (hs _).2 (by simp only [hv, Res.ok_bind]), .bool true,
          ⟨qs, h₃, rfl⟩, ?_⟩
        exact (ihH hv h₃ _).2 (by simp only [hc, Res.ok_bind])
    · exact Sim.refl _

theorem save_readU_sim {σ : State} {s : LStor} {P Q : LPath} {w : LTerm} {u : SVal} {qs : List Seg}
    (hu : (LStor.save s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (hW : Sim (w.elim.eval σ) (w.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue)) :
    Sim (((LStor.save s P w).readU Q).eval σ) (u.findLive qs >>= SVal.asValue) := by
    obtain ⟨wv, hw, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
    rw [LStor.readU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      simp only [saveLeaf, findLive_saveLive_same hu, Res.ok_bind, Close.asValue_toSVal]
      exact Sim.trans (hW) (Sim.of_eq hw)
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨_, w', _, hs', hf⟩ := save_through qs (f :: t) hu
      obtain ⟨e, he⟩ := save_cons_asValue hs'
      refine Sim.halt (by simp only [saveLeaf, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]) ?_
      simp only [hf, Res.ok_bind, he, ne_eq, reduceCtorEq, not_false_eq_true, implies_true]
    | below k =>
      obtain ⟨f, t, rfl, -⟩ := hr
      refine Sim.halt (by simp only [saveLeaf, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]) ?_
      rw [SVal.findLive_append, findLive_saveLive_same hu]
      cases wv <;> simp only [Close.toSVal_int, Res.ok_bind, find_prim_cons, Res.error_bind,
          ne_eq, reduceCtorEq, not_false_eq_true, implies_true, Close.toSVal_bool]
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact ihR hv hq

theorem del_readU_sim {σ : State} {s : LStor} {P Q : LPath} {u : SVal} {qs : List Seg}
    (hu : (LStor.delAt s P).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue))
    (ihM : ∀ (sh : KShape) (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)) :
    Sim (((LStor.delAt s P).readU Q).eval σ) (u.findLive qs >>= SVal.asValue) := by
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨c, hc, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
    rw [LStor.readU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      simp only [delLeaf, LTerm.eval, findLive_saveLive_same hu, Res.ok_bind, asValue_defaultOf]
      have h₁ := ihR hv hq
      rw [hc, Res.ok_bind] at h₁
      exact Sim.bind h₁ fun _ => Sim.refl _
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨_, w', _, hs', hf⟩ := save_through qs (f :: t) hu
      obtain ⟨e, he⟩ := save_cons_asValue hs'
      refine Sim.halt (by simp only [delLeaf, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]) ?_
      simp only [hf, Res.ok_bind, he, ne_eq, reduceCtorEq, not_false_eq_true, implies_true]
    | below rest =>
      obtain ⟨f, t, rfl, hrest⟩ := hr
      simp only [delLeaf]
      have hEnd : Sim ((LTerm.zero (s.readU Q)).eval σ)
          (v.findLive (ps ++ f :: t) >>= fun w => w.defaultOf.asValue) := by
        simp only [LTerm.eval]
        refine (Sim.bind (ihR hv hq) (fun _ => Sim.refl _)).trans
          (Sim.of_eq ?_)
        rw [bind_assoc]; congr 1; funext w; rw [asValue_defaultOf]
      have h := delBelow_sim (v := v) (G := SVal.asValue)
        (fun sh q qs hq' => ihM sh q hv hq') (ihR hv hq) hEnd
        rest P.elim ps (f :: t) hp' hrest rfl
      rw [hc, Res.ok_bind] at h
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind]
      exact h
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact ihR hv hq

theorem save_hasU_sim {σ : State} {s : LStor} {P Q : LPath} {w : LTerm} {u : SVal} {qs : List Seg}
    (hu : (LStor.save s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihH : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.hasU Q).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true))) :
    Sim (((LStor.save s P w).hasU Q).eval σ) (u.findLive qs >>= fun _ => .ok (.bool true)) := by
    obtain ⟨wv, hw, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
    rw [LStor.hasU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      simp only [saveHas, findLive_saveLive_same hu, Res.ok_bind, LTerm.eval]
      exact Sim.refl _
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨_, w', _, _, hf⟩ := save_through qs (f :: t) hu
      simp only [saveHas, hf, Res.ok_bind, LTerm.eval]
      exact Sim.refl _
    | below k =>
      obtain ⟨f, t, rfl, -⟩ := hr
      refine Sim.halt (by simp only [saveHas, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]) ?_
      rw [SVal.findLive_append, findLive_saveLive_same hu]
      cases wv <;> simp only [Close.toSVal_int, Res.ok_bind, find_prim_cons, Res.error_bind,
          ne_eq, reduceCtorEq, not_false_eq_true, implies_true, Close.toSVal_bool]
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact ihH hv hq

theorem del_hasU_sim {σ : State} {s : LStor} {P Q : LPath} {u : SVal} {qs : List Seg}
    (hu : (LStor.delAt s P).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihH : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.hasU Q).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true)))
    (ihM : ∀ (sh : KShape) (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)) :
    Sim (((LStor.delAt s P).hasU Q).eval σ) (u.findLive qs >>= fun _ => .ok (.bool true)) := by
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨c, hc, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
    rw [LStor.hasU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      simp only [delHas, findLive_saveLive_same hu, Res.ok_bind, LTerm.eval]
      exact Sim.refl _
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨_, w', _, _, hf⟩ := save_through qs (f :: t) hu
      simp only [delHas, hf, Res.ok_bind, LTerm.eval]
      exact Sim.refl _
    | below rest =>
      obtain ⟨f, t, rfl, hrest⟩ := hr
      simp only [delHas]
      have h := delBelow_sim (v := v) (G := fun _ => .ok (.bool true))
        (fun sh q qs hq' => ihM sh q hv hq') (ihH hv hq)
        (ihH hv hq) rest P.elim ps (f :: t) hp' hrest rfl
      rw [hc, Res.ok_bind] at h
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind]
      exact h
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact ihH hv hq

theorem save_mapU_sim {σ : State} {s : LStor} {P Q : LPath} {w : LTerm} {u : SVal} {qs : List Seg} {sh : KShape}
    (hu : (LStor.save s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihM : ∀ (sh : KShape) (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)) :
    Sim (((LStor.save s P w).mapU sh Q).eval σ) (u.findLive qs >>= sh.test) := by
    obtain ⟨wv, hw, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
    rw [LStor.mapU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      refine Sim.halt (by simp only [saveMap, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]) ?_
      simp only [findLive_saveLive_same hu, Res.ok_bind]
      cases wv <;> cases sh <;> simp only [KShape.test, kmapF, isMapV, Value.toSVal,
          Bool.false_eq_true, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true, implies_true,
              isFixV]
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu
      simp only [saveMap, hf, Res.ok_bind, save_cons_kmapF hs']
      have := ihM sh Q hv hq
      rw [hw₀, Res.ok_bind] at this
      exact this
    | below rest =>
      obtain ⟨f, t, rfl, -⟩ := hr
      refine Sim.halt (by simp only [saveMap, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]) ?_
      rw [SVal.findLive_append, findLive_saveLive_same hu]
      cases wv <;> simp only [Close.toSVal_int, Res.ok_bind, find_prim_cons, Res.error_bind,
          ne_eq, reduceCtorEq, not_false_eq_true, implies_true, Close.toSVal_bool]
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact ihM sh Q hv hq

theorem del_mapU_sim {σ : State} {s : LStor} {P Q : LPath} {u : SVal} {qs : List Seg} {sh : KShape}
    (hu : (LStor.delAt s P).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihM : ∀ (sh : KShape) (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)) :
    Sim (((LStor.delAt s P).mapU sh Q).eval σ) (u.findLive qs >>= sh.test) := by
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨c, hc, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
    rw [LStor.mapU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      simp only [delMap, findLive_saveLive_same hu, Res.ok_bind, KShape.test_defaultOf]
      have := ihM sh Q hv hq
      rw [hc, Res.ok_bind] at this
      exact this
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu
      simp only [delMap, hf, Res.ok_bind, save_cons_kmapF hs']
      have := ihM sh Q hv hq
      rw [hw₀, Res.ok_bind] at this
      exact this
    | below rest =>
      obtain ⟨f, t, rfl, hrest⟩ := hr
      simp only [delMap]
      have hEnd : Sim ((s.mapU sh Q).eval σ)
          (v.findLive (ps ++ f :: t) >>= fun w => sh.test w.defaultOf) := by
        simp only [KShape.test_defaultOf]; exact ihM sh Q hv hq
      have h := delBelow_sim (v := v) (G := sh.test)
        (fun sh' q qs hq' => ihM sh' q hv hq') (ihM sh Q hv hq)
        hEnd rest P.elim ps (f :: t) hp' hrest rfl
      rw [hc, Res.ok_bind] at h
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind]
      exact h
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact ihM sh Q hv hq

theorem save_lenU_sim {σ : State} {s : LStor} {P Q : LPath} {w : LTerm} {u : SVal} {qs : List Seg}
    (hu : (LStor.save s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihL : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.lenU Q).eval σ) (v.findLive qs >>= Close.arrLen)) :
    Sim (((LStor.save s P w).lenU Q).eval σ) (u.findLive qs >>= Close.arrLen) := by
    obtain ⟨wv, hw, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
    rw [LStor.lenU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      refine Sim.halt (by simp only [saveMap, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]) ?_
      simp only [findLive_saveLive_same hu, Res.ok_bind]
      cases wv <;> simp only [Close.arrLen, Value.toSVal, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu
      simp only [saveMap, hf, Res.ok_bind, save_cons_arrLen hs']
      have := ihL hv hq
      rw [hw₀, Res.ok_bind] at this
      exact this
    | below rest =>
      obtain ⟨f, t, rfl, -⟩ := hr
      refine Sim.halt (by simp only [saveMap, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]) ?_
      rw [SVal.findLive_append, findLive_saveLive_same hu]
      cases wv <;> simp only [Close.toSVal_int, Res.ok_bind, find_prim_cons, Res.error_bind,
          ne_eq, reduceCtorEq, not_false_eq_true, implies_true, Close.toSVal_bool]
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact ihL hv hq

theorem del_lenU_sim {σ : State} {s : LStor} {P Q : LPath} {u : SVal} {qs : List Seg}
    (hu : (LStor.delAt s P).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihL : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.lenU Q).eval σ) (v.findLive qs >>= Close.arrLen))
    (ihM : ∀ (sh : KShape) (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)) :
    Sim (((LStor.delAt s P).lenU Q).eval σ) (u.findLive qs >>= Close.arrLen) := by
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨c, hc, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
    have hEnd := lenEnd_sim (ihL hv hq) (ihM .fixed Q hv hq)
    rw [LStor.lenU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      simp only [delLen, findLive_saveLive_same hu, Res.ok_bind]
      rw [hc, Res.ok_bind] at hEnd
      exact hEnd
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu
      simp only [delLen, hf, Res.ok_bind, save_cons_arrLen hs']
      have := ihL hv hq
      rw [hw₀, Res.ok_bind] at this
      exact this
    | below rest =>
      obtain ⟨f, t, rfl, hrest⟩ := hr
      simp only [delLen]
      have h := delBelow_sim (v := v) (G := Close.arrLen)
        (fun sh' q qs hq' => ihM sh' q hv hq') (ihL hv hq)
        hEnd rest P.elim ps (f :: t) hp' hrest rfl
      rw [hc, Res.ok_bind] at h
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind]
      exact h
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact ihL hv hq

/-! ### Memory and its views in the elimination

The memory readers of the elimination give what `Calculus/MemRead.lean`'s
give, the storage they read eliminated (`LMem.readU_sim`, `LMem.objU_sim`);
a read below a view is a read of memory along the same path
(`view_read_sim`, `findOnCopy`). -/

/-! ### Whether a copy into memory succeeds -/

section CopyOk
open MemNames


theorem Cps.prim (p : PrimVal) : Cps (.prim p) := ⟨{ storage := [] }, by cases p <;> exact ⟨_, rfl⟩⟩

theorem cps_setBy {f : Name} {u old : SVal} (hc : Cps u ↔ Cps old) :
    ∀ {fs : List (Name × SVal)}, lookupBy f fs = some old →
      ((∀ p ∈ setBy f u fs, Cps p.2) ↔ ∀ p ∈ fs, Cps p.2)
  | [], h => by simp only [lookupBy, reduceCtorEq] at h
  | (k, w) :: rest, h => by
    by_cases hk : f = k
    · simp only [lookupBy, hk, if_true, Option.some.injEq] at h
      subst h
      simp only [setBy, hk, if_true, List.forall_mem_cons, hc]
    · simp only [lookupBy, hk, if_false] at h
      simp only [setBy, hk, if_false, List.forall_mem_cons, cps_setBy hc h]

theorem cps_set {u : SVal} : ∀ {es : List SVal} {i : Nat} (hi : i < es.length),
    (Cps u ↔ Cps es[i]) → ((∀ x ∈ es.set i u, Cps x) ↔ ∀ x ∈ es, Cps x)
  | [], _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | x :: rest, 0, _, hc => by
    simp only [List.set_cons_zero, List.forall_mem_cons, List.getElem_cons_zero] at hc ⊢
    rw [hc]
  | x :: rest, i + 1, hi, hc => by
    simp only [List.getElem_cons_succ] at hc
    simp only [List.set_cons_succ, List.forall_mem_cons,
      cps_set (Nat.lt_of_succ_lt_succ hi) hc]

theorem cps_saveLive {new : SVal} : ∀ {ps : List Seg} {v v' old : SVal},
    v.findLive ps = .ok old → v.saveLive ps new = .ok v' → (Cps new ↔ Cps old) →
      (Cps v' ↔ Cps v)
  | [], v, v', old, hf, hs, hc => by
    simp only [SVal.findLive_nil, Except.ok.injEq] at hf
    have : v' = new := by cases v <;> simpa only [SVal.saveLive, Except.ok.injEq] using hs.symm
    subst hf this
    exact hc
  | s :: _, .prim _, _, _, _, hs, _ => by cases s <;> simp only [SVal.saveLive, reduceCtorEq] at hs
  | .field f :: ps, .struct fields, v', old, hf, hs, hc => by
    simp only [SVal.findLive] at hf
    simp only [SVal.saveLive] at hs
    cases hl : lookupBy f fields with
    | none => simp only [hl, reduceCtorEq] at hf
    | some w =>
      rw [hl] at hf hs
      obtain ⟨u, hu, he⟩ := Res.bind_eq_ok.1 hs
      cases he
      rw [Cps.struct_iff, Cps.struct_iff]
      exact cps_setBy (cps_saveLive hf hu hc) hl
  | .at _ :: _, .struct _, _, _, _, hs, _ => by simp only [SVal.saveLive, reduceCtorEq] at hs
  | .at i :: ps, .array elems shadow fx, v', old, hf, hs, hc => by
    simp only [SVal.saveLive] at hs
    split at hs
    · rename_i hi
      simp only [SVal.findLive, dif_pos hi, List.get_eq_getElem] at hf
      obtain ⟨u, hu, he⟩ := Res.bind_eq_ok.1 hs
      cases he
      rw [Cps.array_iff, Cps.array_iff]
      exact cps_set hi.2 (cps_saveLive hf hu hc)
    · cases hs
  | .field _ :: _, .array _ _ _, _, _, _, hs, _ => by simp only [SVal.saveLive, reduceCtorEq] at hs
  | .at i :: ps, .map e d, v', old, hf, hs, hc => by
    simp only [SVal.saveLive] at hs
    split at hs <;>
      (obtain ⟨u, hu, he⟩ := Res.bind_eq_ok.1 hs; cases he
       exact iff_of_false (Cps.not_map _ _) (Cps.not_map _ _))
  | .field _ :: _, .map _ _, _, _, _, hs, _ => by simp only [SVal.saveLive, reduceCtorEq] at hs

theorem segs_rel : ∀ (ps qs : List Seg), qs = ps ∨ (∃ f r, ps = qs ++ f :: r) ∨
    (∃ f r, qs = ps ++ f :: r) ∨ Close.Diverge ps qs
  | [], [] => .inl rfl
  | a :: p, [] => .inr (.inl ⟨a, p, rfl⟩)
  | [], b :: q => .inr (.inr (.inl ⟨b, q, rfl⟩))
  | a :: p, b :: q => by
    by_cases hab : a = b
    · subst hab
      rcases segs_rel p q with rfl | ⟨f, r, rfl⟩ | ⟨f, r, rfl⟩ | hd
      · exact .inl rfl
      · exact .inr (.inl ⟨f, r, rfl⟩)
      · exact .inr (.inr (.inl ⟨f, r, rfl⟩))
      · exact .inr (.inr (.inr (.inr hd)))
    · exact .inr (.inr (.inr (.inl hab)))

theorem cps_findLive_savePrim {v v' : SVal} {ps : List Seg} {a b : PrimVal}
    (hf : v.findLive ps = .ok (.prim a)) (hs : v.saveLive ps (.prim b) = .ok v') (qs : List Seg) :
    (∃ x, v'.findLive qs = .ok x ∧ Cps x) ↔ (∃ x, v.findLive qs = .ok x ∧ Cps x) := by
  rcases segs_rel ps qs with rfl | ⟨f, r, rfl⟩ | ⟨f, r, rfl⟩ | hd
  · rw [findLive_saveLive_same hs, hf]
    exact iff_of_true ⟨_, rfl, Cps.prim b⟩ ⟨_, rfl, Cps.prim a⟩
  · obtain ⟨w, w', h₁, h₂, h₃⟩ := save_through qs (f :: r) hs
    rw [SVal.findLive_append, h₁, Res.ok_bind] at hf
    rw [h₃, h₁]
    have hw := cps_saveLive hf h₂ (iff_of_true (Cps.prim b) (Cps.prim a))
    constructor
    · rintro ⟨x, hx, hc⟩; cases hx; exact ⟨w, rfl, hw.1 hc⟩
    · rintro ⟨x, hx, hc⟩; cases hx; exact ⟨w', rfl, hw.2 hc⟩
  · rw [SVal.findLive_append, SVal.findLive_append, findLive_saveLive_same hs, hf]
    rw [Res.ok_bind', Res.ok_bind']
    apply iff_of_false <;> (rintro ⟨x, hx, -⟩; cases f <;> cases hx)
  · rw [findLive_saveLive_diverge hd hs]

/-- What `cpok` returns on the storage `v` at the path `qs`. -/
def cpR (σ : State) (v : SVal) (qs : List Seg) : Res Value :=
  v.findLive qs >>= fun sv => copyStToM (memBase σ) sv >>= fun _ => .ok (.bool true)

theorem cpok_eval (σ : State) (s : LStor) (q : LPath) :
    (LTerm.cpok s q).eval σ = (s.eval σ >>= fun v => q.eval σ >>= fun qs => cpR σ v qs) := rfl

theorem cpR_ok {σ : State} {v : SVal} {qs : List Seg} {a : Value} :
    cpR σ v qs = .ok a ↔ a = .bool true ∧ ∃ x, v.findLive qs = .ok x ∧ Cps x := by
  unfold cpR
  constructor
  · intro h
    obtain ⟨x, hx, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨r, hr, h⟩ := Res.bind_eq_ok.1 h
    cases h
    exact ⟨rfl, x, hx, _, _, hr⟩
  · rintro ⟨rfl, x, hx, hc⟩
    obtain ⟨r, hr⟩ := hc.at (memBase σ)
    rw [hx, Res.ok_bind, hr, Res.ok_bind]

/-- `cpok` kept whole is what it tests. -/
theorem cpok_keep_sim {σ : State} {s : LStor} {Q : LPath} {v : SVal} {qs : List Seg}
    (hv : s.eval σ = .ok v) (hq : Q.eval σ = .ok qs) :
    Sim ((LTerm.cpok s Q).eval σ) (cpR σ v qs) := by
  rw [cpok_eval, hv, Res.ok_bind, hq, Res.ok_bind]
  exact Sim.refl _

theorem cpR_sim {σ : State} {v v' : SVal} {qs qs' : List Seg}
    (h : (∃ x, v.findLive qs = .ok x ∧ Cps x) ↔ ∃ x, v'.findLive qs' = .ok x ∧ Cps x) :
    Sim (cpR σ v qs) (cpR σ v' qs') := fun _ => by rw [cpR_ok, cpR_ok, h]

/-- **A word written over a word keeps whether a copy succeeds** (Lean
only: `copyStToM` halts on a mapping, and a word is none). -/
theorem save_cpok_sim {σ : State} {s : LStor} {P Q : LPath} {w X C : LTerm} {u : SVal}
    {qs : List Seg} (hu : (LStor.save s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (hX : ∀ {v ps}, s.eval σ = .ok v → P.elim.eval σ = .ok ps →
      Sim (X.eval σ) (v.findLive ps >>= SVal.asValue))
    (hC : ∀ {v}, s.eval σ = .ok v → Sim (C.eval σ) (cpR σ v qs)) :
    Sim ((LTerm.ite (isT X) C (.cpok (.save s P w) Q)).eval σ) (cpR σ u qs) := by
  have hu' := hu
  obtain ⟨wv, hw, hu⟩ := Res.bind_eq_ok.1 hu
  obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
  obtain ⟨ps, hp, hs⟩ := Res.bind_eq_ok.1 hu
  rw [LTerm.eval, isT_eval, Res.ok_bind]
  cases hx : X.eval σ with
  | error e =>
    simp only [pickBranch, cpok_eval, hu', hq, Res.ok_bind]
    exact Sim.refl _
  | ok val =>
    simp only [pickBranch]
    obtain ⟨sv, hf, ha⟩ := Res.bind_eq_ok.1 (((hX hv ((hP ps).2 hp)) val).1 hx)
    cases sv with
    | prim pa =>
      cases wv with
      | int z =>
        exact Sim.trans (hC hv) (cpR_sim (cps_findLive_savePrim hf hs qs).symm)
      | bool z =>
        exact Sim.trans (hC hv) (cpR_sim (cps_findLive_savePrim hf hs qs).symm)
    | struct _ | array _ _ _ | map _ _ => simp only [SVal.asValue, reduceCtorEq] at ha

end CopyOk

/-! ### Writes through a dangling alias: soundness

The `.stale` arms, one lemma per reader.  A stale write is the
interpreter's slot-level `SVal.save` of a word; the facts it rests on are
`Calculus/SlotLemmas.lean`'s. -/

section Stale

variable {σ : State}

/-- A word is a primitive value. -/
theorem toSVal_prim (wv : Value) : ∃ x, wv.toSVal = .prim x := by
  cases wv <;> exact ⟨_, rfl⟩

/-- A stale write that returned: the word, the storage, and the slot path. -/
theorem stale_eval_ok {s : LStor} {P : LPath} {w : LTerm} {u : SVal}
    (hu : (LStor.stale none s P w).eval σ = .ok u) :
    ∃ wv v ps, w.eval σ = .ok wv ∧ s.eval σ = .ok v ∧ P.eval σ = .ok ps ∧
      v.save ps wv.toSVal = .ok u := by
  obtain ⟨wv, hw, hu⟩ := Res.bind_eq_ok.1 hu
  obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
  obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
  exact ⟨wv, v, ps, hw, hv, hp, hu⟩

/-- The slot past the end, read at `r`, as a run: where the slot has the
location (`slotHasU`'s specification). -/
def slotHas (sh : List SVal) (r : List Seg) : Res Value :=
  headR sh >>= fun c => c.findLive r >>= fun _ => .ok (.bool true)

theorem pushSlot_headR {sh sh' : List SVal} (h : headR sh = headR sh') (R : RefTy) :
    (pushSlot (.ref R) sh).1 = (pushSlot (.ref R) sh').1 := by
  cases sh <;> cases sh' <;> simp only [headR, reduceCtorEq, Except.ok.injEq] at h
  · rfl
  · subst h; simp only [pushSlot_ref_cons]

/-- A word written at a slot that returns leaves an array at `ps` only if
one was there, as long. -/
theorem findLive_save_back {x : PrimVal} {v u : SVal} {qs ps : List Seg} {es sh : List SVal}
    {fx : Bool} (h : v.save qs (.prim x) = .ok u) (hu : u.findLive ps = .ok (.array es sh fx)) :
    ∃ es' sh', v.findLive ps = .ok (.array es' sh' fx) ∧ es'.length = es.length := by
  rcases segs_rel ps qs with rfl | ⟨f, r, rfl⟩ | ⟨f, r, rfl⟩ | hd
  · exact absurd (by rw [List.append_nil]; exact hu) (save_prim_not_array [] h)
  · exact absurd hu (save_prim_not_array (f :: r) h)
  · obtain ⟨c, hc⟩ : ∃ c, v.findLive ps = .ok c := by
      cases hc : v.findLive ps with
      | ok c => exact ⟨c, rfl⟩
      | error e => rw [findLive_save_prefix (f :: r) h, hc] at hu; cases hu
    obtain ⟨c', hc', hu'⟩ := save_prefix_ok h hc
    rw [hu] at hu'
    cases hu'
    obtain ⟨hl, -, hfx⟩ := save_cons_shape hc'
    cases c with
    | array es' sh' fx' =>
      simp only [Close.arrLen, isFixV, Except.ok.injEq, PrimVal.int.injEq] at hl hfx
      subst hfx
      exact ⟨es', sh', hc, by omega⟩
    | prim _ | struct _ | map _ _ => simp only [Close.arrLen, reduceCtorEq] at hl
  · exact ⟨es, sh, by rw [← findLive_save_diverge (diverge_flip hd) h, hu], rfl⟩

/-- A stale write below a live read keeps what the read gives, where the
reader keeps a write below a value (`save_cons_shape`). -/
theorem findLive_save_above_eq {G : SVal → Res Value} {new v u : SVal} {qs : List Seg}
    {f : Seg} {t : List Seg}
    (hG : ∀ (c c' : SVal) (a : Seg) (r : List Seg), c.save (a :: r) new = .ok c' → G c' = G c)
    (hs : v.save (qs ++ f :: t) new = .ok u) : (u.findLive qs >>= G) = (v.findLive qs >>= G) := by
  cases hc : v.findLive qs with
  | error e => rw [findLive_save_prefix (f :: t) hs, hc]; rfl
  | ok c =>
    obtain ⟨c', hc', hu⟩ := save_prefix_ok hs hc
    rw [hu, Res.ok_bind, Res.ok_bind]
    exact hG c c' f t hc'

theorem staleOk_sim {H opq : LTerm} {slot : Option (LTerm × LTerm × LTerm)} {y : Res Value}
    (hH : ∀ x, H.eval σ = .ok x → y = .ok x)
    (hS : ∀ k L S, slot = some (k, L, S) → ∀ x,
      (LTerm.kite k L S .err).eval σ = .ok x → y = .ok x)
    (ho : Sim (opq.eval σ) y) : Sim ((staleOk H slot opq).eval σ) y := by
  simp only [staleOk, LTerm.eval]
  refine orElse_sound_sim (fun x hx => ?_) ho
  cases hh : H.eval σ with
  | ok x' => rw [hh, orElseR_ok] at hx; cases hx; exact hH _ hh
  | error e =>
    rw [hh, orElseR_error] at hx
    cases slot with
    | none => simp only [LTerm.eval, reduceCtorEq] at hx
    | some kLS =>
      obtain ⟨k, L, S⟩ := kLS
      exact hS k L S rfl x hx

/-- One direction of `cmp_sim`. -/
theorem cmp_sound {P Q : LPath} {ps qs : List Seg} (hp : P.eval σ = .ok ps)
    (hq : Q.eval σ = .ok qs) {leaf : PathRel → LTerm} {y : Res Value}
    (h : ∀ r : PathRel, r.Holds σ ps qs → ∀ x, (leaf r).eval σ = .ok x → y = .ok x) :
    ∀ x, (((cmpSegs P.segs Q.segs).toTerm leaf).eval σ) = .ok x → y = .ok x := by
  have hp' := LPath.segs_eval σ hp
  have hq' := LPath.segs_eval σ hq
  rw [CaseTree.toTerm_eval σ _ _ (cmpSegs_testsOk σ _ _ hp' hq')]
  exact h _ (cmpSegs_holds σ _ _ hp' hq')

theorem LPath.splitLast_eval : ∀ {Q A : LPath} {k : LTerm} {rest : List SSeg} {qs : List Seg},
    Q.splitLast = some (A, k, rest) → Q.eval σ = .ok qs →
      ∃ as i r, A.eval σ = .ok as ∧ (k.eval σ >>= Value.asInt) = .ok i ∧
        segsEval σ rest = .ok r ∧ qs = as ++ .at i :: r
  | .root _, _, _, _, _, h, _ => by cases h
  | .at q k', A, k, rest, qs, h, he => by
    simp only [LPath.splitLast, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨as, ha, he⟩ := Res.bind_eq_ok.1 he
    obtain ⟨i, hi, he⟩ := Res.bind_eq_ok.1 he
    cases he
    exact ⟨as, i, [], ha, hi, rfl, rfl⟩
  | .field q f, A, k, rest, qs, h, he => by
    simp only [LPath.splitLast, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨A', k', r'⟩, h, rfl, rfl, rfl⟩ := h
    obtain ⟨qs', hq', he⟩ := Res.bind_eq_ok.1 he
    cases he
    obtain ⟨as, i, r, ha, hi, hr, rfl⟩ := LPath.splitLast_eval h hq'
    refine ⟨as, i, r ++ [.field f], ha, hi, segsEval_append σ hr rfl, ?_⟩
    simp only [List.append_assoc, List.cons_append]

/-- **The run guard of a stale write**: `staleOk` returns exactly where the
write does. -/
theorem stale_okE_sim {s : LStor} {q : LPath} {w : LTerm}
    (hs : Sim (s.okE.eval σ) (s.eval σ >>= fun _ => .ok (.bool true)))
    (hW : Sim (w.elim.eval σ) (w.eval σ))
    (hP : Sim (q.elim.eval σ) (q.eval σ))
    (ihH : ∀ {v qs}, s.eval σ = .ok v → q.elim.eval σ = .ok qs →
      Sim ((s.hasU q.elim).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true)))
    (ihL : ∀ (A : LPath) {v qs}, s.eval σ = .ok v → A.eval σ = .ok qs →
      Sim ((s.lenU A).eval σ) (v.findLive qs >>= Close.arrLen))
    (ihS : ∀ (A : LPath) (rest : List SSeg) {v : SVal} {ps : List Seg} {es sh : List SVal}
      {fx : Bool} {r : List Seg}, s.eval σ = .ok v → A.eval σ = .ok ps →
      v.findLive ps = .ok (.array es sh fx) → segsEval σ rest = .ok r →
      ∀ x, (s.slotHasU A rest .err).eval σ = .ok x → slotHas sh r = .ok x) :
    Sim ((LStor.stale none s q w).okE.eval σ)
      ((LStor.stale none s q w).eval σ >>= fun _ => .ok (.bool true)) := by
  simp only [LStor.okE]
  split
  · rename_i hn
    have hG : ∀ {wv v qs}, w.eval σ = .ok wv → s.eval σ = .ok v → q.eval σ = .ok qs →
        Sim ((staleOk (s.hasU q.elim) (match q.elim.splitLast with
          | some (A, k, rest) => some (k, s.lenU A, s.slotHasU A rest .err)
          | none => none) (.sok (.stale none s q w))).eval σ)
          (v.save qs wv.toSVal >>= fun _ => .ok (.bool true)) := by
      intro wv v qs hw hv hq
      have hqe : q.elim.eval σ = .ok qs := (hP qs).2 hq
      have hNL : ∀ t ∈ qs, t ≠ .field "length" := LPath.noLen_eval σ hn hq
      have hok : ∀ c, v.find qs = .ok c →
          (v.save qs wv.toSVal >>= fun _ => (.ok (Value.bool true) : Res Value)) =
            .ok (Value.bool true) := fun c hc => by
        obtain ⟨u, hu⟩ := save_ok_of_find_ok (new := wv.toSVal) hNL hc
        rw [hu]; rfl
      refine staleOk_sim (fun x hx => ?_) (fun k L S hslot x hx => ?_) ?_
      · obtain ⟨c, hc, he⟩ := Res.bind_eq_ok.1 (((ihH hv hqe) x).1 hx)
        cases he
        exact hok c (SVal.find_of_findLive hc)
      · split at hslot
        · rename_i A k' rest hsp
          simp only [Option.some.injEq, Prod.mk.injEq] at hslot
          obtain ⟨rfl, rfl, rfl⟩ := hslot
          obtain ⟨as, i, r, ha, hi, hr, rfl⟩ := LPath.splitLast_eval hsp hqe
          simp only [LTerm.eval, hi, Res.ok_bind] at hx
          obtain ⟨j, hj, hx1⟩ := Res.bind_eq_ok.1 hx
          obtain ⟨n, hnv, hj1⟩ := Res.bind_eq_ok.1 hj
          split at hx1
          · rename_i hij
            subst hij
            obtain ⟨c0, hc0, hl⟩ := Res.bind_eq_ok.1 (((ihL A hv ha) n).1 hnv)
            cases c0 with
            | array es sh fx =>
              simp only [Close.arrLen, Except.ok.injEq] at hl
              subst hl
              simp only [Value.asInt, Except.ok.injEq] at hj1
              subst hj1
              obtain ⟨c, hc, hx'⟩ := Res.bind_eq_ok.1 (ihS A rest hv ha hc0 hr x hx1)
              obtain ⟨t, rfl⟩ := headR_ok hc
              obtain ⟨y, hy, hx'⟩ := Res.bind_eq_ok.1 hx'
              cases hx'
              refine hok y ?_
              rw [find_past_end hc0 r]
              exact SVal.find_of_findLive hy
            | prim _ | struct _ | map _ _ => simp only [Close.arrLen, reduceCtorEq] at hl
          · simp only [reduceCtorEq] at hx1
        · cases hslot
      · simp only [LTerm.eval, LStor.eval, hw, hv, hq, Res.ok_bind, staleSave]
        exact Sim.refl _
    intro a
    simp only [LTerm.eval, LStor.eval, Res.bind_eq_ok]
    constructor
    · rintro ⟨_, h₁, wv, h₂, _, ⟨qs, h₃, -⟩, h₄⟩
      obtain ⟨v, hv, -⟩ := Res.bind_eq_ok.1 ((hs _).1 h₁)
      have hw := (hW wv).1 h₂
      have hq := (hP qs).1 h₃
      obtain ⟨u, hu, he⟩ := Res.bind_eq_ok.1 (((hG hw hv hq) a).1 h₄)
      exact ⟨u, ⟨wv, hw, v, hv, qs, hq, hu⟩, he⟩
    · rintro ⟨u, ⟨wv, hw, v, hv, qs, hq, hu⟩, he⟩
      refine ⟨.bool true, (hs _).2 (by simp only [hv, Res.ok_bind]), wv,
        (hW wv).2 hw, .bool true, ⟨qs, (hP qs).2 hq, rfl⟩, ?_⟩
      exact ((hG hw hv hq) a).2 (by rw [show staleSave none wv v qs = v.save qs wv.toSVal from rfl] at hu; rw [hu]; exact he)
  · exact Sim.refl _

theorem stale_readU_sim {s : LStor} {P Q : LPath} {w : LTerm} {u : SVal} {qs : List Seg}
    (hu : (LStor.stale none s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ)) (hW : Sim (w.elim.eval σ) (w.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue))
    (ihH : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.hasU Q).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true))) :
    Sim (((LStor.stale none s P w).readU Q).eval σ) (u.findLive qs >>= SVal.asValue) := by
  obtain ⟨wv, v, ps, hw, hv, hp, hs⟩ := stale_eval_ok hu
  obtain ⟨x, hx⟩ := toSVal_prim wv
  have hs' : v.save ps (.prim x) = .ok u := hx ▸ hs
  rw [LStor.readU]
  refine cmp_sim ((hP ps).2 hp) hq fun r hr => ?_
  cases r with
  | eq =>
    simp only [PathRel.Holds] at hr
    subst hr
    simp only [staleRead, LTerm.eval]
    rw [findLive_save_live hs]
    refine (Sim.bind (ihH hv hq) fun _ => hW.trans (Sim.of_eq hw)).trans (Sim.of_eq ?_)
    cases v.findLive qs <;> simp only [Res.ok_bind, Res.error_bind, Close.asValue_toSVal]
  | above =>
    obtain ⟨f, t, rfl⟩ := hr
    exact Sim.halt (by simp only [staleRead, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
      implies_true]) (findLive_save_above f t hs)
  | below k =>
    obtain ⟨f, t, rfl, -⟩ := hr
    refine Sim.halt (by simp only [staleRead, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
      implies_true]) fun a h => ?_
    obtain ⟨y, hy, -⟩ := Res.bind_eq_ok.1 h
    exact findLive_save_below f t hs' y hy
  | diverge => simp only [staleRead]; rw [findLive_save_diverge hr hs]; exact ihR hv hq

theorem stale_hasU_sim {s : LStor} {P Q : LPath} {w : LTerm} {u : SVal} {qs : List Seg}
    (hu : (LStor.stale none s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihH : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.hasU Q).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true))) :
    Sim (((LStor.stale none s P w).hasU Q).eval σ) (u.findLive qs >>= fun _ => .ok (.bool true)) := by
  obtain ⟨wv, v, ps, -, hv, hp, hs⟩ := stale_eval_ok hu
  obtain ⟨x, hx⟩ := toSVal_prim wv
  have hs' : v.save ps (.prim x) = .ok u := hx ▸ hs
  rw [LStor.hasU]
  refine cmp_sim ((hP ps).2 hp) hq fun r hr => ?_
  cases r with
  | eq =>
    simp only [PathRel.Holds] at hr
    subst hr
    simp only [staleHas]
    rw [findLive_save_live hs]
    refine (ihH hv hq).trans (Sim.of_eq ?_)
    cases v.findLive qs <;> rfl
  | above =>
    obtain ⟨f, t, rfl⟩ := hr
    simp only [staleHas]
    rw [findLive_save_above_eq (fun _ _ _ _ _ => rfl) hs]
    exact ihH hv hq
  | below k =>
    obtain ⟨f, t, rfl, -⟩ := hr
    refine Sim.halt (by simp only [staleHas, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
      implies_true]) fun a h => ?_
    obtain ⟨y, hy, -⟩ := Res.bind_eq_ok.1 h
    exact findLive_save_below f t hs' y hy
  | diverge => simp only [staleHas]; rw [findLive_save_diverge hr hs]; exact ihH hv hq

theorem stale_lenU_sim {s : LStor} {P Q : LPath} {w : LTerm} {u : SVal} {qs : List Seg}
    (hu : (LStor.stale none s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihL : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.lenU Q).eval σ) (v.findLive qs >>= Close.arrLen)) :
    Sim (((LStor.stale none s P w).lenU Q).eval σ) (u.findLive qs >>= Close.arrLen) := by
  obtain ⟨wv, v, ps, -, hv, hp, hs⟩ := stale_eval_ok hu
  obtain ⟨x, hx⟩ := toSVal_prim wv
  have hs' : v.save ps (.prim x) = .ok u := hx ▸ hs
  rw [LStor.lenU]
  refine cmp_sim ((hP ps).2 hp) hq fun r hr => ?_
  cases r with
  | eq =>
    simp only [PathRel.Holds] at hr
    subst hr
    refine Sim.halt (by simp only [saveMap, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
      implies_true]) ?_
    rw [findLive_save_live hs']
    cases v.findLive qs <;> simp only [Res.ok_bind, Res.error_bind, Close.arrLen, ne_eq,
      reduceCtorEq, not_false_eq_true, implies_true]
  | above =>
    obtain ⟨f, t, rfl⟩ := hr
    simp only [saveMap]
    rw [findLive_save_above_eq (fun _ _ _ _ h => (save_cons_shape h).1) hs]
    exact ihL hv hq
  | below k =>
    obtain ⟨f, t, rfl, -⟩ := hr
    refine Sim.halt (by simp only [saveMap, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
      implies_true]) fun a h => ?_
    obtain ⟨y, hy, -⟩ := Res.bind_eq_ok.1 h
    exact findLive_save_below f t hs' y hy
  | diverge => simp only [saveMap]; rw [findLive_save_diverge hr hs]; exact ihL hv hq

theorem stale_mapU_sim {s : LStor} {P Q : LPath} {w : LTerm} {u : SVal} {qs : List Seg}
    {sh : KShape} (hu : (LStor.stale none s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihM : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)) :
    Sim (((LStor.stale none s P w).mapU sh Q).eval σ) (u.findLive qs >>= sh.test) := by
  obtain ⟨wv, v, ps, -, hv, hp, hs⟩ := stale_eval_ok hu
  obtain ⟨x, hx⟩ := toSVal_prim wv
  have hs' : v.save ps (.prim x) = .ok u := hx ▸ hs
  rw [LStor.mapU]
  refine cmp_sim ((hP ps).2 hp) hq fun r hr => ?_
  cases r with
  | eq =>
    simp only [PathRel.Holds] at hr
    subst hr
    refine Sim.halt (by simp only [saveMap, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
      implies_true]) ?_
    rw [findLive_save_live hs']
    cases v.findLive qs <;> cases sh <;> simp only [Res.ok_bind, Res.error_bind, KShape.test,
      kmapF, isMapV, isFixV, Bool.false_eq_true, ↓reduceIte, ne_eq, reduceCtorEq,
      not_false_eq_true, implies_true]
  | above =>
    obtain ⟨f, t, rfl⟩ := hr
    simp only [saveMap]
    rw [findLive_save_above_eq (fun _ _ _ _ h => by
      obtain ⟨-, hm, hf⟩ := save_cons_shape h
      cases sh <;> simp only [KShape.test, kmapF, hm, hf]) hs]
    exact ihM hv hq
  | below k =>
    obtain ⟨f, t, rfl, -⟩ := hr
    refine Sim.halt (by simp only [saveMap, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
      implies_true]) fun a h => ?_
    obtain ⟨y, hy, -⟩ := Res.bind_eq_ok.1 h
    exact findLive_save_below f t hs' y hy
  | diverge => simp only [saveMap]; rw [findLive_save_diverge hr hs]; exact ihM hv hq

/-- What every slot reader through a stale write needs: the write, the
array before it (as long), and the slot path evaluated. -/
theorem stale_slot_setup {s : LStor} {P' P : LPath} {w : LTerm} {rest : List SSeg}
    {u : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool} {r : List Seg}
    (hu : (LStor.stale none s P' w).eval σ = .ok u) (hp : P.eval σ = .ok ps)
    (hn : u.findLive ps = .ok (.array es sh fx)) (hr : segsEval σ rest = .ok r)
    (ihL : ∀ {v qs}, s.eval σ = .ok v → P.eval σ = .ok qs →
      Sim ((s.lenU P).eval σ) (v.findLive qs >>= Close.arrLen)) :
    ∃ wv x v qs es' sh', w.eval σ = .ok wv ∧ wv.toSVal = .prim x ∧ s.eval σ = .ok v ∧
      P'.eval σ = .ok qs ∧ v.save qs (.prim x) = .ok u ∧
      v.findLive ps = .ok (.array es' sh' fx) ∧ es'.length = es.length ∧
      ((P.at (s.lenU P)).addSegs rest).eval σ = .ok ((ps ++ [.at es.length]) ++ r) := by
  obtain ⟨wv, v, qs, hw, hv, hq, hs⟩ := stale_eval_ok hu
  obtain ⟨x, hx⟩ := toSVal_prim wv
  rw [hx] at hs
  obtain ⟨es', sh', hv', hl⟩ := findLive_save_back hs hn
  have hL : (s.lenU P).eval σ = .ok (.int es.length) := by
    have h := ((ihL hv hp) (.int es'.length)).2 (by rw [hv', Res.ok_bind]; rfl)
    rw [hl] at h
    exact h
  refine ⟨wv, x, v, qs, es', sh', hw, hx, hv, hq, hs, hv', hl, ?_⟩
  rw [LPath.addSegs_eval]
  simp only [LPath.eval, hp, hL, hr, Res.ok_bind, Value.asInt]

/-- A read below a word written at a slot runs through the written slot. -/
theorem stale_below_cases {x : PrimVal} {v u : SVal} {qs ps r : List Seg} {L : Int} {f : Seg}
    {t : List Seg} {es sh : List SVal} {fx : Bool}
    (hs : v.save qs (.prim x) = .ok u) (hn : u.findLive ps = .ok (.array es sh fx))
    (h : (ps ++ [.at L]) ++ r = qs ++ f :: t) :
    ∃ a', qs = (ps ++ [.at L]) ++ a' ∧ r = a' ++ f :: t := by
  rcases List.append_eq_append_iff.1 h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · exact ⟨a', h1, h2⟩
  · cases c' with
    | nil =>
      simp only [List.append_nil, List.nil_append] at h1 h2
      exact ⟨[], by rw [List.append_nil, h1], by rw [List.nil_append, h2]⟩
    | cons y ys =>
      exfalso
      rcases List.append_eq_append_iff.1 h1 with ⟨a', h3, h4⟩ | ⟨b', h3, -⟩
      · cases a' with
        | nil =>
          rw [List.append_nil] at h3
          subst h3
          exact save_prim_not_array [] hs (by rw [List.append_nil]; exact hn)
        | cons z zs =>
          have hlen := congrArg List.length h4
          simp only [List.length_cons, List.length_nil, List.cons_append, List.length_append]
            at hlen
          omega
      · subst h3
        exact save_prim_not_array b' hs hn

/-- **The slot a `push()` recycles, through a stale write**
(`storagePushLengthSaveReferenceElement`, then `selectOnSaveCons`): the word
where the write is at the slot's location, nothing above or below it, the
slot below the write elsewhere. -/
theorem stale_slotU_sim {s : LStor} {P' P : LPath} {w opq : LTerm}
    {rest : List SSeg} {u : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool} {R : RefTy}
    {r : List Seg}
    (hu : (LStor.stale none s P' w).eval σ = .ok u) (hP' : Sim (P'.elim.eval σ) (P'.eval σ))
    (hW : Sim (w.elim.eval σ) (w.eval σ))
    (hp : P.eval σ = .ok ps) (hn : u.findLive ps = .ok (.array es sh fx))
    (hr : segsEval σ rest = .ok r)
    (hopq : Sim (opq.eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue))
    (ihS : ∀ {v : SVal} {es sh : List SVal}, s.eval σ = .ok v →
      v.findLive ps = .ok (.array es sh fx) →
      Sim (opq.eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue) →
      Sim ((s.slotU P rest opq).eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue))
    (ihL : ∀ {v qs}, s.eval σ = .ok v → P.eval σ = .ok qs →
      Sim ((s.lenU P).eval σ) (v.findLive qs >>= Close.arrLen)) :
    Sim (((LStor.stale none s P' w).slotU P rest opq).eval σ)
      ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue) := by
  obtain ⟨wv, x, v, qs, es', sh', hw, hx, hv, hq, hs, hv', hl, hSP⟩ :=
    stale_slot_setup hu hp hn hr ihL
  have hhu := find_slot_head hn
  have hhv := find_slot_head hv'
  rw [hl] at hhv
  rw [LStor.slotU]
  refine cmp_sim ((hP' qs).2 hq) hSP fun rel hrel => ?_
  cases rel with
  | eq =>
    simp only [PathRel.Holds] at hrel
    subst hrel
    obtain ⟨c, c', hc, hc', huc⟩ := find_save_append hs
    rw [hhu] at huc
    obtain ⟨t, rfl⟩ := headR_ok huc
    simp only [saveLeaf]
    split
    · exact hopq
    · rename_i hk
      have hnoAt : r.any Seg.isAt = false := by rw [segsEval_any σ hr]; simpa only [Bool.not_eq_true] using hk
      obtain ⟨y, hy⟩ := find_ok_of_save_ok hc'
      rw [pushSlot_ref_cons, findLive_save_live hc', findLive_eq_find c r hnoAt, hy, Res.ok_bind,
        Res.ok_bind, ← hx, Close.asValue_toSVal]
      exact hW.trans (Sim.of_eq hw)
  | above =>
    obtain ⟨f, t, rfl⟩ := hrel
    have hs2 : v.save ((ps ++ [.at es.length]) ++ (r ++ f :: t)) (.prim x) = .ok u := by
      rw [← List.append_assoc]; exact hs
    obtain ⟨c, c', hc, hc', huc⟩ := find_save_append hs2
    rw [hhu] at huc
    obtain ⟨t', rfl⟩ := headR_ok huc
    rw [pushSlot_ref_cons]
    exact Sim.halt (by simp only [saveLeaf, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
      implies_true]) (findLive_save_above f t hc')
  | below k =>
    obtain ⟨f, t, hft, -⟩ := hrel
    obtain ⟨a', rfl, rfl⟩ := stale_below_cases hs hn hft
    obtain ⟨c, c', hc, hc', huc⟩ := find_save_append hs
    rw [hhu] at huc
    obtain ⟨t', rfl⟩ := headR_ok huc
    rw [pushSlot_ref_cons]
    refine Sim.halt (by simp only [saveLeaf, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
      implies_true]) fun a h => ?_
    obtain ⟨y, hy, -⟩ := Res.bind_eq_ok.1 h
    exact findLive_save_below f t hc' y hy
  | diverge =>
    simp only [saveLeaf]
    have heq : (pushSlot (.ref R) sh).1.findLive r = (pushSlot (.ref R) sh').1.findLive r := by
      rcases find_save_diverge_tail hs hrel with h | ⟨t, c, c', -, ht, hc, hc', huc⟩
      · rw [pushSlot_headR (sh := sh) (sh' := sh') (by rw [← hhu, ← hhv, h]) R]
      · rw [hhu] at huc
        rw [hhv] at hc
        obtain ⟨_, rfl⟩ := headR_ok huc
        obtain ⟨_, rfl⟩ := headR_ok hc
        rw [pushSlot_ref_cons, pushSlot_ref_cons, findLive_save_diverge ht hc']
    rw [heq] at hopq ⊢
    exact ihS hv hv' hopq

theorem delSlotHas_sim {s : LStor} {v e : SVal} {E : LPath} {eps : List Seg}
    {rest : List SSeg} {r : List Seg}
    (hE : E.eval σ = .ok eps) (he : v.findLive eps = .ok e) (hr : segsEval σ rest = .ok r)
    (ihH : ∀ (Q : LPath) {qs}, Q.eval σ = .ok qs →
      Sim ((s.hasU Q).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true)))
    (ihM : ∀ (sh : KShape) (Q : LPath) {qs}, Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)) :
    Sim ((delHas (s.hasU (E.addSegs rest)) E (fun sh q => s.mapU sh q)
      (if rest.isEmpty then .eq else .below rest)).eval σ)
      (e.defaultOf.findLive r >>= fun _ => .ok (.bool true)) := by
  have hQ : (E.addSegs rest).eval σ = .ok (eps ++ r) := by
    rw [LPath.addSegs_eval, hE, Res.ok_bind, hr, Res.ok_bind]
  have hold := ihH _ hQ
  by_cases hemp : rest.isEmpty = true
  · have hr0 : r = [] := (segsEval_isEmpty hr).1 hemp
    subst hr0
    rw [if_pos hemp]
    simp only [delHas, LTerm.eval, SVal.findLive_nil, Res.ok_bind]
    exact Sim.refl _
  · rw [if_neg hemp]
    simp only [delHas]
    have h := delBelow_sim (v := v) (G := fun _ => .ok (.bool true))
      (fun sh q qs hq' => ihM sh q hq') hold hold rest E eps r hE hr rfl
    rw [he, Res.ok_bind] at h
    exact h

/-- **Whether the slot a `pop` vacated has the location** (`storagePopSave`'s
`delAt`, then `selectOnDelAtCons`, `delFieldIndexStruct`). -/
theorem pop_slotHasU_sound {keep : Bool} {s : LStor} {P' P : LPath} {w' opq : LTerm}
    {rest : List SSeg} {v : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool}
    {r : List Seg}
    (hu : (LStor.arr (.pop keep) s P' w').eval σ = .ok v) (hP' : Sim (P'.elim.eval σ) (P'.eval σ))
    (hp : P.eval σ = .ok ps) (hn : v.findLive ps = .ok (.array es sh fx))
    (hr : segsEval σ rest = .ok r)
    (hopq : ∀ x, opq.eval σ = .ok x → slotHas sh r = .ok x)
    (ihH : ∀ (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.hasU Q).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true)))
    (ihM : ∀ (sh : KShape) (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test))
    (ihL : ∀ {v qs}, s.eval σ = .ok v → P.eval σ = .ok qs →
      Sim ((s.lenU P).eval σ) (v.findLive qs >>= Close.arrLen)) :
    ∀ x, (((LStor.arr (.pop keep) s P' w').slotHasU P rest opq).eval σ) = .ok x →
      slotHas sh r = .ok x := by
  rw [LStor.slotHasU]
  split
  · rename_i heq
    have hPe : P'.elim = P := by simpa only [beq_iff_eq] using heq
    obtain ⟨wv, v', ps', c0, c1, -, hv', hp', hc0, hap, hu'⟩ := arr_eval_ok hu
    have hpp : ps' = ps := by
      have := (hP' ps').2 hp'
      rw [hPe, hp] at this
      cases this; rfl
    subst hpp
    rw [findLive_saveLive_same hu'] at hn
    obtain ⟨es0, last, sh0, fx0, rfl, rfl⟩ := AOp.apply_pop_eq hap
    simp only [Except.ok.injEq, SVal.array.injEq] at hn
    obtain ⟨rfl, rfl, rfl⟩ := hn
    have hL := ihL hv' hp
    rw [hc0, Res.ok_bind] at hL
    have hL' : (s.lenU P).eval σ = .ok (.int (es0 ++ [last]).length) := (hL _).2 rfl
    have hE : (P.at (lenPred (s.lenU P))).eval σ = .ok (ps' ++ [.at es0.length]) := by
      simp only [LPath.eval, hp, Res.ok_bind, lenPred_eval hL', Value.asInt]
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
          Int.natCast_add, Int.cast_ofNat_Int, Int.add_sub_cancel]
    have he : v'.findLive (ps' ++ [.at es0.length]) = .ok last := by
      rw [SVal.findLive_append, hc0, Res.ok_bind, findLive_last]
    intro x hx
    simp only [slotHas, headR, Res.ok_bind]
    cases keep
    · simp only [Bool.false_eq_true, if_false] at hx ⊢
      exact ((delSlotHas_sim hE he hr (fun Q _ hq => ihH Q hv' hq)
        (fun sh Q _ hq => ihM sh Q hv' hq)) x).1 hx
    · simp only [if_true] at hx ⊢
      have hQ : ((P.at (lenPred (s.lenU P))).addSegs rest).eval σ =
          .ok ((ps' ++ [.at es0.length]) ++ r) := by
        rw [LPath.addSegs_eval, hE, Res.ok_bind, hr, Res.ok_bind]
      have := ((ihH _ hv' hQ) x).1 hx
      rw [SVal.findLive_append, he, Res.ok_bind] at this
      exact this
  · exact hopq

/-- **Whether the slot past the end has the location, through a stale
write**: as before, nothing below the written word. -/
theorem stale_slotHasU_sound {s : LStor} {P' P : LPath} {w opq : LTerm}
    {rest : List SSeg} {u : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool} {r : List Seg}
    (hu : (LStor.stale none s P' w).eval σ = .ok u) (hP' : Sim (P'.elim.eval σ) (P'.eval σ))
    (hp : P.eval σ = .ok ps) (hn : u.findLive ps = .ok (.array es sh fx))
    (hr : segsEval σ rest = .ok r)
    (hopq : ∀ x, opq.eval σ = .ok x → slotHas sh r = .ok x)
    (ihS : ∀ {v : SVal} {es sh : List SVal}, s.eval σ = .ok v →
      v.findLive ps = .ok (.array es sh fx) →
      (∀ x, opq.eval σ = .ok x → slotHas sh r = .ok x) →
      ∀ x, (s.slotHasU P rest opq).eval σ = .ok x → slotHas sh r = .ok x)
    (ihL : ∀ {v qs}, s.eval σ = .ok v → P.eval σ = .ok qs →
      Sim ((s.lenU P).eval σ) (v.findLive qs >>= Close.arrLen)) :
    ∀ x, (((LStor.stale none s P' w).slotHasU P rest opq).eval σ) = .ok x →
      slotHas sh r = .ok x := by
  obtain ⟨-, x, v, qs, es', sh', -, -, hv, hq, hs, hv', hl, hSP⟩ :=
    stale_slot_setup hu hp hn hr ihL
  have hhu := find_slot_head hn
  have hhv := find_slot_head hv'
  rw [hl] at hhv
  have hrec : slotHas sh r = slotHas sh' r → ∀ x,
      (s.slotHasU P rest opq).eval σ = .ok x → slotHas sh r = .ok x := fun heq y hy => by
    rw [heq] at hopq ⊢
    exact ihS hv hv' hopq y hy
  rw [LStor.slotHasU]
  refine cmp_sound ((hP' qs).2 hq) hSP fun rel hrel => ?_
  cases rel with
  | eq =>
    simp only [PathRel.Holds] at hrel
    subst hrel
    obtain ⟨c, c', hc, hc', huc⟩ := find_save_append hs
    rw [hhu] at huc
    rw [hhv] at hc
    refine hrec ?_
    simp only [slotHas, huc, hc, Res.ok_bind, findLive_save_live hc']
    cases c.findLive r <;> rfl
  | above =>
    obtain ⟨f, t, rfl⟩ := hrel
    have hs2 : v.save ((ps ++ [.at es.length]) ++ (r ++ f :: t)) (.prim x) = .ok u := by
      rw [← List.append_assoc]; exact hs
    obtain ⟨c, c', hc, hc', huc⟩ := find_save_append hs2
    rw [hhu] at huc
    rw [hhv] at hc
    refine hrec ?_
    simp only [slotHas, huc, hc, Res.ok_bind]
    exact findLive_save_prefix_has hc'
  | below k =>
    intro y hy
    simp only [staleHas, LTerm.eval, reduceCtorEq] at hy
  | diverge =>
    refine hrec ?_
    rcases find_save_diverge_tail hs hrel with h | ⟨t, c, c', -, ht, hc, hc', huc⟩
    · simp only [slotHas]
      rw [← hhu, ← hhv, h]
    · rw [hhu] at huc
      rw [hhv] at hc
      simp only [slotHas, huc, hc, Res.ok_bind, findLive_save_diverge ht hc']

/-- **The slot a `push()` recycles, after a copy over the array**
(`storageFieldWriteCopySource`, then `selectOnSaveEmptyIndexStruct`): below
the old length, the old element there, deleted (`selectOnCopyIndexClear`);
at it, the old array's own (`selectOnCopyIndexKeep`); elsewhere, or where a
length does not return, the read itself. -/
theorem copy_slotU_sim {s src : LStor} {P' SQ P : LPath} {opq : LTerm}
    {rest : List SSeg} {u : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool} {R : RefTy}
    {r : List Seg}
    (hu : (LStor.copy s P' src SQ).eval σ = .ok u) (hP' : Sim (P'.elim.eval σ) (P'.eval σ))
    (hSQ : Sim (SQ.elim.eval σ) (SQ.eval σ))
    (hp : P.eval σ = .ok ps) (hn : u.findLive ps = .ok (.array es sh fx))
    (hr : segsEval σ rest = .ok r)
    (hopq : Sim (opq.eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue))
    (ihR : ∀ (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue))
    (ihM : ∀ (sh : KShape) (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test))
    (ihL : ∀ {v qs}, s.eval σ = .ok v → P.eval σ = .ok qs →
      Sim ((s.lenU P).eval σ) (v.findLive qs >>= Close.arrLen))
    (ihL' : ∀ {v qs}, src.eval σ = .ok v → SQ.elim.eval σ = .ok qs →
      Sim ((src.lenU SQ.elim).eval σ) (v.findLive qs >>= Close.arrLen))
    (ihS : ∀ {v : SVal} {es sh : List SVal} {fx : Bool}, s.eval σ = .ok v →
      v.findLive ps = .ok (.array es sh fx) →
      Sim (opq.eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue) →
      Sim ((s.slotU P rest opq).eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue)) :
    Sim (((LStor.copy s P' src SQ).slotU P rest opq).eval σ)
      ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue) := by
  rw [LStor.slotU]
  split
  · rename_i hc
    have hPe : P'.elim = P := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact hc.2
    obtain ⟨sv, sqs, n, v', ps', cur, hsv, hsq, hn', hv', hp', hcur, hu'⟩ := copy_eval_ok hu
    have hpp : ps' = ps := by
      have := (hP' ps').2 hp'
      rw [hPe, hp] at this
      cases this; rfl
    subst hpp
    rw [findLive_saveLive_same hu'] at hn
    have hsq' : SQ.elim.eval σ = .ok sqs := (hSQ sqs).2 hsq
    have hL := ihL hv' hp
    rw [hcur, Res.ok_bind] at hL
    have hL' := ihL' hsv hsq'
    rw [hn', Res.ok_bind] at hL'
    simp only [LTerm.eval, isT_eval]
    cases ha : (src.lenU SQ.elim).eval σ with
    | error e => simp only [Res.error_bind, pickBranch]; exact hopq
    | ok a =>
    cases hb : (s.lenU P).eval σ with
    | error e => simp only [Res.ok_bind, Res.error_bind, pickBranch]; exact hopq
    | ok b =>
    simp only [Res.ok_bind, pickBranch]
    have ha' := (hL' a).1 ha
    have hb' := (hL b).1 hb
    cases n with
    | array nel nsh nfx =>
      cases cur with
      | array oel osh ofx =>
        simp only [Close.arrLen, Except.ok.injEq] at ha' hb'
        subst ha' hb'
        simp only [Value.asInt, Res.ok_bind]
        by_cases hij : (nel.length : Int) = oel.length
        · rw [if_pos hij]
          have hlen : nel.length = oel.length := by exact_mod_cast hij
          obtain ⟨el', hov, -⟩ :=
            overlay_shadow_eq (osh := osh) (nsh := nsh) (ofx := ofx) (nfx := nfx) hlen
          rw [hov] at hn
          simp only [Except.ok.injEq, SVal.array.injEq] at hn
          obtain ⟨-, rfl, rfl⟩ := hn
          exact ihS hv' hcur hopq
        · rw [if_neg hij]
          simp only [evalBinop, applyBinOp, Value.asInt, checkArith, bind, Except.bind]
          by_cases hlt : (nel.length : Int) < oel.length
          · simp only [hlt, decide_true]
            have hlt' : nel.length < oel.length := by exact_mod_cast hlt
            obtain ⟨el', sh', hov, -⟩ :=
              overlay_shadow_lt (osh := osh) (nsh := nsh) (ofx := ofx) (nfx := nfx) hlt'
            rw [hov] at hn
            simp only [Except.ok.injEq, SVal.array.injEq] at hn
            obtain ⟨-, rfl, rfl⟩ := hn
            rw [pushSlot_ref_cons]
            have hE : (P.at (src.lenU SQ.elim)).eval σ = .ok (ps' ++ [.at nel.length]) := by
              simp only [LPath.eval, hp, ha, Res.ok_bind, Value.asInt]
            have he : v'.findLive (ps' ++ [.at nel.length]) = .ok (oel[nel.length]'hlt') := by
              rw [SVal.findLive_append, hcur, Res.ok_bind]
              simp only [SVal.findLive, Int.natCast_nonneg, Int.toNat_natCast, hlt', and_self,
                ↓reduceDIte, List.get_eq_getElem, SVal.findLive_nil]
            exact delSlot_sim hE he hr (fun Q _ hq => ihR Q hv' hq)
              (fun sh Q _ hq => ihM sh Q hv' hq)
          · simp only [hlt, decide_false]
            exact hopq
      | prim _ | struct _ | map _ _ => simp only [Close.arrLen, reduceCtorEq] at hb'
    | prim _ | struct _ | map _ _ => simp only [Close.arrLen, reduceCtorEq] at ha'
  · exact hopq

/-! #### Operations on an array through a dangling alias

A `push` through a stale alias (`LStor.stale (some op)`) is KeY's
`storagePushValueSave` at a slot: where the slot path is live it is the live
operation (`staleOp_live`), and the readers are `.arr`'s; where it is not, a
read at or below it halts on both sides, and one above or apart sees what a
write sees (`findLive_save_prefix`, `findLive_save_diverge`). -/

/-- An operation through a stale alias that returned: the node it found at
the slot path, the operation on it, and the write back. -/
theorem staleOp_eval_ok {op : AOp} {s : LStor} {P : LPath} {w : LTerm} {u : SVal}
    (hu : (LStor.stale (some op) s P w).eval σ = .ok u) :
    ∃ wv v ps c c', w.eval σ = .ok wv ∧ s.eval σ = .ok v ∧ P.eval σ = .ok ps ∧
      v.find ps = .ok c ∧ op.apply wv c = .ok c' ∧ v.save ps c' = .ok u := by
  obtain ⟨wv, hw, hu⟩ := Res.bind_eq_ok.1 hu
  obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
  obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
  obtain ⟨c, hc, hu⟩ := Res.bind_eq_ok.1 hu
  obtain ⟨c', hc', hu⟩ := Res.bind_eq_ok.1 hu
  exact ⟨wv, v, ps, c, c', hw, hv, hp, hc, hc', hu⟩

/-- Where its path is live, an operation through a stale alias is the live
one. -/
theorem staleOp_live {v u c c' c0 : SVal} {ps : List Seg}
    (hc : v.find ps = .ok c) (hs : v.save ps c' = .ok u) (h0 : v.findLive ps = .ok c0) :
    c0 = c ∧ v.saveLive ps c' = .ok u := by
  have h := SVal.find_of_findLive h0
  rw [hc] at h
  cases h
  exact ⟨rfl, by rw [saveLive_eq_save c' h0]; exact hs⟩

theorem kite_halt {k L t e : LTerm} (h : ∀ a, L.eval σ ≠ .ok a) :
    ∀ a, (LTerm.kite k L t e).eval σ ≠ .ok a := by
  intro a ha
  simp only [LTerm.eval] at ha
  obtain ⟨i, -, ha⟩ := Res.bind_eq_ok.1 ha
  obtain ⟨j, hj, -⟩ := Res.bind_eq_ok.1 ha
  obtain ⟨x, hx, -⟩ := Res.bind_eq_ok.1 hj
  exact h x hx

theorem binop_halt {op : BinOp} {p : PrimTy} {a b : LTerm} (h : ∀ x, a.eval σ ≠ .ok x) :
    ∀ x, (LTerm.binop op p a b).eval σ ≠ .ok x := by
  intro x hx
  obtain ⟨y, hy, -⟩ := Res.bind_eq_ok.1 hx
  exact h y hy

/-- **The length after an operation through a dangling alias**
(`selectOnSaveCons` on `size`): `.arr`'s where the path is live, the read
itself or nothing at or below it where it is not. -/
theorem staleOp_lenU_sim {op : AOp} {s : LStor} {P Q : LPath} {w : LTerm} {u : SVal}
    {qs : List Seg}
    (hu : (LStor.stale (some op) s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.lenU Q).eval σ) (v.findLive qs >>= Close.arrLen))
    (ihL : ∀ {v ps}, s.eval σ = .ok v → P.elim.eval σ = .ok ps →
      Sim ((s.lenU P.elim).eval σ) (v.findLive ps >>= Close.arrLen)) :
    Sim (((LStor.stale (some op) s P w).lenU Q).eval σ) (u.findLive qs >>= Close.arrLen) := by
  obtain ⟨wv, v, ps, c, c', -, hv, hp, hc, hap, hs⟩ := staleOp_eval_ok hu
  have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
  have hopq : Sim ((LTerm.len (.stale (some op) s P w) Q).eval σ)
      (u.findLive qs >>= Close.arrLen) :=
    Sim.of_eq (by simp only [LTerm.eval, hu, hq, Res.ok_bind])
  rw [LStor.lenU]
  refine cmp_sim hp' hq fun r hr => ?_
  cases h0 : v.findLive ps with
  | ok c0 =>
    obtain ⟨rfl, hu'⟩ := staleOp_live hc hs h0
    have hL := ihL hv hp'
    rw [h0, Res.ok_bind] at hL
    exact arrLength_sim h0 hap hu' hL (ihR hv hq) hopq (fun _ h => by cases h) r hr
  | error e =>
    have hun : u.findLive ps = .error e := by rw [findLive_save_live hs, h0]; rfl
    have hLn : ∀ a, (s.lenU P.elim).eval σ ≠ .ok a := fun a h => by
      have h' := ((ihL hv hp') a).1 h
      rw [h0] at h'
      cases h'
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      refine Sim.halt ?_ (by rw [hun]; intro a h; cases h)
      cases op <;> exact binop_halt hLn
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      simp only [arrLength]
      rw [findLive_save_above_eq (fun _ _ _ _ h => (save_cons_shape h).1) hs]
      exact ihR hv hq
    | diverge => simp only [arrLength]; rw [findLive_save_diverge hr hs]; exact ihR hv hq
    | below rest =>
      obtain ⟨f, t, rfl, hrest⟩ := hr
      rcases below_cases hrest with ⟨g, rest', rfl⟩ | ⟨k, rest', i, rfl, hk, rfl, hr'⟩
      · exact hopq
      · have hun' : ∀ a, (u.findLive (ps ++ .at i :: t) >>= Close.arrLen) ≠ .ok a := by
          rw [SVal.findLive_append, hun]; intro a h; cases h
        cases op with
        | push => exact Sim.halt (kite_halt hLn) hun'
        | pop _ => exact Sim.halt (kite_halt (binop_halt hLn)) hun'
        | slot E =>
          cases E with
          | ref _ => exact hopq
          | prim _ => exact Sim.halt (kite_halt hLn) hun'

/-- What a guard on an array operation reads of the length: its value. -/
theorem arrOk_lit {op : AOp} {L : LTerm} {x : Value} (h : (arrOk op L).eval σ = .ok x) :
    ∃ n, L.eval σ = .ok n ∧ (arrOk op (.lit n)).eval σ = .ok x := by
  cases hL : L.eval σ with
  | error e =>
    cases op <;> simp only [arrOk, LTerm.eval, hL, bind, Except.bind, evalBinop,
      reduceCtorEq] at h
  | ok n =>
    refine ⟨n, rfl, ?_⟩
    cases op <;> simpa only [arrOk, LTerm.eval, hL] using h

/-- The guard of an array operation on a node it returns on: the operation
applies. -/
theorem arrOk_apply {op : AOp} {wv : Value} {L : LTerm} {d : SVal} {x : Value}
    (h : (arrOk op L).eval σ = .ok x) (hL : ∀ n, L.eval σ = .ok n → Close.arrLen d = .ok n) :
    ∃ d', op.apply wv d = .ok d' ∧ x = .bool true := by
  obtain ⟨n, hn, h⟩ := arrOk_lit h
  have hs := ((arrOk_sim (op := op) (wv := wv) (L := .lit n) (x := .ok d)
    (Sim.of_eq (by rw [Res.ok_bind, hL n hn]; rfl))) x).1 h
  obtain ⟨d', hd', he⟩ := Res.bind_eq_ok.1 (by simpa only [Res.ok_bind] using hs)
  cases he
  exact ⟨d', hd', rfl⟩

/-- **The run guard of an operation through a dangling alias**: where the
live array has the operation (`arrOk` on its length), or the index is the
array's length and the first slot past the end has an array the operation
applies to (`slotLenU`), the write returns; elsewhere the write itself. -/
theorem staleOp_okE_sim {op : AOp} {s : LStor} {q : LPath} {w : LTerm}
    (hs : Sim (s.okE.eval σ) (s.eval σ >>= fun _ => .ok (.bool true)))
    (hW : Sim (w.elim.eval σ) (w.eval σ))
    (hP : Sim (q.elim.eval σ) (q.eval σ))
    (ihL : ∀ (A : LPath) {v qs}, s.eval σ = .ok v → A.eval σ = .ok qs →
      Sim ((s.lenU A).eval σ) (v.findLive qs >>= Close.arrLen))
    (ihS : ∀ (A : LPath) (rest : List SSeg) {v : SVal} {ps : List Seg} {es sh : List SVal}
      {fx : Bool} {r : List Seg}, s.eval σ = .ok v → A.eval σ = .ok ps →
      v.findLive ps = .ok (.array es sh fx) → segsEval σ rest = .ok r →
      ∀ x, (s.slotLenU A rest .err).eval σ = .ok x → slotLen sh r = .ok x) :
    Sim ((LStor.stale (some op) s q w).okE.eval σ)
      ((LStor.stale (some op) s q w).eval σ >>= fun _ => .ok (.bool true)) := by
  simp only [LStor.okE]
  split
  · rename_i hn
    have hG : ∀ {wv v qs}, w.eval σ = .ok wv → s.eval σ = .ok v → q.eval σ = .ok qs →
        Sim ((staleOk (arrOk op (s.lenU q.elim)) (match q.elim.splitLast with
          | some (A, k, rest) => some (k, s.lenU A, arrOk op (s.slotLenU A rest .err))
          | none => none) (.sok (.stale (some op) s q w))).eval σ)
          (staleSave (some op) wv v qs >>= fun _ => .ok (.bool true)) := by
      intro wv v qs hw hv hq
      have hqe : q.elim.eval σ = .ok qs := (hP qs).2 hq
      have hNL : ∀ t ∈ qs, t ≠ .field "length" := LPath.noLen_eval σ hn hq
      have hok : ∀ d d', v.find qs = .ok d → op.apply wv d = .ok d' →
          (staleSave (some op) wv v qs >>= fun _ => (.ok (Value.bool true) : Res Value)) =
            .ok (Value.bool true) := fun d d' hd hd' => by
        obtain ⟨u, hu⟩ := save_ok_of_find_ok (new := d') hNL hd
        simp only [staleSave, hd, hd', hu, Res.ok_bind]
      refine staleOk_sim (fun x hx => ?_) (fun k L S hslot x hx => ?_) ?_
      · have hx' := ((arrOk_sim (op := op) (wv := wv) (ihL q.elim hv hqe)) x).1 hx
        obtain ⟨d, hd, hx'⟩ := Res.bind_eq_ok.1 hx'
        obtain ⟨d', hd', hx'⟩ := Res.bind_eq_ok.1 hx'
        cases hx'
        exact hok d d' (SVal.find_of_findLive hd) hd'
      · split at hslot
        · rename_i A k' rest hsp
          simp only [Option.some.injEq, Prod.mk.injEq] at hslot
          obtain ⟨rfl, rfl, rfl⟩ := hslot
          obtain ⟨as, i, r, ha, hi, hr, rfl⟩ := LPath.splitLast_eval hsp hqe
          simp only [LTerm.eval, hi, Res.ok_bind] at hx
          obtain ⟨j, hj, hx1⟩ := Res.bind_eq_ok.1 hx
          obtain ⟨n, hnv, hj1⟩ := Res.bind_eq_ok.1 hj
          split at hx1
          · rename_i hij
            subst hij
            obtain ⟨c0, hc0, hl⟩ := Res.bind_eq_ok.1 (((ihL A hv ha) n).1 hnv)
            cases c0 with
            | array es sh fx =>
              simp only [Close.arrLen, Except.ok.injEq] at hl
              subst hl
              simp only [Value.asInt, Except.ok.injEq] at hj1
              subst hj1
              obtain ⟨m, hm, -⟩ := arrOk_lit hx1
              obtain ⟨c, hc, hx'⟩ := Res.bind_eq_ok.1 (ihS A rest hv ha hc0 hr m hm)
              obtain ⟨t, rfl⟩ := headR_ok hc
              obtain ⟨y, hy, hl⟩ := Res.bind_eq_ok.1 hx'
              obtain ⟨d', hd', rfl⟩ := arrOk_apply (wv := wv) (d := y) hx1 fun n' hn' => by
                rw [hm] at hn'; cases hn'; exact hl
              refine hok y d' ?_ hd'
              rw [find_past_end hc0 r]
              exact SVal.find_of_findLive hy
            | prim _ | struct _ | map _ _ => simp only [Close.arrLen, reduceCtorEq] at hl
          · simp only [reduceCtorEq] at hx1
        · cases hslot
      · simp only [LTerm.eval, LStor.eval, hw, hv, hq, Res.ok_bind]
        exact Sim.refl _
    intro a
    simp only [LTerm.eval, LStor.eval, Res.bind_eq_ok]
    constructor
    · rintro ⟨_, h₁, wv, h₂, _, ⟨qs, h₃, -⟩, h₄⟩
      obtain ⟨v, hv, -⟩ := Res.bind_eq_ok.1 ((hs _).1 h₁)
      have hw := (hW wv).1 h₂
      have hq := (hP qs).1 h₃
      obtain ⟨u, hu, he⟩ := Res.bind_eq_ok.1 (((hG hw hv hq) a).1 h₄)
      exact ⟨u, ⟨wv, hw, v, hv, qs, hq, hu⟩, he⟩
    · rintro ⟨u, ⟨wv, hw, v, hv, qs, hq, hu⟩, he⟩
      refine ⟨.bool true, (hs _).2 (by simp only [hv, Res.ok_bind]), wv,
        (hW wv).2 hw, .bool true, ⟨qs, (hP qs).2 hq, rfl⟩, ?_⟩
      exact ((hG hw hv hq) a).2 (by rw [hu]; exact he)
  · exact Sim.refl _

/-- No path parts ways with its own extension. -/
theorem not_diverge_append : ∀ (p x : List Seg), ¬ Close.Diverge p (p ++ x)
  | [], _ => Close.not_diverge_nil_left
  | a :: p, x => by
    simp only [List.cons_append, Close.diverge_cons, ne_eq, not_true_eq_false, false_or]
    exact not_diverge_append p x

/-- A write apart from the first slot past an array's end keeps that slot. -/
theorem slot_head_diverge {new v u : SVal} {qs ps : List Seg} {es sh es' sh' : List SVal}
    {fx fx' : Bool} (hs : v.save qs new = .ok u) (hn : u.findLive ps = .ok (.array es sh fx))
    (hv : v.findLive ps = .ok (.array es' sh' fx')) (hl : es'.length = es.length)
    (hd : Close.Diverge qs (ps ++ [.at es.length])) : headR sh = headR sh' := by
  rcases find_save_diverge_tail (p := ps ++ [.at es.length]) (r := []) hs
    (by rw [List.append_nil]; exact hd) with h | ⟨t, c, c', -, ht, -⟩
  · rw [← find_slot_head hn, h, ← hl, find_slot_head hv]
  · exact absurd ht Close.not_diverge_nil_right

/-- A `push` through a dangling alias leaves an array at `ps` only where
one was: as long, unless the push was at `ps` itself. -/
theorem stalePush_setup {wv : Value} {v u c c' : SVal} {qs ps : List Seg} {es sh : List SVal}
    {fx : Bool} (hc : v.find qs = .ok c) (hap : AOp.push.apply wv c = .ok c')
    (hs : v.save qs c' = .ok u) (hn : u.findLive ps = .ok (.array es sh fx)) :
    ∃ es' sh', v.findLive ps = .ok (.array es' sh' fx) ∧ (es'.length = es.length ∨ qs = ps) := by
  rcases segs_rel ps qs with rfl | ⟨f, r, rfl⟩ | ⟨f, r, rfl⟩ | hd
  · rw [findLive_save_live hs] at hn
    obtain ⟨d, hd, hn⟩ := Res.bind_eq_ok.1 hn
    cases hn
    obtain ⟨rfl, -⟩ := staleOp_live hc hs hd
    obtain ⟨es0, sh0, fx0, rfl, h'⟩ := AOp.apply_push_eq hap
    simp only [SVal.array.injEq] at h'
    obtain ⟨-, -, rfl⟩ := h'
    exact ⟨es0, sh0, hd, .inr rfl⟩
  · rw [SVal.findLive_append, findLive_save_live hs] at hn
    obtain ⟨d, hd, hn⟩ := Res.bind_eq_ok.1 hn
    obtain ⟨d0, hd0, hd⟩ := Res.bind_eq_ok.1 hd
    cases hd
    obtain ⟨hdc, -⟩ := staleOp_live hc hs hd0
    rw [hdc] at hd0
    refine ⟨es, sh, ?_, .inl rfl⟩
    rw [SVal.findLive_append, hd0, Res.ok_bind]
    exact apply_push_findLive_array hap hn
  · rw [findLive_save_prefix (f :: r) hs] at hn
    obtain ⟨c0, hc0, hs'⟩ := Res.bind_eq_ok.1 hn
    obtain ⟨hl, -, hfx⟩ := save_cons_shape hs'
    cases c0 with
    | array es' sh' fx' =>
      simp only [Close.arrLen, isFixV, Except.ok.injEq, PrimVal.int.injEq] at hl hfx
      subst hfx
      exact ⟨es', sh', hc0, .inl (by omega)⟩
    | prim _ | struct _ | map _ _ => simp only [Close.arrLen, reduceCtorEq] at hl
  · exact ⟨es, sh, by rw [← findLive_save_diverge (diverge_flip hd) hs, hn], .inl rfl⟩

/-- The array a stale `push` and a slot reader meet at, evaluated: the
slot path, the length, and the array before the push. -/
theorem stalePush_slot_setup {s : LStor} {P' P : LPath} {w : LTerm} {u : SVal} {ps : List Seg}
    {es sh : List SVal} {fx : Bool}
    (hu : (LStor.stale (some .push) s P' w).eval σ = .ok u) (hp : P.eval σ = .ok ps)
    (hn : u.findLive ps = .ok (.array es sh fx))
    (ihL : ∀ {v qs}, s.eval σ = .ok v → P.eval σ = .ok qs →
      Sim ((s.lenU P).eval σ) (v.findLive qs >>= Close.arrLen)) :
    ∃ wv v qs c c' es' sh', w.eval σ = .ok wv ∧ s.eval σ = .ok v ∧ P'.eval σ = .ok qs ∧
      v.find qs = .ok c ∧ AOp.push.apply wv c = .ok c' ∧ v.save qs c' = .ok u ∧
      v.findLive ps = .ok (.array es' sh' fx) ∧ (es'.length = es.length ∨ qs = ps) ∧
      (P.at (s.lenU P)).eval σ = .ok (ps ++ [.at es'.length]) := by
  obtain ⟨wv, v, qs, c, c', hw, hv, hq, hc, hap, hs⟩ := staleOp_eval_ok hu
  obtain ⟨es', sh', hv', hor⟩ := stalePush_setup hc hap hs hn
  have hL : (s.lenU P).eval σ = .ok (.int es'.length) :=
    ((ihL hv hp) (.int es'.length)).2 (by rw [hv', Res.ok_bind]; rfl)
  refine ⟨wv, v, qs, c, c', es', sh', hw, hv, hq, hc, hap, hs, hv', hor, ?_⟩
  simp only [LPath.eval, hp, hL, Res.ok_bind, Value.asInt]

/-- A `push` at the slot past the end: the slot was there, an array, and it
is the pushed one now. -/
theorem stalePush_at_slot {v u c c' : SVal} {ps : List Seg}
    {es sh es' sh' : List SVal} {fx : Bool}
    (hc : v.find (ps ++ [.at es'.length]) = .ok c) (hs : v.save (ps ++ [.at es'.length]) c' = .ok u)
    (hn : u.findLive ps = .ok (.array es sh fx)) (hv : v.findLive ps = .ok (.array es' sh' fx)) :
    ∃ t, sh' = c :: t ∧ sh = c' :: t ∧ es = es' := by
  cases sh' with
  | nil => rw [find_past_end_nil hv []] at hc; cases hc
  | cons c0 t =>
    have h0 := find_past_end hv []
    rw [hc, SVal.find_nil] at h0
    cases h0
    obtain ⟨c'', hc'', hu⟩ := findLive_save_past_end hv hs
    rw [SVal.save_nil] at hc''
    cases hc''
    rw [hn] at hu
    simp only [Except.ok.injEq, SVal.array.injEq] at hu
    obtain ⟨rfl, ⟨rfl, rfl⟩, -⟩ := hu
    exact ⟨t, rfl, rfl, rfl⟩

/-- **The slot a `push()` recycles, through a `push` through a dangling
alias** (`storagePushValueSave`'s `at(n)` and `size` writes, then
`storagePushLengthSaveReferenceElement` and `selectOnSaveCons`): at the old
length the pushed word, the old element elsewhere; the old slot where the
push is apart from it. -/
theorem stalePush_slotU_sim {s : LStor} {P' P : LPath} {w opq : LTerm}
    {rest : List SSeg} {u : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool} {R : RefTy}
    {r : List Seg}
    (hu : (LStor.stale (some .push) s P' w).eval σ = .ok u)
    (hP' : Sim (P'.elim.eval σ) (P'.eval σ)) (hW : Sim (w.elim.eval σ) (w.eval σ))
    (hp : P.eval σ = .ok ps) (hn : u.findLive ps = .ok (.array es sh fx))
    (hr : segsEval σ rest = .ok r)
    (hopq : Sim (opq.eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue))
    (ihSL : ∀ {v : SVal} {es sh : List SVal}, s.eval σ = .ok v →
      v.findLive ps = .ok (.array es sh fx) →
      ∀ x, (s.slotLenU P [] .err).eval σ = .ok x → slotLen sh [] = .ok x)
    (ihL : ∀ {v qs}, s.eval σ = .ok v → P.eval σ = .ok qs →
      Sim ((s.lenU P).eval σ) (v.findLive qs >>= Close.arrLen)) :
    Sim (((LStor.stale (some .push) s P' w).slotU P rest opq).eval σ)
      ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue) := by
  obtain ⟨wv, v, qs, c, c', es', sh', hw, hv, hq, hc, hap, hs, hv', hor, hSP⟩ :=
    stalePush_slot_setup hu hp hn ihL
  rw [LStor.slotU]
  refine cmp_sim ((hP' qs).2 hq) hSP fun rel hrel => ?_
  cases rel with
  | eq =>
    simp only [PathRel.Holds] at hrel
    subst hrel
    obtain ⟨t, rfl, rfl, rfl⟩ := stalePush_at_slot hc hs hn hv'
    obtain ⟨n, hcn, -, hnew, hold⟩ := apply_push_find hap
    refine orElse_sound_sim (fun x hx => ?_) hopq
    rw [pushSlot_ref_cons]
    cases rest with
    | nil => simp only [headKey, LTerm.eval, Res.error_bind, reduceCtorEq] at hx
    | cons a rest' =>
      cases a with
      | field _ => simp only [headKey, LTerm.eval, Res.error_bind, reduceCtorEq] at hx
      | key k =>
        obtain ⟨i, hk, r', hr', rfl⟩ : ∃ i, (k.eval σ >>= Value.asInt) = .ok i ∧
            ∃ r', segsEval σ rest' = .ok r' ∧ r = .at i :: r' := by
          simp only [segsEval] at hr
          obtain ⟨i, hi, hr⟩ := Res.bind_eq_ok.1 hr
          obtain ⟨r', hr', hr⟩ := Res.bind_eq_ok.1 hr
          cases hr
          exact ⟨i, hi, r', hr', rfl⟩
        simp only [headKey] at hx
        obtain ⟨m, hm⟩ : ∃ m, (s.slotLenU P [] .err).eval σ = .ok m := by
          cases h : (s.slotLenU P [] .err).eval σ with
          | ok m => exact ⟨m, rfl⟩
          | error e =>
            simp only [LTerm.eval, hk, h, Res.ok_bind, Res.error_bind, reduceCtorEq] at hx
        have hsl := ihSL hv hv' m hm
        simp only [slotLen, headR, Res.ok_bind, SVal.findLive_nil, hcn] at hsl
        cases hsl
        rw [kite_eval hk hm] at hx
        by_cases hij : i = n
        · rw [if_pos hij] at hx
          subst hij
          cases rest' with
          | nil =>
            cases hr'
            simp only [wordAtKey] at hx
            have hx' := (hW x).1 hx
            rw [hw] at hx'
            cases hx'
            rw [hnew, Res.ok_bind, Close.asValue_toSVal]
          | cons _ _ => simp only [wordAtKey, LTerm.eval, reduceCtorEq] at hx
        · rw [if_neg hij] at hx
          rw [← pushSlot_ref_cons R c' t]
          exact ((hopq x).1 hx)
  | diverge | above | below _ => exact hopq


theorem delSlotLen_sim {s : LStor} {v e : SVal} {E : LPath} {eps : List Seg}
    {rest : List SSeg} {r : List Seg}
    (hE : E.eval σ = .ok eps) (he : v.findLive eps = .ok e) (hr : segsEval σ rest = .ok r)
    (ihL : ∀ (Q : LPath) {qs}, Q.eval σ = .ok qs →
      Sim ((s.lenU Q).eval σ) (v.findLive qs >>= Close.arrLen))
    (ihM : ∀ (sh : KShape) (Q : LPath) {qs}, Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)) :
    Sim ((delLen (s.lenU (E.addSegs rest)) (lenEnd (s.lenU (E.addSegs rest))
      (s.mapU .fixed (E.addSegs rest))) E (fun sh q => s.mapU sh q)
      (if rest.isEmpty then .eq else .below rest)).eval σ)
      (e.defaultOf.findLive r >>= Close.arrLen) := by
  have hQ : (E.addSegs rest).eval σ = .ok (eps ++ r) := by
    rw [LPath.addSegs_eval, hE, Res.ok_bind, hr, Res.ok_bind]
  have hold := ihL _ hQ
  have hEnd := lenEnd_sim hold (ihM .fixed _ hQ)
  by_cases hemp : rest.isEmpty = true
  · have hr0 : r = [] := (segsEval_isEmpty hr).1 hemp
    subst hr0
    rw [if_pos hemp]
    simp only [delLen, SVal.findLive_nil, Res.ok_bind]
    rw [List.append_nil, he, Res.ok_bind] at hEnd
    exact hEnd
  · rw [if_neg hemp]
    simp only [delLen]
    have h := delBelow_sim (v := v) (G := Close.arrLen)
      (fun sh q qs hq' => ihM sh q hq') hold hEnd rest E eps r hE hr rfl
    rw [he, Res.ok_bind] at h
    exact h

/-- **The length of the slot a `pop` vacated** (`storagePopSave`'s `delAt`,
then `selectOnDelAtCons`, `delFieldIndexStruct`, `selectStDelNodeDefault`). -/
theorem pop_slotLenU_sound {keep : Bool} {s : LStor} {P' P : LPath} {w' opq : LTerm}
    {rest : List SSeg} {v : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool}
    {r : List Seg}
    (hu : (LStor.arr (.pop keep) s P' w').eval σ = .ok v) (hP' : Sim (P'.elim.eval σ) (P'.eval σ))
    (hp : P.eval σ = .ok ps) (hn : v.findLive ps = .ok (.array es sh fx))
    (hr : segsEval σ rest = .ok r)
    (hopq : ∀ x, opq.eval σ = .ok x → slotLen sh r = .ok x)
    (ihL : ∀ (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.lenU Q).eval σ) (v.findLive qs >>= Close.arrLen))
    (ihM : ∀ (sh : KShape) (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)) :
    ∀ x, (((LStor.arr (.pop keep) s P' w').slotLenU P rest opq).eval σ) = .ok x →
      slotLen sh r = .ok x := by
  rw [LStor.slotLenU]
  split
  · rename_i heq
    have hPe : P'.elim = P := by simpa only [beq_iff_eq] using heq
    obtain ⟨wv, v', ps', c0, c1, -, hv', hp', hc0, hap, hu'⟩ := arr_eval_ok hu
    have hpp : ps' = ps := by
      have := (hP' ps').2 hp'
      rw [hPe, hp] at this
      cases this; rfl
    subst hpp
    rw [findLive_saveLive_same hu'] at hn
    obtain ⟨es0, last, sh0, fx0, rfl, rfl⟩ := AOp.apply_pop_eq hap
    simp only [Except.ok.injEq, SVal.array.injEq] at hn
    obtain ⟨rfl, rfl, rfl⟩ := hn
    have hL := ihL P hv' hp
    rw [hc0, Res.ok_bind] at hL
    have hL' : (s.lenU P).eval σ = .ok (.int (es0 ++ [last]).length) := (hL _).2 rfl
    have hE : (P.at (lenPred (s.lenU P))).eval σ = .ok (ps' ++ [.at es0.length]) := by
      simp only [LPath.eval, hp, Res.ok_bind, lenPred_eval hL', Value.asInt]
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
          Int.natCast_add, Int.cast_ofNat_Int, Int.add_sub_cancel]
    have he : v'.findLive (ps' ++ [.at es0.length]) = .ok last := by
      rw [SVal.findLive_append, hc0, Res.ok_bind, findLive_last]
    intro x hx
    simp only [slotLen, headR, Res.ok_bind]
    cases keep
    · simp only [Bool.false_eq_true, if_false] at hx ⊢
      exact ((delSlotLen_sim hE he hr (fun Q _ hq => ihL Q hv' hq)
        (fun sh Q _ hq => ihM sh Q hv' hq)) x).1 hx
    · simp only [if_true] at hx ⊢
      have hQ : ((P.at (lenPred (s.lenU P))).addSegs rest).eval σ =
          .ok ((ps' ++ [.at es0.length]) ++ r) := by
        rw [LPath.addSegs_eval, hE, Res.ok_bind, hr, Res.ok_bind]
      have := ((ihL _ hv' hQ) x).1 hx
      rw [SVal.findLive_append, he, Res.ok_bind] at this
      exact this
  · exact hopq

/-- **The length of the slot past the end, through a stale write**: the old
one where the write is apart from the slot. -/
theorem stale_slotLenU_sound {s : LStor} {P' P : LPath} {w opq : LTerm}
    {rest : List SSeg} {u : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool} {r : List Seg}
    (hu : (LStor.stale none s P' w).eval σ = .ok u) (hP' : Sim (P'.elim.eval σ) (P'.eval σ))
    (hp : P.eval σ = .ok ps) (hn : u.findLive ps = .ok (.array es sh fx))
    (hr : segsEval σ rest = .ok r)
    (hopq : ∀ x, opq.eval σ = .ok x → slotLen sh r = .ok x)
    (ihS : ∀ {v : SVal} {es sh : List SVal}, s.eval σ = .ok v →
      v.findLive ps = .ok (.array es sh fx) →
      (∀ x, opq.eval σ = .ok x → slotLen sh r = .ok x) →
      ∀ x, (s.slotLenU P rest opq).eval σ = .ok x → slotLen sh r = .ok x)
    (ihL : ∀ {v qs}, s.eval σ = .ok v → P.eval σ = .ok qs →
      Sim ((s.lenU P).eval σ) (v.findLive qs >>= Close.arrLen)) :
    ∀ x, (((LStor.stale none s P' w).slotLenU P rest opq).eval σ) = .ok x →
      slotLen sh r = .ok x := by
  obtain ⟨-, x, v, qs, es', sh', -, -, hv, hq, hs, hv', hl, -⟩ :=
    stale_slot_setup hu hp hn hr ihL
  have hL : (s.lenU P).eval σ = .ok (.int es'.length) :=
    ((ihL hv hp) (.int es'.length)).2 (by rw [hv', Res.ok_bind]; rfl)
  have hSP : (P.at (s.lenU P)).eval σ = .ok (ps ++ [.at es'.length]) := by
    simp only [LPath.eval, hp, hL, Res.ok_bind, Value.asInt]
  rw [LStor.slotLenU]
  refine cmp_sound ((hP' qs).2 hq) hSP fun rel hrel => ?_
  cases rel with
  | diverge =>
    have hh := slot_head_diverge hs hn hv' hl (by rw [← hl]; exact hrel)
    have heq : slotLen sh r = slotLen sh' r := by simp only [slotLen, hh]
    simp only [slotLeaf]
    rw [heq] at hopq ⊢
    exact ihS hv hv' hopq
  | eq | above | below _ => exact hopq

/-- **The length of the slot past the end, through a `push` through a
dangling alias** (`storagePushValueSave`'s `size` write, `selectOnSaveCons`):
one more where the push is at the slot, the old one apart from it. -/
theorem stalePush_slotLenU_sound {s : LStor} {P' P : LPath} {w opq : LTerm}
    {rest : List SSeg} {u : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool} {r : List Seg}
    (hu : (LStor.stale (some .push) s P' w).eval σ = .ok u)
    (hP' : Sim (P'.elim.eval σ) (P'.eval σ))
    (hp : P.eval σ = .ok ps) (hn : u.findLive ps = .ok (.array es sh fx))
    (hr : segsEval σ rest = .ok r)
    (hopq : ∀ x, opq.eval σ = .ok x → slotLen sh r = .ok x)
    (ihS : ∀ {v : SVal} {es sh : List SVal}, s.eval σ = .ok v →
      v.findLive ps = .ok (.array es sh fx) →
      ∀ x, (s.slotLenU P rest .err).eval σ = .ok x → slotLen sh r = .ok x)
    (ihL : ∀ {v qs}, s.eval σ = .ok v → P.eval σ = .ok qs →
      Sim ((s.lenU P).eval σ) (v.findLive qs >>= Close.arrLen)) :
    ∀ x, (((LStor.stale (some .push) s P' w).slotLenU P rest opq).eval σ) = .ok x →
      slotLen sh r = .ok x := by
  obtain ⟨wv, v, qs, c, c', es', sh', -, hv, hq, hc, hap, hs, hv', hor, hSP⟩ :=
    stalePush_slot_setup hu hp hn ihL
  rw [LStor.slotLenU]
  refine cmp_sound ((hP' qs).2 hq) hSP fun rel hrel => ?_
  cases rel with
  | eq =>
    simp only [PathRel.Holds] at hrel
    subst hrel
    obtain ⟨t, rfl, rfl, rfl⟩ := stalePush_at_slot hc hs hn hv'
    simp only [slotLeaf]
    split
    · rename_i hemp
      have hr0 : r = [] := (segsEval_isEmpty hr).1 hemp
      subst hr0
      intro x hx
      obtain ⟨n, hcn, hc'n, -, -⟩ := apply_push_find hap
      cases hS : (s.slotLenU P rest .err).eval σ with
      | error e => simp only [lenSucc, LTerm.eval, hS, Res.error_bind, reduceCtorEq] at hx
      | ok m =>
        have hsl := ihS hv hv' m hS
        simp only [slotLen, headR, Res.ok_bind, SVal.findLive_nil, hcn] at hsl
        cases hsl
        rw [lenSucc_eval hS] at hx
        cases hx
        simp only [slotLen, headR, Res.ok_bind, SVal.findLive_nil, hc'n]
    · exact hopq
  | diverge | above | below _ => exact hopq

end Stale

/-- A read below a copy from storage, its storage reads eliminated. -/
theorem copySelU_sim {σ : State} {s : LStor} {q q' : LPath} (p : List Seg) (a : LSel) {u : LTerm}
    (hs : Sim (s.okE.eval σ) (s.eval σ >>= fun _ => .ok (.bool true)))
    (hrd : ∀ (Q : LPath) {v : SVal} {qs : List Seg}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue))
    (hln : ∀ (Q : LPath) {v : SVal} {qs : List Seg}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.lenU Q).eval σ) (v.findLive qs >>= Close.arrLen))
    (hq : Sim (q'.eval σ) (q.eval σ))
    (h : copySelG (fun Q => .seq s.okE (.seq (.pok Q) (s.readU Q)))
      (fun Q => .seq s.okE (.seq (.pok Q) (s.lenU Q))) q' p a = some u) :
    ∃ t, copySel s q p a = some t ∧ Sim (u.eval σ) (t.eval σ) := by
  have he := LPath.ext_congr σ hq p
  cases a with
  | fld f =>
    simp only [copySelG] at h
    split at h
    · rename_i hl
      cases h
      exact ⟨LTerm.find s ((q.ext p).field f), by simp only [copySel, copySelG, hl, if_true],
        guard_sim hs (Sim.bind he fun _ => Sim.refl _) fun _ _ hv hq => hrd _ hv hq⟩
    · cases h
  | idx t =>
    simp only [copySelG] at h
    split at h
    · rename_i hl
      cases h
      exact ⟨LTerm.find s ((q.ext p).at t), by simp only [copySel, copySelG, hl, if_true],
        guard_sim hs (Sim.bind he fun _ => Sim.refl _) fun _ _ hv hq => hrd _ hv hq⟩
    · cases h
  | size =>
    simp only [copySelG] at h
    split at h
    · rename_i hl
      cases h
      exact ⟨LTerm.len s (q.ext p), by simp only [copySel, copySelG, hl, if_true],
        guard_sim hs he fun _ _ hv hq => hln _ hv hq⟩
    · cases h

/-- A test below a copy from storage, its guard hoisted: the storage and the
path are tested once, before the tests below them. -/
theorem copyObj_hoist {σ : State} {K P F H L : LTerm} {str : Bool} :
    Rets ((LTerm.seq K (.seq P (if str then .ite (isT L) .err (.ite (isT F) .err H)
        else .ite (isT F) .err H))).eval σ) ↔
      Rets ((if str then LTerm.ite (isT (.seq K (.seq P L))) .err
          (.ite (isT (.seq K (.seq P F))) .err (.seq K (.seq P H)))
        else .ite (isT (.seq K (.seq P F))) .err (.seq K (.seq P H))).eval σ) := by
  cases str <;> simp only [Bool.false_eq_true, ↓reduceIte, seq_rets, ite_isT_rets] <;> grind

/-- A test below a copy from storage, its storage reads eliminated. -/
theorem copyObjU_rets {σ : State} {s : LStor} {Q : LPath} {F H L : LTerm}
    (hF : Sim (F.eval σ) ((LTerm.find s Q).eval σ)) (hH : Sim (H.eval σ) ((LTerm.has s Q).eval σ))
    (hL : Sim (L.eval σ) ((LTerm.len s Q).eval σ)) (str : Bool) :
    Rets ((if str then LTerm.ite (isT L) .err (.ite (isT F) .err H) else .ite (isT F) .err H).eval σ)
      ↔ Rets ((if str then structT s Q else refT s Q).eval σ) := by
  have href : Rets ((LTerm.ite (isT F) .err H).eval σ) ↔ Rets ((refT s Q).eval σ) := by
    rw [refT, ite_isT_rets, ite_isT_rets, rets_of_sim hF, rets_of_sim hH]
  cases str with
  | false => exact href
  | true =>
    show Rets ((LTerm.ite (isT L) .err (.ite (isT F) .err H)).eval σ) ↔
      Rets ((LTerm.ite (isT (.len s Q)) .err (refT s Q)).eval σ)
    rw [ite_isT_rets σ L, ite_isT_rets σ (.len s Q), rets_of_sim hL, href]

/-- A read after a write to memory, the reader of what is below given. -/
theorem readU_write_sim {σ : State} {m : LMem} {j : LId} {b : LSel} {v : LMV} {i : LId} {a : LSel}
    {u : LTerm}
    (ih : ∀ (i : LId) (a : LSel) {u : LTerm}, m.readU i a = some u →
      ∃ t, m.readT i a = some t ∧ Sim (u.eval σ) (t.eval σ))
    (hv : Sim (v.wordU.eval σ) (v.wordT.eval σ))
    (hb : ∀ w, b = .idx w → Sim (b.idxU.eval σ) (w.eval σ))
    (h : (LMem.write m j b v).readU i a = some u) :
    ∃ t, (LMem.write m j b v).readT i a = some t ∧ Sim (u.eval σ) (t.eval σ) := by
  by_cases hij : i = j
  · simp only [LMem.readU, LMem.readT, hij, if_true] at h ⊢
    cases hs : selRel b a with
    | same =>
      simp only [hs, Option.some.injEq] at h ⊢
      subst h
      exact ⟨_, rfl, hv⟩
    | apart =>
      simp only [hs] at h ⊢
      exact ih j a h
    | key r w =>
      obtain ⟨hbw, rfl⟩ := selRel_key hs
      subst hbw
      simp only [hs, Option.map_eq_some_iff] at h ⊢
      obtain ⟨u', hu', rfl⟩ := h
      obtain ⟨t', ht', hs'⟩ := ih j (.idx r) hu'
      exact ⟨_, ⟨t', ht', rfl⟩, kite_congr σ (Sim.refl _) (hb w rfl) hv hs'⟩
  · simp only [LMem.readU, LMem.readT, hij, if_false] at h ⊢
    exact ih i a h

/-- **A word read below a view** (`findOnCopy`, `selectOnCopyMemPrim`/`Ref`,
`readRCons`), the reader given. -/
theorem view_readU_sim {σ : State} {m : LMem} {i : LId} {Q : LPath} {v : SVal} {qs : List Seg}
    (hv : (LStor.view m i).eval σ = .ok v) (hq : Q.eval σ = .ok qs)
    (hrd : ∀ (j : LId) (a : LSel) {u : LTerm}, m.readU j a = some u →
      ∃ t, m.readT j a = some t ∧ Sim (u.eval σ) (t.eval σ)) :
    Sim (((LStor.view m i).readU Q).eval σ) (v.findLive qs >>= SVal.asValue) := by
  have hkeep : Sim ((LTerm.find (.view m i) Q).eval σ) (v.findLive qs >>= SVal.asValue) := by
    simp only [LTerm.eval, hv, hq, Res.ok_bind]
    exact Sim.refl _
  obtain ⟨μ, B, cv, hva, rfl⟩ := LStor.eval_view hv
  simp only [LStor.readU]
  split
  · rename_i p a hQ
    split
    · rename_i j hw
      cases hu : m.readU j a with
      | none => exact hkeep
      | some u =>
        obtain ⟨t, ht, hut⟩ := hrd j a hu
        exact Sim.trans hut (Sim.trans (LMem.readT_sim σ m j a hva.run ht)
          (view_read_sim hva hQ hq hw))
    · exact hkeep
  · exact hkeep

/-- **The length of an array below a view**, the reader given. -/
theorem view_lenU_sim {σ : State} {m : LMem} {i : LId} {Q : LPath} {v : SVal} {qs : List Seg}
    (hv : (LStor.view m i).eval σ = .ok v) (hq : Q.eval σ = .ok qs)
    (hrd : ∀ (j : LId) (a : LSel) {u : LTerm}, m.readU j a = some u →
      ∃ t, m.readT j a = some t ∧ Sim (u.eval σ) (t.eval σ)) :
    Sim (((LStor.view m i).lenU Q).eval σ) (v.findLive qs >>= Close.arrLen) := by
  have hkeep : Sim ((LTerm.len (.view m i) Q).eval σ) (v.findLive qs >>= Close.arrLen) := by
    simp only [LTerm.eval, hv, hq, Res.ok_bind]
    exact Sim.refl _
  obtain ⟨μ, B, cv, hva, rfl⟩ := LStor.eval_view hv
  simp only [LStor.lenU]
  split
  · rename_i p hQ
    split
    · rename_i j hw
      cases hu : m.readU j .size with
      | none => exact hkeep
      | some u =>
        obtain ⟨t, ht, hut⟩ := hrd j .size hu
        exact Sim.trans hut (Sim.trans (LMem.readT_sim σ m j .size hva.run ht)
          (view_len_sim hva hQ hq hw))
    · exact hkeep
  · exact hkeep

/-- **Whether a location is there below a view**, the readers given. -/
theorem view_hasU_sim {σ : State} {m : LMem} {i : LId} {Q : LPath} {v : SVal} {qs : List Seg}
    (hv : (LStor.view m i).eval σ = .ok v) (hq : Q.eval σ = .ok qs)
    (hrd : ∀ (j : LId) (a : LSel) {u : LTerm}, m.readU j a = some u →
      ∃ t, m.readT j a = some t ∧ Sim (u.eval σ) (t.eval σ))
    (hob : ∀ (j : LId) {g : LTerm}, m.objU false j = some g →
      ∃ g', m.nameG j = some g' ∧ (Rets (g.eval σ) ↔ Rets (g'.eval σ))) :
    Sim (((LStor.view m i).hasU Q).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true)) := by
  have hkeep : Sim ((LTerm.has (.view m i) Q).eval σ)
      (v.findLive qs >>= fun _ => .ok (.bool true)) := by
    simp only [LTerm.eval, hv, hq, Res.ok_bind]
    exact Sim.refl _
  obtain ⟨μ, B, cv, hva, rfl⟩ := LStor.eval_view hv
  simp only [LStor.hasU]
  split
  · rename_i p a hQ
    split
    · rename_i j hw
      split
      · rename_i W N hW hN
        obtain ⟨j', hj', hN⟩ := Option.bind_eq_some_iff.1 hN
        obtain ⟨t, ht, hWt⟩ := hrd j a hW
        obtain ⟨g', hg', hNg⟩ := hob j' hN
        exact view_has_sim hva hQ hq hw (Sim.trans hWt (LMem.readT_sim σ m j a hva.run ht))
          (LMem.readI_sim σ m j a hva.run hj').2
          (hNg.trans (LMem.nameG_sim σ m j' hva.run hg'))
      · exact hkeep
    · exact hkeep
  · split
    · rename_i hR
      match Q, hR, hq with
      | .root r, hR, hq =>
        simp only [isViewRoot, beq_iff_eq] at hR
        subst hR
        simp only [LPath.eval, Except.ok.injEq] at hq
        subst hq
        rw [view_findLive, SVal.findLive_nil]
        exact Sim.refl _
      | .field .., hR, _ | .at .., hR, _ => simp only [isViewRoot, Bool.false_eq_true] at hR
    · exact hkeep

/-- No mapping is below a view (Lean only). -/
theorem view_mapU_sim {σ : State} {m : LMem} {i : LId} (sh : KShape) {Q : LPath} {v : SVal}
    {qs : List Seg} (hv : (LStor.view m i).eval σ = .ok v) (hq : Q.eval σ = .ok qs) :
    Sim (((LStor.view m i).mapU sh Q).eval σ) (v.findLive qs >>= sh.test) := by
  cases sh with
  | fixed =>
    simp only [LStor.mapU, LTerm.eval, hv, hq, Res.ok_bind]
    exact Sim.refl _
  | map =>
    obtain ⟨μ, B, cv, hva, rfl⟩ := LStor.eval_view hv
    obtain ⟨n, -, hcv⟩ := hva.obj
    simp only [LStor.mapU]
    refine Sim.halt (fun _ h => by cases h) fun u h => ?_
    cases qs with
    | nil => simp only [SVal.findLive_nil, Res.ok_bind', KShape.test, kmapF, isMapV,
        Bool.false_eq_true, if_false, reduceCtorEq] at h
    | cons s rest =>
      cases s with
      | field f =>
        by_cases hf : f = viewRoot
        · subst hf
          rw [view_findLive] at h
          exact view_noMap hcv rest u h
        · simp only [SVal.findLive, lookupBy, hf, if_false, bind, Except.bind,
            reduceCtorEq] at h
      | «at» k => simp only [SVal.findLive, bind, Except.bind, reduceCtorEq] at h

/-! ### The run guard of a memory: soundness -/

section RunGuard
open MemNames


theorem init_okU_rets {σ : State} {g : LTerm} (h : LMem.init.okU = some g) :
    Rets (g.eval σ) ↔ ∃ r, LMem.init.run σ = .ok r := by
  simp only [LMem.okU, Option.some.injEq] at h
  subst h
  exact iff_of_true (lit_rets σ _) ⟨_, rfl⟩

theorem addM_okU_rets {σ : State} {m : LMem} {k : Nat} {R : RefTy} {g : LTerm}
    (ih : ∀ {G : LTerm}, m.okU = some G → (Rets (G.eval σ) ↔ ∃ r, m.run σ = .ok r))
    (h : (LMem.addM m k R).okU = some g) :
    Rets (g.eval σ) ↔ ∃ r, (LMem.addM m k R).run σ = .ok r := by
  simp only [LMem.okU] at h
  split at h
  · rename_i hc
    obtain ⟨hk, hR⟩ := hc
    rw [ih h]
    constructor
    · rintro ⟨⟨μ', B'⟩, hr⟩
      have hl := LMem.run_nAlloc σ m hr
      obtain ⟨⟨τ, mv⟩, hcp⟩ := (allocOk_cps hR).at μ'
      obtain ⟨id, rfl⟩ := copy_ref hcp (defaultForTy_ref_ne R)
      have hkl : k = B'.length := by omega
      exact ⟨_, by simp only [LMem.run, hr, Res.ok_bind, hkl, if_true, allocDefault,
        defaultForRef, hcp] <;> rfl⟩
    · rintro ⟨r, hr⟩
      obtain ⟨x, hx, -⟩ := Res.bind_eq_ok.1 hr
      exact ⟨x, hx⟩
  · cases h

theorem newArr_okU_rets {σ : State} {m : LMem} {k : Nat} {R : RefTy} {n : LTerm} {g : LTerm}
    (ih : ∀ {G : LTerm}, m.okU = some G → (Rets (G.eval σ) ↔ ∃ r, m.run σ = .ok r))
    (hn : Sim (n.elim.eval σ) (n.eval σ))
    (h : (LMem.newArr m k R n).okU = some g) :
    Rets (g.eval σ) ↔ ∃ r, (LMem.newArr m k R n).run σ = .ok r := by
  simp only [LMem.okU] at h
  split at h
  · rename_i hc
    obtain ⟨hk, hR⟩ := hc
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
    have hi : Rets ((isIntL n.elim).eval σ) ↔ ∃ i, n.eval σ = .ok (.int i) :=
      (isIntL_ret σ _).trans ⟨fun ⟨i, h⟩ => ⟨i, (hn _).1 h⟩, fun ⟨i, h⟩ => ⟨i, (hn _).2 h⟩⟩
    rw [seq_rets, ih hG, hi]
    constructor
    · rintro ⟨⟨⟨μ', B'⟩, hr⟩, c, hc⟩
      have hl := LMem.run_nAlloc σ m hr
      obtain ⟨hcp, hnp⟩ := allocOk_newArr hR c
      obtain ⟨⟨τ, mv⟩, hcopy⟩ := hcp.at μ'
      obtain ⟨id, rfl⟩ := copy_ref hcopy hnp
      have hkl : k = B'.length := by omega
      exact ⟨_, by simp only [LMem.run, hc, hr, Res.ok_bind, Value.asInt, hkl, if_true, hcopy,
        MVal.asRef] <;> rfl⟩
    · rintro ⟨r, hr⟩
      obtain ⟨μ', B', id, c, hr', -, hn', -, -⟩ := LMem.run_newArr (μ := r.1) (B := r.2) hr
      exact ⟨⟨_, hr'⟩, c, hn'⟩
  · cases h

/-- The guard of a copy's run guard, hoisted: the storage and the path are
tested once, before the copy test and the word test. -/
theorem copyOk_hoist {σ : State} {G K P C F T : LTerm} :
    Rets ((LTerm.seq G (.seq K (.seq P (.seq C (.ite (isT F) .err T))))).eval σ) ↔
      Rets ((LTerm.seq G (.seq (.seq K (.seq P C))
        (.ite (isT (.seq K (.seq P F))) .err T))).eval σ) := by
  simp only [seq_rets, ite_isT_rets]
  grind

theorem copySt_okU_rets {σ : State} {m : LMem} {k : Nat} {s : LStor} {q : LPath} {g : LTerm}
    (ih : ∀ {G : LTerm}, m.okU = some G → (Rets (G.eval σ) ↔ ∃ r, m.run σ = .ok r))
    (hC : Sim ((LTerm.seq s.okE (.seq (.pok q.elim) (s.cpokU q.elim))).eval σ)
      ((LTerm.cpok s q).eval σ))
    (hF : Sim ((LTerm.seq s.okE (.seq (.pok q.elim) (s.readU q.elim))).eval σ)
      ((LTerm.find s q).eval σ))
    (h : (LMem.copySt m k s q).okU = some g) :
    Rets (g.eval σ) ↔ ∃ r, (LMem.copySt m k s q).run σ = .ok r := by
  simp only [LMem.okU] at h
  split at h
  · rename_i hk
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [copyOk_hoist, seq_rets, seq_rets, ih hG, rets_of_sim hC, ite_isT_rets, rets_of_sim hF]
    simp only [lit_rets, and_true]
    constructor
    · rintro ⟨⟨⟨μ', B'⟩, hr⟩, ⟨a, hc⟩, hf⟩
      rw [cpok_eval] at hc
      obtain ⟨v, hv, hc⟩ := Res.bind_eq_ok.1 hc
      obtain ⟨qs, hq, hc⟩ := Res.bind_eq_ok.1 hc
      obtain ⟨-, sv, hsv, hcps⟩ := cpR_ok.1 hc
      have hnp : ∀ p, sv ≠ .prim p := by
        rintro p rfl
        obtain ⟨a, ha⟩ : ∃ a, (SVal.prim p).asValue = .ok a := by cases p <;> exact ⟨_, rfl⟩
        exact hf ⟨a, by simp only [LTerm.eval, hv, hq, hsv, Res.ok_bind, ha]⟩
      obtain ⟨⟨τ, mv⟩, hcopy⟩ := hcps.at μ'
      obtain ⟨id, rfl⟩ := copy_ref hcopy hnp
      have hkl : k = B'.length := by have := LMem.run_nAlloc σ m hr; omega
      exact ⟨_, by simp only [LMem.run, hv, hq, hsv, hr, Res.ok_bind, hkl, if_true, hcopy,
        MVal.asRef] <;> rfl⟩
    · rintro ⟨r, hrun⟩
      obtain ⟨μ', B', id, hr', -, ⟨c, rfl⟩, -⟩ := LMem.run_copySt (μ := r.1) (B := r.2) hrun
      obtain ⟨v, qs, w, μ', hv, hq, hw, hc⟩ := c
      refine ⟨⟨_, hr'⟩, ⟨.bool true, ?_⟩, ?_⟩
      · rw [cpok_eval, hv, Res.ok_bind, hq, Res.ok_bind]
        exact cpR_ok.2 ⟨rfl, w, hw, μ', _, hc⟩
      · rintro ⟨a, ha⟩
        simp only [LTerm.eval, hv, hq, hw, Res.ok_bind] at ha
        cases w with
        | prim p => cases p <;> simp only [copyStToM, Except.ok.injEq, Prod.mk.injEq,
            reduceCtorEq, and_false] at hc
        | struct _ | array _ _ _ | map _ _ => simp only [SVal.asValue, reduceCtorEq] at ha
  · cases h

theorem wrGuard_sim {σ : State} {m : LMem} {j : LId} {b : LSel} {W : LTerm}
    (ihO : ∀ (str : Bool) (i : LId) {g : LTerm}, m.objU str i = some g →
      ∃ g', (if str then m.structG i else m.nameG i) = some g' ∧
        (Rets (g.eval σ) ↔ Rets (g'.eval σ)))
    (ihR : ∀ (i : LId) (a : LSel) {u : LTerm}, m.readU i a = some u →
      ∃ t, m.readT i a = some t ∧ Sim (u.eval σ) (t.eval σ))
    (hb : ∀ w, b = .idx w → Sim (b.idxU.eval σ) (w.eval σ))
    (h : wrGuard (fun _ => m.objU true j) (fun _ => m.readU j .size) b.idxU b = some W) :
    ∃ g', m.writeG j b = some g' ∧ (Rets (W.eval σ) ↔ Rets (g'.eval σ)) := by
  cases b with
  | fld f =>
    obtain ⟨g', hg', hr⟩ := ihO true j h
    exact ⟨g', by simpa only [LMem.writeG, ↓reduceIte] using hg', hr⟩
  | idx t =>
    simp only [wrGuard, Option.map_eq_some_iff] at h
    obtain ⟨u, hu, rfl⟩ := h
    obtain ⟨t', ht', hs⟩ := ihR j .size hu
    have hk := hb t rfl
    refine ⟨ltR t t', by simp only [LMem.writeG, LMem.lenT, ht', Option.map_some], ?_⟩
    rw [ltR_rets, ltR_rets]
    constructor
    · rintro ⟨c, d, hc, hd, h0, h1⟩; exact ⟨c, d, (hk _).1 hc, (hs _).1 hd, h0, h1⟩
    · rintro ⟨c, d, hc, hd, h0, h1⟩; exact ⟨c, d, (hk _).2 hc, (hs _).2 hd, h0, h1⟩
  | size => simp only [wrGuard, reduceCtorEq] at h

theorem valGuard_sim {σ : State} {m : LMem} {μ : State} {B : Births} {v : LMV} {V : LTerm}
    (hr : m.run σ = .ok (μ, B))
    (ihO : ∀ (str : Bool) (i : LId) {g : LTerm}, m.objU str i = some g →
      ∃ g', (if str then m.structG i else m.nameG i) = some g' ∧
        (Rets (g.eval σ) ↔ Rets (g'.eval σ)))
    (hv : Sim (v.wordU.eval σ) (v.wordT.eval σ))
    (h : valGuard (.seq v.wordU (.lit (.bool true)))
      (fun _ => v.refId?.bind fun j' => m.objU false j') v = some V) :
    Rets (V.eval σ) ↔ ∃ mv, v.eval σ B = .ok mv := by
  cases v with
  | word t =>
    simp only [valGuard, Option.some.injEq] at h
    subst h
    rw [seq_rets, rets_of_sim hv]
    simp only [lit_rets, and_true, LMV.wordT, LMV.eval]
    constructor
    · rintro ⟨x, hx⟩; exact ⟨_, by rw [hx]; rfl⟩
    · rintro ⟨mv, h⟩
      obtain ⟨x, hx, -⟩ := Res.bind_eq_ok.1 h
      exact ⟨x, hx⟩
  | ref j' =>
    simp only [valGuard, LMV.refId?, Option.bind_some] at h
    obtain ⟨g', hg', hrg⟩ := ihO false j' h
    simp only [Bool.false_eq_true, ↓reduceIte] at hg'
    rw [hrg, LMem.nameG_sim σ m j' hr hg']
    simp only [LMV.eval]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨_, by rw [hn]; rfl⟩
    · rintro ⟨mv, h⟩
      obtain ⟨n, hn, -⟩ := Res.bind_eq_ok.1 h
      exact ⟨n, hn⟩

theorem write_okU_rets {σ : State} {m : LMem} {j : LId} {b : LSel} {v : LMV} {g : LTerm}
    (ih : ∀ {G : LTerm}, m.okU = some G → (Rets (G.eval σ) ↔ ∃ r, m.run σ = .ok r))
    (ihO : ∀ (str : Bool) (i : LId) {g : LTerm}, m.objU str i = some g →
      ∃ g', (if str then m.structG i else m.nameG i) = some g' ∧
        (Rets (g.eval σ) ↔ Rets (g'.eval σ)))
    (ihR : ∀ (i : LId) (a : LSel) {u : LTerm}, m.readU i a = some u →
      ∃ t, m.readT i a = some t ∧ Sim (u.eval σ) (t.eval σ))
    (hv : Sim (v.wordU.eval σ) (v.wordT.eval σ))
    (hb : ∀ w, b = .idx w → Sim (b.idxU.eval σ) (w.eval σ))
    (h : (LMem.write m j b v).okU = some g) :
    Rets (g.eval σ) ↔ ∃ r, (LMem.write m j b v).run σ = .ok r := by
  simp only [LMem.okU, okWrite, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨G, hG, W, hW, V, hV, rfl⟩ := h
  rw [seq_rets, seq_rets, seq_rets, ih hG]
  simp only [lit_rets, and_true]
  obtain ⟨g', hg', hWg⟩ := wrGuard_sim ihO ihR hb hW
  rw [hWg]
  constructor
  · rintro ⟨⟨⟨μ, B⟩, hr⟩, hw, hvr⟩
    obtain ⟨mv, hmv⟩ := (valGuard_sim hr ihO hv hV).1 hvr
    obtain ⟨n, ad, μ₁, hn, had, hwr⟩ := (LMem.writeG_sim σ hr j b hg' mv).1 hw
    exact ⟨_, by simp only [LMem.run, hr, Res.ok_bind, hn, had, hmv, hwr] <;> rfl⟩
  · rintro ⟨r, hrun⟩
    obtain ⟨μ', n', ad, mv, hr, hn, had, hmv, hwr⟩ := LMem.run_write (μ := r.1) (B := r.2) hrun
    exact ⟨⟨_, hr⟩, (LMem.writeG_sim σ hr j b hg' mv).2 ⟨n', ad, _, hn, had, hwr⟩,
      (valGuard_sim hr ihO hv hV).2 ⟨mv, hmv⟩⟩

/-- **The guard of a view returns exactly where the view does** (Lean only):
the memory runs, the name denotes, and a memory whose references all name
older roots holds no cycle, so the copy back returns. -/
theorem view_okE_sim {σ : State} {m : LMem} {i : LId}
    (ih : ∀ {G : LTerm}, m.okU = some G → (Rets (G.eval σ) ↔ ∃ r, m.run σ = .ok r))
    (ihN : ∀ {g : LTerm}, m.objU false i = some g →
      ∃ g', (if false then m.structG i else m.nameG i) = some g' ∧
        (Rets (g.eval σ) ↔ Rets (g'.eval σ))) :
    Sim ((LStor.view m i).okE.eval σ) ((LStor.view m i).eval σ >>= fun _ => .ok (.bool true)) := by
  have hkeep : Sim ((LTerm.sok (.view m i)).eval σ)
      ((LStor.view m i).eval σ >>= fun _ => .ok (.bool true)) := Sim.refl _
  rw [LStor.okE]
  split
  · rename_i hd
    unfold okView
    cases hG : m.okU with
    | none => exact hkeep
    | some G =>
      cases hN : m.objU false i with
      | none => exact hkeep
      | some N =>
        obtain ⟨g', hg', hNg⟩ := ihN hN
        simp only [Bool.false_eq_true, ↓reduceIte] at hg'
        intro a
        constructor
        · intro he
          have hr : Rets ((LTerm.seq G (.seq N (.lit (.bool true)))).eval σ) := ⟨a, he⟩
          have ha : a = .bool true := by
            simp only [LTerm.eval, Res.bind_eq_ok, Except.ok.injEq] at he
            obtain ⟨_, _, _, _, rfl⟩ := he
            rfl
          subst ha
          rw [seq_rets, seq_rets, ih hG, hNg] at hr
          obtain ⟨⟨⟨μ, B⟩, hrun⟩, hn, -⟩ := hr
          obtain ⟨x, hx⟩ := (LMem.nameG_sim σ m i hrun hg').1 hn
          have hdesc := LMem.refDesc_desc σ m hrun hd
          obtain ⟨_, -, -, -, hlo, hhi⟩ :=
            Births.eval_interval (LMem.run_births σ m hrun) (LId.evalR_ok.1 hx)
          obtain ⟨cv, hcv⟩ := copyMem_ok_desc hdesc hlo hhi
          simp only [LStor.eval, hrun, Res.ok_bind, hx, hcv]
        · intro he
          obtain ⟨_, hv, ha⟩ := Res.bind_eq_ok.1 he
          cases ha
          obtain ⟨μ, B, cv, hva, -⟩ := LStor.eval_view hv
          obtain ⟨x, hx, -⟩ := hva.obj
          obtain ⟨_, h1⟩ := (ih hG).2 ⟨_, hva.run⟩
          obtain ⟨_, h2⟩ := hNg.2 ((LMem.nameG_sim σ m i hva.run hg').2 ⟨x, hx⟩)
          simp only [LTerm.eval, h1, h2, Res.ok_bind]
  · exact hkeep

end RunGuard

mutual

/-- **Eliminating the reads of writes keeps what a term returns.**

Example: after `balances[k] = 5; balances[j] = 6;`, the read of
`balances[k]` becomes `j == k ? 6 : (k == k ? 5 : balances[k])`, guarded by
the two writes succeeding; in every state it returns what the read does. -/
theorem LTerm.elim_sim (σ : State) : (t : LTerm) → Sim (t.elim.eval σ) (t.eval σ)
  | .lit _ => Sim.refl _
  | .var _ => Sim.refl _
  | .err => Sim.refl _
  | .env _ => Sim.refl _
  | .findP _ q => Sim.bind (Sim.refl _) fun _ => Sim.bind (LPath.elim_sim σ q) fun _ => Sim.refl _
  | .binop _ _ a b =>
    Sim.bind (LTerm.elim_sim σ a) fun _ => evalBinop_sim (LTerm.elim_sim σ b)
  | .unop _ _ a => Sim.bind (LTerm.elim_sim σ a) fun _ => Sim.refl _
  | .ite c a b =>
    Sim.bind (LTerm.elim_sim σ c) fun _ => pickBranch_sim (LTerm.elim_sim σ a) (LTerm.elim_sim σ b)
  | .find s q => guard_sim (LStor.okE_sim σ s) (LPath.elim_sim σ q)
      fun _ _ hv hq => LStor.readU_sim σ s q.elim hv hq
  | .has s q => guard_sim (LStor.okE_sim σ s) (LPath.elim_sim σ q)
      fun _ _ hv hq => LStor.hasU_sim σ s q.elim hv hq
  | .kmap sh s q => guard_sim (LStor.okE_sim σ s) (LPath.elim_sim σ q)
      fun _ _ hv hq => LStor.mapU_sim σ s sh q.elim hv hq
  | .len s q => guard_sim (LStor.okE_sim σ s) (LPath.elim_sim σ q)
      fun _ _ hv hq => LStor.lenU_sim σ s q.elim hv hq
  | .sok s => LStor.okE_sim σ s
  | .pok q => Sim.bind (LPath.elim_sim σ q) fun _ => Sim.refl _
  | .seq d a => Sim.bind (LTerm.elim_sim σ d) fun _ => LTerm.elim_sim σ a
  | .orElse a b => Sim.orElse (LTerm.elim_sim σ a) (LTerm.elim_sim σ b)
  | .kite a b t e =>
    Sim.bind (Sim.bind (LTerm.elim_sim σ a) fun _ => Sim.refl _) fun i =>
      Sim.bind (Sim.bind (LTerm.elim_sim σ b) fun _ => Sim.refl _) fun j => by
        by_cases h : i = j
        · simp only [h, if_true]; exact LTerm.elim_sim σ t
        · simp only [h, if_false]; exact LTerm.elim_sim σ e
  | .zero a => Sim.bind (LTerm.elim_sim σ a) fun _ => Sim.refl _
  | .cpok s q => guard_sim (LStor.okE_sim σ s) (LPath.elim_sim σ q)
      fun _ _ hv hq => LStor.cpokU_sim σ s q.elim hv hq
termination_by structural x => x

/-- Eliminating keeps the path a path term names: `people[balances[a]]` after
`balances[a] = 5;` names `people[5]`. -/
theorem LPath.elim_sim (σ : State) : (q : LPath) → Sim (q.elim.eval σ) (q.eval σ)
  | .root _ => Sim.refl _
  | .field q _ => Sim.bind (LPath.elim_sim σ q) fun _ => Sim.refl _
  | .at q k => Sim.bind (LPath.elim_sim σ q) fun _ =>
      Sim.bind (Sim.bind (LTerm.elim_sim σ k) fun _ => Sim.refl _) fun _ => Sim.refl _
termination_by structural x => x

/-- The guard of a storage returns exactly when its writes do. -/
theorem LStor.okE_sim (σ : State) :
    (s : LStor) → Sim (s.okE.eval σ) (s.eval σ >>= fun _ => .ok (.bool true))
  | .init => Sim.refl _
  | .save s q w =>
    save_okE_sim (LStor.okE_sim σ s) (LTerm.elim_sim σ w) (LPath.elim_sim σ q) (fun hv hp => LStor.hasU_sim σ s q.elim hv hp)
  | .delAt s q =>
    del_okE_sim (LStor.okE_sim σ s) (LPath.elim_sim σ q) (fun hv hp => LStor.hasU_sim σ s q.elim hv hp)

  | .arr _ s P w => arr_okE_sim (LStor.okE_sim σ s) (LTerm.elim_sim σ w) (LPath.elim_sim σ P)
      fun hv hp => LStor.lenU_sim σ s P.elim hv hp
  | .stale none s q w => stale_okE_sim (LStor.okE_sim σ s) (LTerm.elim_sim σ w)
      (LPath.elim_sim σ q) (fun hv hp => LStor.hasU_sim σ s q.elim hv hp)
      (fun A _ _ hv hp => LStor.lenU_sim σ s A hv hp)
      (fun A rest _ _ _ _ _ _ hv hp hn hr => LStor.slotHasU_sound σ s A rest .err hv hp hn hr
        fun _ h => by simp only [LTerm.eval, reduceCtorEq] at h)
  | .stale (some _) s q w => staleOp_okE_sim (LStor.okE_sim σ s) (LTerm.elim_sim σ w)
      (LPath.elim_sim σ q) (fun A _ _ hv hp => LStor.lenU_sim σ s A hv hp)
      (fun A rest _ _ _ _ _ _ hv hp hn hr => LStor.slotLenU_sound σ s A rest .err hv hp hn hr
        fun _ h => by simp only [LTerm.eval, reduceCtorEq] at h)
  | .copy s P src SQ => copy_okE_sim (LStor.okE_sim σ s) (LStor.okE_sim σ src) (LPath.elim_sim σ P)
      (LPath.elim_sim σ SQ) (fun hv hp => LStor.hasU_sim σ s P.elim hv hp)
      (fun hv hp => LStor.hasU_sim σ src SQ.elim hv hp)
  | .view m _ => view_okE_sim (fun hG => LMem.okU_sim σ m hG)
      fun hN => LMem.objU_sim σ m false _ hN
termination_by structural x => x

/-- **What a read after writes returns**, peeled one write at a time. -/
theorem LStor.readU_sim (σ : State) : (s : LStor) → ∀ (Q : LPath) {v : SVal} {qs : List Seg},
    s.eval σ = .ok v → Q.eval σ = .ok qs → Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue)
  | .init, Q, v, qs, hv, hq => by
    cases hv
    simp only [LStor.readU, LTerm.eval, LStor.eval, hq, Res.ok_bind]
    exact Sim.refl _
  | .save s P w, Q, u, qs, hu, hq =>
    save_readU_sim hu hq (LPath.elim_sim σ P) (LTerm.elim_sim σ w) (fun hv hq => LStor.readU_sim σ s Q hv hq)
  | .delAt s P, Q, u, qs, hu, hq =>
    del_readU_sim hu hq (LPath.elim_sim σ P) (fun hv hq => LStor.readU_sim σ s Q hv hq) (fun sh Q _ _ hv hq => LStor.mapU_sim σ s sh Q hv hq)

  | .arr _ s P w, Q, _, _, hu, hq => arr_readU_sim hu hq (LPath.elim_sim σ P) (LTerm.elim_sim σ w)
      (fun hv hq => LStor.readU_sim σ s Q hv hq) (fun hv hp => LStor.lenU_sim σ s P.elim hv hp)
      (fun rest opq _ _ _ _ _ _ _ hv hp hn hr hopq =>
        LStor.slotU_sim σ s P.elim rest opq hv hp hn hr hopq)
  | .stale none s P w, Q, _, _, hu, hq => stale_readU_sim hu hq (LPath.elim_sim σ P)
      (LTerm.elim_sim σ w) (fun hv hq => LStor.readU_sim σ s Q hv hq)
      (fun hv hq => LStor.hasU_sim σ s Q hv hq)
  | .stale (some _) .., Q, v, qs, hv, hq => by
    simp only [LStor.readU, LTerm.eval, hv, hq, Res.ok_bind]
    exact Sim.refl _
  | .copy s P src SQ, Q, _, _, hu, hq => copy_readU_sim hu hq (LPath.elim_sim σ P)
      (LPath.elim_sim σ SQ) (fun hv hq => LStor.readU_sim σ s Q hv hq)
      (fun Q' _ _ hv hq => LStor.readU_sim σ src Q' hv hq)
      (fun Q' _ _ hv hq => LStor.mapU_sim σ src .map Q' hv hq)
  | .view m _, Q, v, qs, hv, hq =>
    view_readU_sim hv hq fun j a _ h => LMem.readU_sim σ m j a h
termination_by structural x => x

/-- **What the slot a `push()` recycles holds.** -/
theorem LStor.slotU_sim (σ : State) : (s : LStor) → ∀ (P : LPath) (rest : List SSeg) (opq : LTerm)
    {v : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool} {R : RefTy} {r : List Seg},
    s.eval σ = .ok v → P.eval σ = .ok ps → v.findLive ps = .ok (.array es sh fx) →
    segsEval σ rest = .ok r →
    Sim (opq.eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue) →
    Sim ((s.slotU P rest opq).eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue)
  | .arr (.pop _) s P' _ => fun P _ _ _ _ _ _ _ _ _ hv hp hn hr hopq =>
    pop_slotU_sim hv (LPath.elim_sim σ P') hp hn hr hopq
      (fun Q _ _ hv hq => LStor.readU_sim σ s Q hv hq)
      (fun sh Q _ _ hv hq => LStor.mapU_sim σ s sh Q hv hq)
      (fun hv hq => LStor.lenU_sim σ s P hv hq)
  | .delAt s P' => fun P rest opq _ _ _ _ _ _ _ hv hp hn hr hopq =>
    del_slotU_sim hv (LPath.elim_sim σ P') hp hn hr hopq
      (fun Q _ _ hv hq => LStor.readU_sim σ s Q hv hq)
      (fun sh Q _ _ hv hq => LStor.mapU_sim σ s sh Q hv hq)
      (fun hv hq => LStor.lenU_sim σ s P hv hq)
      (fun hv' hn' hopq' => LStor.slotU_sim σ s P rest opq hv' hp hn' hr hopq')
  | .init => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotU]; exact hopq
  | .save .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotU]; exact hopq
  | .arr .push .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotU]; exact hopq
  | .arr (.slot _) .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotU]; exact hopq
  | .stale none s P' w => fun P rest opq _ _ _ _ _ _ _ hv hp hn hr hopq =>
    stale_slotU_sim hv (LPath.elim_sim σ P') (LTerm.elim_sim σ w) hp hn hr hopq
      (fun hv' hn' hopq' => LStor.slotU_sim σ s P rest opq hv' hp hn' hr hopq')
      (fun hv hq => LStor.lenU_sim σ s P hv hq)
  | .stale (some .push) s P' w => fun P rest opq _ _ _ _ _ _ _ hv hp hn hr hopq =>
    stalePush_slotU_sim hv (LPath.elim_sim σ P') (LTerm.elim_sim σ w) hp hn hr hopq
      (fun hv' hn' => LStor.slotLenU_sound σ s P [] .err hv' hp hn' rfl
        fun _ h => by simp only [LTerm.eval, reduceCtorEq] at h)
      (fun hv hq => LStor.lenU_sim σ s P hv hq)
  | .stale (some (.pop _)) .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by
    rw [LStor.slotU]; exact hopq
  | .stale (some (.slot _)) .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by
    rw [LStor.slotU]; exact hopq
  | .copy s P' src SQ => fun P rest opq _ _ _ _ _ _ _ hv hp hn hr hopq =>
    copy_slotU_sim hv (LPath.elim_sim σ P') (LPath.elim_sim σ SQ) hp hn hr hopq
      (fun Q _ _ hv hq => LStor.readU_sim σ s Q hv hq)
      (fun sh Q _ _ hv hq => LStor.mapU_sim σ s sh Q hv hq)
      (fun hv hq => LStor.lenU_sim σ s P hv hq)
      (fun hv hq => LStor.lenU_sim σ src SQ.elim hv hq)
      (fun hv' hn' hopq' => LStor.slotU_sim σ s P rest opq hv' hp hn' hr hopq')
  | .view .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotU]; exact hopq
termination_by structural x => x

/-- **Whether the slot a `push()` recycles has a location**, one direction:
where `slotHasU` returns, the slot has it (`staleOk`'s guard). -/
theorem LStor.slotHasU_sound (σ : State) : (s : LStor) → ∀ (P : LPath) (rest : List SSeg)
    (opq : LTerm) {v : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool} {r : List Seg},
    s.eval σ = .ok v → P.eval σ = .ok ps → v.findLive ps = .ok (.array es sh fx) →
    segsEval σ rest = .ok r → (∀ x, opq.eval σ = .ok x → slotHas sh r = .ok x) →
    ∀ x, (s.slotHasU P rest opq).eval σ = .ok x → slotHas sh r = .ok x
  | .arr (.pop _) s P' _ => fun P _ _ _ _ _ _ _ _ hv hp hn hr hopq =>
    pop_slotHasU_sound hv (LPath.elim_sim σ P') hp hn hr hopq
      (fun Q _ _ hv hq => LStor.hasU_sim σ s Q hv hq)
      (fun sh Q _ _ hv hq => LStor.mapU_sim σ s sh Q hv hq)
      (fun hv hq => LStor.lenU_sim σ s P hv hq)
  | .stale none s P' _ => fun P rest opq _ _ _ _ _ _ hv hp hn hr hopq =>
    stale_slotHasU_sound hv (LPath.elim_sim σ P') hp hn hr hopq
      (fun hv' hn' hopq' => LStor.slotHasU_sound σ s P rest opq hv' hp hn' hr hopq')
      (fun hv hq => LStor.lenU_sim σ s P hv hq)
  | .init => fun _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotHasU]; exact hopq
  | .save .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotHasU]; exact hopq
  | .delAt .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotHasU]; exact hopq
  | .arr .push .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotHasU]; exact hopq
  | .arr (.slot _) .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotHasU]; exact hopq
  | .stale (some _) .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotHasU]; exact hopq
  | .copy .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotHasU]; exact hopq
  | .view .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotHasU]; exact hopq
termination_by structural x => x

/-- **The length the slot a `push()` recycles has**, one direction: where
`slotLenU` returns, the slot has an array that long (`arrLength`'s slot,
the guard of a `push` through a dangling alias). -/
theorem LStor.slotLenU_sound (σ : State) : (s : LStor) → ∀ (P : LPath) (rest : List SSeg)
    (opq : LTerm) {v : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool} {r : List Seg},
    s.eval σ = .ok v → P.eval σ = .ok ps → v.findLive ps = .ok (.array es sh fx) →
    segsEval σ rest = .ok r → (∀ x, opq.eval σ = .ok x → slotLen sh r = .ok x) →
    ∀ x, (s.slotLenU P rest opq).eval σ = .ok x → slotLen sh r = .ok x
  | .arr (.pop _) s P' _ => fun P _ _ _ _ _ _ _ _ hv hp hn hr hopq =>
    pop_slotLenU_sound hv (LPath.elim_sim σ P') hp hn hr hopq
      (fun Q _ _ hv hq => LStor.lenU_sim σ s Q hv hq)
      (fun sh Q _ _ hv hq => LStor.mapU_sim σ s sh Q hv hq)
  | .stale none s P' _ => fun P rest opq _ _ _ _ _ _ hv hp hn hr hopq =>
    stale_slotLenU_sound hv (LPath.elim_sim σ P') hp hn hr hopq
      (fun hv' hn' hopq' => LStor.slotLenU_sound σ s P rest opq hv' hp hn' hr hopq')
      (fun hv hq => LStor.lenU_sim σ s P hv hq)
  | .stale (some .push) s P' _ => fun P rest _ _ _ _ _ _ _ hv hp hn hr hopq =>
    stalePush_slotLenU_sound hv (LPath.elim_sim σ P') hp hn hr hopq
      (fun hv' hn' => LStor.slotLenU_sound σ s P rest .err hv' hp hn' hr
        fun _ h => by simp only [LTerm.eval, reduceCtorEq] at h)
      (fun hv hq => LStor.lenU_sim σ s P hv hq)
  | .init => fun _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotLenU]; exact hopq
  | .save .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotLenU]; exact hopq
  | .delAt .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotLenU]; exact hopq
  | .arr .push .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotLenU]; exact hopq
  | .arr (.slot _) .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotLenU]; exact hopq
  | .stale (some (.pop _)) .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by
    rw [LStor.slotLenU]; exact hopq
  | .stale (some (.slot _)) .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by
    rw [LStor.slotLenU]; exact hopq
  | .copy .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotLenU]; exact hopq
  | .view .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotLenU]; exact hopq
termination_by structural x => x

/-- **Whether a location is there after writes**, peeled one write at a time. -/
theorem LStor.hasU_sim (σ : State) : (s : LStor) → ∀ (Q : LPath) {v : SVal} {qs : List Seg},
    s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.hasU Q).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true))
  | .init, Q, v, qs, hv, hq => by
    cases hv
    simp only [LStor.hasU, LTerm.eval, LStor.eval, hq, Res.ok_bind]
    exact Sim.refl _
  | .save s P w, Q, u, qs, hu, hq =>
    save_hasU_sim hu hq (LPath.elim_sim σ P) (fun hv hq => LStor.hasU_sim σ s Q hv hq)
  | .delAt s P, Q, u, qs, hu, hq =>
    del_hasU_sim hu hq (LPath.elim_sim σ P) (fun hv hq => LStor.hasU_sim σ s Q hv hq) (fun sh Q _ _ hv hq => LStor.mapU_sim σ s sh Q hv hq)

  | .arr _ s P _, Q, _, _, hu, hq => arr_hasU_sim hu hq (LPath.elim_sim σ P)
      (fun hv hq => LStor.hasU_sim σ s Q hv hq) (fun hv hp => LStor.lenU_sim σ s P.elim hv hp)
  | .stale none s P _, Q, _, _, hu, hq => stale_hasU_sim hu hq (LPath.elim_sim σ P)
      (fun hv hq => LStor.hasU_sim σ s Q hv hq)
  | .stale (some _) .., Q, v, qs, hv, hq => by
    simp only [LStor.hasU, LTerm.eval, hv, hq, Res.ok_bind]
    exact Sim.refl _
  | .copy s P src SQ, Q, _, _, hu, hq => copy_hasU_sim hu hq (LPath.elim_sim σ P)
      (LPath.elim_sim σ SQ) (fun hv hq => LStor.hasU_sim σ s Q hv hq)
      (fun Q' _ _ hv hq => LStor.hasU_sim σ src Q' hv hq)
      (fun Q' _ _ hv hq => LStor.mapU_sim σ src .map Q' hv hq)
  | .view m _, Q, v, qs, hv, hq =>
    view_hasU_sim hv hq (fun j a _ h => LMem.readU_sim σ m j a h)
      fun j _ h => LMem.objU_sim σ m false j h
termination_by structural x => x

/-- **Whether a mapping is there after writes**, peeled one write at a time. -/
theorem LStor.mapU_sim (σ : State) : (s : LStor) → ∀ (sh : KShape) (Q : LPath) {v : SVal}
    {qs : List Seg}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)
  | .init, sh, Q, v, qs, hv, hq => by
    cases hv
    simp only [LStor.mapU, LTerm.eval, LStor.eval, hq, Res.ok_bind]
    exact Sim.refl _
  | .save s P w, sh, Q, u, qs, hu, hq =>
    save_mapU_sim hu hq (LPath.elim_sim σ P) (fun sh Q _ _ hv hq => LStor.mapU_sim σ s sh Q hv hq)
  | .delAt s P, sh, Q, u, qs, hu, hq =>
    del_mapU_sim hu hq (LPath.elim_sim σ P) (fun sh Q _ _ hv hq => LStor.mapU_sim σ s sh Q hv hq)

  | .arr _ s P _, sh, Q, _, _, hu, hq => arr_mapU_sim hu hq (LPath.elim_sim σ P)
      (fun hv hq => LStor.mapU_sim σ s sh Q hv hq) (fun hv hp => LStor.lenU_sim σ s P.elim hv hp)
  | .stale none s P _, sh, Q, _, _, hu, hq => stale_mapU_sim hu hq (LPath.elim_sim σ P)
      (fun hv hq => LStor.mapU_sim σ s sh Q hv hq)
  | .stale (some _) .., sh, Q, v, qs, hv, hq => by
    simp only [LStor.mapU, LTerm.eval, hv, hq, Res.ok_bind]
    exact Sim.refl _
  | .copy s P src SQ, sh, Q, _, _, hu, hq => copy_mapU_sim hu hq (LPath.elim_sim σ P)
      (LPath.elim_sim σ SQ) (fun hv hq => LStor.mapU_sim σ s sh Q hv hq)
      (fun Q' _ _ hv hq => LStor.mapU_sim σ src sh Q' hv hq)
      (fun Q' _ _ hv hq => LStor.mapU_sim σ src .map Q' hv hq)
  | .view _ _, sh, Q, v, qs, hv, hq => view_mapU_sim sh hv hq
termination_by structural x => x

/-- **The length of an array after writes**, peeled one write at a time. -/
theorem LStor.lenU_sim (σ : State) : (s : LStor) → ∀ (Q : LPath) {v : SVal} {qs : List Seg},
    s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.lenU Q).eval σ) (v.findLive qs >>= Close.arrLen)
  | .init, Q, v, qs, hv, hq => by
    cases hv
    simp only [LStor.lenU, LTerm.eval, LStor.eval, hq, Res.ok_bind]
    exact Sim.refl _
  | .save s P w, Q, u, qs, hu, hq =>
    save_lenU_sim hu hq (LPath.elim_sim σ P) (fun hv hq => LStor.lenU_sim σ s Q hv hq)
  | .delAt s P, Q, u, qs, hu, hq =>
    del_lenU_sim hu hq (LPath.elim_sim σ P) (fun hv hq => LStor.lenU_sim σ s Q hv hq) (fun sh Q _ _ hv hq => LStor.mapU_sim σ s sh Q hv hq)
  | .arr _ s P _, Q, _, _, hu, hq => arr_lenU_sim hu hq (LPath.elim_sim σ P)
      (fun hv hq => LStor.lenU_sim σ s Q hv hq) (fun hv hp => LStor.lenU_sim σ s P.elim hv hp)
      (fun rest _ _ _ _ _ _ hv hp hn hr => LStor.slotLenU_sound σ s P.elim rest .err hv hp hn hr
        fun _ h => by simp only [LTerm.eval, reduceCtorEq] at h)
  | .stale none s P _, Q, _, _, hu, hq => stale_lenU_sim hu hq (LPath.elim_sim σ P)
      (fun hv hq => LStor.lenU_sim σ s Q hv hq)
  | .stale (some _) s P _, Q, _, _, hu, hq => staleOp_lenU_sim hu hq (LPath.elim_sim σ P)
      (fun hv hq => LStor.lenU_sim σ s Q hv hq) (fun hv hp => LStor.lenU_sim σ s P.elim hv hp)
  | .copy s P src SQ, Q, _, _, hu, hq => copy_lenU_sim hu hq (LPath.elim_sim σ P)
      (LPath.elim_sim σ SQ) (fun hv hq => LStor.lenU_sim σ s Q hv hq)
      (fun Q' _ _ hv hq => LStor.lenU_sim σ src Q' hv hq)
      (fun Q' _ _ hv hq => LStor.mapU_sim σ src .map Q' hv hq)
  | .view m _, Q, v, qs, hv, hq =>
    view_lenU_sim hv hq fun j a _ h => LMem.readU_sim σ m j a h
termination_by structural x => x

/-- **Whether a copy into memory succeeds, after writes**, peeled one word
write at a time. -/
theorem LStor.cpokU_sim (σ : State) : (s : LStor) → ∀ (Q : LPath) {v : SVal} {qs : List Seg},
    s.eval σ = .ok v → Q.eval σ = .ok qs → Sim ((s.cpokU Q).eval σ) (cpR σ v qs)
  | .init, _, _, _, hv, hq => by rw [LStor.cpokU]; exact cpok_keep_sim hv hq
  | .save s P _, Q, _, _, hu, hq => by
    rw [LStor.cpokU]
    exact save_cpok_sim hu hq (LPath.elim_sim σ P) (fun hv hp => LStor.readU_sim σ s P.elim hv hp)
      fun hv => LStor.cpokU_sim σ s Q hv hq
  | .delAt .., _, _, _, hv, hq | .arr .., _, _, _, hv, hq | .stale .., _, _, _, hv, hq
  | .copy .., _, _, _, hv, hq | .view .., _, _, _, hv, hq => by
    rw [LStor.cpokU]; exact cpok_keep_sim hv hq
termination_by structural x => x

/-- An index written to memory, eliminated, returns what it did. -/
theorem LSel.idxU_sim (σ : State) : (b : LSel) → ∀ w, b = .idx w → Sim (b.idxU.eval σ) (w.eval σ)
  | .idx w', w, hb => by
    simp only [LSel.idx.injEq] at hb
    subst hb
    exact LTerm.elim_sim σ w'
  | .fld _, _, hb => nomatch hb
  | .size, _, hb => nomatch hb
termination_by structural x => x

/-- A word written to memory, eliminated, returns what it did. -/
theorem LMV.wordU_sim (σ : State) : (v : LMV) → Sim (v.wordU.eval σ) (v.wordT.eval σ)
  | .word t => LTerm.elim_sim σ t
  | .ref _ => Sim.refl _
termination_by structural x => x

/-- **The memory reader of the elimination gives what `LMem.readT` gives.** -/
theorem LMem.readU_sim (σ : State) : (m : LMem) → ∀ (i : LId) (a : LSel) {u : LTerm},
    m.readU i a = some u → ∃ t, m.readT i a = some t ∧ Sim (u.eval σ) (t.eval σ)
  | .init, _, _, _, h => by simp only [LMem.readU, reduceCtorEq] at h
  | .addM m k R, i, a, u, h => by
    by_cases hk : i.root = k
    · simp only [LMem.readU, LMem.readT, hk, if_true, Option.some.injEq] at h ⊢
      subst h
      exact ⟨_, rfl, Sim.refl _⟩
    · simp only [LMem.readU, LMem.readT, hk, if_false] at h ⊢
      exact LMem.readU_sim σ m i a h
  | .newArr m k R n, i, a, u, h => by
    by_cases hk : i.root = k
    · simp only [LMem.readU, LMem.readT, hk, if_true, Option.some.injEq] at h ⊢
      subst h
      exact ⟨_, rfl, newSel_congr σ R (LTerm.elim_sim σ n) i.path a⟩
    · simp only [LMem.readU, LMem.readT, hk, if_false] at h ⊢
      exact LMem.readU_sim σ m i a h
  | .copySt m k s q, i, a, u, h => by
    by_cases hk : i.root = k
    · simp only [LMem.readU, LMem.readT, hk, if_true] at h ⊢
      exact copySelU_sim i.path a (LStor.okE_sim σ s) (fun Q _ _ hv hq => LStor.readU_sim σ s Q hv hq)
        (fun Q _ _ hv hq => LStor.lenU_sim σ s Q hv hq) (LPath.elim_sim σ q) h
    · simp only [LMem.readU, LMem.readT, hk, if_false] at h ⊢
      exact LMem.readU_sim σ m i a h
  | .write m j b v, i, a, u, h =>
    readU_write_sim (fun i a _ h => LMem.readU_sim σ m i a h) (LMV.wordU_sim σ v)
      (LSel.idxU_sim σ b) h
termination_by structural x => x

/-- **The tests of names in the elimination agree with `nameG` and `structG`.** -/
theorem LMem.objU_sim (σ : State) : (m : LMem) → ∀ (str : Bool) (i : LId) {g : LTerm},
    m.objU str i = some g → ∃ g', (if str then m.structG i else m.nameG i) = some g' ∧
      (Rets (g.eval σ) ↔ Rets (g'.eval σ))
  | .init, _, _, _, h => by simp only [LMem.objU, reduceCtorEq] at h
  | .addM m k R, str, i, g, h => by
    by_cases hk : i.root = k
    · simp only [LMem.objU, hk, if_true, Option.some.injEq] at h
      subst h
      cases str <;> exact ⟨_, by simp only [LMem.structG, LMem.nameG, hk, ↓reduceIte, Bool.false_eq_true], Iff.rfl⟩
    · simp only [LMem.objU, hk, if_false] at h
      obtain ⟨g', hg', hr⟩ := LMem.objU_sim σ m str i h
      cases str <;> exact ⟨g', by simpa only [LMem.structG, LMem.nameG, hk, if_false] using hg', hr⟩
  | .newArr m k R n, str, i, g, h => by
    by_cases hk : i.root = k
    · simp only [LMem.objU, hk, if_true, Option.some.injEq] at h
      subst h
      cases str <;> exact ⟨_, by simp only [LMem.structG, LMem.nameG, hk, ↓reduceIte,
        Bool.false_eq_true], rets_of_sim (newObj_congr σ _ R (LTerm.elim_sim σ n) i.path)⟩
    · simp only [LMem.objU, hk, if_false] at h
      obtain ⟨g', hg', hr⟩ := LMem.objU_sim σ m str i h
      cases str <;> exact ⟨g', by simpa only [LMem.structG, LMem.nameG, hk, if_false] using hg', hr⟩
  | .copySt m k s q, str, i, g, h => by
    by_cases hk : i.root = k
    · simp only [LMem.objU, hk, if_true] at h
      split at h
      · rename_i hl
        simp only [Option.some.injEq] at h
        subst h
        have he := LPath.ext_congr σ (LPath.elim_sim σ q) i.path
        refine ⟨if str then structT s (q.ext i.path) else refT s (q.ext i.path), ?_,
          copyObj_hoist.trans <|
          copyObjU_rets (guard_sim (LStor.okE_sim σ s) he fun _ _ hv hq => LStor.readU_sim σ s _ hv hq)
            (guard_sim (LStor.okE_sim σ s) he fun _ _ hv hq => LStor.hasU_sim σ s _ hv hq)
            (guard_sim (LStor.okE_sim σ s) he fun _ _ hv hq => LStor.lenU_sim σ s _ hv hq) str⟩
        cases str <;> simp only [LMem.structG, LMem.nameG, hk, hl, if_true, Bool.false_eq_true,
          if_false]
      · cases h
    · simp only [LMem.objU, hk, if_false] at h
      obtain ⟨g', hg', hr⟩ := LMem.objU_sim σ m str i h
      cases str <;> exact ⟨g', by simpa only [LMem.structG, LMem.nameG, hk, if_false] using hg', hr⟩
  | .write m _ _ _, str, i, g, h => by
    simp only [LMem.objU] at h
    obtain ⟨g', hg', hr⟩ := LMem.objU_sim σ m str i h
    cases str <;> exact ⟨g', by simpa only [LMem.structG, LMem.nameG] using hg', hr⟩
termination_by structural x => x

/-- **The run guard of a memory returns exactly where the run does.** -/
theorem LMem.okU_sim (σ : State) : (m : LMem) → ∀ {g : LTerm}, m.okU = some g →
    (Rets (g.eval σ) ↔ ∃ r, m.run σ = .ok r)
  | .init, _, h => init_okU_rets h
  | .addM m _ _, _, h => addM_okU_rets (fun hG => LMem.okU_sim σ m hG) h
  | .newArr m _ _ n, _, h => newArr_okU_rets (fun hG => LMem.okU_sim σ m hG) (LTerm.elim_sim σ n) h
  | .copySt m _ s q, _, h => copySt_okU_rets (fun hG => LMem.okU_sim σ m hG)
      (guard_sim (LStor.okE_sim σ s) (LPath.elim_sim σ q)
        fun _ _ hv hq => LStor.cpokU_sim σ s q.elim hv hq)
      (guard_sim (LStor.okE_sim σ s) (LPath.elim_sim σ q)
        fun _ _ hv hq => LStor.readU_sim σ s q.elim hv hq) h
  | .write m _ b v, _, h => write_okU_rets (fun hG => LMem.okU_sim σ m hG)
      (fun str i _ h => LMem.objU_sim σ m str i h) (fun i a _ h => LMem.readU_sim σ m i a h)
      (LMV.wordU_sim σ v) (LSel.idxU_sim σ b) h
termination_by structural x => x
end

/-- Eliminating keeps the meaning of a formula: an equation holds when both
sides return and agree, and eliminating keeps what they return. -/
theorem LFml.elim_holds (σ : State) : (φ : LFml) → (φ.elim.holds σ ↔ φ.holds σ)
  | .tt => Iff.rfl
  | .eq a b => by
    have ha := LTerm.elim_sim σ a
    have hb := LTerm.elim_sim σ b
    simp only [LFml.elim, LFml.holds]
    cases h₁ : a.eval σ with
    | error e =>
      have : ∀ x, a.elim.eval σ ≠ .ok x := fun x hx => by simp only [(ha x).1 hx,
          reduceCtorEq] at h₁
      cases h₂ : a.elim.eval σ with
      | error => simp only
      | ok x => exact absurd h₂ (this x)
    | ok x =>
      rw [(ha x).2 h₁]
      cases h₃ : b.eval σ with
      | error e =>
        have : ∀ y, b.elim.eval σ ≠ .ok y := fun y hy => by simp only [(hb y).1 hy,
            reduceCtorEq] at h₃
        cases h₄ : b.elim.eval σ with
        | error => simp only
        | ok y => exact absurd h₄ (this y)
      | ok y => rw [(hb y).2 h₃]
  | .not φ => by simp only [LFml.elim, LFml.holds, LFml.elim_holds σ φ]
  | .and φ ψ => by simp only [LFml.elim, LFml.holds, LFml.elim_holds σ φ, LFml.elim_holds σ ψ]
  | .imp φ ψ => by simp only [LFml.elim, LFml.holds, LFml.elim_holds σ φ, LFml.elim_holds σ ψ]
  | .all x p φ => by
    simp only [LFml.elim, LFml.holds]
    exact forall_congr' fun v => imp_congr_right fun _ => LFml.elim_holds _ φ

/-! ## The reduction -/

/-- What `sol_decide` proves of `φ`: its updates pushed in, the reads of
writes eliminated.  What is left reads the initial state only: its locals,
and the words and locations of its storage. -/
def _root_.Solidity.Fml.reduce (φ : Fml C) : LFml := (φ.toL Sym.empty).elim

/-- **`⊨ φ` is exactly `φ.reduce` in every state**, for every `φ` in the
fragment: nothing valid is lost, nothing invalid is gained.

Example: what symbolic execution leaves of
`[ balances[k] = 5; balances[j] = 6; uint y = balances[k]; ] (k == j → y == 6)`
is valid exactly when its reduction, a statement about `k`, `j` and whether
`balances[k]` and `balances[j]` are locations, holds in every state. -/
theorem _root_.Solidity.Fml.valid_iff_reduce (φ : Fml C) (hf : φ.inL Sym.empty = true) :
    (⊨ φ) ↔ ∀ σ, φ.reduce.holds σ := by
  rw [Fml.valid_iff_toL φ hf]
  exact forall_congr' fun σ => (LFml.elim_holds σ _).symm

/-! ### Unfolding the reduced formula

The reduced formula reads the initial state only, so it unfolds to a
statement about `σ.getEnv x` and the storage tree `SVal.struct σ.storage`,
which stay atoms.  The equations below state it in `sol_close`'s weakest
preconditions, so that `close_rw` takes it from there. -/

theorem LFml.holds_tt (σ : State) : LFml.tt.holds σ ↔ True := Iff.rfl
/-- `k != j` is `¬ k = j`. -/
theorem LFml.holds_not (σ : State) (φ : LFml) : (LFml.not φ).holds σ ↔ ¬ φ.holds σ := Iff.rfl
/-- `y == 0 && z == 30`. -/
theorem LFml.holds_and (σ : State) (φ ψ : LFml) :
    (LFml.and φ ψ).holds σ ↔ φ.holds σ ∧ ψ.holds σ := Iff.rfl
/-- `k == j → y == 6`. -/
theorem LFml.holds_imp (σ : State) (φ ψ : LFml) :
    (LFml.imp φ ψ).holds σ ↔ (φ.holds σ → ψ.holds σ) := Iff.rfl

/-- `y == 6`: both sides return, and agree. -/
theorem LFml.holds_eq (σ : State) (a b : LTerm) : (LFml.eq a b).holds σ ↔
    Modality.diamond.wp (a.eval σ) fun x => Modality.diamond.wp (b.eval σ) fun y => x = y := by
  simp only [LFml.holds]
  cases a.eval σ <;> cases b.eval σ <;> simp only [Modality.wp, Modality.onHalt]

/-- `delete` of a `uint` leaves `0`. -/
theorem zeroV_int (v : Int) : zeroV (.int v) = .int 0 := rfl
/-- `delete` of a `bool` leaves `false`. -/
theorem zeroV_bool (b : Bool) : zeroV (.bool b) = .bool false := rfl

/-! ## The tactic -/

open Lean Elab Tactic Meta in
/-- Compute `φ.reduce` in a goal `∀ σ, (Fml.reduce φ).holds σ`: the formula
is closed after `sol_symex`, so it is run as compiled code and quoted back,
and the kernel checks the result (`replaceTargetDefEq`), as mini-solkey's
`reduceGoal` does. -/
def reduceGoal (g : MVarId) : MetaM MVarId := do
  let ty ← instantiateMVars (← g.getType)
  let .forallE n d b bi := ty | throwError "sol_decide: expected `∀ σ, …`"
  let_expr LFml.holds _ r := b | throwError "sol_decide: expected `LFml.holds σ …`"
  let r' ← if r.hasFVar || r.hasMVar || r.hasLooseBVars then
      withTransparency .all <| Meta.reduce r (skipTypes := true) (skipProofs := true)
    else
      pure (toExpr (← unsafe evalExpr LFml (mkConst ``LFml) r))
  g.replaceTargetDefEq (.forallE n d (mkApp2 (mkConst ``LFml.holds) (.bvar 0) r') bi)

open Lean Elab Tactic in
/-- Replace `Fml.reduce φ` by the formula it computes to. -/
elab "sol_reduce" : tactic => do replaceMainGoal [← reduceGoal (← getMainGoal)]


/-- The free locals of a formula. -/
def LFml.vars : LFml → List Var
  | .tt => []
  | .eq a b => a.vars ++ b.vars
  | .not φ => φ.vars
  | .and φ ψ | .imp φ ψ => φ.vars ++ ψ.vars
  | .all _ _ φ => φ.vars

/-- A local read as a value halts, is an integer, or is a boolean. -/
theorem value_cases (r : Res Value) :
    (∃ e, r = .error e) ∨ (∃ i, r = .ok (.int i)) ∨ ∃ b, r = .ok (.bool b) := by
  rcases r with e | (i | b)
  · exact .inl ⟨e, rfl⟩
  · exact .inr (.inl ⟨i, rfl⟩)
  · exact .inr (.inr ⟨b, rfl⟩)

/-! The equations of `LTerm.eval` but the local's: a local is split on
first (`sol_decide_split`), so that a key is an integer before the key
tests are unfolded. -/

/-- `10` is `10`. -/
theorem LTerm.eval_lit (σ : State) (v : Value) : (LTerm.lit v).eval σ = .ok v := rfl
/-- `x + 1`: `x`, then the operator. -/
theorem LTerm.eval_binop (σ : State) (op : BinOp) (p : PrimTy) (a b : LTerm) :
    (LTerm.binop op p a b).eval σ = a.eval σ >>= fun x => evalBinop op p x (b.eval σ) := rfl
/-- `!flag`: the operand, then the operator. -/
theorem LTerm.eval_unop (σ : State) (op : UnOp) (p : PrimTy) (a : LTerm) :
    (LTerm.unop op p a).eval σ = a.eval σ >>= fun x => applyUnOp op x >>= unopCheck op p := rfl
/-- `c ? a : b`: the condition, then the branch. -/
theorem LTerm.eval_ite (σ : State) (c a b : LTerm) :
    (LTerm.ite c a b).eval σ = c.eval σ >>= fun cv => pickBranch cv (a.eval σ) (b.eval σ) := rfl
/-- `balances[k]`: the storage, the path, the word there. -/
theorem LTerm.eval_find (σ : State) (s : LStor) (q : LPath) : (LTerm.find s q).eval σ =
    s.eval σ >>= fun v => q.eval σ >>= fun qs => v.findLive qs >>= SVal.asValue := rfl
/-- `balances[k]` is a location. -/
theorem LTerm.eval_has (σ : State) (s : LStor) (q : LPath) : (LTerm.has s q).eval σ =
    s.eval σ >>= fun v => q.eval σ >>= fun qs => v.findLive qs >>= fun _ => .ok (.bool true) := rfl
/-- `ledger.balances` is a mapping. -/
theorem LTerm.eval_kmap (σ : State) (sh : KShape) (s : LStor) (q : LPath) :
    (LTerm.kmap sh s q).eval σ =
      s.eval σ >>= fun v => q.eval σ >>= fun qs => v.findLive qs >>= sh.test := rfl
/-- `values.length`. -/
theorem LTerm.eval_len (σ : State) (s : LStor) (q : LPath) : (LTerm.len s q).eval σ =
    s.eval σ >>= fun v => q.eval σ >>= fun qs => v.findLive qs >>= Close.arrLen := rfl
/-- `a`, or `b` where `a` halts. -/
theorem LTerm.eval_orElse (σ : State) (a b : LTerm) :
    (LTerm.orElse a b).eval σ = orElseR (a.eval σ) (b.eval σ) := rfl
/-- `balances[k] = 5;` succeeds. -/
theorem LTerm.eval_sok (σ : State) (s : LStor) :
    (LTerm.sok s).eval σ = s.eval σ >>= fun _ => .ok (.bool true) := rfl
/-- The key `k` of `balances[k]` is an integer. -/
theorem LTerm.eval_pok (σ : State) (q : LPath) :
    (LTerm.pok q).eval σ = q.eval σ >>= fun _ => .ok (.bool true) := rfl
/-- The guard, then the read. -/
theorem LTerm.eval_seq (σ : State) (d a : LTerm) :
    (LTerm.seq d a).eval σ = d.eval σ >>= fun _ => a.eval σ := rfl
/-- `k == j ? 6 : 5`, the keys compared as integers. -/
theorem LTerm.eval_kite (σ : State) (a b t e : LTerm) : (LTerm.kite a b t e).eval σ =
    (a.eval σ >>= Value.asInt) >>= fun i => (b.eval σ >>= Value.asInt) >>= fun j =>
      if i = j then t.eval σ else e.eval σ := rfl
/-- `delete alice.age;` then `alice.age`: the default of the old word. -/
theorem LTerm.eval_zero (σ : State) (a : LTerm) :
    (LTerm.zero a).eval σ = a.eval σ >>= fun v => .ok (zeroV v) := rfl
/-- A read above a write: `alice` after `alice.age = 3;` is no word. -/
theorem LTerm.eval_err (σ : State) : LTerm.err.eval σ = .error .stuck := rfl
theorem LTerm.eval_env (σ : State) (k : EnvKey) :
    (LTerm.env k).eval σ = .ok (.int (σ.envVal k)) := rfl
theorem LTerm.eval_findP (σ : State) (s : LStor) (q : LPath) : (LTerm.findP s q).eval σ =
    s.eval σ >>= fun v => q.eval σ >>= fun qs => v.find qs >>= SVal.asValue := rfl

open Lean Elab Tactic Meta in
/-- Split on every local of the reduced formula: it halts, is an integer,
or is a boolean.  Afterwards every key is a known integer or halts, and the
key tests unfold to `if i = j`. -/
elab "sol_decide_split" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr LFml.holds σ r := ty | throwError "sol_decide: expected `LFml.holds σ …`"
  let xs ← unsafe evalExpr (List Var) (mkApp (mkConst ``List [levelZero]) (mkConst ``Var))
    (mkApp (mkConst ``LFml.vars) r)
  for x in xs.eraseDups do
    let t := mkApp2 (mkConst ``LTerm.eval) σ (mkApp (mkConst ``LTerm.var) (toExpr x))
    let tt ← Term.exprToSyntax t
    evalTactic (← `(tactic| all_goals
      rcases value_cases $tt with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩))

/-- A storage read halts, or is a word, a struct, an array of either kind, or
a mapping. -/
theorem sval_cases (r : Res SVal) :
    (∃ e, r = .error e) ∨ (∃ p, r = .ok (.prim p)) ∨ (∃ fs, r = .ok (.struct fs)) ∨
      (∃ es sh, r = .ok (.array es sh false)) ∨ (∃ es sh, r = .ok (.array es sh true)) ∨
      ∃ es d, r = .ok (.map es d) := by
  rcases r with e | ((p | fs | ⟨es, sh, _ | _⟩ | ⟨es, d⟩))
  · exact .inl ⟨e, rfl⟩
  · exact .inr (.inl ⟨p, rfl⟩)
  · exact .inr (.inr (.inl ⟨fs, rfl⟩))
  · exact .inr (.inr (.inr (.inl ⟨es, sh, rfl⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨es, sh, rfl⟩))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨es, d, rfl⟩))))

open Lean Elab Tactic Meta in
/-- Split on the shape of every storage read a shape case makes: where a read
below a deleted location crosses a key, what it returns depends on whether the
location above the key is a mapping or a fixed-size array (`delBelow`, the
hypotheses with an `orElseR`), and a case on the read's result settles the
shape tests. -/
elab "sol_decide_reads" : tactic => withMainContext do
  let mut reads : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    -- only the reads a shape case (`orElseR`, `delBelow`) depends on
    unless ty.find? (·.isConstOf ``orElseR) |>.isSome do continue
    let found : Array Expr ← (StateT.run (s := #[]) do
      ty.forEachWhere (fun e => e.isAppOfArity ``SVal.findLive 2 && !e.hasLooseBVars)
        fun e => (modify (·.push e) : StateT (Array Expr) TacticM Unit)) <&> (·.2)
    for e in found do
      unless reads.contains e do reads := reads.push e
  for e in reads do
    let t ← Term.exprToSyntax e
    evalTactic (← `(tactic| all_goals
      rcases sval_cases $t with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩))

attribute [decide_eval] LFml.holds_tt LFml.holds_not LFml.holds_and LFml.holds_imp
  LFml.holds_eq LTerm.eval_lit LTerm.eval_binop LTerm.eval_unop LTerm.eval_ite LTerm.eval_find
  LTerm.eval_has LTerm.eval_kmap LTerm.eval_len LTerm.eval_sok LTerm.eval_pok LTerm.eval_seq
  LTerm.eval_kite LTerm.eval_zero LTerm.eval_err LTerm.eval_env LTerm.eval_findP
  LTerm.eval_orElse LPath.eval
  LStor.eval State.envVal
  zeroV_int zeroV_bool KShape.test kmapF isMapV isFixV orElseR_ok orElseR_error

/-- The first pass of `sol_decide` after the split: unfold the reduced
formula into `sol_close`'s weakest preconditions. -/
macro "sol_decide_unfold" : tactic => `(tactic|
  set_option linter.unusedSimpArgs false in
  simp only [decide_eval, close_rw, *])

/-- The second: every fact in scope for every other. -/
macro "sol_decide_facts" : tactic => `(tactic|
  simp_all (config := { maxSteps := 400000 }) only [decide_eval, close_rw])

/-- The finishing step without the constraints, on a goal `∀ σ, ψ.holds σ`
with `ψ` computed: split on the locals, unfold, and close with `simp`,
`omega` and `grind`, splitting on the shape of a read below a deleted
location where `delBelow` asks.  It does not know how two reads of the
initial storage constrain each other; `sol_decide` (`DecideComplete.lean`)
runs it where the reduction still writes through a member named `length`,
which the constraints do not cover. -/
macro "sol_decide_heuristic" : tactic => `(tactic| (
    intro σ
    sol_decide_split
    all_goals sol_decide_unfold
    all_goals (intros; subst_vars)
    all_goals try sol_decide_facts
    all_goals (try intros)
    -- a read below a deleted location through a key is a case on the
    -- location's shape (`delBelow`): its binds opened, it is a case split
    all_goals first | omega | grind | (sol_decide_reads <;> simp_all only [Res.ok_bind,
      Res.error_bind, KShape.test, kmapF, isMapV, isFixV, orElseR_ok, orElseR_error, if_true,
      if_false, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] <;> grind)))

end Decide

end Solidity
