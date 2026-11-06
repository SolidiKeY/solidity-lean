import Solidity.Optimizer.CSE
import Solidity.Theory.Typed.Mem

/-!
# O03 redundant load elimination over lowering programs

A forward pass that records, for *static loads*, a simple value known to equal
them, and replaces a later occurrence of the load by that value: a second read
of a storage variable or memory slot with no intervening write to it reuses the
local the first read was assigned to, and a read after a store of a simple value
to the same location reuses that value (store-to-load forwarding). The static
loads (`Load`) are

* `x` — a read of a primitive state variable (`Val.read (.root x _)`);
* `v[k]` — a primitive entry of a state-variable mapping or array at a simple
  key (`balances[msg.sender]`, `values[i]`);
* `m.f` — a read of a primitive member of a memory local's struct
  (`Val.readMem (.field (.var m _) f _)`);
* `m[k]` — a read of a primitive element of a memory local's array at a simple
  index (`Val.readMem (.index _ (.var m _) (.simple k))`).

Entries (`LEnt`) are created by `x = ld;` and `T x = ld;` (the holder is the
local `x`), and by `v = s;` / `m.f = s;` / `m[k] = s;` with `s` simple (the
holder is `s`). Loads are replaced in the right-hand sides of local assignments
and declarations, in `require`/`assert`/`if` conditions and in the *value* of a
storage or memory store, not inside a store's location. The invariant is `LEnt.Holds E σ`: every recorded load
evaluates in `σ` to its holder's value, so each replaced read evaluated to that
value (it succeeded), and nothing that can fail is introduced or dropped.

## Alias analysis

The kill rules are a sound may-alias analysis on the intrinsic syntax, each
proved against the semantics:

* a local assignment `i = e` kills the entries whose holder or location reads
  `i` (`LEnt.reads`);
* a storage write `assign l _` kills only the storage entries (keyed ones
  included: the granularity is the state variable) of the root `l` starts at (`Loc.root?`; a write through a storage alias kills every storage
  entry); storage and memory are disjoint, so memory entries survive
  (`Storage.find_write_other`);
* a memory write `assignMem l _` kills only the memory entries it may alias
  (`Load.apart`): a member `f` is apart from a member `g ≠ f` of *any* object
  (two memory locals may alias the same struct, but distinct members never
  overlap), a member from an array element, and two elements at two distinct
  literal indices of any arrays; storage entries survive
  (`Heap.readAddr_writeAddr_apart`).

`require`, `assert` and local value declarations keep every entry; every other
statement (storage and memory declarations, calls, pushes, deletes, allocations,
payments, …) and the exit of a branch,
block or loop clears them, and a loop body starts with none. The pass reads no
gas and no memory size: the lowering IR has neither, and every rewrite here
keeps the heap typing, so no observation changes (`Prog.rle_empty_runC`).
-/
namespace Solidity.Optimizer.ConstFold
open Solidity

variable {C : Contract} {Γ : Ctx}

/-! ## Static loads -/

/-- A load whose location reads no storage and no memory beyond the slot
itself, and only simple values. -/
inductive Load (C : Contract) (Γ : Ctx) : PrimTy → Type where
  | sroot {p : PrimTy} (r : Name) (h : C.rootType r = some (.prim p)) : Load C Γ p
  | mfield {p : PrimTy} {s : Name} (i : Idx Γ (.mem (.struct s)))
      (hm : (Ty.ref (.struct s)).mapFree = true) (f : Name)
      (h : C.fieldType s f = some (.prim p)) : Load C Γ p
  | mindex {p : PrimTy} {R : RefTy} (a : ArrTy R (.prim p)) (i : Idx Γ (.mem R))
      (hm : (Ty.ref R).mapFree = true) (k : Simple C Γ .uint) : Load C Γ p
  /-- `v[k]` of a state variable `v`, a mapping or an array, at a simple key. -/
  | sindex {p : PrimTy} {R : RefTy} {k : PrimTy} (it : IndexTy R k (.prim p)) (r : Name)
      (h : C.rootType r = some (.ref R)) (key : Simple C Γ k) : Load C Γ p

namespace Load

/-- The expression a load is. -/
def toVal {p : PrimTy} : Load C Γ p → Val C Γ p
  | .sroot r h => .read (.root r h)
  | .mfield i hm f h => .readMem (.field (.var i hm) f h)
  | .mindex a i hm k => .readMem (.index a (.var i hm) (.simple k))
  | .sindex it r h key => .read (.index it (.loc (.root r h)) (.simple key))

/-- A mapping's index (every key is in bounds), not an array's. -/
def isMapB {R : RefTy} {k : PrimTy} {V : Ty} : IndexTy R k V → Bool
  | .map => true
  | .arr _ => false

/-- A load a store of its location forwards: a state variable, or a mapping entry. -/
def fwdOk {p : PrimTy} : Load C Γ p → Bool
  | .sroot .. => true
  | .sindex it .. => isMapB it
  | .mfield .. | .mindex .. => false

/-- The state variable a storage load reads. -/
def sroot? {p : PrimTy} : Load C Γ p → Option Name
  | .sroot r _ | .sindex _ r _ _ => some r
  | .mfield .. | .mindex .. => none

/-- The memory location of a memory load. -/
def mloc? {p : PrimTy} : Load C Γ p → Option (MLoc C Γ (.prim p))
  | .sroot .. | .sindex .. => none
  | .mfield i hm f h => some (.field (.var i hm) f h)
  | .mindex a i hm k => some (.index a (.var i hm) (.simple k))

/-- A memory location as a load, if it is static. -/
def ofMLoc? {p : PrimTy} : MLoc C Γ (.prim p) → Option (Load C Γ p)
  | .field (.var i hm) f h => some (.mfield i hm f h)
  | .index a (.var i hm) (.simple k) => some (.mindex a i hm k)
  | .field (.loc _) _ _ | .index _ (.loc _) _ | .index _ (.var ..) (.read _)
  | .index _ (.var ..) (.binop ..) | .index _ (.var ..) (.unop ..)
  | .index _ (.var ..) (.ternary ..) | .index _ (.var ..) (.readMem _)
  | .index _ (.var ..) (.len ..) | .index _ (.var ..) (.mlen ..)
  | .index _ (.var ..) (.modular ..) | .index _ (.var ..) (.hash ..) => none

theorem ofMLoc?_eq {p : PrimTy} {m : MLoc C Γ (.prim p)} {l : Load C Γ p}
    (h : ofMLoc? m = some l) : l.toVal = .readMem m := by
  match m, h with
  | .field (.var i hm) f h', h => cases h; rfl
  | .index a (.var i hm) (.simple k), h => cases h; rfl

/-- A storage location as a load, if it is static. -/
def ofLoc? {p : PrimTy} : Loc C Γ (.prim p) → Option (Load C Γ p)
  | .root r h => some (.sroot r h)
  | .index it b i =>
    match b, i with
    | .loc (.root r h), .simple key => some (.sindex it r h key)
    | _, _ => none
  | .field .. => none

theorem ofLoc?_eq {p : PrimTy} {l : Loc C Γ (.prim p)} {ld : Load C Γ p}
    (h : ofLoc? l = some ld) : ld.toVal = .read l := by
  cases l with
  | root r h' => cases h; rfl
  | field => simp only [ofLoc?, reduceCtorEq] at h
  | index it b i =>
    cases b with
    | alias => simp only [ofLoc?, reduceCtorEq] at h
    | loc l' =>
      cases l' with
      | root r h' =>
        cases i with
        | simple key => cases h; rfl
        | read | binop | unop | ternary | readMem | len | mlen | modular | hash =>
          simp only [ofLoc?, reduceCtorEq] at h
      | field | index => simp only [ofLoc?, reduceCtorEq] at h

/-- An expression as a load, if it is one. -/
def ofVal? {p : PrimTy} : Val C Γ p → Option (Load C Γ p)
  | .read l => ofLoc? l
  | .readMem m => ofMLoc? m
  | .simple _ | .binop .. | .unop .. | .ternary ..
  | .len .. | .mlen .. | .modular .. | .hash .. => none

theorem ofVal?_eq {p : PrimTy} {v : Val C Γ p} {l : Load C Γ p} (h : ofVal? v = some l) :
    l.toVal = v := by
  cases v with
  | read l => exact ofLoc?_eq h
  | readMem m => exact ofMLoc?_eq h
  | simple | binop | unop | ternary | len | mlen | modular | hash =>
    simp only [ofVal?, reduceCtorEq] at h

/-- Two loads that are syntactically the same. -/
def beq {p : PrimTy} : Load C Γ p → Load C Γ p → Bool
  | .sroot r _, .sroot r' _ => r == r'
  | .mfield i _ f _, .mfield i' _ f' _ => i.toNat == i'.toNat && f == f'
  | .mindex _ i _ k, .mindex _ i' _ k' => i.toNat == i'.toNat && Simple.beq k k'
  | .sindex (k := k) _ r _ key, .sindex (k := k') _ r' _ key' =>
    r == r' && if hk : k' = k then Simple.beq key (hk ▸ key') else false
  | .sroot .., .mfield .. | .sroot .., .mindex .. | .mfield .., .sroot ..
  | .mfield .., .mindex .. | .mindex .., .sroot .. | .mindex .., .mfield ..
  | .sindex .., .sroot .. | .sindex .., .mfield .. | .sindex .., .mindex ..
  | .sroot .., .sindex .. | .mfield .., .sindex .. | .mindex .., .sindex .. => false

/-- Two positions of one context at one number have one type. -/
theorem ty_of_toNat {t u : LTy} (i : Idx Γ t) (j : Idx Γ u) (h : i.toNat = j.toNat) : t = u := by
  have hi := Idx.getElem?_toNat i
  have hj := Idx.getElem?_toNat j
  rw [h, hj] at hi
  exact (Option.some.inj hi).symm

theorem ArrTy.eq {R : RefTy} {E : Ty} (a b : ArrTy R E) : a = b := by
  cases a <;> cases b <;> rfl

theorem IndexTy.eq {R : RefTy} {k : PrimTy} {V : Ty} (a b : IndexTy R k V) : a = b := by
  cases a with
  | map => cases b with
    | map => rfl
    | arr a' => cases a'
  | arr a => cases b with
    | map => cases a
    | arr b' => rw [ArrTy.eq a b']

theorem eq_of_beq {p : PrimTy} : (a b : Load C Γ p) → a.beq b = true → a = b
  | .sroot r h, .sroot r' h', e => by
    simp only [beq, beq_iff_eq] at e
    subst e
    rfl
  | .mfield (s := s) i hm f h, .mfield (s := s') i' hm' f' h', e => by
    simp only [beq, Bool.and_eq_true, beq_iff_eq] at e
    obtain ⟨hi, rfl⟩ := e
    have hs : s = s' := by
      have := ty_of_toNat i i' hi
      simp only [LTy.mem.injEq, RefTy.struct.injEq] at this
      exact this
    subst hs
    obtain rfl := Idx.toNat_inj i i' hi
    rfl
  | .mindex (R := R) a i hm k, .mindex (R := R') a' i' hm' k', e => by
    simp only [beq, Bool.and_eq_true, beq_iff_eq] at e
    obtain ⟨hi, hk⟩ := e
    have hR : R = R' := by
      have := ty_of_toNat i i' hi
      simp only [LTy.mem.injEq] at this
      exact this
    subst hR
    obtain rfl := Idx.toNat_inj i i' hi
    obtain rfl := ArrTy.eq a a'
    rw [Simple.beq_eq k k' hk]
  | .sindex (R := R) (k := k) it r h key, .sindex (R := R') (k := k') it' r' h' key', e => by
    simp only [beq, Bool.and_eq_true, beq_iff_eq] at e
    obtain ⟨rfl, e⟩ := e
    obtain rfl : R = R' := Ty.ref.inj (Option.some.inj (h.symm.trans h'))
    split at e
    · next hk =>
      subst hk
      obtain rfl := IndexTy.eq it it'
      rw [Simple.beq_eq key key' e]
    · simp only [Bool.false_eq_true] at e
  | .sroot .., .mfield .., e | .sroot .., .mindex .., e | .mfield .., .sroot .., e
  | .mfield .., .mindex .., e | .mindex .., .sroot .., e | .mindex .., .mfield .., e
  | .sindex .., .sroot .., e | .sindex .., .mfield .., e | .sindex .., .mindex .., e
  | .sroot .., .sindex .., e | .mfield .., .sindex .., e | .mindex .., .sindex .., e => by
    simp only [beq, Bool.false_eq_true] at e

end Load

/-! ## Loads under local changes -/

private theorem get_set_ne {H : HTy} {Γ : Ctx} {t u : LTy} : (i : Idx Γ t) → (j : Idx Γ u) →
    (v : t.TDenote C H) → (e : TEnv C H Γ) → i.toNat ≠ j.toNat →
      TEnv.get j (TEnv.set i v e) = TEnv.get j e
  | .here, .here, _, _, h => absurd rfl h
  | .here, .there _, _, _, _ => rfl
  | .there _, .here, _, _, _ => rfl
  | .there i, .there j, v, e, h => get_set_ne i j v e.2 fun h' => h (congrArg (· + 1) h')

private theorem get_set {H : HTy} {Γ : Ctx} {t : LTy} : (i : Idx Γ t) → (v : t.TDenote C H) →
    (e : TEnv C H Γ) → TEnv.get i (TEnv.set i v e) = v
  | .here, _, _ => rfl
  | .there i, v, e => get_set i v e.2

/-- A memory local's object, without the state-indexed matcher. -/
theorem mvalT_var {R : RefTy} (σ : State C Γ) (i : Idx Γ (.mem R))
    (hm : (Ty.ref R).mapFree = true) :
    MPath.mvalT σ (.var i hm) =
      Option.elim (TEnv.get i σ.env : Option (HRef σ.H R)) (.error .revert) .ok := by
  simp only [MPath.mvalT]
  split <;> next h => simp only [h, Option.elim]

namespace Load

/-- Does the load's location read the local at position `n`? -/
def reads {p : PrimTy} (n : Nat) : Load C Γ p → Bool
  | .sroot .. => false
  | .mfield i .. => i.toNat == n
  | .mindex _ i _ k => i.toNat == n || readsAt n k
  | .sindex _ _ _ key => readsAt n key

theorem evalT_setLocal {p q : PrimTy} (σ : State C Γ) (i : Idx Γ (.val q)) (v : q.Denote) :
    (l : Load C Γ p) → l.reads i.toNat = false →
      l.toVal.evalT (σ.setLocal i v) = l.toVal.evalT σ
  | .sroot .., _ => rfl
  | .mfield j hm f h, hr => by
    simp only [reads, beq_eq_false_iff_ne] at hr
    simp only [toVal, Val.evalT, MLoc.addrT, mvalT_var, State.setLocal]
    rw [get_set_ne i j v σ.env (Ne.symm hr)]
  | .mindex a j hm k, hr => by
    simp only [reads, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hr
    have hk := evalT_setLocal_of_not_reads σ i v k hr.2
    simp only [toVal, Val.evalT, MLoc.addrT, mvalT_var, State.setLocal] at hk ⊢
    rw [get_set_ne i j v σ.env (Ne.symm hr.1), hk]
  | .sindex it r h key, hr => by
    simp only [reads] at hr
    have hk := evalT_setLocal_of_not_reads σ i v key hr
    simp only [toVal, Val.evalT, Loc.resolveT, SPath.resolveT, ok_bind] at hk ⊢
    rw [hk]
    rfl

/-- A load read one local deeper. -/
def shift {t : LTy} {p : PrimTy} : Load C Γ p → Load C (t :: Γ) p
  | .sroot r h => .sroot r h
  | .mfield i hm f h => .mfield i.there hm f h
  | .mindex a i hm k => .mindex a i.there hm (shiftS k)
  | .sindex it r h key => .sindex it r h (shiftS key)

theorem evalT_shift {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) {p : PrimTy} :
    (l : Load C Γ p) → (l.shift (t := t)).toVal.evalT (σ.push v) = l.toVal.evalT σ
  | .sroot .. => rfl
  | .mfield .. => by
    simp only [shift, toVal, Val.evalT, MLoc.addrT, mvalT_var]
    rfl
  | .mindex a i hm k => by
    simp only [shift, toVal, Val.evalT, MLoc.addrT, mvalT_var, shiftS_evalT]
    rfl
  | .sindex it r h key => by
    simp only [shift, toVal, Val.evalT, Loc.resolveT, SPath.resolveT, ok_bind, shiftS_evalT]
    rfl

/-- A storage write leaves every memory load. -/
theorem evalT_withStorage_mem {p : PrimTy} (σ : State C Γ) (st : Storage C) :
    (l : Load C Γ p) → l.mloc?.isSome = true → l.toVal.evalT (σ.withStorage st) = l.toVal.evalT σ
  | .sroot .., h | .sindex .., h => by simp only [mloc?, Option.isSome_none, Bool.false_eq_true] at h
  | .mfield .., _ => by
    simp only [toVal, Val.evalT, MLoc.addrT, mvalT_var]
    rfl
  | .mindex .., _ => by
    simp only [toVal, Val.evalT, MLoc.addrT, mvalT_var]
    rfl

/-- A memory write leaves every storage load. -/
theorem evalT_withHeap_storage {p : PrimTy} (σ : State C Γ) (hp : Heap σ.H) :
    (l : Load C Γ p) → l.mloc? = none → l.toVal.evalT (σ.withHeap hp) = l.toVal.evalT σ
  | .sroot .., _ => rfl
  | .sindex .., _ => rfl
  | .mfield .., h | .mindex .., h => by simp only [mloc?, reduceCtorEq] at h

end Load

/-! ## Entries -/

/-- The load `l` is known to evaluate to the simple value `s`. -/
structure LEnt (C : Contract) (Γ : Ctx) where
  p : PrimTy
  l : Load C Γ p
  s : Simple C Γ p

/-- Every recorded load evaluates to its holder. -/
def LEnt.Holds (E : List (LEnt C Γ)) (σ : State C Γ) : Prop :=
  ∀ a ∈ E, a.l.toVal.evalT σ = .ok (a.s.evalT σ)

theorem LEnt.holds_nil (σ : State C Γ) : LEnt.Holds ([] : List (LEnt C Γ)) σ :=
  fun _ h => nomatch h

theorem LEnt.holds_filter {E : List (LEnt C Γ)} {σ : State C Γ} (hE : LEnt.Holds E σ)
    (f : LEnt C Γ → Bool) : LEnt.Holds (E.filter f) σ :=
  fun a ha => hE a (List.mem_filter.mp ha).1

/-- The holder of a recorded load. -/
def LEnt.find? {p : PrimTy} (l : Load C Γ p) : List (LEnt C Γ) → Option (Simple C Γ p)
  | [] => none
  | a :: E =>
    if h : a.p = p then
      if Load.beq (h ▸ a.l) l then some (h ▸ a.s) else LEnt.find? l E
    else LEnt.find? l E

theorem LEnt.find?_evalT {E : List (LEnt C Γ)} {σ : State C Γ} (hE : LEnt.Holds E σ)
    {p : PrimTy} (l : Load C Γ p) {s : Simple C Γ p} (hf : LEnt.find? l E = some s) :
    l.toVal.evalT σ = .ok (s.evalT σ) := by
  induction E with
  | nil => simp only [LEnt.find?, reduceCtorEq] at hf
  | cons a E ih =>
    have ha := hE a List.mem_cons_self
    have hE' : LEnt.Holds E σ := fun b hb => hE b (List.mem_cons_of_mem a hb)
    obtain ⟨q, l', s'⟩ := a
    simp only [LEnt.find?] at hf
    split at hf
    · next e =>
      subst e
      split at hf
      · next hb =>
        simp only [Option.some.injEq] at hf
        subst hf
        rw [← Load.eq_of_beq _ _ hb]
        exact ha
      · exact ih hE' hf
    · exact ih hE' hf

/-! ## Rewriting reads -/

/-- Replace every recorded static load by its holder. -/
def _root_.Solidity.Val.rle (E : List (LEnt C Γ)) : {p : PrimTy} → Val C Γ p → Val C Γ p
  | _, .binop op h hq a b => .binop op h hq (a.rle E) (b.rle E)
  | _, .unop op h hq a => .unop op h hq (a.rle E)
  | _, .ternary c a b => .ternary (c.rle E) (a.rle E) (b.rle E)
  | _, .modular op a b k => .modular op (a.rle E) (b.rle E) (k.rle E)
  | _, v@(.read _) | _, v@(.readMem _) =>
    match Load.ofVal? v with
    | some l =>
      match LEnt.find? l E with
      | some s => .simple s
      | none => v
    | none => v
  | _, v@(.simple _) | _, v@(.len ..) | _, v@(.mlen ..) | _, v@(.hash ..) => v

theorem _root_.Solidity.Val.rle_evalT {E : List (LEnt C Γ)} {σ : State C Γ}
    (hE : LEnt.Holds E σ) : {p : PrimTy} → (v : Val C Γ p) → (v.rle E).evalT σ = v.evalT σ
  | _, .binop op h hq a b => by
    simp only [Val.rle, Val.evalT, Val.rle_evalT hE a, Val.rle_evalT hE b]
  | _, .unop op h hq a => by simp only [Val.rle, Val.evalT, Val.rle_evalT hE a]
  | _, .ternary c a b => by
    simp only [Val.rle, Val.evalT, Val.rle_evalT hE c, Val.rle_evalT hE a, Val.rle_evalT hE b]
  | _, .modular op a b k => by
    simp only [Val.rle, Val.evalT, Val.rle_evalT hE a, Val.rle_evalT hE b, Val.rle_evalT hE k]
  | _, .read l => by
    simp only [Val.rle]
    split
    · next ld hl =>
      split
      · next s hs =>
        rw [← Load.ofVal?_eq hl, LEnt.find?_evalT hE ld hs]
        rfl
      · rfl
    · rfl
  | _, .readMem l => by
    simp only [Val.rle]
    split
    · next ld hl =>
      split
      · next s hs =>
        rw [← Load.ofVal?_eq hl, LEnt.find?_evalT hE ld hs]
        rfl
      · rfl
    · rfl
  | _, .simple _ | _, .len .. | _, .mlen .. | _, .hash .. => rfl

/-! ## Storage: writes leave other roots -/

mutual
theorem _root_.Solidity.SPath.resolveT_rootName {σ : State C Γ} : {T : Ty} → (b : SPath C Γ T) →
    {n : Name} → b.root? = some n → {ref : SRef C T} → b.resolveT σ = .ok ref → ref.root = n
  | _, .alias _, _, h, _, _ => by simp only [SPath.root?, reduceCtorEq] at h
  | _, .loc l, _, h, _, hr => Loc.resolveT_rootName l h hr

theorem _root_.Solidity.Loc.resolveT_rootName {σ : State C Γ} : {T : Ty} → (l : Loc C Γ T) →
    {n : Name} → l.root? = some n → {ref : SRef C T} → l.resolveT σ = .ok ref → ref.root = n
  | _, .root r _, _, h, _, hr => by
    simp only [Loc.root?, Option.some.injEq] at h
    simp only [Loc.resolveT, Except.ok.injEq] at hr
    subst h hr
    rfl
  | _, .field b _ _, _, h, _, hr => by
    simp only [Loc.root?] at h
    simp only [Loc.resolveT, bind, Except.bind, pure, Except.pure] at hr
    split at hr
    · exact absurd hr (by simp only [reduceCtorEq, not_false_eq_true])
    · next r hb =>
      cases hr
      exact SPath.resolveT_rootName b h hb
  | _, .index _ b _, _, h, _, hr => by
    simp only [Loc.root?] at h
    simp only [Loc.resolveT, bind, Except.bind, pure, Except.pure] at hr
    split at hr
    · exact absurd hr (by simp only [reduceCtorEq, not_false_eq_true])
    · next r hb =>
      repeat' split at hr
      all_goals first
        | exact absurd hr (by simp only [reduceCtorEq, not_false_eq_true])
        | (cases hr; exact SPath.resolveT_rootName b h hb)
end

/-- A save at a reference leaves every reference at another root. -/
theorem Storage.find_save_other {st st' : Storage C} {U W : Ty} {ref : SRef C U} {v : SVal U}
    (h : st.save ref v = some st') (q : SRef C W) (hq : q.root ≠ ref.root) :
    st'.find q = st.find q := by
  simp only [Storage.save, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨x, -, rfl⟩ := h
  simp only [Storage.find]
  rw [SFields.get_set_ne _ ref.hroot q.hroot (Ne.symm hq)]

/-- A write at a reference leaves every reference at another root. -/
theorem Storage.find_write_other {st st' : Storage C} {U W : Ty} {ref : SRef C U} {v : SVal U}
    (h : st.write ref v = some st') (q : SRef C W) (hq : q.root ≠ ref.root) :
    st'.find q = st.find q := by
  unfold Storage.write at h
  split at h
  · exact Storage.find_save_other h q hq
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, -, h⟩ := h
    exact Storage.find_save_other h q hq

theorem Storage.find_write_prim {st st' : Storage C} {p : PrimTy} {ref : SRef C (.prim p)}
    {x : p.Denote} (h : st.write ref (.prim x) = some st') : st'.find ref = some (.prim x) := by
  unfold Storage.write at h
  simp only [SVal.isPrim, Ty.isPrimitive, ite_true] at h
  exact Storage.find_save_same h

theorem find_root {st : Storage C} {T : Ty} (n : Name) (h : C.rootType n = some T) :
    st.find (SRef.ofRoot n h) = some (st.get h) := rfl

theorem Simple.evalT_withStorage (σ : State C Γ) (st : Storage C) {p : PrimTy} (s : Simple C Γ p) :
    s.evalT (σ.withStorage st) = s.evalT σ := by
  cases s <;> rfl

theorem Simple.evalT_withHeap (σ : State C Γ) (hp : Heap σ.H) {p : PrimTy} (s : Simple C Γ p) :
    s.evalT (σ.withHeap hp) = s.evalT σ := by
  cases s <;> rfl

/-- A storage load reads only references at its state variable: a write at
another root leaves it (`uint a = total; age = 5;` keeps `total`, and
`balances[k]` survives `age = 5;`). -/
theorem Load.evalT_storage_write (σ : State C Γ) {st : Storage C} {U : Ty} {ref : SRef C U}
    {v : SVal U} (hw : σ.storage.write ref v = some st) {p : PrimTy} :
    (l : Load C Γ p) → {r : Name} → l.sroot? = some r → r ≠ ref.root →
      l.toVal.evalT (σ.withStorage st) = l.toVal.evalT σ
  | .sroot r' h, r, hl, hr => by
    simp only [Load.sroot?, Option.some.injEq] at hl
    subst hl
    simp only [Load.toVal, Val.evalT, Loc.resolveT, ok_bind]
    rw [show (σ.withStorage st).storage = st from rfl,
      Storage.find_write_other hw (SRef.ofRoot r' h) hr]
  | .sindex it r' h key, r, hl, hr => by
    simp only [Load.sroot?, Option.some.injEq] at hl
    subst hl
    simp only [Load.toVal, Val.evalT, Loc.resolveT, SPath.resolveT, Storage.checkIndex, ok_bind,
      Simple.evalT_withStorage]
    rw [show (σ.withStorage st).storage = st from rfl,
      Storage.find_write_other hw (SRef.ofRoot r' h) hr]
    simp only [TRes.ofOpt]
    split
    · simp only [pure, Except.pure, ok_bind]
      rw [Storage.find_write_other hw ((SRef.ofRoot r' h).index it (key.evalT σ)) hr]
    · rfl
  | .mfield .., _, hl, _ | .mindex .., _, hl, _ => by
    simp only [Load.sroot?, reduceCtorEq] at hl

/-! ## Memory: field-sensitive apartness -/

/-- Two memory locations that never share a slot, whatever objects their
bases name: two distinct members, a member and an element, or two elements at
distinct literal indices. -/
def _root_.Solidity.MLoc.apartB {T U : Ty} : MLoc C Γ T → MLoc C Γ U → Bool
  | .field _ f _, .field _ g _ => f != g
  | .field .., .index .. => true
  | .index .., .field .. => true
  | .index _ _ (.simple (.lit n _)), .index _ _ (.simple (.lit m _)) => n != m
  | .index _ _ _, .index _ _ _ => false

theorem _root_.Solidity.MLoc.apartB_index {R R' : RefTy} {T U : Ty} {a : ArrTy R T}
    {a' : ArrTy R' U} {x : MPath C Γ (.ref R)} {y : MPath C Γ (.ref R')} {i j : Val C Γ .uint}
    (h : (MLoc.index a x i).apartB (MLoc.index a' y j) = true) :
    ∃ n m hn hm, i = .simple (.lit n hn) ∧ j = .simple (.lit m hm) ∧ n ≠ m := by
  cases i with
  | simple si =>
    cases si with
    | lit n hn =>
      cases j with
      | simple sj =>
        cases sj with
        | lit m hm =>
          simp only [MLoc.apartB, bne_iff_ne] at h
          exact ⟨n, m, hn, hm, rfl, rfl, h⟩
        | «local» | env => simp only [MLoc.apartB, Bool.false_eq_true] at h
      | read | binop | unop | ternary | readMem | len | mlen | modular | hash =>
        simp only [MLoc.apartB, Bool.false_eq_true] at h
    | «local» | env => simp only [MLoc.apartB, Bool.false_eq_true] at h
  | read | binop | unop | ternary | readMem | len | mlen | modular | hash =>
    simp only [MLoc.apartB, Bool.false_eq_true] at h

theorem _root_.Solidity.MLoc.addrT_apart {σ : State C Γ} {T U : Ty} {m : MLoc C Γ T}
    {m' : MLoc C Γ U} (hap : m.apartB m' = true) {a : MAddr σ.H T} {b : MAddr σ.H U}
    (ha : m.addrT σ = .ok a) (hb : m'.addrT σ = .ok b) : a.Apart b := by
  cases m with
  | field x f hf =>
    simp only [MLoc.addrT, bind, Except.bind, pure, Except.pure] at ha
    split at ha
    · exact absurd ha (by simp only [reduceCtorEq, not_false_eq_true])
    · cases ha
      cases m' with
      | field y g hg =>
        simp only [MLoc.addrT, bind, Except.bind, pure, Except.pure] at hb
        split at hb
        · exact absurd hb (by simp only [reduceCtorEq, not_false_eq_true])
        · cases hb
          simp only [MLoc.apartB, bne_iff_ne] at hap
          exact hap
      | index _ y j =>
        simp only [MLoc.addrT, bind, Except.bind, pure, Except.pure] at hb
        repeat' split at hb
        all_goals first
          | exact absurd hb (by simp only [reduceCtorEq, not_false_eq_true])
          | (cases hb; trivial)
  | index _ x i =>
    simp only [MLoc.addrT, bind, Except.bind, pure, Except.pure] at ha
    repeat' split at ha
    all_goals first
      | exact absurd ha (by simp only [reduceCtorEq, not_false_eq_true])
      | skip
    cases ha
    cases m' with
    | field y g hg =>
      simp only [MLoc.addrT, bind, Except.bind, pure, Except.pure] at hb
      split at hb
      · exact absurd hb (by simp only [reduceCtorEq, not_false_eq_true])
      · cases hb; trivial
    | index _ y j =>
      simp only [MLoc.addrT, bind, Except.bind, pure, Except.pure] at hb
      repeat' split at hb
      all_goals first
        | exact absurd hb (by simp only [reduceCtorEq, not_false_eq_true])
        | skip
      cases hb
      obtain ⟨n, m, hn, hm, rfl, rfl, hnm⟩ := MLoc.apartB_index hap
      simp only [Val.evalT, Simple.evalT, Except.ok.injEq] at *
      subst_vars
      intro _ he
      exact hnm (congrArg Subtype.val he)

/-! ## Memory loads across a write -/

namespace Load

theorem mloc?_toVal {p : PrimTy} {l : Load C Γ p} {m : MLoc C Γ (.prim p)}
    (h : l.mloc? = some m) : l.toVal = .readMem m := by
  cases l <;> simp only [mloc?, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem ofMLoc?_mloc {p : PrimTy} {m : MLoc C Γ (.prim p)} {l : Load C Γ p}
    (h : ofMLoc? m = some l) : l.mloc? = some m := by
  match m, h with
  | .field (.var i hm) f h', h => cases h; rfl
  | .index a (.var i hm) (.simple k), h => cases h; rfl

/-- A static memory location's address reads no heap. -/
theorem addrT_withHeap {p : PrimTy} (σ : State C Γ) (hp : Heap σ.H) {l : Load C Γ p}
    {m : MLoc C Γ (.prim p)} (h : l.mloc? = some m) :
    m.addrT (σ.withHeap hp) = m.addrT σ := by
  cases l <;> simp only [mloc?, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [MLoc.addrT, mvalT_var] <;> rfl

/-- A memory load apart from a written location reads as before the write (`xs[0]` after `xs[1] = 6;`). -/
theorem evalT_write_apart (σ : State C Γ) {T : Ty} {m' : MLoc C Γ T} {a : MAddr σ.H T}
    {mv : MVal σ.H T} {hp : Heap σ.H} (ha : m'.addrT σ = .ok a)
    (hw : σ.heap.writeAddr a mv = some hp) {p : PrimTy} (l : Load C Γ p)
    {m : MLoc C Γ (.prim p)} (hm : l.mloc? = some m) (hap : m'.apartB m = true) :
    l.toVal.evalT (σ.withHeap hp) = l.toVal.evalT σ := by
  rw [mloc?_toVal hm]
  simp only [Val.evalT, addrT_withHeap σ hp hm]
  cases hb : m.addrT σ with
  | error e => rfl
  | ok b =>
    simp only [bind, Except.bind]
    rw [show (σ.withHeap hp).heap = hp from rfl,
      Heap.readAddr_writeAddr_apart hw (MLoc.addrT_apart hap ha hb)]

/-- A static memory location reads back what was written there (`xs[0] = 4;` then `xs[0]` is `4`). -/
theorem evalT_write_same (σ : State C Γ) {p : PrimTy} {m : MLoc C Γ (.prim p)}
    {a : MAddr σ.H (.prim p)} {x : p.Denote} {hp : Heap σ.H} (ha : m.addrT σ = .ok a)
    (hw : σ.heap.writeAddr a x = some hp) {l : Load C Γ p} (hl : ofMLoc? m = some l) :
    l.toVal.evalT (σ.withHeap hp) = .ok x := by
  rw [ofMLoc?_eq hl]
  simp only [Val.evalT, addrT_withHeap σ hp (ofMLoc?_mloc hl), ha, ok_bind]
  rw [show (σ.withHeap hp).heap = hp from rfl, Heap.readAddr_writeAddr_same hw]
  rfl

end Load

/-! ## Entry updates -/

namespace LEnt

/-- Does the entry read the local at position `n`, in its holder or its location? -/
def reads (n : Nat) (a : LEnt C Γ) : Bool := readsAt n a.s || a.l.reads n

/-- Entries after `i = r;` (`r` already rewritten). -/
def set {q : PrimTy} (E : List (LEnt C Γ)) (i : Idx Γ (.val q)) (r : Val C Γ q) :
    List (LEnt C Γ) :=
  let kept := E.filter fun a => !a.reads i.toNat
  match Load.ofVal? r with
  | some l => if l.reads i.toNat then kept else ⟨q, l, .local i⟩ :: kept
  | none => kept

theorem holds_set {E : List (LEnt C Γ)} {σ : State C Γ} (hE : Holds E σ) {q : PrimTy}
    (i : Idx Γ (.val q)) (r : Val C Γ q) (v : q.Denote) (hv : r.evalT σ = .ok v) :
    Holds (set E i r) (σ.setLocal i v) := by
  have hkept : Holds (E.filter fun a => !a.reads i.toNat) (σ.setLocal i v) := by
    intro a ha
    obtain ⟨hmem, hk⟩ := List.mem_filter.mp ha
    simp only [reads, Bool.not_or, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hk
    rw [Load.evalT_setLocal σ i v a.l hk.2, hE a hmem, evalT_setLocal_of_not_reads σ i v a.s hk.1]
  unfold set
  split
  · next l hl =>
    split
    · exact hkept
    · next hr =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simp only [Bool.not_eq_true] at hr
        show l.toVal.evalT (σ.setLocal i v) = .ok (TEnv.get i (TEnv.set i v σ.env))
        rw [Load.evalT_setLocal σ i v l hr, Load.ofVal?_eq hl, hv, get_set]
      · exact hkept a ha
  · exact hkept

/-- An entry read one local deeper. -/
def shift {t : LTy} (a : LEnt C Γ) : LEnt C (t :: Γ) := ⟨a.p, a.l.shift, shiftS a.s⟩

/-- Entries after `T x = init;` (`init` already rewritten). -/
def decl {q : PrimTy} (E : List (LEnt C Γ)) (init : Option (Val C Γ q)) :
    List (LEnt C (.val q :: Γ)) :=
  let sh := E.map shift
  match init.bind Load.ofVal? with
  | some l => ⟨q, l.shift, .local .here⟩ :: sh
  | none => sh

theorem holds_decl {E : List (LEnt C Γ)} {σ : State C Γ} (hE : Holds E σ) {q : PrimTy}
    (init : Option (Val C Γ q)) (v : q.Denote) (hv : ∀ e, init = some e → e.evalT σ = .ok v) :
    Holds (decl E init) (σ.push (t := .val q) v) := by
  have hsh : Holds (E.map (shift (t := .val q))) (σ.push (t := .val q) v) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    show b.l.shift.toVal.evalT (σ.push (t := .val q) v) = .ok ((shiftS b.s).evalT _)
    rw [Load.evalT_shift, shiftS_evalT, hE b hb]
  unfold decl
  split
  · next l hl =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · obtain ⟨e, he, hel⟩ := Option.bind_eq_some_iff.mp hl
      show l.shift.toVal.evalT (σ.push (t := .val q) v) = .ok v
      rw [Load.evalT_shift, Load.ofVal?_eq hel, hv e he]
    · exact hsh a ha
  · exact hsh

/-- Entries a storage write at the root `n?` leaves (every one when the
write may reach any root). -/
def keepS (n? : Option Name) (E : List (LEnt C Γ)) : List (LEnt C Γ) :=
  E.filter fun a =>
    match a.l.sroot? with
    | some r =>
      match n? with
      | some n => r != n
      | none => false
    | none => true

/-- The entry a store of a simple value makes at a state variable, or at a
mapping entry of one at a simple key (`balances[k] = s;`; an array element is
not forwarded, its bounds being the array's). -/
def storeEnt? {T : Ty} (l : Loc C Γ T) : Src C Γ T → Option (LEnt C Γ)
  | .val v =>
    match simple? v, Load.ofLoc? l with
    | some s, some ld => if ld.fwdOk then some ⟨_, ld, s⟩ else none
    | _, _ => none
  | .copy .. | .fixedCopy .. | .copyMem .. | .fixedCopyMem .. => none

/-- Entries after `l = r;` (`r` already rewritten). -/
def store {T : Ty} (E : List (LEnt C Γ)) (l : Loc C Γ T) (r : Src C Γ T) : List (LEnt C Γ) :=
  (storeEnt? l r).toList ++ keepS l.root? E

/-- Entries a memory write at `m` leaves. -/
def keepM {T : Ty} (m : MLoc C Γ T) (E : List (LEnt C Γ)) : List (LEnt C Γ) :=
  E.filter fun a =>
    match a.l.mloc? with
    | none => true
    | some m0 => m.apartB m0

/-- The entry a store of a simple value at a static memory location makes. -/
def mstoreEnt? {T : Ty} (m : MLoc C Γ T) : MSrc C Γ T → Option (LEnt C Γ)
  | .val v =>
    match v with
    | .simple s => (Load.ofMLoc? m).map fun l => ⟨_, l, s⟩
    | _ => none
  | .ref _ => none

/-- Entries after `m = r;` in memory (`r` already rewritten). -/
def mstore {T : Ty} (E : List (LEnt C Γ)) (m : MLoc C Γ T) (r : MSrc C Γ T) :
    List (LEnt C Γ) :=
  (mstoreEnt? m r).toList ++ keepM m E

end LEnt

/-! ## Storage and memory writes, step by step -/

/-- `l = r;` that returns: its value, its reference and the written storage (`total = 5;`). -/
theorem assign_ok {T : Ty} {l : Loc C Γ T} {r : Src C Γ T} {σ : State C Γ}
    {o : Out C σ.H Γ} (ho : TRun.assign l r σ = .ok o) :
    ∃ sv ref st, r.valueT σ = .ok sv ∧ l.resolveT σ = .ok ref ∧
      σ.storage.write ref sv = some st ∧ o.st = σ.withStorage st := by
  simp only [TRun.assign, bind, Except.bind, pure, Except.pure] at ho
  split at ho
  · exact absurd ho (by simp only [reduceCtorEq, not_false_eq_true])
  · next sv hsv =>
    split at ho
    · exact absurd ho (by simp only [reduceCtorEq, not_false_eq_true])
    · next ref href =>
      split at ho
      · exact absurd ho (by simp only [reduceCtorEq, not_false_eq_true])
      · next st hst =>
        cases ho
        refine ⟨sv, ref, st, hsv, href, ?_, rfl⟩
        cases hw : σ.storage.write ref sv with
        | none => simp only [hw, TRes.ofOpt, reduceCtorEq] at hst
        | some st' => simp only [hw, TRes.ofOpt, Except.ok.injEq] at hst; rw [hst]

/-- `m = r;` in memory that returns: its value, address and heap (`xs[0] = 4;`). -/
theorem assignMem_ok {T : Ty} {m : MLoc C Γ T} {r : MSrc C Γ T} {σ : State C Γ}
    {o : Out C σ.H Γ} (ho : TRun.assignMem m r σ = .ok o) :
    ∃ mv a hp, r.mvalT σ = .ok mv ∧ m.addrT σ = .ok a ∧
      σ.heap.writeAddr a mv = some hp ∧ o.st = σ.withHeap hp := by
  simp only [TRun.assignMem, bind, Except.bind, pure, Except.pure] at ho
  split at ho
  · exact absurd ho (by simp only [reduceCtorEq, not_false_eq_true])
  · next mv hmv =>
    split at ho
    · exact absurd ho (by simp only [reduceCtorEq, not_false_eq_true])
    · next a ha =>
      split at ho
      · exact absurd ho (by simp only [reduceCtorEq, not_false_eq_true])
      · next hp hhp =>
        cases ho
        refine ⟨mv, a, hp, hmv, ha, ?_, rfl⟩
        cases hw : σ.heap.writeAddr a mv with
        | none => simp only [hw, TRes.ofOpt, reduceCtorEq] at hhp
        | some hp' => simp only [hw, TRes.ofOpt, Except.ok.injEq] at hhp; rw [hhp]

namespace LEnt

/-- The entries after `l = r;` hold where it returns (`uint a = total; age = 5;` keeps `total ↦ a`). -/
theorem holds_store {E : List (LEnt C Γ)} {σ : State C Γ} (hE : Holds E σ) {T : Ty}
    (l : Loc C Γ T) (r : Src C Γ T) {o : Out C σ.H Γ} (ho : TRun.assign l r σ = .ok o) :
    Holds (store E l r) o.st := by
  obtain ⟨sv, ref, st, hsv, href, hw, hst⟩ := assign_ok ho
  rw [hst]
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · -- the forwarded store
    cases r with
    | copy | fixedCopy | copyMem | fixedCopyMem =>
      simp only [storeEnt?, Option.toList_none, List.not_mem_nil] at ha
    | val v =>
      simp only [storeEnt?] at ha
      cases hs : simple? v with
      | none => simp only [hs, Option.toList_none, List.not_mem_nil] at ha
      | some s =>
        cases hl : Load.ofLoc? l with
        | none => simp only [hs, hl, Option.toList_none, List.not_mem_nil] at ha
        | some ld =>
          simp only [hs, hl] at ha
          split at ha
          · next hfw =>
            simp only [Option.toList_some, List.mem_singleton] at ha
            subst ha
            have hv := simple?_eq hs
            subst hv
            have hlv := Load.ofLoc?_eq hl
            simp only [Src.valueT, Val.evalT, pure, Except.pure, bind, Except.bind,
              Except.ok.injEq] at hsv
            subst hsv
            cases ld with
            | sroot n h =>
              simp only [Load.toVal, Val.read.injEq] at hlv
              subst hlv
              simp only [Loc.resolveT, Except.ok.injEq] at href
              subst href
              show Val.evalT (σ.withStorage st) (.read (.root n h)) = _
              simp only [Val.evalT, Loc.resolveT, ok_bind]
              rw [show (σ.withStorage st).storage = st from rfl, Storage.find_write_prim hw,
                Simple.evalT_withStorage]
              rfl
            | sindex it n h key =>
              cases it with
              | arr => simp only [Load.fwdOk, Load.isMapB, Bool.false_eq_true] at hfw
              | map =>
                simp only [Load.toVal, Val.read.injEq] at hlv
                subst hlv
                simp only [Loc.resolveT, SPath.resolveT, ok_bind, Storage.checkIndex,
                  find_root, Storage.inBounds, TRes.ofOpt, Option.bind_eq_bind,
                  Option.bind_some] at href
                cases href
                show Val.evalT (σ.withStorage st) (.read (.index .map (.loc (.root n h))
                  (.simple key))) = _
                simp only [Val.evalT, Loc.resolveT, SPath.resolveT, ok_bind,
                  Storage.checkIndex, find_root, Storage.inBounds, TRes.ofOpt,
                  Option.bind_eq_bind, Option.bind_some, Simple.evalT_withStorage, pure,
                  Except.pure]
                rw [show (σ.withStorage st).storage = st from rfl, Storage.find_write_prim hw]
                rfl
            | mfield | mindex => simp only [Load.fwdOk, Bool.false_eq_true] at hfw
          · simp only [Option.toList_none, List.not_mem_nil] at ha
  · obtain ⟨hmem, hk⟩ := List.mem_filter.mp ha
    have hold := hE a hmem
    obtain ⟨q, ld, s⟩ := a
    rw [show (⟨q, ld, s⟩ : LEnt C Γ).s.evalT (σ.withStorage st) = s.evalT σ from
      Simple.evalT_withStorage σ st s]
    cases hs : ld.sroot? with
    | some rn =>
      simp only [hs] at hk
      cases hn : l.root? with
      | none => simp only [hn, Bool.false_eq_true] at hk
      | some n =>
        simp only [hn, bne_iff_ne] at hk
        rw [Load.evalT_storage_write σ hw ld hs (by rw [Loc.resolveT_rootName l hn href]; exact hk)]
        exact hold
    | none =>
      cases ld with
      | sroot | sindex => simp only [Load.sroot?, reduceCtorEq] at hs
      | mfield | mindex => rw [Load.evalT_withStorage_mem σ st _ rfl]; exact hold

/-- The entries after a memory store hold where it returns (`xs[1] = 6;` keeps `xs[0] ↦ 4`). -/
theorem holds_mstore {E : List (LEnt C Γ)} {σ : State C Γ} (hE : Holds E σ) {T : Ty}
    (m : MLoc C Γ T) (r : MSrc C Γ T) {o : Out C σ.H Γ} (ho : TRun.assignMem m r σ = .ok o) :
    Holds (mstore E m r) o.st := by
  obtain ⟨mv, ad, hp, hmv, had, hw, hst⟩ := assignMem_ok ho
  rw [hst]
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · cases r with
    | val v =>
      cases v with
      | simple s =>
        simp only [mstoreEnt?] at ha
        cases hl : Load.ofMLoc? m with
        | none => simp only [hl, Option.map_none, Option.toList_none, List.not_mem_nil] at ha
        | some l =>
          simp only [hl, Option.map_some, Option.toList_some, List.mem_singleton] at ha
          subst ha
          simp only [MSrc.mvalT, Val.evalT, Except.ok.injEq] at hmv
          subst hmv
          show l.toVal.evalT (σ.withHeap hp) = .ok (s.evalT (σ.withHeap hp))
          rw [Load.evalT_write_same σ had hw hl, Simple.evalT_withHeap]
      | read | binop | unop | ternary | readMem | len | mlen | modular | hash =>
        simp only [mstoreEnt?, Option.toList_none, List.not_mem_nil] at ha
    | ref => simp only [mstoreEnt?, Option.toList_none, List.not_mem_nil] at ha
  · obtain ⟨hmem, hk⟩ := List.mem_filter.mp ha
    have hold := hE a hmem
    obtain ⟨q, ld, s⟩ := a
    rw [show (⟨q, ld, s⟩ : LEnt C Γ).s.evalT (σ.withHeap hp) = s.evalT σ from
      Simple.evalT_withHeap σ hp s]
    cases hm0 : ld.mloc? with
    | none => rw [Load.evalT_withHeap_storage σ hp ld hm0]; exact hold
    | some m0 =>
      simp only [hm0] at hk
      rw [Load.evalT_write_apart σ had hw ld hm0 hk]
      exact hold

end LEnt

/-! ## The pass -/

/-- Rewrite a storage source's value. -/
def _root_.Solidity.Src.rle (E : List (LEnt C Γ)) : {T : Ty} → Src C Γ T → Src C Γ T
  | _, .val v => .val (v.rle E)
  | _, s@(.copy ..) | _, s@(.fixedCopy ..) | _, s@(.copyMem ..) | _, s@(.fixedCopyMem ..) => s

theorem _root_.Solidity.Src.rle_valueT {E : List (LEnt C Γ)} {σ : State C Γ}
    (hE : LEnt.Holds E σ) : {T : Ty} → (r : Src C Γ T) → (r.rle E).valueT σ = r.valueT σ
  | _, .val v => by simp only [Src.rle, Src.valueT, Val.rle_evalT hE]
  | _, .copy .. | _, .fixedCopy .. | _, .copyMem .. | _, .fixedCopyMem .. => rfl

/-- Rewrite a memory source's value. -/
def _root_.Solidity.MSrc.rle (E : List (LEnt C Γ)) : {T : Ty} → MSrc C Γ T → MSrc C Γ T
  | _, .val v => .val (v.rle E)
  | _, s@(.ref _) => s

theorem _root_.Solidity.MSrc.rle_mvalT {E : List (LEnt C Γ)} {σ : State C Γ}
    (hE : LEnt.Holds E σ) : {T : Ty} → (r : MSrc C Γ T) → (r.rle E).mvalT σ = r.mvalT σ
  | _, .val v => by simp only [MSrc.rle, MSrc.mvalT, Val.rle_evalT hE]
  | _, .ref _ => rfl

mutual
/-- Eliminate redundant loads in one statement: the rewritten statement and the
entries after it. -/
def Stmt.rle : {Γ Γ' : Ctx} → List (LEnt C Γ) → Stmt C Γ Γ' → Stmt C Γ Γ' × List (LEnt C Γ')
  | _, _, E, .assignLocal i r =>
    let r' := r.rle E
    (.assignLocal i r', LEnt.set E i r')
  | _, _, E, .declLocal p x init =>
    let init' := init.map (Val.rle E)
    (.declLocal p x init', LEnt.decl E init')
  | _, _, E, .require c => (.require (c.rle E), E)
  | _, _, E, .assert c => (.assert (c.rle E), E)
  | _, _, E, .ite c thn els => (.ite (c.rle E) (Prog.rle E thn) (Prog.rle E els), [])
  | _, _, E, .block body => (.block (Prog.rle E body), [])
  | _, _, _, .loop a c body => (.loop a c (Prog.rle [] body), [])
  | _, _, E, .assign l r =>
    let r' := r.rle E
    (.assign l r', LEnt.store E l r')
  | _, _, E, .assignMem m r =>
    let r' := r.rle E
    (.assignMem m r', LEnt.mstore E m r')
  | _, _, _, s@(.rebind ..) | _, _, _, s@(.declStorage ..)
  | _, _, _, s@(.opAssign ..) | _, _, _, s@(.incDec ..) | _, _, _, s@(.assignIncDec ..)
  | _, _, _, s@(.assignLocalPush ..) | _, _, _, s@(.push ..) | _, _, _, s@(.pop ..)
  | _, _, _, s@(.transfer ..) | _, _, _, s@(.send ..) | _, _, _, s@(.declMem ..)
  | _, _, _, s@(.rebindMem ..) | _, _, _, s@(.assignFromMem ..) | _, _, _, s@(.delete ..)
  | _, _, _, s@(.deleteMem ..) | _, _, _, s@(.assignNew ..)
  | _, _, _, s@.revert | _, _, _, s@.assumeFalse | _, _, _, s@(.call ..)
  | _, _, _, s@(.tryCall ..) | _, _, _, s@(.pushOpAssign ..) | _, _, _, s@(.pushIncDec ..)
  | _, _, _, s@(.callReceiver ..) | _, _, _, s@(.callReceiverPush ..)
  | _, _, _, s@(.callRec ..) | _, _, _, s@(.revertData ..) | _, _, _, s@(.catchData ..) =>
    (s, [])

/-- Eliminate redundant loads in a sequence. -/
def Prog.rle : {Γ Γ' : Ctx} → List (LEnt C Γ) → Prog C Γ Γ' → Prog C Γ Γ'
  | _, _, _, .nil => .nil
  | _, _, E, .cons s P =>
    let r := Stmt.rle E s
    .cons r.1 (Prog.rle r.2 P)
end

/-! ## Preservation -/

mutual
/-- A statement's rewrite runs as it does where the entry facts hold, and the
exit entries hold in each state it leaves. -/
theorem Stmt.rle_runC : {Γ Γ' : Ctx} → (E : List (LEnt C Γ)) → (s : Stmt C Γ Γ') →
    (σ : State C Γ) → LEnt.Holds E σ →
      Stmt.runC (Stmt.rle E s).1 σ = Stmt.runC s σ ∧
      ∀ o, Stmt.runC s σ = .ok o → LEnt.Holds (Stmt.rle E s).2 o.st
  | _, _, E, .assignLocal i r, σ, hE => by
    refine ⟨?_, ?_⟩
    · simp only [Stmt.rle, Stmt.runC, TRun.assignLocal, Val.rle_evalT hE]
    · intro o ho
      simp only [Stmt.runC, TRun.assignLocal, bind, Except.bind] at ho
      cases hr : r.evalT σ with
      | error e => simp only [hr, reduceCtorEq] at ho
      | ok v =>
        simp only [hr, pure, Except.pure, Except.ok.injEq] at ho
        subst ho
        exact LEnt.holds_set hE i (r.rle E) v (by rw [Val.rle_evalT hE, hr])
  | _, _, E, .declLocal p x init, σ, hE => by
    refine ⟨?_, ?_⟩
    · cases init <;> simp only [Stmt.rle, Stmt.runC, TRun.declLocal, Option.map, Val.rle_evalT hE]
    · intro o ho
      simp only [Stmt.rle]
      cases init with
      | none =>
        simp only [Stmt.runC, TRun.declLocal, pure, Except.pure, bind, Except.bind,
          Except.ok.injEq] at ho
        subst ho
        exact LEnt.holds_decl hE _ _ (fun _ h => nomatch h)
      | some e =>
        simp only [Stmt.runC, TRun.declLocal, bind, Except.bind] at ho
        cases he : e.evalT σ with
        | error err => simp only [he, reduceCtorEq] at ho
        | ok v =>
          simp only [he, pure, Except.pure, Except.ok.injEq] at ho
          subst ho
          refine LEnt.holds_decl hE _ v fun e' he' => ?_
          simp only [Option.map, Option.some.injEq] at he'
          subst he'
          rw [Val.rle_evalT hE, he]
  | _, _, E, .require c, σ, hE => by
    refine ⟨?_, ?_⟩
    · simp only [Stmt.rle, Stmt.runC, TRun.require, Val.rle_evalT hE]
    · intro o ho
      simp only [Stmt.runC, TRun.require, bind, Except.bind] at ho
      cases hc : c.evalT σ with
      | error e => simp only [hc, reduceCtorEq] at ho
      | ok v =>
        cases hb : boolT v
        · simp only [hc, hb, Bool.false_eq_true, ite_false, reduceCtorEq] at ho
        · simp only [hc, hb, ite_true, pure, Except.pure, Except.ok.injEq] at ho
          subst ho
          exact hE
  | _, _, E, .assert c, σ, hE => by
    refine ⟨?_, ?_⟩
    · simp only [Stmt.rle, Stmt.runC, TRun.assert, Val.rle_evalT hE]
    · intro o ho
      simp only [Stmt.runC, TRun.assert, bind, Except.bind] at ho
      cases hc : c.evalT σ with
      | error e => simp only [hc, reduceCtorEq] at ho
      | ok v =>
        cases hb : boolT v
        · simp only [hc, hb, Bool.false_eq_true, ite_false, reduceCtorEq] at ho
        · simp only [hc, hb, ite_true, pure, Except.pure, Except.ok.injEq] at ho
          subst ho
          exact hE
  | _, _, E, .ite c thn els, σ, hE => by
    refine ⟨?_, fun _ _ => LEnt.holds_nil _⟩
    simp only [Stmt.rle, Stmt.runC, TRun.ite, Val.rle_evalT hE,
      (Prog.rle_runC E thn σ hE), (Prog.rle_runC E els σ hE)]
    rw [Subsingleton.elim (Prog.rle E thn).ext thn.ext,
      Subsingleton.elim (Prog.rle E els).ext els.ext]
  | _, _, E, .block body, σ, hE => by
    refine ⟨?_, fun _ _ => LEnt.holds_nil _⟩
    simp only [Stmt.rle, Stmt.runC, TRun.block, (Prog.rle_runC E body σ hE)]
    rw [Subsingleton.elim (Prog.rle E body).ext body.ext]
  | _, _, _, .loop a c body, σ, _ => by
    refine ⟨?_, fun _ _ => LEnt.holds_nil _⟩
    have hb : Prog.runC (Prog.rle [] body) = Prog.runC body :=
      funext fun τ => Prog.rle_runC [] body τ (LEnt.holds_nil τ)
    simp only [Stmt.rle, Stmt.runC]
    rw [hb, TRun.loop_congr (fun _ => rfl) body.ext]
  | _, _, E, .assign l r, σ, hE =>
    ⟨by simp only [Stmt.rle, Stmt.runC, TRun.assign, Src.rle_valueT hE],
      fun o ho => by
        simp only [Stmt.rle]
        have ho' : TRun.assign l (r.rle E) σ = .ok o := by
          simp only [Stmt.runC] at ho
          simp only [TRun.assign, Src.rle_valueT hE]
          exact ho
        exact LEnt.holds_store hE l (r.rle E) ho'⟩
  | _, _, E, .assignMem m r, σ, hE =>
    ⟨by simp only [Stmt.rle, Stmt.runC, TRun.assignMem, MSrc.rle_mvalT hE],
      fun o ho => by
        simp only [Stmt.rle]
        have ho' : TRun.assignMem m (r.rle E) σ = .ok o := by
          simp only [Stmt.runC] at ho
          simp only [TRun.assignMem, MSrc.rle_mvalT hE]
          exact ho
        exact LEnt.holds_mstore hE m (r.rle E) ho'⟩
  | _, _, _, .rebind .., _, _ | _, _, _, .declStorage .., _, _
  | _, _, _, .opAssign .., _, _ | _, _, _, .incDec .., _, _ | _, _, _, .assignIncDec .., _, _
  | _, _, _, .assignLocalPush .., _, _ | _, _, _, .push .., _, _ | _, _, _, .pop .., _, _
  | _, _, _, .transfer .., _, _ | _, _, _, .send .., _, _ | _, _, _, .declMem .., _, _
  | _, _, _, .rebindMem .., _, _ | _, _, _, .assignFromMem .., _, _
  | _, _, _, .delete .., _, _ | _, _, _, .deleteMem .., _, _
  | _, _, _, .assignNew .., _, _ | _, _, _, .revert, _, _ | _, _, _, .assumeFalse, _, _
  | _, _, _, .call .., _, _ | _, _, _, .tryCall .., _, _ | _, _, _, .pushOpAssign .., _, _
  | _, _, _, .pushIncDec .., _, _ | _, _, _, .callReceiver .., _, _
  | _, _, _, .callReceiverPush .., _, _ | _, _, _, .callRec .., _, _
  | _, _, _, .revertData .., _, _ | _, _, _, .catchData .., _, _ =>
    ⟨rfl, fun _ _ => LEnt.holds_nil _⟩

/-- A sequence's rewrite runs as it does where the entry facts hold. -/
theorem Prog.rle_runC : {Γ Γ' : Ctx} → (E : List (LEnt C Γ)) → (P : Prog C Γ Γ') →
    (σ : State C Γ) → LEnt.Holds E σ → Prog.runC (Prog.rle E P) σ = Prog.runC P σ
  | _, _, _, .nil, _, _ => rfl
  | _, _, E, .cons s P, σ, hE => by
    obtain ⟨hrun, hout⟩ := Stmt.rle_runC E s σ hE
    simp only [Prog.rle, Prog.runC, TRun.seq, hrun]
    cases ho : Stmt.runC s σ with
    | error e => rfl
    | ok o =>
      dsimp only
      rw [Prog.rle_runC _ P o.st (hout o ho)]
end

/-- **Redundant load elimination preserves the typed run**, with no premise. -/
theorem _root_.Solidity.Prog.rle_empty_runC {Γ Γ' : Ctx} (P : Prog C Γ Γ') :
    Prog.runC (Prog.rle [] P) = Prog.runC P :=
  funext fun σ => Prog.rle_runC [] P σ (LEnt.holds_nil σ)

/-- Redundant load elimination as an O01 pass preserving `SameRun`. -/
theorem rle_preserves (Γ Γ' : Ctx) :
    Preserves (SameRun (C := C) (Γ := Γ) (Γ' := Γ'))
      (Prog.rle [] : Lowering.Pass C Γ Γ') :=
  fun P => (Prog.rle_empty_runC P).symm

end Solidity.Optimizer.ConstFold
