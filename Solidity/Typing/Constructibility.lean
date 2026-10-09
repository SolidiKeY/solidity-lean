import Solidity.Typing.Reachability

/-!
# Which storages are reachable, exactly

`Reachability.lean` proves reachable ⇒ canonical (`reachable_canon`).  The
converse needs four more facts, which every run keeps and `SVal.canon` does
not say; `SVal.tight` is exactly them:

- an array whose element type has no well-formed default has no slots at
  all: `push()` needs the default, and nothing else makes one (no struct of
  the table lacks one since decision 16 refused a repeated member name,
  `refusedStructs`; the clause stays for a type `defaultOkS` refuses);
- the slots past the end of an array of words are cleared: `pop`, `delete`
  and a shorter copy clear what they leave, and past an end only a reference
  reaches, never a word;
- a fixed-size array has nothing past its end;
- a mapping keyed by a reference type has no entries: no program indexes
  it (`IndexTy.map` takes a word key; a `bool` one is hashed as `0`/`1`,
  `Value.keyAt`).

Everything canonical and tight is reachable when its words, mapping keys
and array slots are in range (`SVal.fits`: a literal is in its type's
range, `Simple.lit`), by one scoped program (`Build.rootsProg`, over
`Syntax/Scoped.lean`): a word is assigned; a struct is filled member by member
through an alias bound to it; a dynamic array is pushed to its whole run of
slots, then each slot past the end is bound to an alias, popped, and filled
through the alias (the only way to write past an end), then the live
elements are filled; a fixed-size array element by element; a mapping entry
by entry, each created by a `delete` so that an entry holding the default is
there too.  Each alias is declared in a block of its own (`Build.bound`), so
a fill leaves the context it starts in and its caller's aliases, read by
position, as they were.  The builder runs by the typed run (`TRuns`): each
step is read on the erasure (`SRuns.of_agrees`), and none loops or pushes
onto `2^256 - 1` elements, so each ends in the state its erasure says.  The
proof tracks the root's value, on the erasure, as a chain of writes at one
path (`Wrote`), which is why every fill starts from the default and from a
path where writing what is there changes nothing.

The other direction is `Prog.run_tight`, an invariant the typed run keeps
on the erasure (`RunInv`, `Typing/TypedRunInv.lean`) beside
`Prog.run_canon`'s, for a
contract whose types have well-formed
defaults all the way down (`Ty.okDeep`).  It needs two facts about paths:
a word is written only into a live slot (`IdxLive`, from
`State.checkIndex`), and an alias is bound only along numeric keys
(`KeysOK`, which every alias local keeps, `LTy.Keys`), so along keys of
word type (`Ty.isKey`).  Under `Ty.okDeep` the first clause
of `SVal.tight` is vacuous, so no memory object needs tracking: a copy out
of memory has no mapping and nothing past its ends (`SVal.plain`).  Whether
that clause is also necessary for a contract with a root `defaultOkS`
refuses is not proved here: it would need the store typing to claim memory objects only
at types with well-formed defaults, threaded through every allocation.
-/

namespace Solidity

open Semantics
open SemanticsProperties (lookupBy_eq_some_mem lookupBy_defaultForFields SVal.find_nil
  SVal.save_nil SVal.find_append SVal.save_append
  State.findStorage_append State.saveStorage_append)
open Semantics.SVal.canon (canonFields canonElems canonEntries)

variable {C : Contract}

/-! ## The tight values -/

/-- What every reachable value satisfies beyond `SVal.canon`: an array whose
elements have no well-formed default has no slots at all, the slots past the
end of an array of words are cleared, a fixed-size array has no slots past
its end, and a mapping no program indexes (a reference key) has no entries. -/
def Semantics.SVal.tight : Semantics.SVal → Ty → Prop
  | Semantics.SVal.struct fields, Ty.ref (RefTy.struct s) => tightFields s fields
  | Semantics.SVal.array elems shadow _, Ty.ref (RefTy.array E) =>
      (E.defaultOkS = false → elems = [] ∧ shadow = []) ∧
      (E.isPrimitive = true → ∀ w ∈ shadow, w = defaultForTy E) ∧
      tightElems E elems ∧ tightElems E shadow
  | Semantics.SVal.array elems shadow _, Ty.ref (RefTy.fixed E _) => shadow = [] ∧ tightElems E elems
  | Semantics.SVal.map entries _, Ty.ref (RefTy.mapping K V) =>
      (K.isKey = false → entries = []) ∧ tightEntries V entries
  | _, _ => True
where
  tightFields (s : Name) : List (Name × Semantics.SVal) → Prop
    | [] => True
    | (n, v) :: rest =>
        (match lookupBy n (structDef s) with
         | some T => v.tight T
         | none => True) ∧ tightFields s rest
  tightElems (E : Ty) : List Semantics.SVal → Prop
    | [] => True
    | v :: rest => v.tight E ∧ tightElems E rest
  tightEntries (V : Ty) : List (Int × Semantics.SVal) → Prop
    | [] => True
    | (_, v) :: rest => v.tight V ∧ tightEntries V rest

open Semantics.SVal.tight (tightFields tightElems tightEntries)

/-- Every root canonical and tight at its declared type. -/
def TightStorage (C : Contract) (st : List (Name × Semantics.SVal)) : Prop :=
  ∀ r T v, lookupBy r C.vars = some T → lookupBy r st = some v → v.tight T

/-- A mapping key a literal writes: a number in its type's range, a `bool`
key `0` or `1` (`false`/`true`, as `Value.keyAt` hashes them). -/
def PrimTy.keyFits : PrimTy → Int → Bool
  | .bool, k => k == 0 || k == 1
  | .uint, k => PrimTy.uint.inRange k
  | .int, k => PrimTy.int.inRange k

/-- What the builder needs to write `v` with literals (`Simple.lit`, which is
in its type's range): every word and every mapping key in its type's range,
and every array's slots, past its end too, numbered below `2^256` (a dynamic
array's fewer than `2^256` in all: the builder pushes them all, and a push
onto `2^256 - 1` elements is out of gas, `Storage.full`). -/
def Semantics.SVal.fits : Semantics.SVal → Ty → Prop
  | Semantics.SVal.prim (.int z), Ty.prim p => p.inRange z = true
  | Semantics.SVal.struct fields, Ty.ref (RefTy.struct s) => fitsFields s fields
  | Semantics.SVal.array elems shadow _, Ty.ref (RefTy.array E) =>
      elems.length + shadow.length < 2 ^ 256 ∧ fitsElems E elems ∧ fitsElems E shadow
  | Semantics.SVal.array elems _ _, Ty.ref (RefTy.fixed E _) => elems.length ≤ 2 ^ 256 ∧ fitsElems E elems
  | Semantics.SVal.map entries _, Ty.ref (RefTy.mapping K V) => fitsEntries K V entries
  | _, _ => True
where
  fitsFields (s : Name) : List (Name × Semantics.SVal) → Prop
    | [] => True
    | (n, v) :: rest =>
        (match lookupBy n (structDef s) with
         | some T => v.fits T
         | none => True) ∧ fitsFields s rest
  fitsElems (E : Ty) : List Semantics.SVal → Prop
    | [] => True
    | v :: rest => v.fits E ∧ fitsElems E rest
  fitsEntries (K V : Ty) : List (Int × Semantics.SVal) → Prop
    | [] => True
    | (key, v) :: rest =>
        (match K with
         | .prim k => k.keyFits key = true
         | .ref _ => True) ∧ v.fits V ∧ fitsEntries K V rest

open Semantics.SVal.fits (fitsFields fitsElems fitsEntries)

/-- Every root's words, keys and slots in range. -/
def FitsStorage (C : Contract) (st : List (Name × Semantics.SVal)) : Prop :=
  ∀ r T v, lookupBy r C.vars = some T → lookupBy r st = some v → v.fits T

namespace Build

/-! ## The builder -/

/-- The storage alias the builder binds at depth `d`. -/
def slot (d : Nat) : Var := .fresh "slot" d

theorem inRange_of_lt {j : Nat} (h : j < 2 ^ 256) : PrimTy.uint.inRange (j : Int) = true := by
  simp only [PrimTy.inRange, decide_eq_true_eq]
  exact ⟨Int.natCast_nonneg j, Int.ofNat_lt.mpr h⟩

/-! ## Storage algebra

Writes at a root, as lists: `putSt` is `State.saveStorage`'s storage. -/

open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne setBy_setBy_self)

/-- The storage `State.saveStorage` leaves. -/
def putSt (st : List (Name × Semantics.SVal)) (r : Name) (segs : List Seg) (X : Semantics.SVal) :
    Res (List (Name × Semantics.SVal)) :=
  match lookupBy r st with
  | some V => do let u ← V.save segs X; pure (setBy r u st)
  | none => .error .undef

/-- `st'` is `st` with `X` saved at `r.segs`. -/
def Wrote (st st' : List (Name × Semantics.SVal)) (r : Name) (segs : List Seg) (X : Semantics.SVal) : Prop :=
  putSt st r segs X = .ok st'

/-- `putSt` at a state's storage is `State.storeRes`. -/
theorem putSt_eq (σ : Semantics.State) (r : Name) (segs : List Seg) (X : Semantics.SVal) :
    putSt σ.storage r segs X = σ.storeRes r segs X := rfl

theorem saveStorage_ok {σ : Semantics.State} {r : Name} {segs : List Seg} {X : Semantics.SVal}
    {st : List (Name × Semantics.SVal)} (h : putSt σ.storage r segs X = .ok st) :
    σ.saveStorage r segs X = .ok { σ with storage := st } := by
  rw [SemanticsProperties.State.saveStorage_eq, ← putSt_eq, h]; rfl

theorem putSt_of_saveStorage {σ τ : Semantics.State} {r : Name} {segs : List Seg} {X : Semantics.SVal}
    (h : σ.saveStorage r segs X = .ok τ) : putSt σ.storage r segs X = .ok τ.storage := by
  rw [SemanticsProperties.State.saveStorage_eq, ← putSt_eq] at h
  obtain ⟨st, hst, h⟩ := bind_ok_inv h
  cases h; exact hst

theorem setBy_of_lookupBy [DecidableEq κ] {k : κ} {v : α} :
    ∀ {l : List (κ × α)}, lookupBy k l = some v → setBy k v l = l
  | [], h => nomatch h
  | (k', v') :: rest, h => by
    by_cases hk : k = k'
    · subst hk; simp only [lookupBy, ↓reduceIte, Option.some.injEq] at h; subst h; simp only [setBy,
                    ↓reduceIte]
    · simp only [lookupBy, if_neg hk] at h
      simp only [setBy, hk, ↓reduceIte, setBy_of_lookupBy h]

/-- Saving twice at one path keeps the second: `alice.age = 1; alice.age = 2;`. -/
theorem save_save : ∀ {segs : List Seg} {v v₁ a : Semantics.SVal} (b : Semantics.SVal),
    v.save segs a = .ok v₁ → v₁.save segs b = v.save segs b
  | [], v, v₁, a, b, h => by
    rw [SVal.save_nil] at h; cases h; rw [SVal.save_nil, SVal.save_nil]
  | .field n :: rest, .struct fields, v₁, a, b, h => by
    simp only [Semantics.SVal.save] at h ⊢
    split at h
    · rename_i old hold
      obtain ⟨u, hu, h⟩ := bind_ok_inv h
      cases h
      simp only [Semantics.SVal.save, lookupBy_setBy_self, save_save b hu]
      cases old.save rest b <;> simp only [setBy_setBy_self]
    · exact nomatch h
  | .at i :: rest, .array elems sh fx, v₁, a, b, h => by
    simp only [Semantics.SVal.save] at h
    split at h
    · rename_i hb
      obtain ⟨u, hu, h⟩ := bind_ok_inv h
      cases h
      have hlen : ((elems ++ sh).set i.toNat u).length = (elems ++ sh).length := List.length_set ..
      have hb' : 0 ≤ i ∧ i.toNat < (((elems ++ sh).set i.toNat u).take elems.length ++
          ((elems ++ sh).set i.toNat u).drop elems.length).length := by
        rw [List.take_append_drop, hlen]; exact hb
      simp only [Semantics.SVal.save, dif_pos hb', dif_pos hb]
      have hget : (((elems ++ sh).set i.toNat u).take elems.length ++
          ((elems ++ sh).set i.toNat u).drop elems.length).get ⟨i.toNat, hb'.2⟩ = u := by
        simp only [List.get_eq_getElem, List.take_append_drop, List.getElem_set_self]
      rw [hget, save_save b hu]
      have htl : (((elems ++ sh).set i.toNat u).take elems.length).length = elems.length := by
        simp only [List.length_take, List.length_set, List.length_append, Nat.le_add_right,
            Nat.min_eq_left]
      cases ((elems ++ sh).get ⟨i.toNat, hb.2⟩).save rest b <;>
        simp only [htl, List.take_append_drop, List.set_set]
    · exact nomatch h
  | .at i :: rest, .map entries dflt, v₁, a, b, h => by
    simp only [Semantics.SVal.save] at h
    split at h
    · rename_i old hold
      obtain ⟨u, hu, h⟩ := bind_ok_inv h
      cases h
      simp only [Semantics.SVal.save, lookupBy_setBy_self, hold, save_save b hu]
      cases old.save rest b <;> simp only [setBy_setBy_self]
    · rename_i hold
      obtain ⟨u, hu, h⟩ := bind_ok_inv h
      cases h
      simp only [Semantics.SVal.save, lookupBy_setBy_self, hold, save_save b hu]
      cases dflt.save rest b <;> simp only [setBy_setBy_self]
  | .field _ :: _, .prim _, _, _, _, h | .at _ :: _, .prim _, _, _, _, h
  | .at _ :: _, .struct _, _, _, _, h | .field _ :: _, .array .., _, _, _, h
  | .field _ :: _, .map .., _, _, _, h => by simp only [Semantics.SVal.save, reduceCtorEq] at h

/-! ### Chains of writes at one path -/

theorem Wrote.trans {st₀ st₁ st₂ : List (Name × Semantics.SVal)} {r : Name} {segs : List Seg}
    {X Y : Semantics.SVal} (h₁ : Wrote st₀ st₁ r segs X) (h₂ : Wrote st₁ st₂ r segs Y) :
    Wrote st₀ st₂ r segs Y := by
  unfold Wrote putSt at *
  split at h₁
  · rename_i V hV
    obtain ⟨u, hu, h₁⟩ := bind_ok_inv h₁
    cases h₁
    rw [lookupBy_setBy_self] at h₂
    simp only [save_save Y hu] at h₂
    obtain ⟨u', hu', h₂⟩ := bind_ok_inv h₂
    cases h₂
    simp only [hu', bind_pure_comp, setBy_setBy_self]; rfl
  · exact nomatch h₁

/-- After a write, saving the same value again changes nothing. -/
theorem Wrote.noop {st₀ st : List (Name × Semantics.SVal)} {r : Name} {segs : List Seg} {X : Semantics.SVal}
    (h : Wrote st₀ st r segs X) : Wrote st st r segs X := by
  unfold Wrote putSt at *
  split at h
  · rename_i V hV
    obtain ⟨u, hu, h⟩ := bind_ok_inv h
    cases h
    rw [lookupBy_setBy_self]
    simp only [save_save X hu, hu]
    simp only [setBy_setBy_self, bind_pure_comp]; rfl
  · exact nomatch h

/-- After a write, the path reads what was written. -/
theorem Wrote.find {st₀ st : List (Name × Semantics.SVal)} {r : Name} {segs : List Seg} {X : Semantics.SVal}
    (h : Wrote st₀ st r segs X) :
    ∃ V, lookupBy r st = some V ∧ V.find segs = .ok X := by
  unfold Wrote putSt at h
  split at h
  · obtain ⟨u, hu, h⟩ := bind_ok_inv h
    cases h
    exact ⟨u, lookupBy_setBy_self _ _ _, SemanticsProperties.SVal.find_save_same hu⟩
  · exact nomatch h

theorem Wrote.findStorage {σ : Semantics.State} {st₀ : List (Name × Semantics.SVal)} {r : Name} {segs : List Seg}
    {X : Semantics.SVal} (h : Wrote st₀ σ.storage r segs X) : σ.findStorage r segs = .ok X := by
  obtain ⟨V, hV, hf⟩ := h.find
  simp only [State.findStorage, hV, hf]

/-- A write below `segs` is a write at `segs` of what is there, updated. -/
theorem Wrote.up {st st' : List (Name × Semantics.SVal)} {r : Name} {segs rest : List Seg}
    {N N' w : Semantics.SVal} (hN : ∃ V, lookupBy r st = some V ∧ V.find segs = .ok N)
    (hs : N.save rest w = .ok N') (h : Wrote st st' r (segs ++ rest) w) :
    Wrote st st' r segs N' := by
  obtain ⟨V, hV, hf⟩ := hN
  unfold Wrote putSt at *
  simp only [hV] at h ⊢
  rw [SVal.save_append V segs rest w N hf, hs] at h
  exact h

/-! ### One step down -/

theorem save_field {fs : List (Name × Semantics.SVal)} {n : Name} {c : Semantics.SVal} (w : Semantics.SVal)
    (h : lookupBy n fs = some c) :
    (Semantics.SVal.struct fs).save [.field n] w = .ok (.struct (setBy n w fs)) := by
  simp only [Semantics.SVal.save, h, SVal.save_nil]; rfl

theorem save_at_map (es : List (Int × Semantics.SVal)) (dflt : Semantics.SVal) (k : Int) (w : Semantics.SVal) :
    (Semantics.SVal.map es dflt).save [.at k] w = .ok (.map (setBy k w es) dflt) := by
  simp only [Semantics.SVal.save]
  split <;> rfl

/-- The first slot past the end, written: a popped slot filled through its alias. -/
theorem save_at_shadow (es sh : List Semantics.SVal) (x w : Semantics.SVal) (fx : Bool) :
    (Semantics.SVal.array es (x :: sh) fx).save [.at (es.length : Int)] w = .ok (.array es (w :: sh) fx) := by
  have hb : 0 ≤ (es.length : Int) ∧ (es.length : Int).toNat < (es ++ x :: sh).length := by
    simp only [Int.ofNat_zero_le, Int.toNat_natCast, List.length_append, List.length_cons,
        Nat.lt_add_right_iff_pos, Nat.zero_lt_succ, and_self]
  simp only [Semantics.SVal.save]
  rw [dif_pos hb]
  simp only [bind, Except.bind, Int.toNat_natCast, Nat.le_refl, List.set_append_right, Nat.sub_self,
      List.set_cons_zero, List.take_left', List.drop_left']

/-- A live element written: `values[j] = w;`. -/
theorem save_at_live (es rest sh : List Semantics.SVal) (x w : Semantics.SVal) (fx : Bool) :
    (Semantics.SVal.array (es ++ x :: rest) sh fx).save [.at (es.length : Int)] w =
      .ok (.array (es ++ w :: rest) sh fx) := by
  have hb : 0 ≤ (es.length : Int) ∧ (es.length : Int).toNat < (es ++ x :: rest ++ sh).length := by
    simp only [Int.ofNat_zero_le, Int.toNat_natCast, List.append_assoc, List.cons_append,
        List.length_append, List.length_cons, Nat.lt_add_right_iff_pos, Nat.zero_lt_succ, and_self]
  simp only [Semantics.SVal.save]
  rw [dif_pos hb]
  have hset : (es ++ x :: rest ++ sh).set (es.length : Int).toNat w = (es ++ w :: rest) ++ sh := by
    simp only [List.append_assoc, List.cons_append, Int.toNat_natCast, Nat.le_refl,
        List.set_append_right, Nat.sub_self, List.set_cons_zero]
  have hl : (es ++ x :: rest).length = (es ++ w :: rest).length := by simp only [List.length_append,
                                                                          List.length_cons]
  simp only [bind, Except.bind, hset, hl, List.take_left', List.drop_left']

/-- Saving what a path already holds, one step below a no-op write, is a no-op. -/
theorem Wrote.down {st : List (Name × Semantics.SVal)} {r : Name} {segs rest : List Seg} {N c : Semantics.SVal}
    (h : Wrote st st r segs N) (hs : N.save rest c = .ok N) : Wrote st st r (segs ++ rest) c := by
  obtain ⟨V, hV, hf⟩ := h.find
  unfold Wrote putSt at *
  simp only [hV] at h ⊢
  rw [SVal.save_append V segs rest c N hf, hs]
  exact h

/-! ## Defaults and association lists -/

/-- `delete` of a fresh default changes nothing: a popped fresh slot and a
deleted absent mapping entry are the type's default. -/
theorem defaultOf_default (T : Ty) : (defaultForTy T).defaultOf = defaultForTy T := by
  induction T using defaultForTy.induct
    (motive2 := fun l => SVal.defaultOf.defaultOfFields (defaultForFields l) = defaultForFields l)
    with
  | case1 => simp only [defaultForTy, Semantics.SVal.defaultOf]
  | case2 => simp only [defaultForTy, Semantics.SVal.defaultOf]
  | case3 => simp only [defaultForTy, Semantics.SVal.defaultOf]
  | case4 name ih => rw [defaultForTy]; simp only [Semantics.SVal.defaultOf, ih]
  | case5 elem => simp only [defaultForTy, Semantics.SVal.defaultOf, SVal.defaultOf.defaultOfElems,
      List.append_nil]
  | case6 elem n ih =>
    rw [defaultForTy]; simp only [Semantics.SVal.defaultOf]
    congr 1
    induction n with
    | zero => rfl
    | succ k ihk => simp only [List.replicate_succ, SVal.defaultOf.defaultOfElems, ih, ihk]
  | case7 key value ih => rw [defaultForTy]; rfl
  | case8 => simp only [defaultForFields, SVal.defaultOf.defaultOfFields]
  | case9 n t rest iht ihrest =>
    simp only [defaultForFields, SVal.defaultOf.defaultOfFields, iht, ihrest]

/-- The structs `defaultOkS` admits: no member name twice, and every member
of a type `defaultOkS` admits. -/
theorem struct_ok {s : Name} (h : s ∈ defaultOkStructs) :
    nodupKeysB (structDef s) = true ∧ ∀ nt ∈ structDef s, nt.2.defaultOkS = true := by
  simp only [defaultOkStructs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨by decide, ?_⟩ <;> simp only [structDef, List.mem_cons, List.not_mem_nil, or_false,
                                   forall_eq, Ty.defaultOkS, String.reduceEq, imp_self,
                                   forall_eq_or_imp, defaultOkStructs, or_self, decide_true,
                                   and_self, or_true]

theorem lookupBy_append_left_none [DecidableEq κ] {k : κ} {l₂ : List (κ × α)} :
    ∀ {l₁ : List (κ × α)}, lookupBy k l₁ = none → lookupBy k (l₁ ++ l₂) = lookupBy k l₂
  | [], _ => rfl
  | (k', v') :: rest, h => by
    by_cases hk : k = k'
    · simp only [lookupBy, hk, ↓reduceIte, reduceCtorEq] at h
    · simp only [lookupBy, if_neg hk] at h
      simp only [List.cons_append, lookupBy, hk, ↓reduceIte, lookupBy_append_left_none h]

theorem setBy_append_left_none [DecidableEq κ] {k : κ} {v : α} {l₂ : List (κ × α)} :
    ∀ {l₁ : List (κ × α)}, lookupBy k l₁ = none → setBy k v (l₁ ++ l₂) = l₁ ++ setBy k v l₂
  | [], _ => rfl
  | (k', v') :: rest, h => by
    by_cases hk : k = k'
    · simp only [lookupBy, hk, ↓reduceIte, reduceCtorEq] at h
    · simp only [lookupBy, if_neg hk] at h
      simp only [List.cons_append, setBy, hk, ↓reduceIte, setBy_append_left_none h]

/-- Writing a member that is there, in the middle: `alice.age = 3;`. -/
theorem setBy_mid [DecidableEq κ] {k : κ} {v x : α} {l₁ l₂ : List (κ × α)}
    (h : lookupBy k l₁ = none) : setBy k v (l₁ ++ (k, x) :: l₂) = l₁ ++ (k, v) :: l₂ := by
  rw [setBy_append_left_none h]; simp only [setBy, ↓reduceIte]

theorem lookupBy_mid [DecidableEq κ] {k : κ} {x : α} {l₁ l₂ : List (κ × α)}
    (h : lookupBy k l₁ = none) : lookupBy k (l₁ ++ (k, x) :: l₂) = some x := by
  rw [lookupBy_append_left_none h]; simp only [lookupBy, ↓reduceIte]

theorem nodupKeysB_mid [DecidableEq κ] {k : κ} {x : α} {l₂ : List (κ × α)} :
    ∀ {l₁ : List (κ × α)}, nodupKeysB (l₁ ++ (k, x) :: l₂) = true → lookupBy k l₁ = none
  | [], _ => rfl
  | (k', v') :: rest, h => by
    simp only [List.cons_append, nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    by_cases hk : k = k'
    · subst hk
      rw [lookupBy_mid (nodupKeysB_mid h.2)] at h
      exact nomatch h.1
    · simp only [lookupBy, hk, ↓reduceIte, nodupKeysB_mid h.2]

/-- A write succeeds where another write along the same path did. -/
theorem save_ok_any : ∀ {segs : List Seg} {v v₁ a : Semantics.SVal} (b : Semantics.SVal),
    v.save segs a = .ok v₁ → ∃ v₂, v.save segs b = .ok v₂
  | [], v, _, _, b, _ => ⟨b, SVal.save_nil v b⟩
  | .field n :: rest, .struct fields, v₁, a, b, h => by
    simp only [Semantics.SVal.save] at h ⊢
    split at h
    · rename_i old hold
      obtain ⟨u, hu, -⟩ := bind_ok_inv h
      obtain ⟨u', hu'⟩ := save_ok_any b hu
      simp only [hu']; exact ⟨_, rfl⟩
    · exact nomatch h
  | .at i :: rest, .array elems sh fx, v₁, a, b, h => by
    simp only [Semantics.SVal.save] at h ⊢
    split at h
    · rename_i hb
      obtain ⟨u, hu, -⟩ := bind_ok_inv h
      obtain ⟨u', hu'⟩ := save_ok_any b hu
      rw [dif_pos hb, hu']; exact ⟨_, rfl⟩
    · exact nomatch h
  | .at i :: rest, .map entries dflt, v₁, a, b, h => by
    simp only [Semantics.SVal.save] at h ⊢
    split at h
    · rename_i old hold
      obtain ⟨u, hu, -⟩ := bind_ok_inv h
      obtain ⟨u', hu'⟩ := save_ok_any b hu
      simp only [hu']; exact ⟨_, rfl⟩
    · rename_i hold
      obtain ⟨u, hu, -⟩ := bind_ok_inv h
      obtain ⟨u', hu'⟩ := save_ok_any b hu
      simp only [hu']; exact ⟨_, rfl⟩
  | .field _ :: _, .prim _, _, _, _, h | .at _ :: _, .prim _, _, _, _, h
  | .at _ :: _, .struct _, _, _, _, h | .field _ :: _, .array .., _, _, _, h
  | .field _ :: _, .map .., _, _, _, h => by simp only [Semantics.SVal.save, reduceCtorEq] at h

theorem Wrote.any {st₀ st : List (Name × Semantics.SVal)} {r : Name} {segs : List Seg} {X : Semantics.SVal}
    (h : Wrote st₀ st r segs X) (Y : Semantics.SVal) : ∃ st', Wrote st₀ st' r segs Y := by
  unfold Wrote putSt at *
  split at h
  · obtain ⟨u, hu, -⟩ := bind_ok_inv h
    obtain ⟨u', hu'⟩ := save_ok_any Y hu
    rw [hu']; exact ⟨_, rfl⟩
  · exact nomatch h

/-- A statement that only saves at `r.segs`, as a chain step. -/
theorem Wrote.save {σ τ : Semantics.State} {st₀ : List (Name × Semantics.SVal)} {r : Name} {segs : List Seg}
    {X Y : Semantics.SVal} (hc : Wrote st₀ σ.storage r segs X) (h : σ.saveStorage r segs Y = .ok τ) :
    Wrote st₀ τ.storage r segs Y :=
  hc.trans (putSt_of_saveStorage h)

theorem saveStorage_env {σ τ : Semantics.State} {r : Name} {segs : List Seg} {Y : Semantics.SVal}
    (h : σ.saveStorage r segs Y = .ok τ) : τ.env = σ.env :=
  (SemanticsProperties.State.saveStorage_frame h).2.2.1

theorem Wrote.saveStorage {σ : Semantics.State} {st₀ : List (Name × Semantics.SVal)} {r : Name} {segs : List Seg}
    {X : Semantics.SVal} (hc : Wrote st₀ σ.storage r segs X) (Y : Semantics.SVal) :
    ∃ τ, σ.saveStorage r segs Y = .ok τ ∧ Wrote st₀ τ.storage r segs Y ∧ τ.env = σ.env := by
  obtain ⟨st', h'⟩ := hc.noop.any Y
  have h := saveStorage_ok h'
  exact ⟨_, h, hc.save h, saveStorage_env h⟩

theorem sizeOf_lt_fields {fields : List (Name × Semantics.SVal)} {nw : Name × Semantics.SVal} (h : nw ∈ fields) :
    sizeOf nw.2 < sizeOf (Semantics.SVal.struct fields) := by
  have := List.sizeOf_lt_of_mem h
  obtain ⟨n, w⟩ := nw
  simp only [Prod.mk.sizeOf_spec, Semantics.SVal.struct.sizeOf_spec, gt_iff_lt] at this ⊢; omega

theorem sizeOf_lt_elems {elems shadow : List Semantics.SVal} {fx : Bool} {w : Semantics.SVal} (h : w ∈ elems) :
    sizeOf w < sizeOf (Semantics.SVal.array elems shadow fx) := by
  have := List.sizeOf_lt_of_mem h
  simp only [Semantics.SVal.array.sizeOf_spec, Bool.sizeOf_eq_one, gt_iff_lt]; omega

theorem sizeOf_lt_shadow {elems shadow : List Semantics.SVal} {fx : Bool} {w : Semantics.SVal} (h : w ∈ shadow) :
    sizeOf w < sizeOf (Semantics.SVal.array elems shadow fx) := by
  have := List.sizeOf_lt_of_mem h
  simp only [Semantics.SVal.array.sizeOf_spec, Bool.sizeOf_eq_one, gt_iff_lt]; omega

theorem sizeOf_lt_entries {entries : List (Int × Semantics.SVal)} {dflt : Semantics.SVal} {kw : Int × Semantics.SVal}
    (h : kw ∈ entries) : sizeOf kw.2 < sizeOf (Semantics.SVal.map entries dflt) := by
  have := List.sizeOf_lt_of_mem h
  obtain ⟨k, w⟩ := kw
  simp only [Prod.mk.sizeOf_spec, Semantics.SVal.map.sizeOf_spec, gt_iff_lt] at this ⊢; omega

end Build

end Solidity

/-! ## The builder, over the scoped syntax

`fill d T q v` reads in any context `Γ` and leaves it: an alias a fill binds
is declared in a block of its own, so it ends with the fill, and the
aliases the fill's caller is filling through are read by position. -/

namespace Solidity

open Semantics hiding State
open SemanticsProperties (lookupBy_eq_some_mem lookupBy_defaultForFields SVal.find_nil
  SVal.save_nil SVal.find_append SVal.save_append lookupBy_setBy_self lookupBy_setBy_ne
  setBy_setBy_self)
open Semantics.SVal.canon (canonFields canonElems canonEntries)
open Semantics.SVal.tight (tightFields tightElems tightEntries)
open Semantics.SVal.fits (fitsFields fitsElems fitsEntries)

variable {C : Contract}

/-- A sequence followed by another. -/
def Prog.append {Γ Δ Ε : Ctx} : Prog C Γ Δ → Prog C Δ Ε → Prog C Γ Ε
  | .nil, Q => Q
  | .cons s P, Q => .cons s (P.append Q)

/-- One statement `n` times. -/
def Prog.rep {Γ : Ctx} (n : Nat) (s : Stmt C Γ Γ) : Prog C Γ Γ :=
  match n with
  | 0 => .nil
  | n + 1 => .cons s (Prog.rep n s)

namespace Build

open Solidity.Build

/-- The literal `n` at the numeric type `p`, or `0` where `n` is out of its
range (a value the builder is given has none, `SVal.fits`). -/
def numLit {Γ : Ctx} (p : PrimTy) (hp : p.isNumeric = true) (n : Int) : Simple C Γ p :=
  if h : p.inRange n = true then .lit n h
  else .lit 0 (by cases p <;> first | rfl | exact absurd hp (by decide))

theorem numLit_eq {Γ : Ctx} {p : PrimTy} {hp : p.isNumeric = true} {n : Int}
    (h : p.inRange n = true) : numLit (C := C) (Γ := Γ) p hp n = .lit n h := dif_pos h

/-- The key `n` at the key type `p`: a numeric literal, or `true` for `1` and
`false` otherwise. -/
def keyLit {Γ : Ctx} : (p : PrimTy) → Int → Simple C Γ p
  | .bool, n => .bool (n == 1)
  | .uint, n => numLit .uint rfl n
  | .int, n => numLit .int rfl n

/-- A word written at `l`: `alice.age = 3;`. -/
def primProg {Γ : Ctx} : (p : PrimTy) → Loc C Γ (.prim p) → Semantics.SVal → Prog C Γ Γ
  | .bool, l, .bool b => .cons (.assign l (.val (.simple (.bool b)))) .nil
  | .uint, l, .int z => .cons (.assign l (.val (.simple (numLit .uint rfl z)))) .nil
  | .int, l, .int z => .cons (.assign l (.val (.simple (numLit .int rfl z)))) .nil
  | _, _, _ => .nil

/-- `{ R storage slot d = q; body }`: the alias bound for the body, which
fills through it, and ended with the block. -/
def bound {Γ : Ctx} (d : Nat) (R : RefTy) (q : SPath C Γ (.ref R))
    (body : Prog C (.alias R :: Γ) (.alias R :: Γ)) : Prog C Γ Γ :=
  .cons (.block (.cons (.declStorage R (slot d) (some (.path q))) body)) .nil

mutual

/-- A program that turns the default at `q : T` into `v`.  A word is
assigned.  Anything else binds an alias to `q` in a block and fills through
it: a struct member by member; a dynamic array by pushing every slot it has,
popping those past its end one at a time (each bound to a deeper alias
before its `pop`, and filled through it after), then filling the live
elements; a fixed-size array element by element; a mapping entry by entry,
each created by a `delete` first. -/
def fill {Γ : Ctx} (d : Nat) : (T : Ty) → SPath C Γ T → Semantics.SVal → Prog C Γ Γ
  | .prim p, .loc l, v => primProg p l v
  | .ref (.struct s), q, .struct fields => bound d (.struct s) q (fillFields d s .here fields)
  | .ref (.array E), q, .array elems shadow _ =>
      bound d (.array E) q
        (if hE : E.defaultOkS = true then
          (Prog.rep (elems.length + shadow.length)
              (.push (.alias .here : SPath C _ (.array E)) none (by simp only [Option.isSome_none,
                  hE, Bool.or_true]))).append
            ((fillShadow d E .here elems.length shadow).append
              (fillElems d (ArrTy.dyn (E := E)) .here 0 elems))
        else .nil)
  | .ref (.fixed E n), q, .array elems _ _ =>
      bound d (.fixed E n) q (fillElems d (ArrTy.fixed (E := E) (n := n)) .here 0 elems)
  | .ref (.mapping (.prim k) V), q, .map entries _ =>
      bound d (.mapping (.prim k) V) q (fillEntries d k V .here entries)
  | _, _, _ => .nil

/-- The members of a struct bound to `a`, one after another. -/
def fillFields {Γ : Ctx} (d : Nat) (s : Name) (a : Idx Γ (.alias (.struct s))) :
    List (Name × Semantics.SVal) → Prog C Γ Γ
  | [] => .nil
  | (n, w) :: rest =>
      (match h : lookupBy n (structDef s) with
       | some T => fill (d + 1) T (.loc (.field (.alias a) n h)) w
       | none => .nil).append (fillFields d s a rest)

/-- The slots past the end of the array bound to `a`, from the last: slot
`i` bound, popped, then filled through its alias.  A word slot is only
popped (it is cleared). -/
def fillShadow {Γ : Ctx} (d : Nat) (E : Ty) (a : Idx Γ (.alias (.array E))) (i : Nat) :
    List Semantics.SVal → Prog C Γ Γ
  | [] => .nil
  | w :: rest =>
      (fillShadow d E a (i + 1) rest).append
        (match E, a with
         | .prim p, a => .cons (.pop (E := .prim p) (.alias a)) .nil
         | .ref R, a =>
             bound (d + 1) R (.loc (.index (.arr .dyn) (.alias a)
                 (.simple (numLit .uint rfl (i : Int)))))
               (.cons (.pop (E := .ref R) (.alias a.there))
                 (fill (d + 1) (.ref R) (.alias .here) w)))

/-- The live elements of the array bound to `a`, from index `j`. -/
def fillElems {Γ : Ctx} {R : RefTy} {E : Ty} (d : Nat) (ak : ArrTy R E) (a : Idx Γ (.alias R))
    (j : Nat) : List Semantics.SVal → Prog C Γ Γ
  | [] => .nil
  | w :: rest =>
      (fill (d + 1) E (.loc (.index (.arr ak) (.alias a) (.simple (numLit .uint rfl (j : Int)))))
          w).append (fillElems d ak a (j + 1) rest)

/-- The entries of the mapping bound to `a`: each created by `delete`, then
filled. -/
def fillEntries {Γ : Ctx} (d : Nat) (k : PrimTy) (V : Ty)
    (a : Idx Γ (.alias (.mapping (.prim k) V))) : List (Int × Semantics.SVal) → Prog C Γ Γ
  | [] => .nil
  | (key, w) :: rest =>
      .cons (.delete (.index .map (.alias a) (.simple (keyLit k key)) : Loc C Γ V))
        ((fill (d + 1) V (.loc (.index .map (.alias a) (.simple (keyLit k key)))) w).append
          (fillEntries d k V a rest))

end

/-- The whole program: every root filled. -/
def rootsProg (C : Contract) : List (Name × Semantics.SVal) → Prog C [] []
  | [] => .nil
  | (r, v) :: rest =>
      (match h : C.rootType r with
       | some T => fill 0 T (.loc (.root r h)) v
       | none => .nil).append (rootsProg C rest)

/-! ### One statement at a time -/

section Steps

variable {Γ : Ctx}

/-- The alias at `a` is bound to `r.segs`. -/
def Bound (σ : EState C Γ) {R : RefTy} (a : Idx Γ (.alias R)) (r : Name) (segs : List Seg) :
    Prop :=
  (Env.get a σ.env : Option (Name × List Seg)) = some (r, segs)

theorem aliasPath_bound {σ : EState C Γ} {R : RefTy} {a : Idx Γ (.alias R)} {r : Name}
    {segs : List Seg} (h : Bound σ a r segs) : aliasPath σ a = .ok (r, segs) := by
  unfold aliasPath Bound at *
  rw [h]; rfl

theorem resolve_alias {σ : EState C Γ} {R : RefTy} {a : Idx Γ (.alias R)} {r : Name}
    {segs : List Seg} (h : Bound σ a r segs) : (SPath.alias (C := C) a).resolve σ = .ok (r, segs) :=
  aliasPath_bound h

theorem resolve_field {σ : EState C Γ} {s n : Name} {T : Ty} {a : Idx Γ (.alias (.struct s))}
    {r : Name} {segs : List Seg} (hf : C.fieldType s n = some T) (h : Bound σ a r segs) :
    (SPath.loc (Loc.field (.alias a) n hf)).resolve σ = .ok (r, segs ++ [.field n]) := by
  simp only [SPath.resolve, Loc.resolve, aliasPath_bound h, bind, Except.bind]
  rfl

theorem resolve_index_arr {σ : EState C Γ} {R : RefTy} {E : Ty} (ak : ArrTy R E)
    {a : Idx Γ (.alias R)} {j : Nat} {r : Name} {segs : List Seg} {es sh : List Semantics.SVal} {fx : Bool}
    (h : Bound σ a r segs) (hf : σ.glob.findStorage r segs = .ok (.array es sh fx))
    (hj : j < es.length) (hb : j < 2 ^ 256) :
    (SPath.loc (C := C)
        (Loc.index (.arr ak) (.alias a) (.simple (numLit .uint rfl (j : Int))))).resolve σ =
      .ok (r, segs ++ [.at (j : Int)]) := by
  rw [numLit_eq (inRange_of_lt hb)]
  simp only [SPath.resolve, Loc.resolve, bind, Except.bind, aliasPath_bound h, Val.eval, Simple.eval,
      pure, Except.pure, Value.keyAt, Value.asInt, Semantics.State.checkIndex, hf, Int.ofNat_zero_le,
      Int.toNat_natCast, hj, and_self, ↓reduceIte]

theorem keyLit_keyAt (σ : EState C Γ) {k : PrimTy} {key : Int} (hr : k.keyFits key = true) :
    ((Val.simple (keyLit (C := C) (Γ := Γ) k key)).eval σ >>= Value.keyAt k) = .ok key := by
  cases k with
  | bool =>
    simp only [PrimTy.keyFits, Bool.or_eq_true, beq_iff_eq] at hr
    rcases hr with rfl | rfl <;> rfl
  | uint => rw [keyLit, numLit_eq (p := .uint) hr]; rfl
  | int => rw [keyLit, numLit_eq (p := .int) hr]; rfl

theorem resolve_index_map {σ : EState C Γ} {k : PrimTy} {V : Ty} {key : Int}
    (hr : k.keyFits key = true)
    {a : Idx Γ (.alias (.mapping (.prim k) V))}
    {r : Name} {segs : List Seg} {es : List (Int × Semantics.SVal)} {dflt : Semantics.SVal}
    (h : Bound σ a r segs) (hf : σ.glob.findStorage r segs = .ok (.map es dflt)) :
    (SPath.loc (C := C)
        (Loc.index (V := V) .map (.alias a) (.simple (keyLit k key)))).resolve σ =
      .ok (r, segs ++ [.at key]) := by
  have hk := keyLit_keyAt (C := C) σ hr
  simp only [bind, Except.bind] at hk
  simp only [SPath.resolve, Loc.resolve, aliasPath_bound h, bind, Except.bind]
  split at hk
  · exact nomatch hk
  · rename_i w hw
    rw [hk]
    simp only [Semantics.State.checkIndex, bind, Except.bind, hf, pure, Except.pure]

/-! #### Typed runs

The builder's programs run by the typed run (`Prog.run`).  A run from `σ`
to `τ` is `TRuns σ P τ`; what the proofs track is the states' erasure,
where the builder's storage algebra (`Wrote`) lives.  Each statement's step
is read on the erasure (`SRuns.of_agrees`, `Semantics/StepErase.lean`):
it ends (no step of the builder loops, and no push lands on `2^256 - 1`
elements, `TRes.Ends`), so it ends in the state its erasure says. -/

/-- `P` runs, by the typed run, from `σ` to `τ`. -/
def TRuns {Γ' : Ctx} (σ : State C Γ) (P : Prog C Γ Γ') (τ : State C Γ') : Prop :=
  ∃ o : Out C σ.H Γ', P.run σ = .ok o ∧ o.st = τ

/-- `s` runs, by the typed run, from `σ` to `τ`. -/
def SRuns {Γ' : Ctx} (σ : State C Γ) (s : Stmt C Γ Γ') (τ : State C Γ') : Prop :=
  ∃ o : Out C σ.H Γ', s.run σ = .ok o ∧ o.st = τ

theorem TRuns.nil (σ : State C Γ) : TRuns σ (.nil : Prog C Γ Γ) σ := ⟨_, rfl, rfl⟩

theorem TRuns.cons {Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂}
    {τ : State C Γ₁} {υ : State C Γ₂} (hs : SRuns σ s τ) (hP : TRuns τ P υ) :
    TRuns σ (.cons s P) υ := by
  obtain ⟨o, ho, rfl⟩ := hs
  obtain ⟨o', ho', rfl⟩ := hP
  exact ⟨_, by rw [Prog.run_cons_ok ho, ho']; rfl, rfl⟩

theorem TRuns.cons_inv {Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂}
    {υ : State C Γ₂} (h : TRuns σ (.cons s P) υ) : ∃ τ, SRuns σ s τ ∧ TRuns τ P υ := by
  obtain ⟨o, ho, rfl⟩ := h
  cases hs : s.run σ with
  | error e =>
    have he : Prog.run σ (.cons s P) = .error e := by
      show TRun.seq s.runR P.runR σ = _
      simp only [TRun.seq, Stmt.run] at hs ⊢
      rw [hs]
    rw [he] at ho
    cases ho
  | ok o₁ =>
    rw [Prog.run_cons_ok hs] at ho
    cases hp : Prog.run o₁.st P with
    | error e => rw [hp] at ho; cases ho
    | ok o₂ =>
      rw [hp] at ho
      cases ho
      exact ⟨o₁.st, ⟨o₁, hs, rfl⟩, ⟨o₂, hp, rfl⟩⟩

theorem TRuns.append : {Γ Δ Ε : Ctx} → {σ : State C Γ} → {P : Prog C Γ Δ} →
    {Q : Prog C Δ Ε} → {τ : State C Δ} → {υ : State C Ε} → TRuns σ P τ → TRuns τ Q υ →
    TRuns σ (P.append Q) υ
  | _, _, _, _, .nil, _, _, _, hP, hQ => by
    obtain ⟨o, ho, rfl⟩ := hP
    cases ho
    exact hQ
  | _, _, _, _, .cons _ _, _, _, _, hP, hQ =>
    let ⟨_, hs, hP'⟩ := hP.cons_inv
    TRuns.cons hs (TRuns.append hP' hQ)

/-- A typed result that ends agrees with an untyped one that ends in `b`:
it ends in a state erasing to `b`. -/
theorem TRes.Agrees.ok_of_ends {α β : Type} {f : α → β} {t : TRes α} {u : Res β} {b : β}
    (ha : TRes.Agrees f t u) (hu : u = .ok b) (he : t.Ends) : ∃ a, t = .ok a ∧ f a = b :=
  match t, ha, he with
  | .ok a, ha, _ => ⟨a, rfl, Except.ok.inj ((show u = .ok (f a) from ha).symm.trans hu)⟩
  | .error .revert, ha, _ => nomatch (show u = .error .revert from ha).symm.trans hu
  | .error .panic, ha, _ => nomatch (show u = .error .panic from ha).symm.trans hu
  | .error .diverge, _, he => absurd rfl he.1
  | .error .exhausted, _, he => absurd rfl he.2

/-- A statement whose typed step ends, read on the erasure: where what it
erases to ends in `τ`, the typed step ends in a state erasing to `τ`. -/
theorem SRuns.of_agrees {Γ' : Ctx} {s : Stmt C Γ Γ'} {u : EState C Γ → Res (EState C Γ')}
    {σ : State C Γ} {τ : EState C Γ'} (ha : StepAgrees s.runR u) (he : (s.run σ).Ends)
    (hu : u σ.erase = .ok τ) : ∃ σ', SRuns σ s σ' ∧ σ'.erase = τ :=
  let ⟨o, ho, hoe⟩ := TRes.Agrees.ok_of_ends (ha σ) hu he
  ⟨o.st, ⟨o, ho, rfl⟩, hoe⟩

/-- A push of a default ends when the array it lands on, read on the
erasure, has fewer than `2^256 - 1` elements. -/
theorem push_none_ends {σ : State C Γ} {E : Ty} (b : SPath C Γ (.array E))
    (hp : ∀ r segs elems sh fx, b.resolve σ.erase = .ok (r, segs) →
      σ.erase.glob.findStorage r segs = .ok (.array elems sh fx) → elems.length + 1 < 2 ^ 256) :
    (TRun.push b none σ).Ends := by
  unfold TRun.push
  have hres := b.resolveT_erase σ
  have hnd := SPath.resolveT_ends σ b
  cases hr : b.resolveT σ with
  | error e =>
    rw [hr] at hnd
    simp only [bind, Except.bind]
    exact ⟨fun h' => hnd.1 (by cases h'; rfl), fun h' => hnd.2 (by cases h'; rfl)⟩
  | ok ref =>
    rw [hr] at hres
    have hfull : σ.storage.full ref = false :=
      Storage.full_eq_false rfl ref fun elems sh fx hf => hp _ _ elems sh fx hres hf
    simp only [bind, Except.bind, pure, Except.pure, hfull, Bool.false_eq_true, ↓reduceIte]
    exact (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _

theorem run_push {σ : State C Γ} {E : Ty} {a : Idx Γ (.alias (.array E))} {r : Name}
    {segs : List Seg} {es : List Semantics.SVal} {fx : Bool}
    (hd : (none.isSome || E.defaultOkS) = true) (hb : Bound σ.erase a r segs)
    (hf : σ.erase.glob.findStorage r segs = .ok (.array es [] fx)) (hl : es.length + 1 < 2 ^ 256)
    {τ : Semantics.State}
    (hτ : σ.erase.glob.saveStorage r segs (.array (es ++ [defaultForTy E]) [] fx) = .ok τ) :
    ∃ σ', SRuns σ (.push (C := C) (.alias a : SPath C Γ (.array E)) none hd) σ' ∧
      σ'.erase = σ.erase.withGlob τ := by
  refine SRuns.of_agrees (s := .push (.alias a) none hd) (TRun.push_erase _ none)
    (push_none_ends _ fun r' segs' elems sh fx' hr hf' => ?_) ?_
  · rw [resolve_alias hb] at hr
    cases hr
    rw [hf] at hf'
    cases hf'
    exact hl
  · refine Eq.trans (?_ : _ = σ.erase.withGlob <$> σ.erase.glob.saveStorage r segs
      (.array (es ++ [defaultForTy E]) [] fx)) (by rw [hτ]; rfl)
    simp only [bind, Except.bind, SPath.resolve, aliasPath_bound hb, pushAt, hf, Src.pushVal, pure,
        Except.pure, Semantics.pushSlot]

theorem run_pop {σ : State C Γ} {E : Ty} {a : Idx Γ (.alias (.array E))} {r : Name}
    {segs : List Seg} {es sh : List Semantics.SVal} {last : Semantics.SVal} {fx : Bool}
    (hb : Bound σ.erase a r segs)
    (hf : σ.erase.glob.findStorage r segs = .ok (.array (es ++ [last]) sh fx)) {τ : Semantics.State}
    (hτ : σ.erase.glob.saveStorage r segs
      (.array es ((if E.isMapping then last else last.defaultOf) :: sh) fx) = .ok τ) :
    ∃ σ', SRuns σ (.pop (C := C) (E := E) (.alias a)) σ' ∧ σ'.erase = σ.erase.withGlob τ := by
  refine SRuns.of_agrees (s := .pop (.alias a)) (TRun.pop_erase _)
    ((SPath.resolveT_ends σ _).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _) ?_
  refine Eq.trans (?_ : _ = σ.erase.withGlob <$> σ.erase.glob.saveStorage r segs
    (.array es ((if E.isMapping then last else last.defaultOf) :: sh) fx)) (by rw [hτ]; rfl)
  simp only [bind, Except.bind, SPath.resolve, aliasPath_bound hb, popAt, hf, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.reverse_reverse]

theorem run_delete {σ : State C Γ} {T : Ty} {l : Loc C Γ T} {r : Name} {segs : List Seg}
    {cur : Semantics.SVal} (hl : l.resolve σ.erase = .ok (r, segs))
    (hf : σ.erase.glob.findStorage r segs = .ok cur) {τ : Semantics.State}
    (hτ : σ.erase.glob.saveStorage r segs cur.defaultOf = .ok τ) :
    ∃ σ', SRuns σ (.delete l) σ' ∧ σ'.erase = σ.erase.withGlob τ := by
  refine SRuns.of_agrees (s := .delete l) (TRun.delete_erase l)
    ((Loc.resolveT_ends σ l).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _) ?_
  refine Eq.trans (?_ : _ = σ.erase.withGlob <$> σ.erase.glob.saveStorage r segs cur.defaultOf)
    (by rw [hτ]; rfl)
  simp only [bind, Except.bind, hl, hf]

theorem run_primProg {σ : State C Γ} {p : PrimTy} {l : Loc C Γ (.prim p)} {r : Name}
    {segs : List Seg} {v : Semantics.SVal} (hl : l.resolve σ.erase = .ok (r, segs))
    (hv : v.canon (.prim p)) (hfit : v.fits (.prim p)) {τ : Semantics.State}
    (hτ : σ.erase.glob.saveStorage r segs v = .ok τ) :
    ∃ σ', TRuns σ (primProg p l v) σ' ∧ σ'.erase = σ.erase.withGlob τ := by
  cases p <;> cases v <;> try (exact hv.elim)
  all_goals rename_i pv; cases pv <;> try (exact hv.elim)
  all_goals simp only [SVal.fits] at hfit
  all_goals first
    | simp only [primProg, numLit_eq hfit]
    | skip
  all_goals
    refine Exists.imp (fun σ' (h : SRuns σ _ σ' ∧ σ'.erase = σ.erase.withGlob τ) =>
      ⟨TRuns.cons h.1 (TRuns.nil _), h.2⟩) ?_
    exact SRuns.of_agrees (TRun.assign_erase l _)
      ((Src.valueT_ends σ _).bind fun _ => (Loc.resolveT_ends σ _).bind fun _ =>
        (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _)
      (by simp only [bind, Except.bind, Src.value, Val.eval, Simple.eval, pure, Except.pure,
          Value.toSVal, hl, State.writeStorage_prim, hτ]; rfl)

/-- The alias a `bound` block declares, bound to `q`. -/
theorem run_decl {d : Nat} {R : RefTy} {σ : State C Γ} {q : SPath C Γ (.ref R)} {r : Name}
    {segs : List Seg} (hq : q.resolve σ.erase = .ok (r, segs)) :
    ∃ σ₀, SRuns σ (.declStorage R (slot d) (some (.path q))) σ₀ ∧
      σ₀.erase = σ.erase.push (t := .alias R) (some (r, segs)) :=
  SRuns.of_agrees (s := .declStorage R (slot d) (some (.path q))) (TRun.declStorage_erase R (some (.path q)))
    (((SPath.resolveT_ends σ q).bind fun _ => TRes.Ends.ok _).bind fun _ => TRes.Ends.ok _)
    (by simp only [ARhs.eval, hq, bind, Except.bind, pure, Except.pure])

theorem run_block {Γ₁ : Ctx} (σ : State C Γ) (P : Prog C Γ Γ₁) :
    Stmt.run σ (.block P) = (Prog.run σ P).map fun o => ⟨o.st.drop P.ext, o.ext⟩ := rfl

/-- A block that binds an alias to `q` and runs `body` through it. -/
theorem run_bound {d : Nat} {R : RefTy} {σ : State C Γ} {q : SPath C Γ (.ref R)}
    {body : Prog C (.alias R :: Γ) (.alias R :: Γ)} {σ₀ σ₁ : State C (.alias R :: Γ)}
    (h0 : SRuns σ (.declStorage R (slot d) (some (.path q))) σ₀) (hb : TRuns σ₀ body σ₁) :
    TRuns σ (bound d R q body) (σ₁.drop (.push .refl)) := by
  obtain ⟨o, ho, rfl⟩ := TRuns.cons h0 hb
  refine TRuns.cons ⟨⟨o.st.drop (.push .refl), o.ext⟩, ?_, rfl⟩ (TRuns.nil _)
  rw [run_block, ho, Ext.eq_of_depth (Prog.ext _) (.push .refl)]
  rfl

end Steps

/-! ### The builder writes what it is given -/

/-- What `fill` does for one value `v`: from the default at `q`, in any
context, it leaves `v` there, changing nothing else, the locals as they
were. -/
def FillOK (C : Contract) (v : Semantics.SVal) : Prop :=
  ∀ (T : Ty) (d : Nat) (Γ : Ctx) (q : SPath C Γ T) (σ : State C Γ) (r : Name) (segs : List Seg),
    v.canon T → v.tight T → v.fits T → T.defaultOkS = true → q.resolve σ.erase = .ok (r, segs) →
    Wrote σ.erase.storage σ.erase.storage r segs (defaultForTy T) →
    ∃ σ', TRuns σ (fill d T q v) σ' ∧ Wrote σ.erase.storage σ'.erase.storage r segs v ∧
      σ'.erase.env = σ.erase.env

section Fills

variable {Γ : Ctx}

/-- A save in a scoped state, as a write at one path. -/
theorem Wrote.saveCore {σ : EState C Γ} {st₀ : List (Name × Semantics.SVal)} {r : Name} {segs : List Seg}
    {X : Semantics.SVal} (hc : Wrote st₀ σ.storage r segs X) (Y : Semantics.SVal) :
    ∃ τ, σ.glob.saveStorage r segs Y = .ok τ ∧ Wrote st₀ (σ.withGlob τ).storage r segs Y := by
  obtain ⟨τ, hτ, hW, -⟩ := Solidity.Build.Wrote.saveStorage (σ := σ.glob) hc Y
  exact ⟨τ, hτ, hW⟩

/-- A child filled below the node at `r.segs`: the node, `N`, becomes `N'`. -/
theorem child_step {d : Nat} {T : Ty} {q : SPath C Γ T} {σ : State C Γ}
    {st₀ : List (Name × Semantics.SVal)} {r : Name} {segs : List Seg} {seg : Seg}
    {N N' w : Semantics.SVal}
    (hw : FillOK C w) (hc : w.canon T) (ht : w.tight T) (hf : w.fits T) (hok : T.defaultOkS = true)
    (hq : q.resolve σ.erase = .ok (r, segs ++ [seg])) (hchain : Wrote st₀ σ.erase.storage r segs N)
    (hnoop : N.save [seg] (defaultForTy T) = .ok N) (hs : N.save [seg] w = .ok N') :
    ∃ σ', TRuns σ (fill (d + 1) T q w) σ' ∧ Wrote st₀ σ'.erase.storage r segs N' ∧
      σ'.erase.env = σ.erase.env := by
  obtain ⟨σ', hrun, hW, he⟩ :=
    hw T (d + 1) Γ q σ r (segs ++ [seg]) hc ht hf hok hq (hchain.noop.down hnoop)
  exact ⟨σ', hrun, hchain.trans (Wrote.up hchain.noop.find hs hW), he⟩

theorem Bound.of_env {σ σ' : EState C Γ} {R : RefTy} {a : Idx Γ (.alias R)} {r : Name}
    {segs : List Seg} (he : σ'.env = σ.env) (h : Bound σ a r segs) : Bound σ' a r segs := by
  unfold Bound; rw [he]; exact h

theorem fillFields_run {d : Nat} {s r : Name} {segs : List Seg} {a : Idx Γ (.alias (.struct s))} :
    ∀ (todo pre : List (Name × Semantics.SVal)) (sdRest : List (Name × Ty)) (σ : State C Γ)
      (st₀ : List (Name × Semantics.SVal)),
      (∀ nw ∈ todo, FillOK C nw.2) → canonFields s todo → tightFields s todo → fitsFields s todo →
      todo.map (·.1) = sdRest.map (·.1) →
      (∀ nt ∈ sdRest, lookupBy nt.1 (structDef s) = some nt.2 ∧ nt.2.defaultOkS = true ∧
        lookupBy nt.1 pre = none) →
      nodupKeysB sdRest = true →
      Bound σ.erase a r segs →
      Wrote st₀ σ.erase.storage r segs (.struct (pre ++ defaultForFields sdRest)) →
      ∃ σ', TRuns σ (fillFields (C := C) d s a todo) σ' ∧
        Wrote st₀ σ'.erase.storage r segs (.struct (pre ++ todo)) ∧ σ'.erase.env = σ.erase.env
  | [], pre, sdRest, σ, st₀, _, _, _, _, hmap, _, _, _, hW => by
    cases sdRest with
    | cons _ _ => simp only [List.map_nil, List.map_cons, List.nil_eq, reduceCtorEq] at hmap
    | nil => exact ⟨σ, TRuns.nil σ, by simpa only [List.append_nil, defaultForFields] using hW, rfl⟩
  | (n, w) :: todo, pre, sdRest, σ, st₀, hIH, hc, ht, hfit, hmap, hsd, hnd, hB, hW => by
    cases sdRest with
    | nil => simp only [List.map_cons, List.map_nil, reduceCtorEq] at hmap
    | cons nt sdRest =>
      obtain ⟨n', t⟩ := nt
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨rfl, hmap⟩ := hmap
      obtain ⟨hlook, hok, hpre⟩ := hsd (n, t) (List.mem_cons_self ..)
      dsimp only at hlook hok hpre
      simp only [nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hnd
      simp only [canonFields, hlook] at hc
      simp only [tightFields, hlook] at ht
      simp only [fitsFields, hlook] at hfit
      simp only [fillFields]
      split
      · rename_i T heq
        have hT : T = t := by rw [hlook] at heq; exact (Option.some.inj heq).symm
        subst hT
        have hN : (Semantics.SVal.struct (pre ++ defaultForFields ((n, T) :: sdRest))).save [.field n]
            (defaultForTy T) = .ok (.struct (pre ++ defaultForFields ((n, T) :: sdRest))) := by
          simp only [defaultForFields]
          rw [save_field _ (lookupBy_mid hpre), setBy_of_lookupBy (lookupBy_mid hpre)]
        have hs : (Semantics.SVal.struct (pre ++ defaultForFields ((n, T) :: sdRest))).save [.field n] w =
            .ok (.struct ((pre ++ [(n, w)]) ++ defaultForFields sdRest)) := by
          simp only [defaultForFields]
          rw [save_field _ (lookupBy_mid hpre), setBy_mid hpre]; simp only [List.append_assoc,
                                                                     List.cons_append,
                                                                     List.nil_append]
        obtain ⟨σ₁, hrun₁, hW₁, he₁⟩ := child_step (hIH (n, w) (List.mem_cons_self ..)) hc.1
          ht.1 hfit.1 hok (resolve_field _ hB) hW hN hs
        obtain ⟨σ₂, hrun₂, hW₂, he₂⟩ := fillFields_run todo (pre ++ [(n, w)]) sdRest σ₁ st₀
          (fun nw hm => hIH nw (List.mem_cons_of_mem _ hm)) hc.2 ht.2 hfit.2 hmap
          (fun nt hm => by
            obtain ⟨h1, h2, h3⟩ := hsd nt (List.mem_cons_of_mem _ hm)
            refine ⟨h1, h2, ?_⟩
            rw [lookupBy_append_left_none h3]
            have hne : nt.1 ≠ n := by
              intro he
              have := lookupBy_isSome_of_mem (k := nt.1) (v := nt.2) hm
              rw [he, hnd.1] at this; exact nomatch this
            simp only [lookupBy, hne, ↓reduceIte])
          hnd.2 (hB.of_env he₁) hW₁
        exact ⟨σ₂, TRuns.append hrun₁ hrun₂,
          by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hW₂,
          he₂.trans he₁⟩
      · rename_i heq; rw [hlook] at heq; exact nomatch heq

theorem fillElems_run {R : RefTy} {E : Ty} {d : Nat} (ak : ArrTy R E) {a : Idx Γ (.alias R)}
    {r : Name} {segs : List Seg} (hE : E.defaultOkS = true) :
    ∀ (L pre sh : List Semantics.SVal) (fx : Bool) (σ : State C Γ)
      (st₀ : List (Name × Semantics.SVal)),
      (∀ w ∈ L, FillOK C w) → canonElems E L → tightElems E L → fitsElems E L →
      pre.length + L.length ≤ 2 ^ 256 → Bound σ.erase a r segs →
      Wrote st₀ σ.erase.storage r segs
        (.array (pre ++ List.replicate L.length (defaultForTy E)) sh fx) →
      ∃ σ', TRuns σ (fillElems (C := C) d ak a pre.length L) σ' ∧
        Wrote st₀ σ'.erase.storage r segs (.array (pre ++ L) sh fx) ∧ σ'.erase.env = σ.erase.env
  | [], pre, sh, fx, σ, st₀, _, _, _, _, _, _, hW => ⟨σ, TRuns.nil σ,
      by simpa only [List.append_nil, List.length_nil, List.replicate_zero] using hW, rfl⟩
  | w :: L, pre, sh, fx, σ, st₀, hIH, hc, ht, hfit, hlen, hB, hW => by
    simp only [fillElems]
    simp only [List.length_cons, List.replicate_succ] at hW
    have hq := resolve_index_arr (C := C) ak (j := pre.length) hB
      (Wrote.findStorage (σ := σ.erase.glob) hW) (by simp only [List.length_append, List.length_cons,
          List.length_replicate, Nat.lt_add_right_iff_pos, Nat.zero_lt_succ])
      (by simp only [List.length_cons] at hlen; omega)
    obtain ⟨σ₁, hrun₁, hW₁, he₁⟩ := child_step (d := d) (hIH w (List.mem_cons_self ..)) hc.1
      ht.1 hfit.1 hE hq hW (save_at_live ..) (save_at_live ..)
    obtain ⟨σ₂, hrun₂, hW₂, he₂⟩ := fillElems_run ak hE L (pre ++ [w]) sh fx σ₁ st₀
      (fun w hm => hIH w (List.mem_cons_of_mem _ hm)) hc.2 ht.2 hfit.2
      (by simp only [List.length_cons] at hlen; simp only [List.length_append, List.length_cons,
        List.length_nil]; omega)
      (hB.of_env he₁)
      (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hW₁)
    refine ⟨σ₂, TRuns.append hrun₁
        (by simpa only [List.length_append, List.length_cons, List.length_nil,
          Nat.zero_add] using hrun₂),
      by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hW₂,
      he₂.trans he₁⟩

/-- `values.push();` `n` times on an array with nothing past its end, below
the bound. -/
theorem pushes_run {E : Ty} {a : Idx Γ (.alias (.array E))} {r : Name} {segs : List Seg}
    (hd : (none.isSome || E.defaultOkS) = true) :
    ∀ (n : Nat) (es : List Semantics.SVal) (σ : State C Γ) (st₀ : List (Name × Semantics.SVal)),
      Bound σ.erase a r segs → Wrote st₀ σ.erase.storage r segs (.array es [] false) →
      es.length + n < 2 ^ 256 →
      ∃ σ', TRuns σ (Prog.rep n
          (Stmt.push (C := C) (.alias a : SPath C Γ (.array E)) none hd)) σ' ∧
        Wrote st₀ σ'.erase.storage r segs (.array (es ++ List.replicate n (defaultForTy E)) [] false) ∧
        σ'.erase.env = σ.erase.env
  | 0, es, σ, st₀, _, hW, _ => ⟨σ, TRuns.nil σ,
      by simpa only [List.replicate_zero, List.append_nil] using hW, rfl⟩
  | n + 1, es, σ, st₀, hB, hW, hl => by
    obtain ⟨τ, hτ, hWτ⟩ := Wrote.saveCore hW (.array (es ++ [defaultForTy E]) [] false)
    obtain ⟨σ₁, hs₁, he₁⟩ := run_push hd hB (Wrote.findStorage (σ := σ.erase.glob) hW)
      (by omega) hτ
    obtain ⟨σ', hrun, hW', henv'⟩ := pushes_run hd n (es ++ [defaultForTy E]) σ₁ st₀
      (by rw [he₁]; exact hB) (by rw [he₁]; exact hWτ)
      (by simp only [List.length_append, List.length_singleton]; omega)
    refine ⟨σ', TRuns.cons hs₁ hrun,
      by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hW', ?_⟩
    rw [henv', he₁]
    rfl

theorem fillShadow_run {E : Ty} {d : Nat} {a : Idx Γ (.alias (.array E))} {r : Name}
    {segs : List Seg} (hE : E.defaultOkS = true) :
    ∀ (S SH : List Semantics.SVal) (i : Nat) (σ : State C Γ) (st₀ : List (Name × Semantics.SVal)),
      (∀ w ∈ S, FillOK C w) → canonElems E S → tightElems E S → fitsElems E S →
      i + S.length ≤ 2 ^ 256 →
      (E.isPrimitive = true → ∀ w ∈ S, w = defaultForTy E) → Bound σ.erase a r segs →
      Wrote st₀ σ.erase.storage r segs
        (.array (List.replicate (i + S.length) (defaultForTy E)) SH false) →
      ∃ σ', TRuns σ (fillShadow (C := C) d E a i S) σ' ∧
        Wrote st₀ σ'.erase.storage r segs
          (.array (List.replicate i (defaultForTy E)) (S ++ SH) false) ∧
        σ'.erase.env = σ.erase.env
  | [], SH, i, σ, st₀, _, _, _, _, _, _, _, hW => ⟨σ, TRuns.nil σ,
      by simpa only [List.nil_append, List.length_nil, Nat.add_zero] using hW, rfl⟩
  | w :: S, SH, i, σ, st₀, hIH, hc, ht, hfit, hlen, hprim, hB, hW => by
    simp only [fillShadow]
    obtain ⟨σ₁, hrun₁, hW₁, he₁⟩ := fillShadow_run hE S SH (i + 1) σ st₀
      (fun w hm => hIH w (List.mem_cons_of_mem _ hm)) hc.2 ht.2 hfit.2
      (by simp only [List.length_cons] at hlen; omega)
      (fun hp w hm => hprim hp w (List.mem_cons_of_mem _ hm)) hB
      (by simpa only [Nat.add_assoc, Nat.add_comm 1, List.length_cons] using hW)
    have hB₁ : Bound σ₁.erase a r segs := hB.of_env he₁
    rw [List.replicate_succ'] at hW₁
    have hf₁ := Wrote.findStorage (σ := σ₁.erase.glob) hW₁
    obtain ⟨τ, hτ, hWτ⟩ := Wrote.saveCore hW₁
      (.array (List.replicate i (defaultForTy E)) (defaultForTy E :: (S ++ SH)) false)
    have hdef : ∀ T : Ty,
        (if T.isMapping = true then defaultForTy T else (defaultForTy T).defaultOf) =
          defaultForTy T := by
      intro T; split <;> simp only [defaultOf_default]
    cases E with
    | prim p =>
      have hw : w = defaultForTy (.prim p) := hprim rfl w (List.mem_cons_self ..)
      subst hw
      obtain ⟨σ₂, hs₂, he₂⟩ := run_pop hB₁ hf₁ (by rw [hdef]; exact hτ)
      refine ⟨σ₂, TRuns.append hrun₁ (TRuns.cons hs₂ (TRuns.nil _)), ?_, ?_⟩
      · rw [he₂]; simpa only [List.cons_append] using hWτ
      · rw [he₂]; exact he₁
    | ref R =>
      dsimp only
      have hq := resolve_index_arr (C := C) (ArrTy.dyn (E := .ref R)) (j := i) hB₁ hf₁ (by
        simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil,
          Nat.zero_add, Nat.lt_add_one])
        (by simp only [List.length_cons] at hlen; omega)
      -- in the block: the slot bound, popped, then filled through its alias
      obtain ⟨σ₂, hd₂, he₂⟩ := run_decl (d := d + 1) hq
      have hB₂ : Bound σ₂.erase (Idx.there a) r segs := by rw [he₂]; exact hB₁
      have hf₂ : σ₂.erase.glob.findStorage r segs = .ok (.array
          (List.replicate i (defaultForTy (.ref R)) ++ [defaultForTy (.ref R)]) (S ++ SH) false) := by
        rw [he₂]; exact hf₁
      obtain ⟨σ₃, hs₃, he₃⟩ := run_pop (E := .ref R) hB₂ hf₂ (τ := τ)
        (by rw [hdef, he₂]; exact hτ)
      have hBτ : Bound σ₃.erase Idx.here r (segs ++ [.at (i : Int)]) := by rw [he₃, he₂]; rfl
      have hsh : ∀ x : Semantics.SVal, (Semantics.SVal.array (List.replicate i (defaultForTy (.ref R)))
          (defaultForTy (.ref R) :: (S ++ SH)) false).save [.at (i : Int)] x =
          .ok (.array (List.replicate i (defaultForTy (.ref R))) (x :: (S ++ SH)) false) := by
        intro x
        have := save_at_shadow (List.replicate i (defaultForTy (.ref R))) (S ++ SH)
          (defaultForTy (.ref R)) x false
        simpa only [List.length_replicate] using this
      obtain ⟨σ₄, hrun₄, hW₄, he₄⟩ := child_step (d := d) (hIH w (List.mem_cons_self ..))
        hc.1 ht.1 hfit.1 hE (resolve_alias hBτ)
        (show Wrote st₀ σ₃.erase.storage r segs _ by rw [he₃]; exact hWτ)
        (hsh _) (hsh w)
      refine ⟨σ₄.drop (.push .refl), TRuns.append hrun₁ (run_bound hd₂ (TRuns.cons hs₃ hrun₄)),
        by rw [State.drop_erase]; simpa only [List.cons_append] using hW₄, ?_⟩
      rw [State.drop_erase]
      show σ₄.erase.env.2 = σ.erase.env
      rw [he₄, he₃, he₂]
      exact he₁

theorem fillEntries_run {d : Nat} {k : PrimTy} {V : Ty}
    {a : Idx Γ (.alias (.mapping (.prim k) V))} {r : Name} {segs : List Seg}
    (hV : V.defaultOkS = true) :
    ∀ (todo done : List (Int × Semantics.SVal)) (σ : State C Γ)
      (st₀ : List (Name × Semantics.SVal)),
      (∀ kw ∈ todo, FillOK C kw.2) → canonEntries V todo → tightEntries V todo →
      fitsEntries (.prim k) V todo → nodupKeysB (done ++ todo) = true → Bound σ.erase a r segs →
      Wrote st₀ σ.erase.storage r segs (.map done (defaultForTy V)) →
      ∃ σ', TRuns σ (fillEntries (C := C) d k V a todo) σ' ∧
        Wrote st₀ σ'.erase.storage r segs (.map (done ++ todo) (defaultForTy V)) ∧
        σ'.erase.env = σ.erase.env
  | [], done, σ, st₀, _, _, _, _, _, _, hW =>
    ⟨σ, TRuns.nil σ, by simpa only [List.append_nil] using hW, rfl⟩
  | (key, w) :: todo, done, σ, st₀, hIH, hc, ht, hfit, hnd, hB, hW => by
    have hkey : lookupBy key done = none := nodupKeysB_mid hnd
    have hf := Wrote.findStorage (σ := σ.erase.glob) hW
    have hq := resolve_index_map (C := C) (V := V) (key := key) hfit.1 hB hf
    -- `delete balances[key];` creates the entry at the default
    have hcur : σ.erase.glob.findStorage r (segs ++ [.at key]) = .ok (defaultForTy V) := by
      rw [SemanticsProperties.State.findStorage_append, hf]
      simp only [bind, Except.bind, Semantics.SVal.find, hkey]
    have hmid : ∀ x y : Semantics.SVal, setBy key y (done ++ [(key, x)]) = done ++ [(key, y)] :=
      fun x y => setBy_mid hkey
    have hN₁ : (Semantics.SVal.map done (defaultForTy V)).save [.at key] (defaultForTy V) =
        .ok (.map (done ++ [(key, defaultForTy V)]) (defaultForTy V)) := by
      rw [save_at_map, show done = done ++ [] from (List.append_nil _).symm,
        setBy_append_left_none hkey]
      simp only [setBy, List.append_nil]
    obtain ⟨τ, hτ, hWτ⟩ :=
      Wrote.saveCore hW (.map (done ++ [(key, defaultForTy V)]) (defaultForTy V))
    have hτd : σ.erase.glob.saveStorage r (segs ++ [.at key]) (defaultForTy V).defaultOf =
        .ok τ := by
      rw [defaultOf_default, SemanticsProperties.State.saveStorage_append hf, hN₁]
      exact hτ
    obtain ⟨σ₁, hs₁, he₁⟩ := run_delete (C := C)
      (l := Loc.index .map (.alias a) (.simple (keyLit k key)))
      (by simpa only [SPath.resolve] using hq) hcur hτd
    have hBτ : Bound σ₁.erase a r segs := by rw [he₁]; exact hB
    have hWτ' : Wrote st₀ σ₁.erase.storage r segs
        (.map (done ++ [(key, defaultForTy V)]) (defaultForTy V)) := by rw [he₁]; exact hWτ
    have hqτ := resolve_index_map (C := C) (V := V) (key := key) hfit.1 hBτ
      (Wrote.findStorage (σ := σ₁.erase.glob) hWτ')
    obtain ⟨σ₂, hrun₂, hW₂, he₂⟩ := child_step (d := d) (hIH (key, w) (List.mem_cons_self ..))
      hc.1 ht.1 hfit.2.1 hV hqτ hWτ' (by rw [save_at_map, hmid]) (by rw [save_at_map, hmid])
    obtain ⟨σ₃, hrun₃, hW₃, he₃⟩ := fillEntries_run hV todo (done ++ [(key, w)]) σ₂ st₀
      (fun kw hm => hIH kw (List.mem_cons_of_mem _ hm)) hc.2 ht.2 hfit.2.2
      (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hnd)
      (hBτ.of_env he₂) hW₂
    refine ⟨σ₃, ?_, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hW₃,
                           ?_⟩
    · simp only [fillEntries]
      exact TRuns.cons hs₁ (TRuns.append hrun₂ hrun₃)
    · rw [he₃, he₂, he₁]
      rfl

/-- **The builder writes what it is given**: from the default at a typed
path, `fill` leaves any canonical, tight value there. -/
theorem fill_ok : ∀ v : Semantics.SVal, FillOK C v
  | .prim pv => by
    intro T d Γ q σ r segs hc ht hf hok hq h0
    cases T with
    | ref R => cases pv <;> cases R <;> simp only [SVal.canon] at hc
    | prim p =>
      cases q with
      | loc l =>
        have hl : l.resolve σ.erase = .ok (r, segs) := by simpa only [SPath.resolve] using hq
        obtain ⟨τ, hτ, hWτ⟩ := Wrote.saveCore h0 (.prim pv)
        obtain ⟨σ', hrun, he⟩ := run_primProg hl hc hf hτ
        exact ⟨σ', hrun, by rw [he]; exact hWτ, by rw [he]; rfl⟩
  | .struct fields => by
    intro T d Γ q σ r segs hc ht hf hok hq h0
    cases T with
    | prim p => simp only [SVal.canon] at hc
    | ref R =>
      cases R with
      | struct s =>
        obtain ⟨hnames, hcf⟩ := hc
        have hs : s ∈ defaultOkStructs := by simpa only [Ty.defaultOkS, decide_eq_true_eq] using hok
        obtain ⟨hnd, hmok⟩ := struct_ok hs
        obtain ⟨σ₁, hd₁, he₁⟩ := run_decl (d := d) hq
        obtain ⟨σ', hrun, hW, he⟩ := fillFields_run (C := C) (d := d) (s := s) (a := .here)
          fields []
          (structDef s) σ₁ σ.erase.storage
          (fun nw _ => fill_ok nw.2) hcf ht hf hnames
          (fun nt hm => ⟨lookupBy_eq_of_nodup hnd hm, hmok nt hm, rfl⟩) hnd
          (by rw [he₁]; rfl)
          (by rw [he₁]; rw [defaultForTy] at h0; simpa only [List.nil_append] using h0)
        refine ⟨σ'.drop (.push .refl), run_bound hd₁ hrun, by
          rw [State.drop_erase]; simpa only [List.nil_append] using hW, ?_⟩
        rw [State.drop_erase]
        show σ'.erase.env.2 = σ.erase.env
        rw [he, he₁]; rfl
      | array _ => simp only [SVal.canon] at hc
      | fixed _ _ => simp only [SVal.canon] at hc
      | mapping _ _ => simp only [SVal.canon] at hc
  | .array elems shadow fx => by
    intro T d Γ q σ r segs hc ht hf hok hq h0
    cases T with
    | prim p => simp only [SVal.canon] at hc
    | ref R =>
      cases R with
      | struct _ => simp only [SVal.canon] at hc
      | mapping _ _ => simp only [SVal.canon] at hc
      | array E =>
        obtain ⟨hfx, hce, hcs⟩ := hc
        subst hfx
        obtain ⟨hne, hpr, hte, hts⟩ := ht
        obtain ⟨hlen, hfe, hfs⟩ := hf
        obtain ⟨σ₁, hd₁, he₁⟩ := run_decl (d := d) hq
        have hB : Bound σ₁.erase .here r segs := by rw [he₁]; rfl
        have h0' : Wrote σ.erase.storage σ₁.erase.storage r segs (.array [] [] false) := by
          rw [defaultForTy] at h0; rw [he₁]; exact h0
        by_cases hE : E.defaultOkS = true
        · obtain ⟨σ₂, hrun₂, hW₂, henv₂⟩ := pushes_run (C := C) (E := E) (a := .here)
            (by simp only [Option.isSome_none, hE,
                Bool.or_true]) (elems.length + shadow.length) [] σ₁ σ.erase.storage hB h0'
            (by simp only [List.length_nil, Nat.zero_add]; exact hlen)
          obtain ⟨σ₃, hrun₃, hW₃, he₃⟩ := fillShadow_run (C := C) (d := d) hE shadow []
            elems.length σ₂ σ.erase.storage (fun w _ => fill_ok w) hcs hts hfs (by omega) hpr
            (hB.of_env henv₂) (by simpa only [List.nil_append] using hW₂)
          obtain ⟨σ₄, hrun₄, hW₄, he₄⟩ := fillElems_run (C := C) (d := d) (ArrTy.dyn (E := E)) hE
            elems [] shadow false σ₃ σ.erase.storage (fun w _ => fill_ok w) hce hte hfe
            (by simp only [List.length_nil, Nat.zero_add]; omega)
            ((hB.of_env henv₂).of_env he₃)
            (by simpa only [List.nil_append, List.append_nil] using hW₃)
          have hbody : TRuns σ₁ ((Prog.rep (elems.length + shadow.length)
              (.push (.alias .here : SPath C _ (.array E)) none (by simp only [Option.isSome_none,
                  hE, Bool.or_true]))).append
              ((fillShadow d E .here elems.length shadow).append
                (fillElems d (ArrTy.dyn (E := E)) .here 0 elems))) σ₄ :=
            TRuns.append hrun₂ (TRuns.append hrun₃ hrun₄)
          refine ⟨σ₄.drop (.push .refl), ?_,
            by rw [State.drop_erase]; simpa only [List.nil_append] using hW₄, ?_⟩
          · show TRuns σ (bound d (.array E) q (if hE : E.defaultOkS = true then _ else _)) _
            rw [dif_pos hE]
            exact run_bound hd₁ hbody
          · rw [State.drop_erase]
            show σ₄.erase.env.2 = σ.erase.env
            rw [he₄, he₃, henv₂, he₁]; rfl
        · obtain ⟨rfl, rfl⟩ := hne (by simpa only [Bool.not_eq_true] using hE)
          refine ⟨σ₁.drop (.push .refl), ?_, by rw [State.drop_erase]; exact h0', ?_⟩
          · show TRuns σ (bound d (.array E) q (if hE : E.defaultOkS = true then _ else _)) _
            rw [dif_neg hE]
            exact run_bound hd₁ (TRuns.nil _)
          · rw [State.drop_erase, he₁]; rfl
      | fixed E n =>
        obtain ⟨hfx, hlen, hce, -⟩ := hc
        subst hfx; subst hlen
        obtain ⟨hsh, hte⟩ := ht
        obtain ⟨hlen, hfe⟩ := hf
        subst hsh
        have hE : E.defaultOkS = true := by simpa only [Ty.defaultOkS] using hok
        obtain ⟨σ₁, hd₁, he₁⟩ := run_decl (d := d) hq
        obtain ⟨σ', hrun, hW, he⟩ := fillElems_run (C := C) (d := d)
          (ArrTy.fixed (E := E) (n := elems.length)) (a := .here)
          hE elems [] [] true σ₁ σ.erase.storage (fun w _ => fill_ok w)
          hce hte hfe (by simpa only [List.length_nil, Nat.zero_add, Nat.reducePow] using hlen)
          (by rw [he₁]; rfl)
          (by rw [defaultForTy] at h0; rw [he₁]; simpa only [List.nil_append] using h0)
        refine ⟨σ'.drop (.push .refl), run_bound hd₁ hrun, by
          rw [State.drop_erase]; simpa only [List.nil_append] using hW, ?_⟩
        rw [State.drop_erase]
        show σ'.erase.env.2 = σ.erase.env
        rw [he, he₁]; rfl
  | .map entries dflt => by
    intro T d Γ q σ r segs hc ht hf hok hq h0
    cases T with
    | prim p => simp only [SVal.canon] at hc
    | ref R =>
      cases R with
      | struct _ => simp only [SVal.canon] at hc
      | array _ => simp only [SVal.canon] at hc
      | fixed _ _ => simp only [SVal.canon] at hc
      | mapping K V =>
        obtain ⟨hnd, hce, hd, -⟩ := hc
        subst hd
        obtain ⟨hkey, hte⟩ := ht
        have hV : V.defaultOkS = true := by simpa only [Ty.defaultOkS] using hok
        cases K with
        | ref R' =>
          obtain rfl := hkey rfl
          have h0' : Wrote σ.erase.storage σ.erase.storage r segs (.map [] (defaultForTy V)) := by
            rw [defaultForTy] at h0; exact h0
          exact ⟨σ, TRuns.nil σ, h0', rfl⟩
        | prim k =>
          obtain ⟨σ₁, hd₁, he₁⟩ := run_decl (d := d) hq
          have h0' : Wrote σ.erase.storage σ₁.erase.storage r segs (.map [] (defaultForTy V)) := by
            rw [defaultForTy] at h0; rw [he₁]; exact h0
          obtain ⟨σ', hrun, hW, he⟩ := fillEntries_run (C := C) (d := d) (a := .here) hV
            entries [] σ₁ σ.erase.storage (fun kw _ => fill_ok kw.2) hce hte hf
            (by simpa only [List.nil_append] using hnd) (by rw [he₁]; rfl) h0'
          refine ⟨σ'.drop (.push .refl), run_bound hd₁ hrun, by
            rw [State.drop_erase]; simpa only [List.nil_append] using hW, ?_⟩
          rw [State.drop_erase]
          show σ'.erase.env.2 = σ.erase.env
          rw [he, he₁]; rfl
termination_by v => sizeOf v
decreasing_by
  all_goals first
    | exact sizeOf_lt_fields (by assumption)
    | exact sizeOf_lt_elems (by assumption)
    | exact sizeOf_lt_shadow (by assumption)
    | exact sizeOf_lt_entries (by assumption)

/-! ### Every root -/

theorem rootsProg_run :
    ∀ (todo done cf : List (Name × Semantics.SVal)) (σ : State C []),
      σ.erase.storage = done ++ cf → cf.map (·.1) = todo.map (·.1) →
      nodupKeysB (done ++ todo) = true →
      (∀ rv ∈ cf, ∃ T, lookupBy rv.1 C.vars = some T ∧ rv.2 = defaultForTy T) →
      (∀ rv ∈ todo, ∃ T, lookupBy rv.1 C.vars = some T ∧ rv.2.canon T ∧ rv.2.tight T ∧
        rv.2.fits T ∧ T.defaultOkS = true) →
      ∃ σ', TRuns σ (rootsProg C todo) σ' ∧ σ'.erase.storage = done ++ todo
  | [], done, cf, σ, hst, hmap, _, _, _ => by
    cases cf with
    | cons _ _ => simp only [List.map_cons, List.map_nil, reduceCtorEq] at hmap
    | nil => exact ⟨σ, TRuns.nil σ, by simpa only [List.append_nil] using hst⟩
  | (r, v) :: todo, done, cf, σ, hst, hmap, hnd, hcf, htodo => by
    cases cf with
    | nil => simp only [List.map_nil, List.map_cons, List.nil_eq, reduceCtorEq] at hmap
    | cons rx cf =>
      obtain ⟨r', x⟩ := rx
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨hr, hmap⟩ := hmap
      subst r'
      obtain ⟨T', hT', rfl⟩ := hcf (r, x) (List.mem_cons_self ..)
      obtain ⟨T, hT, hc, ht, hf, hok⟩ := htodo (r, v) (List.mem_cons_self ..)
      dsimp only at hT' hT hc ht hf hok
      have hTT : T' = T := by rw [hT] at hT'; exact (Option.some.inj hT').symm
      subst T'
      have hdone : lookupBy r done = none := nodupKeysB_mid hnd
      have hlook : lookupBy r σ.erase.storage = some (defaultForTy T) := by
        rw [hst, lookupBy_mid hdone]
      simp only [rootsProg]
      split
      · rename_i T₀ h
        have hT₀ : T₀ = T := by
          have h' : lookupBy r C.vars = some T₀ := h
          rw [hT] at h'; exact (Option.some.inj h').symm
        subst T₀
        have h0 : Wrote σ.erase.storage σ.erase.storage r [] (defaultForTy T) := by
          unfold Wrote putSt
          simp only [hlook, SVal.save_nil, bind, Except.bind, pure, Except.pure,
            setBy_of_lookupBy hlook]
        obtain ⟨σ₁, hrun₁, hW₁, -⟩ := fill_ok v T 0 [] (.loc (.root r h)) σ r [] hc ht hf hok
          rfl h0
        have hst₁ : σ₁.erase.storage = (done ++ [(r, v)]) ++ cf := by
          unfold Wrote putSt at hW₁
          simp only [hlook, SVal.save_nil, bind, Except.bind, pure, Except.pure,
            Except.ok.injEq] at hW₁
          rw [← hW₁, hst, setBy_mid hdone]; simp only [List.append_assoc, List.cons_append,
                                                List.nil_append]
        obtain ⟨σ₂, hrun₂, hst₂⟩ := rootsProg_run todo (done ++ [(r, v)]) cf σ₁ hst₁ hmap
          (by simpa only [List.append_assoc, List.cons_append,
                  List.nil_append] using hnd) (fun rv hm => hcf rv (List.mem_cons_of_mem _ hm))
          (fun rv hm => htodo rv (List.mem_cons_of_mem _ hm))
        exact ⟨σ₂, TRuns.append hrun₁ hrun₂,
          by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hst₂⟩
      · rename_i h
        have h' : lookupBy r C.vars = none := h
        rw [hT] at h'; exact nomatch h'

end Fills


end Build

end Solidity

namespace Solidity

open Semantics

open Semantics
open SemanticsProperties (lookupBy_eq_some_mem lookupBy_defaultForFields SVal.find_nil
  SVal.save_nil SVal.find_append SVal.save_append
  State.findStorage_append State.saveStorage_append)
open Semantics.SVal.canon (canonFields canonElems canonEntries)
open Semantics.SVal.tight (tightFields tightElems tightEntries)
open Semantics.SVal.fits (fitsFields fitsElems fitsEntries)

variable {C : Contract}

open Build



/-- Keys decide `nodupKeysB`. -/
theorem nodupKeysB_of_map_fst_eq {α β : Type} :
    ∀ {l : List (Name × α)} {l' : List (Name × β)}, l.map (·.1) = l'.map (·.1) →
      nodupKeysB l' = true → nodupKeysB l = true
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp only [List.map_nil, List.map_cons, List.nil_eq,
                                                  reduceCtorEq] at h
  | (a, x) :: l, (b, y) :: l', h, hnd => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hnd ⊢
    refine ⟨?_, nodupKeysB_of_map_fst_eq h hnd.2⟩
    cases hl : lookupBy a l with
    | none => rfl
    | some _ =>
      have := lookupBy_isSome_of_map_fst (k := a) h.symm (by simp only [hl, Option.isSome_some])
      rw [hnd.1] at this; exact nomatch this

/-- **Canonical and tight ⇒ reachable, by one program**: `Build.rootsProg`,
run by the typed run from `C`'s initial state, leaves exactly `st`. -/
theorem storage_tight (hnd : nodupKeysB C.vars = true) (hok : C.vars.all (·.2.defaultOkS) = true)
    {st : List (Name × Semantics.SVal)} (hc : CanonStorage C st) (ht : TightStorage C st)
    (hf : FitsStorage C st) :
    ∃ σ, Build.TRuns (State.init C) (Build.rootsProg C st) σ ∧
      σ.erase.storage = st := by
  have hstnd : nodupKeysB st = true := nodupKeysB_of_map_fst_eq hc.1 hnd
  have hroots : ∀ rv ∈ st, ∃ T, lookupBy rv.1 C.vars = some T ∧ rv.2.canon T ∧ rv.2.tight T ∧
      rv.2.fits T ∧ T.defaultOkS = true := by
    intro rv hmem
    have hname : rv.1 ∈ C.vars.map (·.1) := by rw [← hc.1]; exact List.mem_map_of_mem hmem
    obtain ⟨g, hg, hg1⟩ := List.mem_map.mp hname
    have hlook : lookupBy rv.1 C.vars = some g.2 := by
      rw [← hg1]; exact lookupBy_eq_of_nodup hnd hg
    have hrv : lookupBy rv.1 st = some rv.2 := lookupBy_eq_of_nodup hstnd hmem
    obtain ⟨v, hv, hcv⟩ := hc.2 rv.1 g.2 hlook
    rw [hrv] at hv; cases hv
    exact ⟨g.2, hlook, hcv, ht rv.1 g.2 rv.2 hlook hrv, hf rv.1 g.2 rv.2 hlook hrv,
      List.all_eq_true.mp hok g hg⟩
  have hdefs : ∀ rv ∈ C.initStorage, ∃ T, lookupBy rv.1 C.vars = some T ∧ rv.2 = defaultForTy T := by
    intro rv hmem
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hmem
    exact ⟨g.2, lookupBy_eq_of_nodup hnd hg, rfl⟩
  obtain ⟨σ, hrun, hst⟩ := Build.rootsProg_run st [] C.initStorage
    (State.init C) (by rw [Reachable.init_erase]; rfl)
    (by rw [hc.1]; simp only [Contract.initStorage, List.map_map, List.map_inj_left,
      Function.comp_apply, implies_true])
    (by simpa only [List.nil_append] using hstnd) hdefs hroots
  exact ⟨σ, hrun, by simpa only [List.nil_append] using hst⟩

/-- **Canonical and tight ⇒ reachable**, for words, keys and slots in range. -/
theorem canon_reachable (hnd : nodupKeysB C.vars = true) (hok : C.vars.all (·.2.defaultOkS) = true)
    {st : List (Name × Semantics.SVal)} (hc : CanonStorage C st) (ht : TightStorage C st)
    (hf : FitsStorage C st) : Reachable C st := by
  obtain ⟨_, ⟨o, ho, rfl⟩, hst⟩ := storage_tight hnd hok hc ht hf
  exact ⟨[], Build.rootsProg C st, o, ho, hst⟩

/-- **Nothing inferable is missing**: a property of storage that holds
initially and that every program keeps, by the typed run from any typed
state whose storage is canonical, holds of every canonical, tight storage.
The typed state is well-typed and its heap canonical by construction
(`State.erase_wt`, `State.erase_canonHeap`), so the step asks only the
storage's canonicity, which a typed storage does not give (decision 75). -/
theorem no_hidden_invariant (hnd : nodupKeysB C.vars = true)
    (hok : C.vars.all (·.2.defaultOkS) = true) (P : List (Name × Semantics.SVal) → Prop)
    (hinit : P C.initStorage)
    (hstep : ∀ (Γ' : Ctx) (σ : State C []) (o : Out C σ.H Γ')
      (prog : Prog C [] Γ'), CanonStorage C σ.erase.storage →
      prog.run σ = .ok o → P σ.erase.storage → P o.st.erase.storage)
    (st : List (Name × Semantics.SVal)) (hc : CanonStorage C st) (ht : TightStorage C st)
    (hf : FitsStorage C st) : P st := by
  obtain ⟨_, ⟨o, ho, rfl⟩, hst⟩ := storage_tight hnd hok hc ht hf
  rw [← hst]
  exact hstep _ _ o _ (by rw [Reachable.init_erase]; exact (Canon.init rfl).storage) ho
    (by rw [Reachable.init_erase]; exact hinit)

/-! ## Reachable storages are tight

The converse direction: every storage a program reaches is tight,
for a contract whose types have well-formed defaults all the way down
(`Ty.okDeep`: no array of a struct `defaultOkS` refuses).
Then the first clause of `SVal.tight` is vacuous, no memory object matters,
and what is left is kept by every write: a word is written into a live slot
(`State.checkIndex`, `IdxLive`), a mapping is indexed only at a number
(`KeysOK`: an alias was bound along such a path), and `pop`, `delete`, a
copy, a push leave cleared words and nothing past a fixed-size array's end. -/

section Exact

open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne)

/-- `T`'s default is well-formed all the way down: a struct `defaultOkS`
admits, and arrays and mappings of such. -/
def Ty.okDeep : Ty → Bool
  | .prim _ => true
  | .ref (.struct s) => s ∈ defaultOkStructs
  | .ref (.array E) => E.okDeep
  | .ref (.fixed E _) => E.okDeep
  | .ref (.mapping _ V) => V.okDeep

theorem struct_okDeep {s : Name} (h : s ∈ defaultOkStructs) :
    ∀ nt ∈ structDef s, nt.2.okDeep = true := by
  simp only [defaultOkStructs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [structDef, List.mem_cons, List.not_mem_nil, or_false, forall_eq, Ty.okDeep,
        String.reduceEq, imp_self, forall_eq_or_imp, defaultOkStructs, or_self, decide_true,
        and_self, or_true]

theorem okDeep_defaultOkS : ∀ {T : Ty}, T.okDeep = true → T.defaultOkS = true
  | .prim _, _ => rfl
  | .ref (.struct _), h => by simpa only [Ty.defaultOkS, decide_eq_true_eq, Ty.okDeep] using h
  | .ref (.array _), _ => rfl
  | .ref (.fixed E _), h => by
    simp only [Ty.okDeep] at h; simpa only [Ty.defaultOkS] using okDeep_defaultOkS (T := E) h
  | .ref (.mapping _ V), h => by
    simp only [Ty.okDeep] at h; simpa only [Ty.defaultOkS] using okDeep_defaultOkS (T := V) h

theorem okDeep_segTy {T T' : Ty} {seg : Seg} (h : T.okDeep = true) (hs : segTy T seg = some T') :
    T'.okDeep = true := by
  cases T with
  | prim _ => cases seg <;> simp only [segTy, reduceCtorEq] at hs
  | ref R =>
    cases R with
    | struct s =>
      cases seg with
      | field n =>
        simp only [segTy] at hs
        exact struct_okDeep (by simpa only [Ty.okDeep, decide_eq_true_eq] using h) (n,
                                    T') (lookupBy_eq_some_mem hs)
      | «at» _ => simp only [segTy, reduceCtorEq] at hs
    | array E => cases seg <;> simp only [segTy, reduceCtorEq,
                                   Option.some.injEq] at hs; subst hs; simpa only [Ty.okDeep] using h
    | fixed E _ => cases seg <;> simp only [segTy, reduceCtorEq,
                                     Option.some.injEq] at hs; subst hs; simpa only [Ty.okDeep] using h
    | mapping _ V => cases seg <;> simp only [segTy, reduceCtorEq,
                                       Option.some.injEq] at hs; subst hs; simpa only [Ty.okDeep] using h

theorem okDeep_tyAtSegs : ∀ {segs : List Seg} {T T' : Ty}, T.okDeep = true →
    tyAtSegs T segs = some T' → T'.okDeep = true
  | [], T, T', h, hs => by simp only [tyAtSegs, Option.some.injEq] at hs; subst hs; exact h
  | seg :: rest, T, T', h, hs => by
    simp only [tyAtSegs] at hs
    split at hs
    · rename_i Surface.Tm hm; exact okDeep_tyAtSegs (okDeep_segTy h hm) hs
    · exact nomatch hs

/-- Every mapping on the way is indexed by a number: an alias bound along
the path, or a path resolved, took its keys from `uint`/`int` values. -/
def KeysOK : Ty → List Seg → Prop
  | _, [] => True
  | T, seg :: rest => (∀ K V, T = .ref (.mapping K V) → K.isKey = true) ∧
      (match segTy T seg with
       | some T' => KeysOK T' rest
       | none => True)

theorem KeysOK_append : ∀ {segs : List Seg} {T T₁ : Ty} (seg : Seg),
    KeysOK T segs → tyAtSegs T segs = some T₁ →
    (∀ K V, T₁ = .ref (.mapping K V) → K.isKey = true) → KeysOK T (segs ++ [seg])
  | [], T, T₁, seg, _, hs, hk => by
    simp only [tyAtSegs, Option.some.injEq] at hs; subst hs
    refine ⟨hk, ?_⟩
    split <;> trivial
  | s :: rest, T, T₁, seg, hk₀, hs, hk => by
    simp only [tyAtSegs] at hs
    obtain ⟨hk₁, hk₂⟩ := hk₀
    refine ⟨hk₁, ?_⟩
    split at hs
    · rename_i Surface.Tm hm
      simp only [hm] at hk₂ ⊢
      exact KeysOK_append seg hk₂ hs hk
    · exact nomatch hs

/-- A word written through an index is written into a live slot: the index
was checked against the length where the path was taken. -/
def IdxLive (v : Semantics.SVal) (segs : List Seg) : Prop :=
  ∀ pre i, segs = pre ++ [.at i] → ∀ es sh fx, v.find pre = .ok (.array es sh fx) →
    0 ≤ i ∧ i.toNat < es.length

/-! ### Tight lists -/

theorem tightElems_iff {E : Ty} : ∀ {l : List Semantics.SVal}, tightElems E l ↔ ∀ v ∈ l, v.tight E
  | [] => by simp only [tightElems, List.not_mem_nil, false_implies, implies_true]
  | v :: rest => by simp only [tightElems, tightElems_iff (l := rest), List.mem_cons,
                        forall_eq_or_imp]

theorem tightEntries_iff {V : Ty} :
    ∀ {l : List (Int × Semantics.SVal)}, tightEntries V l ↔ ∀ kv ∈ l, kv.2.tight V
  | [] => by simp only [tightEntries, List.not_mem_nil, false_implies, implies_true]
  | (k, v) :: rest => by simp only [tightEntries, tightEntries_iff (l := rest), Prod.forall,
                             List.mem_cons, forall_eq_or_imp]

theorem tightFields_lookup {s : Name} {fields : List (Name × Semantics.SVal)} {n : Name} {v : Semantics.SVal}
    {T : Ty} (h : tightFields s fields) (hl : lookupBy n fields = some v)
    (hT : lookupBy n (structDef s) = some T) : v.tight T := by
  induction fields with
  | nil => simp only [lookupBy, reduceCtorEq] at hl
  | cons p rest ih =>
    obtain ⟨n', v'⟩ := p
    simp only [tightFields] at h
    by_cases hn : n = n'
    · subst hn
      simp only [lookupBy, ↓reduceIte, Option.some.injEq] at hl; subst hl
      simpa only [hT] using h.1
    · simp only [lookupBy, hn, ↓reduceIte] at hl
      exact ih h.2 hl

theorem tightFields_setBy {s : Name} {fields : List (Name × Semantics.SVal)} {n : Name} {w : Semantics.SVal} {T : Ty}
    (h : tightFields s fields) (hd : lookupBy n (structDef s) = some T) (hw : w.tight T) :
    tightFields s (setBy n w fields) := by
  induction fields with
  | nil => simp only [setBy, tightFields, hd, hw, and_self]
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp only [tightFields] at h
    by_cases hn : n = k
    · subst hn; simp only [setBy, ↓reduceIte, tightFields, hd, hw, h.2, and_self]
    · simp only [setBy, if_neg hn, tightFields]; exact ⟨h.1, ih h.2⟩

theorem tightEntries_setBy {V : Ty} {entries : List (Int × Semantics.SVal)} {i : Int} {w : Semantics.SVal}
    (h : tightEntries V entries) (hw : w.tight V) : tightEntries V (setBy i w entries) := by
  induction entries with
  | nil => simp only [setBy, tightEntries, hw, and_self]
  | cons p rest ih =>
    obtain ⟨j, v⟩ := p
    by_cases hi : i = j
    · subst hi; simp only [setBy, ↓reduceIte, tightEntries, hw, h.2, and_self]
    · simp only [setBy, if_neg hi, tightEntries]; exact ⟨h.1, ih h.2⟩

theorem tightEntries_lookup {V : Ty} {entries : List (Int × Semantics.SVal)} {i : Int} {v : Semantics.SVal}
    (h : tightEntries V entries) (hl : lookupBy i entries = some v) : v.tight V :=
  tightEntries_iff.mp h (i, v) (lookupBy_eq_some_mem hl)

theorem mem_set_or {l : List Semantics.SVal} {i : Nat} {u v : Semantics.SVal} (h : v ∈ l.set i u) : v ∈ l ∨ v = u := by
  rcases List.mem_or_eq_of_mem_set h with h | h
  · exact Or.inl h
  · exact Or.inr h

/-! ### Defaults, reads, writes -/

/-- A fresh default is tight. -/
theorem defaultForTy_tight : ∀ {T : Ty}, T.defaultOkS = true → (defaultForTy T).tight T := by
  intro T
  induction T using defaultForTy.induct
    (motive2 := fun l => ∀ (s : Name), (∀ nt ∈ l, lookupBy nt.1 (structDef s) = some nt.2 ∧
      nt.2.defaultOkS = true) → tightFields s (defaultForFields l)) with
  | case1 => intro _; simp only [defaultForTy, SVal.tight]
  | case2 => intro _; simp only [defaultForTy, SVal.tight]
  | case3 => intro _; simp only [defaultForTy, SVal.tight]
  | case4 name ih =>
    intro h
    have hs : name ∈ defaultOkStructs := by simpa only [Ty.defaultOkS, decide_eq_true_eq] using h
    obtain ⟨hnd, hok⟩ := struct_ok hs
    rw [defaultForTy]
    exact ih name fun nt hm => ⟨lookupBy_eq_of_nodup hnd hm, hok nt hm⟩
  | case5 elem => intro _; simp only [defaultForTy, SVal.tight, and_self, implies_true,
                               List.not_mem_nil, false_implies, tightElems]
  | case6 elem n ih =>
    intro h
    have hE : elem.defaultOkS = true := by simpa only [Ty.defaultOkS] using h
    rw [defaultForTy]
    refine ⟨rfl, tightElems_iff.mpr fun v hv => ?_⟩
    rw [List.eq_of_mem_replicate hv]; exact ih hE
  | case7 key value ih =>
    intro _
    rw [defaultForTy]
    exact ⟨fun _ => rfl, trivial⟩
  | case8 => simp only [defaultForFields, tightFields]
  | case9 n t rest iht ihrest =>
    rename_i s h
    obtain ⟨hl, hok⟩ := h (n, t) (List.mem_cons_self ..)
    simp only [defaultForFields, tightFields, hl]
    exact ⟨iht hok, ihrest s fun nt hm => h nt (List.mem_cons_of_mem _ hm)⟩

/-- What `find` reaches in a tight value is tight. -/
theorem find_tight : ∀ {segs : List Seg} {v : Semantics.SVal} {T T' : Ty} {w : Semantics.SVal},
    v.canon T → v.tight T → T.okDeep = true → tyAtSegs T segs = some T' → v.find segs = .ok w →
      w.tight T'
  | [], v, T, T', w, _, ht, _, hs, hf => by
    simp only [tyAtSegs, Option.some.injEq] at hs
    subst hs
    rw [SemanticsProperties.SVal.find_nil] at hf; cases hf; exact ht
  | seg :: rest, v, T, T', w, h, ht, hok, hs, hf => by
    simp only [tyAtSegs] at hs
    cases hseg : segTy T seg with
    | none => rw [hseg] at hs; exact nomatch hs
    | some Surface.Tm =>
      rw [hseg] at hs
      have hokm := okDeep_segTy hok hseg
      cases seg with
      | field n =>
        cases T with
        | prim _ => simp only [segTy, reduceCtorEq] at hseg
        | ref r =>
          cases r with
          | struct s =>
            obtain ⟨fields, rfl, -, hfs⟩ := canon_struct h
            simp only [segTy] at hseg
            simp only [Semantics.SVal.find] at hf
            split at hf
            · rename_i v' hl
              obtain ⟨Tf, hd, hv⟩ := canonFields_lookup hfs hl
              rw [hseg] at hd; cases hd
              exact find_tight hv (tightFields_lookup ht hl hseg) hokm hs hf
            · exact nomatch hf
          | array _ => simp only [segTy, reduceCtorEq] at hseg
          | fixed _ _ => simp only [segTy, reduceCtorEq] at hseg
          | mapping _ _ => simp only [segTy, reduceCtorEq] at hseg
      | «at» i =>
        cases T with
        | prim _ => simp only [segTy, reduceCtorEq] at hseg
        | ref r =>
          cases r with
          | struct _ => simp only [segTy, reduceCtorEq] at hseg
          | array E =>
            obtain ⟨elems, sh, rfl, he, hsh⟩ := canon_array h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            obtain ⟨-, -, hte, hts⟩ := ht
            simp only [Semantics.SVal.find] at hf
            split at hf
            · have hm := List.get_mem (elems ++ sh) ⟨i.toNat, by omega⟩
              refine find_tight (canonElems_mem (canonElems_append he hsh) hm) ?_ hokm hs hf
              rcases List.mem_append.mp hm with hm | hm
              · exact tightElems_iff.mp hte _ hm
              · exact tightElems_iff.mp hts _ hm
            · exact nomatch hf
          | fixed E _ =>
            obtain ⟨elems, sh, rfl, -, he, hsh⟩ := canon_fixed h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            obtain ⟨rfl, hte⟩ := ht
            simp only [Semantics.SVal.find] at hf
            split at hf
            · have hm := List.get_mem (elems ++ []) ⟨i.toNat, by omega⟩
              refine find_tight (canonElems_mem (canonElems_append he hsh) hm) ?_ hokm hs hf
              exact tightElems_iff.mp hte _ (by simp only [List.get_eq_getElem, List.append_nil,
                                                    List.getElem_mem])
            · exact nomatch hf
          | mapping K V =>
            obtain ⟨es, d, rfl, -, hes, hdd, hd⟩ := canon_map h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            obtain ⟨-, htes⟩ := ht
            simp only [Semantics.SVal.find] at hf
            split at hf
            · rename_i v' hl
              exact find_tight (canonEntries_lookup hes hl) (tightEntries_lookup htes hl) hokm hs hf
            · subst hdd
              exact find_tight hd (defaultForTy_tight (okDeep_defaultOkS hokm)) hokm hs hf

theorem IdxLive.child {v c : Semantics.SVal} {seg : Seg} {rest : List Seg} (h : IdxLive v (seg :: rest))
    (hc : v.find [seg] = .ok c) : IdxLive c rest := by
  intro pre i hrest es sh fx hf
  refine h (seg :: pre) i (by simp only [hrest, List.cons_append]) es sh fx ?_
  have := SVal.find_append v [seg] pre
  simp only [List.singleton_append] at this
  rw [this, hc]; exact hf

/-- A word at a primitive type has no path below it. -/
theorem save_prim_cons {v : Semantics.SVal} {p : PrimTy} (hc : v.canon (.prim p)) (seg : Seg)
    (rest : List Seg) (new : Semantics.SVal) : ∃ e, v.save (seg :: rest) new = .error e := by
  cases v with
  | prim _ => cases seg <;> exact ⟨_, rfl⟩
  | struct _ => cases p <;> simp only [SVal.canon] at hc
  | array _ _ _ => cases p <;> simp only [SVal.canon] at hc
  | map _ _ => cases p <;> simp only [SVal.canon] at hc

/-- Saving a tight value at a path whose mappings are indexed by numbers,
into a live slot when it is a word, keeps the tree tight. -/
theorem save_tight : ∀ {segs : List Seg} {v : Semantics.SVal} {T T' : Ty} {new w : Semantics.SVal},
    v.canon T → v.tight T → T.okDeep = true → tyAtSegs T segs = some T' → KeysOK T segs →
    (T'.isPrimitive = true → IdxLive v segs) → new.tight T' → v.save segs new = .ok w →
      w.tight T
  | [], v, T, T', new, w, _, _, _, hs, _, _, hn, hf => by
    simp only [tyAtSegs, Option.some.injEq] at hs
    subst hs
    rw [SVal.save_nil] at hf; cases hf; exact hn
  | seg :: rest, v, T, T', new, w, h, ht, hok, hs, hk, hlive, hn, hf => by
    simp only [tyAtSegs] at hs
    obtain ⟨hk₁, hk₂⟩ := hk
    cases hseg : segTy T seg with
    | none => rw [hseg] at hs; exact nomatch hs
    | some Surface.Tm =>
      rw [hseg] at hs
      simp only [hseg] at hk₂
      have hokm := okDeep_segTy hok hseg
      cases seg with
      | field n =>
        cases T with
        | prim _ => simp only [segTy, reduceCtorEq] at hseg
        | ref r =>
          cases r with
          | struct s =>
            obtain ⟨fields, rfl, -, hfs⟩ := canon_struct h
            simp only [segTy] at hseg
            simp only [Semantics.SVal.save] at hf
            split at hf
            · rename_i old hl
              obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
              cases hf
              obtain ⟨Tf, hd, hv⟩ := canonFields_lookup hfs hl
              rw [hseg] at hd; cases hd
              have hchild : (Semantics.SVal.struct fields).find [.field n] = .ok old := by
                simp only [Semantics.SVal.find, hl, SemanticsProperties.SVal.find_nil]
              exact tightFields_setBy ht hseg (save_tight hv (tightFields_lookup ht hl hseg) hokm
                hs hk₂ (fun hp => (hlive hp).child hchild) hn hup)
            · exact nomatch hf
          | array _ => simp only [segTy, reduceCtorEq] at hseg
          | fixed _ _ => simp only [segTy, reduceCtorEq] at hseg
          | mapping _ _ => simp only [segTy, reduceCtorEq] at hseg
      | «at» i =>
        cases T with
        | prim _ => simp only [segTy, reduceCtorEq] at hseg
        | ref r =>
          cases r with
          | struct _ => simp only [segTy, reduceCtorEq] at hseg
          | array E =>
            obtain ⟨elems, sh, rfl, he, hsh⟩ := canon_array h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            obtain ⟨-, hpr, hte, hts⟩ := ht
            simp only [Semantics.SVal.save] at hf
            split at hf
            · rename_i hb
              obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
              cases hf
              have hm := List.get_mem (elems ++ sh) ⟨i.toNat, hb.2⟩
              have hct : ((elems ++ sh).get ⟨i.toNat, hb.2⟩).tight E := by
                rcases List.mem_append.mp hm with hm | hm
                · exact tightElems_iff.mp hte _ hm
                · exact tightElems_iff.mp hts _ hm
              have hcc := canonElems_mem (canonElems_append he hsh) hm
              have hchild : (Semantics.SVal.array elems sh false).find [.at i] =
                  .ok ((elems ++ sh).get ⟨i.toNat, hb.2⟩) := by
                simp only [Semantics.SVal.find, dif_pos hb, SemanticsProperties.SVal.find_nil]
              have hupt := save_tight hcc hct hokm hs hk₂ (fun hp => (hlive hp).child hchild) hn hup
              have hall : ∀ x ∈ (elems ++ sh).set i.toNat up, x.tight E := by
                intro x hx
                rcases mem_set_or hx with hx | rfl
                · rcases List.mem_append.mp hx with hx | hx
                  · exact tightElems_iff.mp hte _ hx
                  · exact tightElems_iff.mp hts _ hx
                · exact hupt
              refine ⟨fun hf => absurd hf (by simp only [okDeep_defaultOkS hokm, Bool.true_eq_false,
                                                  not_false_eq_true]), ?_,
                tightElems_iff.mpr fun x hx => hall x (List.mem_of_mem_take hx),
                tightElems_iff.mpr fun x hx => hall x (List.mem_of_mem_drop hx)⟩
              intro hp
              cases rest with
              | cons s' r' =>
                obtain ⟨p, rfl⟩ : ∃ p, E = .prim p := by
                  cases E with
                  | prim p => exact ⟨p, rfl⟩
                  | ref _ => simp only [Ty.isPrimitive, Bool.false_eq_true] at hp
                obtain ⟨e, he'⟩ := save_prim_cons hcc s' r' new
                rw [he'] at hup; exact nomatch hup
              | nil =>
                simp only [tyAtSegs, Option.some.injEq] at hs
                subst hs
                have hl := hlive hp [] i rfl elems sh false (SemanticsProperties.SVal.find_nil _)
                have hdrop : ((elems ++ sh).set i.toNat up).drop elems.length = sh := by
                  rw [List.set_append_left _ _ hl.2,
                    List.drop_left' (by simp only [List.length_set])]
                rw [hdrop]
                exact hpr hp
            · exact nomatch hf
          | fixed E n =>
            obtain ⟨elems, sh, rfl, hlen, he, hsh⟩ := canon_fixed h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            obtain ⟨rfl, hte⟩ := ht
            simp only [Semantics.SVal.save] at hf
            split at hf
            · rename_i hb
              obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
              cases hf
              have hm := List.get_mem (elems ++ []) ⟨i.toNat, hb.2⟩
              have hmm : (elems ++ []).get ⟨i.toNat, hb.2⟩ ∈ elems := by
                simp only [List.get_eq_getElem, List.append_nil, List.getElem_mem]
              have hcc := canonElems_mem (canonElems_append he hsh) hm
              have hchild : (Semantics.SVal.array elems [] true).find [.at i] =
                  .ok ((elems ++ []).get ⟨i.toNat, hb.2⟩) := by
                simp only [Semantics.SVal.find, dif_pos hb, SemanticsProperties.SVal.find_nil]
              have hupt := save_tight hcc (tightElems_iff.mp hte _ hmm) hokm hs hk₂
                (fun hp => (hlive hp).child hchild) hn hup
              refine ⟨?_, tightElems_iff.mpr fun x hx => ?_⟩
              · simp only [List.append_nil, List.drop_eq_nil_iff, List.length_set, Nat.le_refl]
              · have hx' := List.mem_of_mem_take hx
                rcases mem_set_or hx' with hx' | rfl
                · exact tightElems_iff.mp hte _ (by simpa only [List.append_nil] using hx')
                · exact hupt
            · exact nomatch hf
          | mapping K V =>
            obtain ⟨es, d, rfl, -, hes, hdd, hd⟩ := canon_map h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            obtain ⟨-, htes⟩ := ht
            have hkey : K.isKey = true := hk₁ K V rfl
            simp only [Semantics.SVal.save] at hf
            split at hf
            · rename_i old hl
              obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
              cases hf
              have hchild : (Semantics.SVal.map es d).find [.at i] = .ok old := by
                simp only [Semantics.SVal.find, hl, SemanticsProperties.SVal.find_nil]
              exact ⟨fun h => absurd h (by simp only [hkey, Bool.true_eq_false, not_false_eq_true]),
                                               tightEntries_setBy htes
                (save_tight (canonEntries_lookup hes hl) (tightEntries_lookup htes hl) hokm hs hk₂
                  (fun hp => (hlive hp).child hchild) hn hup)⟩
            · rename_i hl
              obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
              cases hf
              have hchild : (Semantics.SVal.map es d).find [.at i] = .ok d := by
                simp only [Semantics.SVal.find, hl, SemanticsProperties.SVal.find_nil]
              subst hdd
              exact ⟨fun h => absurd h (by simp only [hkey, Bool.true_eq_false, not_false_eq_true]),
                                               tightEntries_setBy htes
                (save_tight hd (defaultForTy_tight (okDeep_defaultOkS hokm)) hokm hs hk₂
                  (fun hp => (hlive hp).child hchild) hn hup)⟩

/-! ### `delete`, copies, pushes -/

theorem defaultOf_prim {v : Semantics.SVal} {p : PrimTy} (h : v.canon (.prim p)) :
    v.defaultOf = defaultForTy (.prim p) := by
  cases v with
  | prim pv => cases p <;> cases pv <;> simp_all only [SVal.canon, Semantics.SVal.defaultOf,
                                            defaultForTy]
  | struct _ => cases p <;> simp only [SVal.canon] at h
  | array _ _ _ => cases p <;> simp only [SVal.canon] at h
  | map _ _ => cases p <;> simp only [SVal.canon] at h

theorem defaultOfElems_prim {p : PrimTy} : ∀ {elems : List Semantics.SVal}, canonElems (.prim p) elems →
    ∀ w ∈ SVal.defaultOf.defaultOfElems elems, w = defaultForTy (.prim p)
  | [], _, w, hw => by simp only [SVal.defaultOf.defaultOfElems, List.not_mem_nil] at hw
  | v :: rest, h, w, hw => by
    simp only [SVal.defaultOf.defaultOfElems, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact defaultOf_prim h.1
    · exact defaultOfElems_prim h.2 w hw

theorem member_okDeep {s n : Name} {T : Ty} (hs : (Ty.ref (.struct s)).okDeep = true)
    (h : lookupBy n (structDef s) = some T) : T.okDeep = true :=
  struct_okDeep (by simpa only [Ty.okDeep, decide_eq_true_eq] using hs) (n,
                        T) (lookupBy_eq_some_mem h)

mutual

/-- `delete` keeps a value tight: words cleared, arrays emptied into their
cleared slots, mappings untouched. -/
theorem Semantics.SVal.defaultOf_tight : ∀ {v : Semantics.SVal} {T : Ty}, v.canon T → v.tight T → T.okDeep = true →
    v.defaultOf.tight T
  | .prim pv, .prim _, _, _, _ => by cases pv <;> trivial
  | .struct fields, .ref (.struct s), hc, ht, hok =>
    Semantics.SVal.defaultOfFields_tight hc.2 ht (fun hl => member_okDeep hok hl)
  | .array elems sh false, .ref (.array E), hc, ht, hok => by
    have hE : E.okDeep = true := by simpa only [Ty.okDeep] using hok
    refine ⟨fun hf => absurd hf (by simp only [okDeep_defaultOkS hE, Bool.true_eq_false,
                                        not_false_eq_true]), fun hp w hw => ?_, trivial,
      tightElems_iff.mpr fun w hw => ?_⟩
    · rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨p, rfl⟩ : ∃ p, E = .prim p := by
          cases E with
          | prim p => exact ⟨p, rfl⟩
          | ref _ => simp only [Ty.isPrimitive, Bool.false_eq_true] at hp
        exact defaultOfElems_prim hc.2.1 w hw
      · exact ht.2.1 hp w hw
    · rcases List.mem_append.mp hw with hw | hw
      · exact tightElems_iff.mp (Semantics.SVal.defaultOfElems_tight hc.2.1 ht.2.2.1 hE) w hw
      · exact tightElems_iff.mp ht.2.2.2 w hw
  | .array elems sh true, .ref (.fixed E n), hc, ht, hok =>
    ⟨ht.1, Semantics.SVal.defaultOfElems_tight hc.2.2.1 ht.2 (by simpa only [Ty.okDeep] using hok)⟩
  | .array _ _ true, .ref (.array _), hc, _, _ => nomatch hc.1
  | .array _ _ false, .ref (.fixed _ _), hc, _, _ => nomatch hc.1
  | .map _ _, .ref (.mapping _ _), _, ht, _ => ht
  | .prim pv, .ref _, hc, _, _ => by cases pv <;> exact hc.elim
  | .struct _, .prim _, hc, _, _ | .array _ _ _, .prim _, hc, _, _ | .map _ _, .prim _, hc, _, _ =>
    hc.elim
  | .struct _, .ref (.array _), hc, _, _ | .struct _, .ref (.mapping _ _), hc, _, _
  | .struct _, .ref (.fixed _ _), hc, _, _ => hc.elim
  | .array _ _ _, .ref (.struct _), hc, _, _ | .array _ _ _, .ref (.mapping _ _), hc, _, _ =>
    hc.elim
  | .map _ _, .ref (.struct _), hc, _, _ | .map _ _, .ref (.array _), hc, _, _
  | .map _ _, .ref (.fixed _ _), hc, _, _ => hc.elim

theorem Semantics.SVal.defaultOfFields_tight {s : Name} :
    ∀ {fields : List (Name × Semantics.SVal)}, canonFields s fields → tightFields s fields →
      (∀ {n T}, lookupBy n (structDef s) = some T → T.okDeep = true) →
      tightFields s (SVal.defaultOf.defaultOfFields fields)
  | [], _, _, _ => trivial
  | (n, v) :: rest, hc, ht, hok => by
    refine ⟨?_, Semantics.SVal.defaultOfFields_tight hc.2 ht.2 hok⟩
    have h1 := hc.1
    have h2 := ht.1
    revert h1 h2
    cases hl : lookupBy n (structDef s) with
    | none => intro _ _; trivial
    | some T => intro h1 h2; exact Semantics.SVal.defaultOf_tight h1 h2 (hok hl)

theorem Semantics.SVal.defaultOfElems_tight {E : Ty} :
    ∀ {elems : List Semantics.SVal}, canonElems E elems → tightElems E elems → E.okDeep = true →
      tightElems E (SVal.defaultOf.defaultOfElems elems)
  | [], _, _, _ => trivial
  | _ :: _, hc, ht, hE =>
    ⟨Semantics.SVal.defaultOf_tight hc.1 ht.1 hE, Semantics.SVal.defaultOfElems_tight hc.2 ht.2 hE⟩

end

mutual

/-- A value laid on fresh slots is tight: nothing is past its arrays' ends. -/
theorem Semantics.SVal.strip_tight : ∀ {v : Semantics.SVal} {T : Ty}, v.tight T → v.strip.tight T
  | .prim _, _, h => by simpa only [Semantics.SVal.strip] using h
  | .struct fields, .ref (.struct _), h => Semantics.SVal.stripFields_tight h
  | .array _ _ _, .ref (.array _), h =>
    ⟨(fun hE => by obtain ⟨h1, -⟩ := h.1 hE; subst h1; exact ⟨rfl, rfl⟩),
      (fun _ w hw => by simp only [List.not_mem_nil] at hw), Semantics.SVal.stripElems_tight h.2.2.1,
          trivial⟩
  | .array _ _ _, .ref (.fixed _ _), h => ⟨rfl, Semantics.SVal.stripElems_tight h.2⟩
  | .map _ _, _, h => by simpa only [Semantics.SVal.strip] using h
  | .struct _, .prim _, _ | .struct _, .ref (.array _), _ | .struct _, .ref (.mapping _ _), _
  | .struct _, .ref (.fixed _ _), _ => trivial
  | .array _ _ _, .prim _, _ | .array _ _ _, .ref (.struct _), _
  | .array _ _ _, .ref (.mapping _ _), _ => trivial

theorem Semantics.SVal.stripFields_tight {s : Name} :
    ∀ {fields : List (Name × Semantics.SVal)}, tightFields s fields →
      tightFields s (SVal.strip.stripFields fields)
  | [], _ => trivial
  | (n, v) :: rest, h => by
    refine ⟨?_, Semantics.SVal.stripFields_tight h.2⟩
    have h1 := h.1
    revert h1
    cases lookupBy n (structDef s) with
    | none => intro _; trivial
    | some T => exact fun h => Semantics.SVal.strip_tight h

theorem Semantics.SVal.stripElems_tight {E : Ty} :
    ∀ {elems : List Semantics.SVal}, tightElems E elems → tightElems E (SVal.strip.stripElems elems)
  | [], _ => trivial
  | _ :: _, h => ⟨Semantics.SVal.strip_tight h.1, Semantics.SVal.stripElems_tight h.2⟩

end

mutual

/-- **A copy keeps storage tight**: the old slots past the new length are
cleared, the ones past the old length kept, and a fixed-size array is
copied over one of its own length. -/
theorem Semantics.SVal.overlay_tight {old new : Semantics.SVal} {T : Ty} (hoc : old.canon T) (hot : old.tight T)
    (hnc : new.canon T) (hnt : new.tight T) (hok : T.okDeep = true) :
    (old.overlay new).tight T := by
  match new with
  | .prim p => cases old <;> simpa only [Semantics.SVal.overlay, Semantics.SVal.strip] using hnt
  | .struct nfs =>
      cases old with
      | struct ofs =>
          cases T with
          | prim p => cases p <;> exact hnc.elim
          | ref r =>
              cases r with
              | struct s =>
                  exact Semantics.SVal.overlayFields_tight hoc.2 hot hnc.2 hnt
                    (fun hl => member_okDeep hok hl)
              | array _ => exact hnc.elim
              | fixed _ _ => exact hnc.elim
              | mapping _ _ => exact hnc.elim
      | prim _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_tight hnt
      | array _ _ _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_tight hnt
      | map _ _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_tight hnt
  | .array nel nsh nfx =>
      cases old with
      | array oel osh ofx =>
          cases T with
          | prim p => cases p <;> exact hnc.elim
          | ref r =>
              cases r with
              | array E =>
                  have hE : E.okDeep = true := by simpa only [Ty.okDeep] using hok
                  simp only [Semantics.SVal.overlay]
                  refine ⟨fun hf => absurd hf (by simp only [okDeep_defaultOkS hE,
                                                      Bool.true_eq_false, not_false_eq_true]),
                                                      fun hp w hw => ?_,
                    Semantics.SVal.overlayElems_tight (canonElems_append hoc.2.1 hoc.2.2)
                      (tightElems_iff.mpr fun x hx => ?_) hnc.2.1 hnt.2.2.1 hE,
                    tightElems_iff.mpr fun x hx => ?_⟩
                  · rcases List.mem_append.mp hw with hw | hw
                    · obtain ⟨p, rfl⟩ : ∃ p, E = .prim p := by
                        cases E with
                        | prim p => exact ⟨p, rfl⟩
                        | ref _ => simp only [Ty.isPrimitive, Bool.false_eq_true] at hp
                      exact defaultOfElems_prim (canonElems_drop _ hoc.2.1) w hw
                    · exact hot.2.1 hp w (List.mem_of_mem_drop hw)
                  · rcases List.mem_append.mp hx with hx | hx
                    · exact tightElems_iff.mp hot.2.2.1 x hx
                    · exact tightElems_iff.mp hot.2.2.2 x hx
                  · rcases List.mem_append.mp hx with hx | hx
                    · exact tightElems_iff.mp (SVal.defaultOfElems_tight
                        (canonElems_drop _ hoc.2.1)
                        (tightElems_iff.mpr fun y hy =>
                          tightElems_iff.mp hot.2.2.1 y (List.mem_of_mem_drop hy)) hE) x hx
                    · exact tightElems_iff.mp hot.2.2.2 x (List.mem_of_mem_drop hx)
              | fixed E n =>
                  have hE : E.okDeep = true := by simpa only [Ty.okDeep] using hok
                  have holen : oel.length = n := hoc.2.1
                  have hnlen : nel.length = n := hnc.2.1
                  obtain ⟨hsh, hote⟩ := hot
                  subst hsh
                  simp only [Semantics.SVal.overlay]
                  refine ⟨?_, Semantics.SVal.overlayElems_tight (canonElems_append hoc.2.2.1 hoc.2.2.2)
                    (by simpa only [List.append_nil] using hote) hnc.2.2.1 hnt.2 hE⟩
                  rw [hnlen, ← holen]; simp only [List.drop_length, defaultOf.defaultOfElems,
                                           Nat.sub_self, List.drop_nil, List.append_nil]
              | struct _ => exact hnc.elim
              | mapping _ _ => exact hnc.elim
      | prim _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_tight hnt
      | struct _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_tight hnt
      | map _ _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_tight hnt
  | .map ne nd =>
      cases old with
      | map oe od => simpa only [Semantics.SVal.overlay] using hot
      | prim _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_tight hnt
      | struct _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_tight hnt
      | array _ _ _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_tight hnt

theorem Semantics.SVal.overlayFields_tight {s : Name} {ofs nfs : List (Name × Semantics.SVal)}
    (hoc : canonFields s ofs) (hot : tightFields s ofs) (hnc : canonFields s nfs)
    (hnt : tightFields s nfs) (hok : ∀ {n T}, lookupBy n (structDef s) = some T → T.okDeep = true) :
    tightFields s (SVal.overlay.overlayFields ofs nfs) := by
  match nfs with
  | [] => trivial
  | (n, v) :: rest =>
      refine ⟨?_, Semantics.SVal.overlayFields_tight hoc hot hnc.2 hnt.2 hok⟩
      have h1 := hnc.1
      have h2 := hnt.1
      revert h1 h2
      cases hdef : lookupBy n (structDef s) with
      | none => intro _ _; trivial
      | some T =>
          intro h1 h2
          cases hl : lookupBy n ofs with
          | none => exact SVal.strip_tight h2
          | some o =>
              obtain ⟨T', hd', hoc'⟩ := canonFields_lookup hoc hl
              rw [hdef] at hd'
              cases hd'
              exact Semantics.SVal.overlay_tight hoc' (tightFields_lookup hot hl hdef) h1 h2 (hok hdef)

theorem Semantics.SVal.overlayElems_tight {E : Ty} {olds news : List Semantics.SVal}
    (hoc : canonElems E olds) (hot : tightElems E olds) (hnc : canonElems E news)
    (hnt : tightElems E news) (hE : E.okDeep = true) :
    tightElems E (SVal.overlay.overlayElems olds news) := by
  match olds, news with
  | o :: os, v :: rest =>
    exact ⟨Semantics.SVal.overlay_tight hoc.1 hot.1 hnc.1 hnt.1 hE,
      Semantics.SVal.overlayElems_tight hoc.2 hot.2 hnc.2 hnt.2 hE⟩
  | [], rest => simpa only [SVal.overlay.overlayElems] using SVal.stripElems_tight hnt
  | _ :: _, [] => trivial

end

/-! ### Memory copied back -/

/-- A value with no mapping and nothing past its arrays' ends: what a copy
out of memory gives. -/
def Semantics.SVal.plain : Semantics.SVal → Prop
  | .prim _ => True
  | .struct fields => plainFields fields
  | .array elems shadow _ => shadow = [] ∧ plainElems elems
  | .map _ _ => False
where
  plainFields : List (Name × Semantics.SVal) → Prop
    | [] => True
    | (_, v) :: rest => v.plain ∧ plainFields rest
  plainElems : List Semantics.SVal → Prop
    | [] => True
    | v :: rest => v.plain ∧ plainElems rest

open Semantics.SVal.plain (plainFields plainElems)

mutual

theorem plain_tight : ∀ {v : Semantics.SVal} {T : Ty}, v.plain → v.canon T → T.okDeep = true → v.tight T
  | .prim _, .prim _, _, _, _ => trivial
  | .prim pv, .ref _, _, hc, _ => by cases pv <;> exact hc.elim
  | .struct fields, .ref (.struct s), hp, hc, hok =>
    plainFields_tight hp hc.2 (fun hl => member_okDeep hok hl)
  | .array elems sh _, .ref (.array E), hp, hc, hok => by
    obtain ⟨rfl, hpe⟩ := hp
    have hE : E.okDeep = true := by simpa only [Ty.okDeep] using hok
    exact ⟨fun hf => absurd hf (by simp only [okDeep_defaultOkS hE, Bool.true_eq_false,
                                       not_false_eq_true]),
                                       fun _ w hw => by simp only [List.not_mem_nil] at hw,
      plainElems_tight hpe hc.2.1 hE, trivial⟩
  | .array elems sh _, .ref (.fixed E _), hp, hc, hok => by
    obtain ⟨rfl, hpe⟩ := hp
    exact ⟨rfl, plainElems_tight hpe hc.2.2.1 (by simpa only [Ty.okDeep] using hok)⟩
  | .map _ _, .prim _, hp, _, _ | .map _ _, .ref _, hp, _, _ => hp.elim
  | .struct _, .prim _, _, _, _ | .struct _, .ref (.array _), _, _, _
  | .struct _, .ref (.mapping _ _), _, _, _ | .struct _, .ref (.fixed _ _), _, _, _ => trivial
  | .array _ _ _, .prim _, _, _, _ | .array _ _ _, .ref (.struct _), _, _, _
  | .array _ _ _, .ref (.mapping _ _), _, _, _ => trivial

theorem plainFields_tight {s : Name} :
    ∀ {fields : List (Name × Semantics.SVal)}, plainFields fields → canonFields s fields →
      (∀ {n T}, lookupBy n (structDef s) = some T → T.okDeep = true) → tightFields s fields
  | [], _, _, _ => trivial
  | (n, v) :: rest, hp, hc, hok => by
    refine ⟨?_, plainFields_tight hp.2 hc.2 hok⟩
    have h1 := hc.1
    revert h1
    cases hl : lookupBy n (structDef s) with
    | none => intro _; trivial
    | some T => intro h1; exact plain_tight hp.1 h1 (hok hl)

theorem plainElems_tight {E : Ty} :
    ∀ {elems : List Semantics.SVal}, plainElems elems → canonElems E elems → E.okDeep = true →
      tightElems E elems
  | [], _, _, _ => trivial
  | _ :: _, hp, hc, hE => ⟨plain_tight hp.1 hc.1 hE, plainElems_tight hp.2 hc.2 hE⟩

end

theorem copyMFields_plain {s : Semantics.State} {rem : List Nat}
    (IH : ∀ {mv : Semantics.MVal} {sv : Semantics.SVal}, copyMToSt s rem mv = .ok sv → sv.plain) :
    ∀ {fields : List (Name × Semantics.MVal)} {sfields : List (Name × Semantics.SVal)},
      copyMFields s rem fields = .ok sfields → plainFields sfields
  | [], sfields, hcopy => by
    simp only [copyMFields, Except.ok.injEq] at hcopy
    subst hcopy; trivial
  | (n, v) :: rest, sfields, hcopy => by
    rw [copyMFields] at hcopy
    obtain ⟨sv, hv, hcopy⟩ := bind_ok_inv hcopy
    obtain ⟨srest, hrest, hcopy⟩ := bind_ok_inv hcopy
    cases hcopy
    exact ⟨IH hv, copyMFields_plain IH hrest⟩

theorem copyMElems_plain {s : Semantics.State} {rem : List Nat}
    (IH : ∀ {mv : Semantics.MVal} {sv : Semantics.SVal}, copyMToSt s rem mv = .ok sv → sv.plain) :
    ∀ {elems : List Semantics.MVal} {selems : List Semantics.SVal}, copyMElems s rem elems = .ok selems →
      plainElems selems
  | [], selems, hcopy => by
    simp only [copyMElems, Except.ok.injEq] at hcopy
    subst hcopy; trivial
  | v :: rest, selems, hcopy => by
    rw [copyMElems] at hcopy
    obtain ⟨sv, hv, hcopy⟩ := bind_ok_inv hcopy
    obtain ⟨srest, hrest, hcopy⟩ := bind_ok_inv hcopy
    cases hcopy
    exact ⟨IH hv, copyMElems_plain IH hrest⟩

/-- A copy out of memory has no mapping and nothing past its arrays' ends. -/
theorem copyMToSt_plain {s : Semantics.State} {rem : List Nat} :
    ∀ {mv : Semantics.MVal} {sv : Semantics.SVal}, copyMToSt s rem mv = .ok sv → sv.plain := by
  intro mv sv hcopy
  cases mv with
  | prim p =>
    cases p <;> simp only [copyMToSt, Except.ok.injEq] at hcopy <;> subst hcopy <;> trivial
  | ref id =>
    by_cases hmem : id ∈ rem
    · simp only [copyMToSt, hmem, dif_pos] at hcopy
      split at hcopy
      · obtain ⟨sfields, hfs, hcopy⟩ := bind_ok_inv hcopy
        cases hcopy
        exact copyMFields_plain (fun hc' => copyMToSt_plain hc') hfs
      · obtain ⟨selems, hes, hcopy⟩ := bind_ok_inv hcopy
        cases hcopy
        exact ⟨rfl, copyMElems_plain (fun hc' => copyMToSt_plain hc') hes⟩
      · exact nomatch hcopy
    · simp only [copyMToSt, hmem, dif_neg, not_false_iff] at hcopy
      exact nomatch hcopy
termination_by rem.length
decreasing_by all_goals
  (have h1 := List.length_erase_of_mem hmem
   have h2 := List.length_pos_of_mem hmem
   omega)

/-! ### The state -/

/-- What a run keeps beyond `Canon`, of the global state: tight storage.
The scoped state adds its aliases (`Tight`). -/
structure Semantics.Tight (C : Contract) (σ : Semantics.State) : Prop where
  storage : TightStorage C σ.storage

/-- Every root's type has well-formed defaults all the way down. -/
def DeepOk (C : Contract) : Prop := ∀ r T, lookupBy r C.vars = some T → T.okDeep = true

namespace Semantics.Tight

variable {H : HeapTy} {σ σ' : State}

theorem of_eq (ht : Tight C σ) (hs : σ'.storage = σ.storage) : Tight C σ' :=
  ⟨hs ▸ ht.storage⟩

theorem find (hd : DeepOk C) (hc : Canon C H σ) (ht : Tight C σ) {r : Name} {segs : List Seg}
    {T' : Ty} {w : SVal} (hT : C.layout.tyAt r segs = some T') (hf : σ.findStorage r segs = .ok w) :
    w.tight T' := by
  obtain ⟨T, hr, hs⟩ := Layout.tyAt_split hT
  obtain ⟨V, hV, hcV⟩ := hc.storage.2 r T hr
  simp only [State.findStorage, hV] at hf
  exact find_tight hcV (ht.storage r T V hr hV) (hd r T hr) hs hf

theorem save (hd : DeepOk C) (hc : Canon C H σ) (ht : Tight C σ) {r : Name} {segs : List Seg}
    {T' : Ty} {new : SVal} (hT : C.layout.tyAt r segs = some T')
    (hk : ∀ T, lookupBy r C.vars = some T → KeysOK T segs)
    (hlive : T'.isPrimitive = true → ∀ V, lookupBy r σ.storage = some V → IdxLive V segs)
    (hnew : new.tight T') (h : σ.saveStorage r segs new = .ok σ') : Tight C σ' := by
  obtain ⟨T, hr, hs⟩ := Layout.tyAt_split hT
  obtain ⟨V, hV, hcV⟩ := hc.storage.2 r T hr
  obtain ⟨_, up, hV', hup, rfl⟩ := SemanticsProperties.State.saveStorage_ok_inv h
  cases hV.symm.trans hV'
  refine ⟨fun r' T'' v hr' hv => ?_⟩
  change lookupBy r' (setBy r up σ.storage) = _ at hv
  by_cases he : r' = r
  · subst he
    rw [lookupBy_setBy_self] at hv; cases hv
    cases hr.symm.trans hr'
    exact save_tight hcV (ht.storage r' T V hr hV) (hd r' T hr) hs (hk T hr)
      (fun hp => hlive hp V hV) hnew hup
  · rw [lookupBy_setBy_ne he] at hv; exact ht.storage r' T'' v hr' hv

theorem write (hd : DeepOk C) (hc : Canon C H σ) (ht : Tight C σ) {r : Name} {segs : List Seg}
    {T' : Ty} {new : SVal} (hT : C.layout.tyAt r segs = some T')
    (hk : ∀ T, lookupBy r C.vars = some T → KeysOK T segs)
    (hlive : T'.isPrimitive = true → ∀ V, lookupBy r σ.storage = some V → IdxLive V segs)
    (hnc : new.canon T') (hnt : new.tight T') (h : σ.writeStorage r segs new = .ok σ') :
    Tight C σ' := by
  rcases State.writeStorage_ok_inv h with h | ⟨cur, hcur, h⟩
  · exact ht.save hd hc hT hk hlive hnt h
  · obtain ⟨T, hr, hs⟩ := Layout.tyAt_split hT
    exact ht.save hd hc hT hk hlive (SVal.overlay_tight (hc.find hT hcur) (ht.find hd hc hT hcur)
      hnc hnt (okDeep_tyAtSegs (hd r T hr) hs)) h

end Semantics.Tight

/-! ### Paths -/

theorem append_single_ne {l l' : List Seg} {a b : Seg} (h : l ++ [a] = l' ++ [b]) :
    l = l' ∧ a = b := by
  have := List.append_inj' h rfl
  simpa only [List.cons.injEq, and_true] using this

/-! ### Pushes and pops -/

section Effects

variable {H : HeapTy} {σ σ' : Semantics.State}

theorem pushSlot_tight {E : Ty} {shadow : List Semantics.SVal} (hE : E.defaultOkS = true)
    (hsh : tightElems E shadow) :
    (Semantics.pushSlot E shadow).1.tight E ∧ (∀ w ∈ (Semantics.pushSlot E shadow).2, w ∈ shadow) := by
  cases shadow with
  | nil => exact ⟨defaultForTy_tight hE, fun w hw => by simp only [Semantics.pushSlot,
      List.not_mem_nil] at hw⟩
  | cons c rest =>
    refine ⟨?_, fun w hw => List.mem_cons_of_mem _ hw⟩
    simp only [Semantics.pushSlot]
    split
    · exact defaultForTy_tight hE
    · exact hsh.1

/-- An array one element longer, the slot it took gone from past its end. -/
theorem pushed_tight {E : Ty} {elems shadow shadow' : List Semantics.SVal} {x : Semantics.SVal}
    (hE : E.okDeep = true) (ht : (Semantics.SVal.array elems shadow false).tight (.ref (.array E)))
    (hx : x.tight E) (hsub : ∀ w ∈ shadow', w ∈ shadow) :
    (Semantics.SVal.array (elems ++ [x]) shadow' false).tight (.ref (.array E)) := by
  obtain ⟨-, hpr, hte, hts⟩ := ht
  refine ⟨fun hf => absurd hf (by simp only [okDeep_defaultOkS hE, Bool.true_eq_false,
                                      not_false_eq_true]), fun hp w hw => hpr hp w (hsub w hw),
    tightElems_iff.mpr fun w hw => ?_, tightElems_iff.mpr fun w hw => tightElems_iff.mp hts w (hsub w hw)⟩
  rcases List.mem_append.mp hw with hw | hw
  · exact tightElems_iff.mp hte w hw
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; subst hw; exact hx

theorem arr_okDeep {E : Ty} (hd : DeepOk C) {r : Name} {segs : List Seg}
    (hT : C.layout.tyAt r segs = some (.ref (.array E))) : E.okDeep = true := by
  obtain ⟨T, hr, hs⟩ := Layout.tyAt_split hT
  simpa only [Ty.okDeep] using okDeep_tyAtSegs (hd r T hr) hs

theorem pushAt_tight (hd : DeepOk C) (hc : Canon C H σ) (ht : Semantics.Tight C σ) {E : Ty} {r : Name}
    {segs : List Seg} {val : Semantics.SVal → Res Semantics.SVal} (hT : C.layout.tyAt r segs = some (.ref (.array E)))
    (hk : ∀ T, lookupBy r C.vars = some T → KeysOK T segs)
    (hval : ∀ slot v, slot.tight E → val slot = .ok v → v.tight E)
    (h : pushAt σ E r segs val = .ok σ') : Semantics.Tight C σ' := by
  have hE := arr_okDeep hd hT
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  have hts := ht.find hd hc hT hsv
  obtain ⟨elems, shadow, rfl, -, -⟩ := canon_array (hc.find hT hsv)
  obtain ⟨newElem, hnew, h⟩ := bind_ok_inv h
  obtain ⟨hs1, hs2⟩ := pushSlot_tight (okDeep_defaultOkS hE) hts.2.2.2
  exact ht.save hd hc hT hk (fun hp => by simp only [Ty.isPrimitive, Bool.false_eq_true] at hp)
    (pushed_tight hE hts (hval _ _ hs1 hnew) hs2) h

theorem pushPlaceAt_tight (hd : DeepOk C) (hc : Canon C H σ) (ht : Semantics.Tight C σ) {E : Ty} {r : Name}
    {segs : List Seg} {n : Int} (hT : C.layout.tyAt r segs = some (.ref (.array E)))
    (hk : ∀ T, lookupBy r C.vars = some T → KeysOK T segs)
    (h : pushPlaceAt σ E r segs = .ok (σ', n)) : Semantics.Tight C σ' := by
  have hE := arr_okDeep hd hT
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  have hts := ht.find hd hc hT hsv
  obtain ⟨elems, shadow, rfl, -, -⟩ := canon_array (hc.find hT hsv)
  obtain ⟨σ₁, hσ₁, h⟩ := bind_ok_inv h
  cases h
  obtain ⟨hs1, hs2⟩ := pushSlot_tight (okDeep_defaultOkS hE) hts.2.2.2
  exact ht.save hd hc hT hk (fun hp => by simp only [Ty.isPrimitive, Bool.false_eq_true] at hp)
    (pushed_tight hE hts hs1 hs2) hσ₁

theorem popAt_tight (hd : DeepOk C) (hc : Canon C H σ) (ht : Semantics.Tight C σ) {E : Ty} {r : Name}
    {segs : List Seg} (hT : C.layout.tyAt r segs = some (.ref (.array E)))
    (hk : ∀ T, lookupBy r C.vars = some T → KeysOK T segs)
    (h : popAt σ E.isMapping r segs = .ok σ') : Semantics.Tight C σ' := by
  have hE := arr_okDeep hd hT
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  have hts := ht.find hd hc hT hsv
  obtain ⟨elems, shadow, rfl, he, hsh⟩ := canon_array (hc.find hT hsv)
  obtain ⟨-, hpr, hte, htsh⟩ := hts
  simp only at h
  split at h
  · exact nomatch h
  · rename_i last restRev hrev
    have hmem : ∀ v, v ∈ last :: restRev → v ∈ elems := by
      intro v hv; rw [← hrev] at hv; exact List.mem_reverse.mp hv
    have hlc := canonElems_mem he (hmem last List.mem_cons_self)
    have hlt := tightElems_iff.mp hte last (hmem last List.mem_cons_self)
    refine ht.save hd hc hT hk (fun hp => by simp only [Ty.isPrimitive,
                                                 Bool.false_eq_true] at hp) ?_ h
    refine ⟨fun hf => absurd hf (by simp only [okDeep_defaultOkS hE, Bool.true_eq_false,
                                        not_false_eq_true]), fun hp w hw => ?_,
      tightElems_iff.mpr fun v hv => tightElems_iff.mp hte v
        (hmem v (List.mem_cons_of_mem _ (List.mem_reverse.mp hv))), ?_⟩
    · rcases List.mem_cons.mp hw with rfl | hw
      · obtain ⟨p, rfl⟩ : ∃ p, E = .prim p := by
          cases E with
          | prim p => exact ⟨p, rfl⟩
          | ref _ => simp only [Ty.isPrimitive, Bool.false_eq_true] at hp
        simp only [Ty.isMapping, Bool.false_eq_true, ↓reduceIte]
        exact defaultOf_prim hlc
      · exact hpr hp w hw
    · refine ⟨?_, htsh⟩
      split
      · exact hlt
      · exact SVal.defaultOf_tight hlc hlt hE

end Effects

/-! ### What does not touch storage or aliases -/

section Frames

variable {σ σ' : Semantics.State}

/-- Storage and locals as they were: a write into memory, an allocation. -/
def Semantics.SE (σ σ' : Semantics.State) : Prop := σ'.storage = σ.storage ∧ σ'.env = σ.env

theorem Semantics.SE.tight (h : SE σ σ') (ht : Semantics.Tight C σ) : Semantics.Tight C σ' := ht.of_eq h.1

theorem Semantics.SE.trans {σ₁ σ₂ σ₃ : Semantics.State} (h₁ : SE σ₁ σ₂) (h₂ : SE σ₂ σ₃) : SE σ₁ σ₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

theorem memWriteField_se {id : Nat} {f : Name} {mv : Semantics.MVal}
    (h : memWriteField σ id f mv = .ok σ') : SE σ σ' := by
  obtain ⟨o, _, h⟩ := bind_ok_inv h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · exact nomatch h

theorem memWriteIndex_se {id : Nat} {i : Int} {mv : Semantics.MVal}
    (h : memWriteIndex σ id i mv = .ok σ') : SE σ σ' := by
  obtain ⟨o, _, h⟩ := bind_ok_inv h
  split at h
  · split at h
    · cases h; exact ⟨rfl, rfl⟩
    · exact nomatch h
  · exact nomatch h

theorem writeLoc_se {loc : Addr} {v : Value} (h : writeLoc σ loc v = .ok σ') : SE σ σ' := by
  cases loc with
  | memoryField id f =>
    obtain ⟨o, _, h⟩ := bind_ok_inv h
    split at h
    · cases h; exact ⟨rfl, rfl⟩
    · exact nomatch h
  | memoryIndex id i =>
    obtain ⟨o, _, h⟩ := bind_ok_inv h
    split at h
    · split at h
      · cases h; exact ⟨rfl, rfl⟩
      · exact nomatch h
    · exact nomatch h

theorem writeAddr_se {a : Addr} {mv : Semantics.MVal} (h : writeAddr σ mv a = .ok σ') : SE σ σ' := by
  cases a with
  | memoryField id f => exact memWriteField_se h
  | memoryIndex id i => exact memWriteIndex_se h

theorem opMem_se {op : BinOp} {p : PrimTy} {loc : Addr} {v : Value}
    (h : opMem σ op p loc v = .ok σ') : SE σ σ' :=
  let ⟨_, _, _, _, _, h⟩ := opMem_ok_inv h
  writeLoc_se h

theorem bumpMem_se {op : IncDec} {p : PrimTy} {loc : Addr} {w : Value}
    (h : bumpMem σ op p loc = .ok (σ', w)) : SE σ σ' :=
  let ⟨_, _, _, h, _⟩ := bumpMem_ok_inv h
  writeLoc_se h

theorem copyStToM_se {v : Semantics.SVal} {mv : Semantics.MVal} (h : copyStToM σ v = .ok (σ', mv)) : SE σ σ' := by
  have := SemanticsProperties.copyStToM_frame σ v σ' mv h
  exact ⟨this.1, this.2.1⟩

theorem allocDefault_se {R : RefTy} {id : Nat} (h : allocDefault σ R = .ok (σ', id)) : SE σ σ' := by
  simp only [allocDefault] at h
  split at h
  · rename_i hc; cases h; exact copyStToM_se hc
  · exact nomatch h
  · exact nomatch h

theorem memClear_se {a : Addr} : ∀ {T : Ty}, memClear σ a T = .ok σ' → SE σ σ'
  | .prim _, h => writeAddr_se h
  | .ref _, h => by
    obtain ⟨⟨σ₁, id⟩, h₁, h⟩ := bind_ok_inv h
    exact (allocDefault_se h₁).trans (writeAddr_se h)

theorem transferAt_se {addr amt : Int} (h : transferAt σ addr amt = .ok σ') : SE σ σ' := by
  unfold transferAt at h
  split at h
  · exact nomatch h
  · cases h; rw [State.pay_eq]; exact ⟨rfl, rfl⟩

theorem pay_se (addr amt : Int) : SE σ (σ.pay addr amt) := by
  rw [State.pay_eq]; exact ⟨rfl, rfl⟩

end Frames

/-! ### Statements -/

section Run

variable {Γ : Ctx} {H : HeapTy} {σ σ' : Semantics.State}

theorem IdxLive.nil (V : Semantics.SVal) : IdxLive V [] := fun _ _ h => by simp only [List.nil_eq,
    List.append_eq_nil_iff, List.cons_ne_self, and_false] at h

/-- A word written back at a checked path: `alice.age += 1;`. -/
theorem Semantics.Tight.saveWord (hd : DeepOk C) (hc : Canon C H σ) (ht : Semantics.Tight C σ) {r : Name}
    {segs : List Seg} {p : PrimTy} {v : Value} (hT : C.layout.tyAt r segs = some (.prim p))
    (hk : ∀ T, lookupBy r C.vars = some T → KeysOK T segs)
    (hlive : ∀ V, lookupBy r σ.storage = some V → IdxLive V segs)
    (h : σ.saveStorage r segs v.toSVal = .ok σ') : Semantics.Tight C σ' :=
  ht.save hd hc hT hk (fun _ => hlive) (by cases v <;> trivial) h

theorem opStore_tight (hd : DeepOk C) (hc : Canon C H σ) (ht : Semantics.Tight C σ) {op : BinOp}
    {p : PrimTy} {r : Name} {segs : List Seg} {v : Value}
    (hT : C.layout.tyAt r segs = some (.prim p)) (hk : ∀ T, lookupBy r C.vars = some T → KeysOK T segs)
    (hlive : ∀ V, lookupBy r σ.storage = some V → IdxLive V segs)
    (h : opStore σ op p r segs v = .ok σ') : Semantics.Tight C σ' :=
  let ⟨_, _, _, _, _, h⟩ := opStore_ok_inv h
  ht.saveWord hd hc hT hk hlive h

theorem bumpStore_tight (hd : DeepOk C) (hc : Canon C H σ) (ht : Semantics.Tight C σ) {op : IncDec}
    {p : PrimTy} {r : Name} {segs : List Seg} {w : Value}
    (hT : C.layout.tyAt r segs = some (.prim p)) (hk : ∀ T, lookupBy r C.vars = some T → KeysOK T segs)
    (hlive : ∀ V, lookupBy r σ.storage = some V → IdxLive V segs)
    (h : bumpStore σ op p r segs = .ok (σ', w)) : Semantics.Tight C σ' :=
  let ⟨_, _, _, h, _⟩ := bumpStore_ok_inv h
  ht.saveWord hd hc hT hk hlive h

/-- A copy out of memory stored at a checked location: `alice = m;`. -/
theorem copyMToSt_tight (hd : DeepOk C) {s : Semantics.State} {rem : List Nat} {mv : Semantics.MVal} {sv : Semantics.SVal}
    {r : Name} {segs : List Seg} {T : Ty} (hT : C.layout.tyAt r segs = some T)
    (hsc : sv.canon T) (h : copyMToSt s rem mv = .ok sv) : sv.tight T := by
  obtain ⟨T₀, hr, hs⟩ := Layout.tyAt_split hT
  exact plain_tight (copyMToSt_plain h) hsc (okDeep_tyAtSegs (hd r T₀ hr) hs)

end Run

section RunAll

variable {Γ : Ctx} {H : HeapTy} {σ σ' : Semantics.State}

theorem tyAt_okDeep (hd : DeepOk C) {r : Name} {segs : List Seg} {T : Ty}
    (hT : C.layout.tyAt r segs = some T) : T.okDeep = true := by
  obtain ⟨T₀, hr, hs⟩ := Layout.tyAt_split hT
  exact okDeep_tyAtSegs (hd r T₀ hr) hs

end RunAll

end Exact

end Solidity

/-! ### Over the scoped syntax -/

namespace Solidity

open Semantics hiding State
open SemanticsProperties (lookupBy_eq_some_mem lookupBy_setBy_self lookupBy_setBy_ne)
open Semantics.SVal.canon (canonFields canonElems canonEntries)
open Semantics.SVal.tight (tightFields tightElems tightEntries)

variable {C : Contract}

/-- An alias is bound, if at all, along a path whose mappings are indexed by
numbers; every other local is unconstrained. -/
def LTy.Keys (C : Contract) : (t : LTy) → t.Denote C → Prop
  | .alias _, o => ∀ r segs, o = some (r, segs) → ∃ T, lookupBy r C.vars = some T ∧ KeysOK T segs
  | .val _, _ => True
  | .mem _, _ => True
  | .old, _ => True
  | .oldNet, _ => True

/-- What a run keeps beyond `Canon`: tight storage, and aliases bound along
numeric keys. -/
structure Tight (C : Contract) {Γ : Ctx} (σ : EState C Γ) : Prop where
  storage : TightStorage C σ.storage
  env : Env.All (LTy.Keys C) σ.env

namespace Tight

variable {Γ : Ctx} {σ : EState C Γ}

theorem glob (ht : Tight C σ) : Semantics.Tight C σ.glob := ⟨ht.storage⟩

theorem withGlob (ht : Tight C σ) {τ : Semantics.State} (hτ : Semantics.Tight C τ) :
    Tight C (σ.withGlob τ) :=
  ⟨hτ.storage, ht.env⟩

/-- A global step that leaves storage as it was. -/
theorem withGlob_se (ht : Tight C σ) {τ : Semantics.State} (h : SE σ.glob τ) :
    Tight C (σ.withGlob τ) :=
  ht.withGlob (ht.glob.of_eq h.1)

theorem setLocal (ht : Tight C σ) {t : LTy} (i : Idx Γ t) {v : t.Denote C}
    (hv : LTy.Keys C t v) : Tight C (σ.setLocal i v) :=
  ⟨ht.storage, Env.All.set i ht.env hv⟩

theorem push (ht : Tight C σ) {t : LTy} {v : t.Denote C} (hv : LTy.Keys C t v) :
    Tight C (σ.push v) :=
  ⟨ht.storage, hv, ht.env⟩

theorem of_eq {σ' : EState C Γ} (ht : Tight C σ) (hs : σ'.storage = σ.storage)
    (he : σ'.env = σ.env) : Tight C σ' :=
  ⟨hs ▸ ht.storage, he ▸ ht.env⟩

end Tight

/-! #### Paths -/

section Paths

variable {Γ : Ctx} {H : HeapTy} {σ : EState C Γ}


mutual

/-- A path resolves along numeric keys. -/
theorem SPath.resolve_keys (hwt : RunWT C H σ) (hte : Env.All (LTy.Keys C) σ.env) :
    ∀ {T : Ty} (p : SPath C Γ T) {r : Name} {segs : List Seg},
      p.resolve σ = .ok (r, segs) → ∀ T₀, lookupBy r C.vars = some T₀ → KeysOK T₀ segs
  | _, @SPath.alias _ _ R i, r, segs, h, T₀, hr => by
    have hk : LTy.Keys C (.alias R) (Env.get i σ.env) := hte.get i
    change aliasPath σ i = _ at h
    unfold aliasPath at h
    split at h
    · rename_i p hp
      cases h
      obtain ⟨T, hT, hks⟩ := hk _ _ hp
      rw [hr] at hT; cases hT; exact hks
    · exact nomatch h
  | _, .loc l, r, segs, h, T₀, hr => Loc.resolve_keys hwt hte l h T₀ hr

theorem Loc.resolve_keys (hwt : RunWT C H σ) (hte : Env.All (LTy.Keys C) σ.env) :
    ∀ {T : Ty} (l : Loc C Γ T) {r : Name} {segs : List Seg},
      l.resolve σ = .ok (r, segs) → ∀ T₀, lookupBy r C.vars = some T₀ → KeysOK T₀ segs
  | _, .root r' _, r, segs, h, T₀, _ => by
    simp only [Loc.resolve, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; trivial
  | _, .field b f hf, r, segs, h, T₀, hr => by
    obtain ⟨⟨r0, s0⟩, h0, h⟩ := bind_ok_inv h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hb := SPath.resolve_wt hwt b h0
    obtain ⟨T, hT, hs⟩ := Layout.tyAt_split hb
    cases hr.symm.trans hT
    exact KeysOK_append _ (SPath.resolve_keys hwt hte b h0 T₀ hr) hs
      (fun K V h => nomatch h)
  | _, .index it b i, r, segs, h, T₀, hr => by
    obtain ⟨⟨r0, s0⟩, h0, h⟩ := bind_ok_inv h
    obtain ⟨w, hwv, h⟩ := bind_ok_inv h
    obtain ⟨iv, hiv, h⟩ := bind_ok_inv h
    bind_inv h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hb := SPath.resolve_wt hwt b h0
    obtain ⟨T, hT, hs⟩ := Layout.tyAt_split hb
    cases hr.symm.trans hT
    refine KeysOK_append _ (SPath.resolve_keys hwt hte b h0 T₀ hr) hs ?_
    intro K V hKV
    cases it with
    | map =>
      simp only [Ty.ref.injEq, RefTy.mapping.injEq] at hKV
      obtain ⟨rfl, rfl⟩ := hKV
      rfl
    | arr a => cases a <;> exact nomatch hKV

end

/-- An index is live where the path is taken. -/
theorem Loc.resolve_live : ∀ {T : Ty} (l : Loc C Γ T) {r : Name} {segs : List Seg},
    l.resolve σ = .ok (r, segs) → ∀ V, lookupBy r σ.storage = some V → IdxLive V segs
  | _, .root r' _, r, segs, h, V, _ => by
    simp only [Loc.resolve, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro pre i hseg
    simp only [List.nil_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false] at hseg
  | _, .field b f hf, r, segs, h, V, _ => by
    obtain ⟨⟨r0, s0⟩, h0, h⟩ := bind_ok_inv h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro pre i hseg
    exact nomatch (append_single_ne hseg).2
  | _, .index it b i, r, segs, h, V, hV => by
    obtain ⟨⟨r0, s0⟩, h0, h⟩ := bind_ok_inv h
    obtain ⟨w, hwv, h⟩ := bind_ok_inv h
    obtain ⟨iv, hiv, h⟩ := bind_ok_inv h
    obtain ⟨u, hck, h⟩ := bind_ok_inv h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro pre j hseg es sh fx hf
    obtain ⟨rfl, hj⟩ := append_single_ne hseg
    cases hj
    simp only [Semantics.State.checkIndex, Semantics.State.findStorage, EState.glob, hV, hf, bind,
      Except.bind] at hck
    split at hck
    · assumption
    · exact nomatch hck

end Paths

/-! #### Statements -/

section Effects

variable {Γ : Ctx} {H : HeapTy} {σ σ' : EState C Γ}

theorem Src.value_tight (hd : DeepOk C) (hwt : RunWT C H σ) (hc : Canon C H σ.glob)
    (ht : Tight C σ) {T : Ty} {r : Src C Γ T} {sv : Semantics.SVal} (h : r.value σ = .ok sv) :
    sv.tight T := by
  cases r with
  | val v =>
    obtain ⟨w, _, h⟩ := bind_ok_inv h
    cases h; cases w <;> trivial
  | copy p _ =>
    obtain ⟨⟨r, segs⟩, hr, h⟩ := bind_ok_inv h
    exact ht.glob.find hd hc (SPath.resolve_wt hwt p hr) h

theorem OpLoc.store_tight (hd : DeepOk C) (hwt : RunWT C H σ) (hc : Canon C H σ.glob)
    (ht : Tight C σ) {op : BinOp} :
    ∀ {p : PrimTy} (l : OpLoc C Γ p) {v : Value}, l.store σ op v = .ok σ' → Tight C σ'
  | p, .local i, v, h => by
    obtain ⟨n₁, _, h⟩ := bind_ok_inv h
    obtain ⟨n₂, _, h⟩ := bind_ok_inv h
    cases h
    exact ht.setLocal i trivial
  | p, .root r hr, v, h => by
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact ht.withGlob (opStore_tight hd hc ht.glob (Contract.layout_tyAt_root hr)
      (fun _ _ => trivial) (fun V _ => IdxLive.nil V) hτ)
  | p, .field b f hf, v, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact ht.withGlob (opStore_tight hd hc ht.glob (Loc.resolve_wt hwt (.field b f hf) hr)
      (Loc.resolve_keys hwt ht.env (.field b f hf) hr) (Loc.resolve_live (.field b f hf) hr) hτ)
  | p, .index it b i, v, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact ht.withGlob (opStore_tight hd hc ht.glob (Loc.resolve_wt hwt (.index it b (.simple i)) hr)
      (Loc.resolve_keys hwt ht.env (.index it b (.simple i)) hr)
      (Loc.resolve_live (.index it b (.simple i)) hr) hτ)
  | p, .mfield b f hf, v, h => by
    iterate 2 bind_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact ht.withGlob_se (opMem_se hτ)
  | p, .mindex ak b i, v, h => by
    iterate 4 bind_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact ht.withGlob_se (opMem_se hτ)

theorem OpLoc.bump_tight (hd : DeepOk C) (hwt : RunWT C H σ) (hc : Canon C H σ.glob)
    (ht : Tight C σ) {op : IncDec} :
    ∀ {p : PrimTy} (l : OpLoc C Γ p) {w : Value}, l.bump σ op = .ok (σ', w) → Tight C σ'
  | p, .local i, w, h => by
    obtain ⟨m, _, h⟩ := bind_ok_inv h
    obtain ⟨n, _, h⟩ := bind_ok_inv h
    cases h
    exact ht.setLocal i trivial
  | p, .root r hr, w, h => by
    obtain ⟨⟨τ, v⟩, hτ, h⟩ := map_ok_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ht.withGlob (bumpStore_tight hd hc ht.glob (Contract.layout_tyAt_root hr)
      (fun _ _ => trivial) (fun V _ => IdxLive.nil V) hτ)
  | p, .field b f hf, w, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ, v⟩, hτ, h⟩ := map_ok_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ht.withGlob (bumpStore_tight hd hc ht.glob (Loc.resolve_wt hwt (.field b f hf) hr)
      (Loc.resolve_keys hwt ht.env (.field b f hf) hr) (Loc.resolve_live (.field b f hf) hr) hτ)
  | p, .index it b i, w, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ, v⟩, hτ, h⟩ := map_ok_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ht.withGlob (bumpStore_tight hd hc ht.glob
      (Loc.resolve_wt hwt (.index it b (.simple i)) hr)
      (Loc.resolve_keys hwt ht.env (.index it b (.simple i)) hr)
      (Loc.resolve_live (.index it b (.simple i)) hr) hτ)
  | p, .mfield b f hf, w, h => by
    iterate 2 bind_inv h
    obtain ⟨⟨τ, v⟩, hτ, h⟩ := map_ok_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ht.withGlob_se (bumpMem_se hτ)
  | p, .mindex ak b i, w, h => by
    iterate 4 bind_inv h
    obtain ⟨⟨τ, v⟩, hτ, h⟩ := map_ok_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ht.withGlob_se (bumpMem_se hτ)

/-- A storage write through a location: `alice.age = 3;`, `alice = bob;`. -/
theorem Tight.writeLoc (hd : DeepOk C) (hwt : RunWT C H σ) (hc : Canon C H σ.glob)
    (ht : Tight C σ) {T : Ty} {l : Loc C Γ T} {r : Name} {segs : List Seg} {sv : Semantics.SVal}
    {τ : Semantics.State} (hr : l.resolve σ = .ok (r, segs)) (hsc : sv.canon T)
    (hst : sv.tight T) (h : σ.glob.writeStorage r segs sv = .ok τ) : Tight C (σ.withGlob τ) :=
  ht.withGlob (ht.glob.write hd hc (Loc.resolve_wt hwt l hr) (Loc.resolve_keys hwt ht.env l hr)
    (fun _ => Loc.resolve_live l hr) hsc hst h)

/-- `p = alice;`, `p = persons.push();` name a path along numeric keys. -/
theorem ARhs.eval_tight (hd : DeepOk C) (hwt : RunWT C H σ) (hc : Canon C H σ.glob)
    (ht : Tight C σ) {R : RefTy} {r : ARhs C Γ R} {σ₁ : EState C Γ} {root : Name}
    {segs : List Seg} (h : r.eval σ = .ok (σ₁, (root, segs))) :
    Tight C σ₁ ∧ LTy.Keys C (.alias R) (some (root, segs)) := by
  cases r with
  | path p =>
    obtain ⟨rs, hr, h⟩ := bind_ok_inv h
    cases h
    obtain ⟨T, hT, -⟩ := Layout.tyAt_split (SPath.resolve_wt hwt p hr)
    refine ⟨ht, fun r' s' he => ?_⟩
    cases he
    exact ⟨T, hT, SPath.resolve_keys hwt ht.env p hr T hT⟩
  | push b hdo =>
    obtain ⟨⟨root', segs'⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ, n⟩, hpush, h⟩ := bind_ok_inv h
    cases h
    have hty := SPath.resolve_wt hwt b hr
    have hk := SPath.resolve_keys hwt ht.env b hr
    obtain ⟨T, hT, hs⟩ := Layout.tyAt_split hty
    refine ⟨ht.withGlob (pushPlaceAt_tight hd hc ht.glob hty hk hpush), fun r' s' he => ?_⟩
    cases he
    exact ⟨T, hT, KeysOK_append _ (hk T hT) hs (fun K V h => nomatch h)⟩

/-- `m = n;`, `m = alice;` leave storage and the locals as they were. -/
theorem MRhs.eval_se {R : RefTy} {r : MRhs C Γ R} {σ₁ : EState C Γ} {id : Nat}
    (h : r.eval σ = .ok (σ₁, id)) : σ₁.storage = σ.storage ∧ σ₁.env = σ.env := by
  cases r with
  | alias p =>
    bind_inv h
    obtain ⟨id', _, h⟩ := bind_ok_inv h
    cases h
    exact ⟨rfl, rfl⟩
  | copy p _ =>
    iterate 2 bind_inv h
    obtain ⟨⟨τ, mv⟩, hcopy, h⟩ := bind_ok_inv h
    obtain ⟨id', _, h⟩ := bind_ok_inv h
    cases h
    exact ⟨(copyStToM_se hcopy).1, rfl⟩
  | newArr n _ =>
    iterate 2 bind_inv h
    obtain ⟨⟨τ, mv⟩, hcopy, h⟩ := bind_ok_inv h
    obtain ⟨id', _, h⟩ := bind_ok_inv h
    cases h
    exact ⟨(copyStToM_se hcopy).1, rfl⟩

/-- A memory write leaves storage and the locals as they were. -/
theorem MLoc.write_se {mv : Semantics.MVal} :
    ∀ {T : Ty} (l : MLoc C Γ T), l.write σ mv = .ok σ' → σ'.storage = σ.storage ∧ σ'.env = σ.env
  | _, .field b f _, h => by
    iterate 2 bind_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact ⟨(memWriteField_se hτ).1, rfl⟩
  | _, .index _ b i, h => by
    iterate 4 bind_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact ⟨(memWriteIndex_se hτ).1, rfl⟩

end Effects

/-! #### One statement at a time -/

section Leaves

variable {Γ : Ctx} {H : HeapTy} {σ : State C Γ}

theorem tight_assign (hd : DeepOk C) (hwt : RunWT C H σ.erase) (hc : Canon C H σ.erase.glob) (ht : Tight C σ.erase)
    {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) {o : Out C σ.H Γ} (h : TRun.assign l r σ = .ok o) : Tight C o.st.erase := by
  have h := (TRun.assign_erase l r).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
  obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
  exact ht.writeLoc hd hwt hc hr (Src.value_canon hwt hc hsv) (Src.value_tight hd hwt hc ht hsv) hτ

theorem tight_rebind (hd : DeepOk C) (hwt : RunWT C H σ.erase) (hc : Canon C H σ.erase.glob) (ht : Tight C σ.erase)
    {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) {o : Out C σ.H Γ} (h : TRun.rebind i r σ = .ok o) :
    Tight C o.st.erase := by
  have h := (TRun.rebind_erase i r).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  obtain ⟨⟨σ₁, root, segs⟩, he, h⟩ := bind_ok_inv h
  cases h
  obtain ⟨ht₁, hk⟩ := ARhs.eval_tight hd hwt hc ht he
  exact ht₁.setLocal i hk

theorem tight_assignLocal (ht : Tight C σ.erase) {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p)
    {o : Out C σ.H Γ} (h : TRun.assignLocal i r σ = .ok o) : Tight C o.st.erase := by
  have h := (TRun.assignLocal_erase i r).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  obtain ⟨w, _, h⟩ := bind_ok_inv h
  cases h
  exact ht.setLocal i trivial

theorem tight_declLocal (ht : Tight C σ.erase) (p : PrimTy) (init : Option (Val C Γ p))
    {o : Out C σ.H (.val p :: Γ)} (h : TRun.declLocal p init σ = .ok o) : Tight C o.st.erase := by
  have h := (TRun.declLocal_erase p init).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  cases init with
  | none => cases h; exact ht.push trivial
  | some e =>
    obtain ⟨w, _, h⟩ := bind_ok_inv h
    cases h
    exact ht.push trivial

theorem tight_declStorage (hd : DeepOk C) (hwt : RunWT C H σ.erase) (hc : Canon C H σ.erase.glob)
    (ht : Tight C σ.erase) (R : RefTy) (init : Option (ARhs C Γ R))
    {o : Out C σ.H (.alias R :: Γ)} (h : TRun.declStorage R init σ = .ok o) : Tight C o.st.erase := by
  have h := (TRun.declStorage_erase R init).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  cases init with
  | none => cases h; exact ht.push (t := .alias R) (fun _ _ h => nomatch h)
  | some r =>
    obtain ⟨⟨σ₁, root, segs⟩, he, h⟩ := bind_ok_inv h
    cases h
    obtain ⟨ht₁, hk⟩ := ARhs.eval_tight hd hwt hc ht he
    exact ht₁.push hk

theorem tight_push (hd : DeepOk C) (hwt : RunWT C H σ.erase) (hc : Canon C H σ.erase.glob) (ht : Tight C σ.erase)
    {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E)) {o : Out C σ.H Γ} (h : TRun.push b v σ = .ok o) :
    Tight C o.st.erase := by
  have h := (TRun.push_erase b v).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
  obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
  refine ht.withGlob (pushAt_tight hd hc ht.glob (SPath.resolve_wt hwt b hr)
    (SPath.resolve_keys hwt ht.env b hr) ?_ hτ)
  intro slot w hslot hw
  cases v with
  | none => cases hw; exact hslot
  | some r =>
    obtain ⟨v, hv, hw⟩ := bind_ok_inv hw
    cases hw
    exact SVal.strip_tight (Src.value_tight hd hwt hc ht hv)

theorem tight_pop (hd : DeepOk C) (hwt : RunWT C H σ.erase) (hc : Canon C H σ.erase.glob) (ht : Tight C σ.erase)
    {E : Ty} (b : SPath C Γ (.array E)) {o : Out C σ.H Γ} (h : TRun.pop b σ = .ok o) : Tight C o.st.erase := by
  have h := (TRun.pop_erase b).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
  obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
  exact ht.withGlob (popAt_tight hd hc ht.glob (SPath.resolve_wt hwt b hr)
    (SPath.resolve_keys hwt ht.env b hr) hτ)

theorem tight_transfer (ht : Tight C σ.erase) (r a : Val C Γ .uint) {o : Out C σ.H Γ} (h : TRun.transfer r a σ = .ok o) :
    Tight C o.st.erase := by
  have h := (TRun.transfer_erase r a).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  iterate 4 bind_inv h
  obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
  exact ht.withGlob_se (transferAt_se hτ)

theorem tight_send (ht : Tight C σ.erase) (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint)
    {o : Out C σ.H Γ} (h : TRun.send pv r a σ = .ok o) : Tight C o.st.erase := by
  have h := (TRun.send_erase pv r a).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  iterate 4 bind_inv h
  unfold sendAt at h
  split at h
  · exact nomatch h
  · split at h <;> cases h
    · exact (ht.withGlob_se (pay_se _ _)).setLocal pv trivial
    · exact (ht.withGlob_se (pay_se _ _)).setLocal pv trivial
    · exact ht.setLocal pv trivial

theorem tight_declMem (ht : Tight C σ.erase) (R : RefTy) (init : Option (MRhs C Γ R))
    (hm : (Ty.ref R).mapFree = true)
    {o : Out C σ.H (.mem R :: Γ)} (h : TRun.declMem R init hm σ = .ok o) : Tight C o.st.erase := by
  have h := (TRun.declMem_erase R init hm).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  cases init with
  | none =>
    obtain ⟨⟨τ, id⟩, ha, h⟩ := bind_ok_inv h
    cases h
    exact (ht.withGlob_se (allocDefault_se ha)).push trivial
  | some r =>
    obtain ⟨⟨σ₁, id⟩, he, h⟩ := bind_ok_inv h
    cases h
    obtain ⟨hs, hen⟩ := MRhs.eval_se he
    exact (ht.of_eq hs hen).push trivial

theorem tight_rebindMem (ht : Tight C σ.erase) {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R)
    {o : Out C σ.H Γ} (h : TRun.rebindMem i r σ = .ok o) : Tight C o.st.erase := by
  have h := (TRun.rebindMem_erase i r).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  obtain ⟨⟨σ₁, id⟩, he, h⟩ := bind_ok_inv h
  cases h
  obtain ⟨hs, hen⟩ := MRhs.eval_se he
  exact (ht.of_eq hs hen).setLocal i trivial

theorem tight_assignFromMem (hd : DeepOk C) (hwt : RunWT C H σ.erase) (hc : Canon C H σ.erase.glob)
    (ht : Tight C σ.erase) {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R))
    {o : Out C σ.H Γ} (h : TRun.assignFromMem l p σ = .ok o) : Tight C o.st.erase := by
  have h := (TRun.assignFromMem_erase l p).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
  obtain ⟨id, hid, h⟩ := bind_ok_inv h
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
  obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
  have hm := MPath.mval_wt hwt p hm0
  rw [MVal.asRef_ok hid] at hm
  have hT := Loc.resolve_wt hwt l hr
  have hsc := copyMToSt_canon hwt.glob.heap hc.heap hm hsv
  exact ht.writeLoc hd hwt hc hr hsc (copyMToSt_tight hd hT hsc hsv) hτ

theorem tight_assignMem (ht : Tight C σ.erase) {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T)
    {o : Out C σ.H Γ} (h : TRun.assignMem l r σ = .ok o) : Tight C o.st.erase := by
  have h := (TRun.assignMem_erase l r).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  obtain ⟨mv, _, h⟩ := bind_ok_inv h
  obtain ⟨hs, hen⟩ := MLoc.write_se l h
  exact ht.of_eq hs hen

theorem tight_delete (hd : DeepOk C) (hwt : RunWT C H σ.erase) (hc : Canon C H σ.erase.glob) (ht : Tight C σ.erase)
    {T : Ty} (l : Loc C Γ T) {o : Out C σ.H Γ} (h : TRun.delete l σ = .ok o) : Tight C o.st.erase := by
  have h := (TRun.delete_erase l).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
  obtain ⟨cur, hcur, h⟩ := bind_ok_inv h
  obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
  have hty := Loc.resolve_wt hwt l hr
  exact ht.withGlob (ht.glob.save hd hc hty (Loc.resolve_keys hwt ht.env l hr)
    (fun _ => Loc.resolve_live l hr)
    (SVal.defaultOf_tight (hc.find hty hcur) (ht.glob.find hd hc hty hcur) (tyAt_okDeep hd hty)) hτ)

theorem tight_deleteMem (ht : Tight C σ.erase) {T : Ty} (p : MPath C Γ T)
    {o : Out C σ.H Γ} (h : TRun.deleteMem p σ = .ok o) : Tight C o.st.erase := by
  have h := (TRun.deleteMem_erase p).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  cases p with
  | var i _ =>
    obtain ⟨⟨τ, id⟩, ha, h⟩ := bind_ok_inv h
    cases h
    exact (ht.withGlob_se (allocDefault_se ha)).setLocal i trivial
  | loc l =>
    obtain ⟨a, _, h⟩ := bind_ok_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact ht.withGlob_se (memClear_se hτ)

theorem tight_assignNew (hd : DeepOk C) (hwt : RunWT C H σ.erase) (hc : Canon C H σ.erase.glob)
    (ht : Tight C σ.erase) {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint) (hn : R.newArrOk = true)
    {o : Out C σ.H Γ} (h : TRun.assignNew l n hn σ = .ok o) : Tight C o.st.erase := by
  have h := (TRun.assignNew_erase l n hn).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  bind_inv h
  obtain ⟨nv, _, h⟩ := bind_ok_inv h
  obtain ⟨⟨τ, mv⟩, hcopy, h⟩ := bind_ok_inv h
  obtain ⟨id, hid, h⟩ := bind_ok_inv h
  have ht₁ : Tight C (σ.withGlob τ) := ht.withGlob_se (copyStToM_se hcopy)
  cases l with
  | store l =>
    obtain ⟨H', hout, hmv⟩ := copyStToM_canon hwt.glob.heapTyNodup hwt.glob.heap hwt.glob.heapWf
      hc.heap (newArrVal_hasTy hn nv) (newArrVal_canon hn nv) hcopy
    rw [MVal.asRef_ok (show mv.asRef = .ok id from hid)] at hmv
    have h₁ := CopyOutC.wtCanon hwt hc hout
    obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨τ', hτ', rfl⟩ := map_ok_inv h
    have hg₁ : StateWT H' C.layout τ := hwt.glob.ofCopyOut hout.out
    have hc₁ : Canon C H' τ := ⟨hout.out.storage ▸ hc.storage, hout.canon⟩
    have hT := Loc.resolve_wt h₁.1 l hr
    have hsc := copyMToSt_canon hg₁.heap hc₁.heap hmv hsv
    have hτt : Semantics.Tight C τ := ⟨ht₁.storage⟩
    exact ht₁.withGlob (hτt.write hd hc₁ hT (Loc.resolve_keys h₁.1 ht₁.env l hr)
      (fun _ => Loc.resolve_live l hr) hsc (copyMToSt_tight hd hT hsc hsv) hτ')
  | mem l =>
    obtain ⟨hs, hen⟩ := MLoc.write_se l h
    exact ht₁.of_eq hs hen

theorem tight_opAssign (hd : DeepOk C) (hwt : RunWT C H σ.erase) (hc : Canon C H σ.erase.glob)
    (ht : Tight C σ.erase) {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (r : Val C Γ p) {o : Out C σ.H Γ}
    (h : TRun.opAssign op l r σ = .ok o) : Tight C o.st.erase := by
  have h := (TRun.opAssign_erase op hop hp l r).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  obtain ⟨v, _, h⟩ := bind_ok_inv h
  exact OpLoc.store_tight hd hwt hc ht l h

theorem tight_incDec (hd : DeepOk C) (hwt : RunWT C H σ.erase) (hc : Canon C H σ.erase.glob)
    (ht : Tight C σ.erase) {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
    (l : OpLoc C Γ p) {o : Out C σ.H Γ} (h : TRun.incDec op l σ = .ok o) : Tight C o.st.erase := by
  have h := (TRun.incDec_erase op hp l).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  obtain ⟨⟨σ₁, w⟩, hb, h⟩ := bind_ok_inv h
  cases h
  exact OpLoc.bump_tight hd hwt hc ht l hb

theorem tight_assignIncDec (hd : DeepOk C) (hwt : RunWT C H σ.erase) (hc : Canon C H σ.erase.glob)
    (ht : Tight C σ.erase) {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) {o : Out C σ.H Γ}
    (h : TRun.assignIncDec i op l σ = .ok o) : Tight C o.st.erase := by
  have h := (TRun.assignIncDec_erase i op hp l).ok h
  generalize o.st.erase = σ' at h ⊢
  generalize σ.erase = σ at *
  try dsimp only at h
  obtain ⟨⟨σ₁, w⟩, hb, h⟩ := bind_ok_inv h
  cases h
  exact (OpLoc.bump_tight hd hwt hc ht l hb).setLocal i trivial

end Leaves

/-! #### The run keeps the state tight -/

/-- What a run keeps beyond its types: the storage canonical and tight, every
alias bound along keys (well-typedness and the heap's canonicity hold by
construction, `State.erase_wt`, `State.erase_canonHeap`). -/
def tightInv (C : Contract) : RunInv C where
  glob H τ := (canonInv C).glob H τ ∧ Semantics.Tight C τ
  loc _ t v := LTy.Keys C t v
  loc_mono _ h := h
  reglob e h := ⟨(canonInv C).reglob e h.1, ⟨h.2.storage⟩⟩

/-- The storage canonical and tight, every alias bound along keys. -/
abbrev RunTight (C : Contract) {Γ : Ctx} (H : HeapTy) (σ : EState C Γ) : Prop :=
  (tightInv C).Holds H σ

namespace RunTight

variable {Γ : Ctx} {H : HeapTy} {σ : EState C Γ}

theorem canon (h : RunTight C H σ) : RunCanon C H σ :=
  ⟨h.1.1, Env.all_true σ.env⟩

theorem tight (h : RunTight C H σ) : Tight C σ :=
  ⟨h.1.2.storage, h.2⟩

theorem mk' (hc : RunCanon C H σ) (ht : Tight C σ) : RunTight C H σ :=
  ⟨⟨hc.1, ht.glob⟩, ht.env⟩

end RunTight

/-- A typed leaf keeps the state tight when it keeps it canonical and, from
a state whose erasure is canonical and tight, leaves one whose erasure is
tight. -/
theorem tkeepsT_of (hnd : nodupKeysB C.vars = true) {Γ Γ' : Ctx} {t : TStep C Γ Γ'}
    (hc : (canonInv C).TKeeps t)
    (ht : ∀ (H : HeapTy) (σ : State C Γ) (o : Out C σ.H Γ'), RunWT C H σ.erase →
      Canon C H σ.erase.glob → Tight C σ.erase → t σ = .ok o → Tight C o.st.erase) :
    (tightInv C).TKeeps t := by
  intro σ o h hrun
  replace h : RunTight C (HTy.toHeapTy 0 σ.H) σ.erase := h
  exact RunTight.mk' (hc σ o (RunTight.canon h) hrun)
    (ht _ σ o (State.erase_wt hnd σ) (RunCanon.typed (RunTight.canon h)) (RunTight.tight h) hrun)

/-- Every local of a call's parameters, return variables or decoded data is
a value, or a fresh memory object: no alias. -/
theorem Args.eval_keys {Γ : Ctx} {σ : EState C Γ} : {ps : Ctx} → (args : Args C Γ ps) →
    {a : Env C ps} → args.eval σ = .ok a → Env.All (LTy.Keys C) a
  | _, .nil, _, _ => trivial
  | _, .snoc as _ _ _, _, h => by
    obtain ⟨r, hr, h⟩ := bind_ok_inv h
    obtain ⟨v, _, h⟩ := bind_ok_inv h
    cases h
    exact ⟨trivial, Args.eval_keys as hr⟩

theorem Binders.keys : {ρ : Ctx} → (bs : Binders ρ) → (r : Env C ρ) → Env.All (LTy.Keys C) r
  | _, .nil, _ => trivial
  | _, .snoc bs _ _, r => ⟨trivial, Binders.keys bs r.2⟩

theorem CodeBinder.keys {κ : Ctx} (code : CodeBinder κ) (r : Env C κ) : Env.All (LTy.Keys C) r := by
  cases code with
  | none => trivial
  | some _ => exact ⟨trivial, trivial⟩

theorem CallRet.enter_tight {Γ rs Γ' : Ctx} (ret : CallRet Γ rs Γ') {τ τ' : Semantics.State}
    {r : Env C rs} (h : ret.enter τ = .ok (τ', r)) :
    τ'.storage = τ.storage ∧ Env.All (LTy.Keys C) r := by
  cases ret with
  | none => cases h; exact ⟨rfl, trivial⟩
  | val p x res => cases h; exact ⟨rfl, trivial, trivial⟩
  | rets bs => cases h; exact ⟨rfl, Binders.keys bs _⟩
  | mem R x hd hm =>
    obtain ⟨⟨τ₁, id⟩, ha, h⟩ := bind_ok_inv h
    cases h
    exact ⟨(allocDefault_se ha).1, trivial, trivial⟩


/-- A call's entry keeps the storage tight: no return variable is an
alias. -/
theorem tightInv.enter (hnd : nodupKeysB C.vars = true) {Γ Γ' ps rs : Ctx}
    (ret : CallRet Γ rs Γ') (σ : State C Γ) (a : TEnv C σ.H ps)
    (h : RunTight C (HTy.toHeapTy 0 σ.H) (σ.withEnv a).erase) :
    RunTight C (HTy.toHeapTy 0 (ret.enterT (σ.withEnv a)).st.H)
      (ret.enterT (σ.withEnv a)).st.erase := by
  have hc := canonInv.enter hnd ret σ a (RunTight.canon h)
  obtain ⟨τ', r, hen, he⟩ := CallRet.enterT_ok ret σ a
  obtain ⟨hs, hk⟩ := CallRet.enter_tight ret hen
  rw [he] at hc ⊢
  exact ⟨⟨hc.1, h.1.2.of_eq hs⟩, Env.All.append rs hk h.2⟩

mutual

/-- **Tightness, statement level**: a statement run from a well-typed,
canonical, tight state ends in a tight one. -/
theorem Stmt.keeps_tight (hd : DeepOk C) (hnd : nodupKeysB C.vars = true) :
    {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → (tightInv C).TKeeps (Stmt.runR s)
  | _, _, .assign l r =>
    tkeepsT_of hnd (keepsC_assign hnd l r) fun _ _ _ hwt hc ht h => tight_assign hd hwt hc ht l r h
  | _, _, .rebind i r =>
    tkeepsT_of hnd (keepsC_rebind hnd i r) fun _ _ _ hwt hc ht h => tight_rebind hd hwt hc ht i r h
  | _, _, .assignLocal i r =>
    tkeepsT_of hnd (keepsC_assignLocal hnd i r) fun _ _ _ _ _ ht h => tight_assignLocal ht i r h
  | _, _, .declLocal p _ init =>
    tkeepsT_of hnd (keepsC_declLocal hnd p init) fun _ _ _ _ _ ht h => tight_declLocal ht p init h
  | _, _, .declStorage R _ init =>
    tkeepsT_of hnd (keepsC_declStorage hnd R init) fun _ _ _ hwt hc ht h =>
      tight_declStorage hd hwt hc ht R init h
  | _, _, .opAssign op hop hp l r =>
    tkeepsT_of hnd (keepsC_opAssign hnd op hop hp l r) fun _ _ _ hwt hc ht h =>
      tight_opAssign hd hwt hc ht op hop hp l r h
  | _, _, .incDec op hp l =>
    tkeepsT_of hnd (keepsC_incDec hnd op hp l) fun _ _ _ hwt hc ht h =>
      tight_incDec hd hwt hc ht op hp l h
  | _, _, .assignIncDec i op hp l _ =>
    tkeepsT_of hnd (keepsC_assignIncDec hnd i op hp l) fun _ _ _ hwt hc ht h =>
      tight_assignIncDec hd hwt hc ht i op hp l h
  | _, _, .push b v hdo =>
    tkeepsT_of hnd (keepsC_push hnd b v hdo) fun _ _ _ hwt hc ht h => tight_push hd hwt hc ht b v h
  | _, _, .pop b =>
    tkeepsT_of hnd (keepsC_pop hnd b) fun _ _ _ hwt hc ht h => tight_pop hd hwt hc ht b h
  | _, _, .transfer r a =>
    tkeepsT_of hnd (keepsC_transfer hnd r a) fun _ _ _ _ _ ht h => tight_transfer ht r a h
  | _, _, .send pv r a =>
    tkeepsT_of hnd (keepsC_send hnd pv r a) fun _ _ _ _ _ ht h => tight_send ht pv r a h
  | _, _, .declMem R _ init hdo hm =>
    tkeepsT_of hnd (keepsC_declMem hnd R init hdo hm) fun _ _ _ _ _ ht h =>
      tight_declMem ht R init hm h
  | _, _, .rebindMem i r =>
    tkeepsT_of hnd (keepsC_rebindMem hnd i r) fun _ _ _ _ _ ht h => tight_rebindMem ht i r h
  | _, _, .assignFromMem l p =>
    tkeepsT_of hnd (keepsC_assignFromMem hnd l p) fun _ _ _ hwt hc ht h =>
      tight_assignFromMem hd hwt hc ht l p h
  | _, _, .assignMem l r =>
    tkeepsT_of hnd (keepsC_assignMem hnd l r) fun _ _ _ _ _ ht h => tight_assignMem ht l r h
  | _, _, .delete l =>
    tkeepsT_of hnd (keepsC_delete hnd l) fun _ _ _ hwt hc ht h => tight_delete hd hwt hc ht l h
  | _, _, .deleteMem p hdo =>
    tkeepsT_of hnd (keepsC_deleteMem hnd p hdo) fun _ _ _ _ _ ht h => tight_deleteMem ht p h
  | _, _, .assignNew l n hn =>
    tkeepsT_of hnd (keepsC_assignNew hnd l n hn) fun _ _ _ hwt hc ht h =>
      tight_assignNew hd hwt hc ht l n hn h
  | _, _, .ite c thn els =>
    RunInv.tkeeps_ite c thn.ext els.ext (Prog.keeps_tight hd hnd thn) (Prog.keeps_tight hd hnd els)
  | _, _, .require c => RunInv.tkeeps_require c
  | _, _, .assert c => RunInv.tkeeps_assert c
  | _, _, .revert => RunInv.tkeeps_revert
  | _, _, .call _ args ret body =>
    RunInv.tkeeps_call args ret body.ext
      (fun _ _ _ _ ha => Args.eval_keys args ha) (tightInv.enter hnd ret)
      (Prog.keeps_tight hd hnd body)
  | _, _, .tryCall call rets ok err code pnc other =>
    RunInv.tkeeps_tryCall call rets ok.ext err.ext code pnc.ext other.ext
      (fun _ _ r _ _ => Binders.keys rets r) (fun _ _ r _ => CodeBinder.keys code r)
      (Prog.keeps_tight hd hnd ok) (Prog.keeps_tight hd hnd err) (Prog.keeps_tight hd hnd pnc)
      (Prog.keeps_tight hd hnd other)
  | _, _, .loop _ c body => RunInv.tkeeps_loop c body.ext (Prog.keeps_tight hd hnd body)
  | _, _, .block body => RunInv.tkeeps_block body.ext (Prog.keeps_tight hd hnd body)

/-- **Tightness, block level.** -/
theorem Prog.keeps_tight (hd : DeepOk C) (hnd : nodupKeysB C.vars = true) :
    {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → (tightInv C).TKeeps (Prog.runR P)
  | _, _, .nil => RunInv.tkeeps_nil
  | _, _, .cons s P => RunInv.tkeeps_seq (Stmt.keeps_tight hd hnd s) (Prog.keeps_tight hd hnd P)

end

/-- **Tightness**: a block run by the typed run from a state whose erasure
has canonical, tight storage and aliases along keys ends, if in a state, in
one whose erasure is tight. -/
theorem Prog.run_tight (hd : DeepOk C) (hnd : nodupKeysB C.vars = true) {Γ Γ' : Ctx}
    (P : Prog C Γ Γ') {σ : State C Γ} {o : Out C σ.H Γ'} (hc : CanonStorage C σ.erase.storage)
    (ht : Tight C σ.erase) (h : P.run σ = .ok o) : Tight C o.st.erase :=
  RunTight.tight (Prog.keeps_tight hd hnd P σ o (RunTight.mk' (RunCanon.of_storage hc) ht) h)

/-- A contract starts tight: each root at its type's default, no alias. -/
theorem Tight.init (hd : DeepOk C) : Tight C (EState.ofSem C.initState) := by
  refine ⟨fun r T v hr hv => ?_, trivial⟩
  simp only [EState.ofSem, EState.ofGlob, Contract.initState, Contract.initStorage,
    lookupBy_map_snd, hr, Option.map_some, Option.some.injEq] at hv
  subst hv
  exact defaultForTy_tight (okDeep_defaultOkS (hd r T hr))

end Solidity

namespace Solidity

open Semantics
open SemanticsProperties (lookupBy_eq_some_mem)
open Semantics.SVal.canon (canonFields canonElems canonEntries)
open Semantics.SVal.tight (tightFields tightElems tightEntries)

variable {C : Contract}

section Exact


/-! ### The characterisation -/

theorem deepOk_of_all (h : C.vars.all (·.2.okDeep) = true) : DeepOk C :=
  fun _ _ hr => List.all_eq_true.mp h _ (lookupBy_eq_some_mem hr)

theorem defaultOkS_of_deep (h : C.vars.all (·.2.okDeep) = true) :
    C.vars.all (·.2.defaultOkS) = true :=
  List.all_eq_true.mpr fun g hg => okDeep_defaultOkS (List.all_eq_true.mp h g hg)

/-- **Reachable ⇒ tight.** -/
theorem reachable_tight (hnd : nodupKeysB C.vars = true) (hdeep : C.vars.all (·.2.okDeep) = true)
    {st : List (Name × Semantics.SVal)} (h : Reachable C st) : TightStorage C st := by
  obtain ⟨Γ', P, o, hrun, rfl⟩ := h
  have hc : CanonStorage C (State.init C).erase.storage := by
    rw [Reachable.init_erase]; exact (Canon.init (σ := C.initState) rfl).storage
  have ht : Tight C (State.init C).erase := by
    rw [Reachable.init_erase]; exact Tight.init (deepOk_of_all hdeep)
  exact (Prog.run_tight (deepOk_of_all hdeep) hnd P hc ht hrun).storage

/-- **Reachable ⇒ canonical and tight**, for a contract whose types have
well-formed defaults all the way down. -/
theorem reachable_shape (hnd : nodupKeysB C.vars = true) (hdeep : C.vars.all (·.2.okDeep) = true)
    {st : List (Name × Semantics.SVal)} (h : Reachable C st) : CanonStorage C st ∧ TightStorage C st :=
  ⟨(reachable_canon hnd h).2, reachable_tight hnd hdeep h⟩

/-- **The reachable storages, exactly**: for a contract whose types have
well-formed defaults all the way down, a storage whose words, keys and slots
are in range (`FitsStorage`, what a literal can write) is reachable by a
program iff it is canonical and tight. -/
theorem reachable_iff (hnd : nodupKeysB C.vars = true) (hdeep : C.vars.all (·.2.okDeep) = true)
    {st : List (Name × Semantics.SVal)} (hf : FitsStorage C st) :
    Reachable C st ↔ CanonStorage C st ∧ TightStorage C st :=
  ⟨reachable_shape hnd hdeep, fun ⟨hc, ht⟩ => canon_reachable hnd (defaultOkS_of_deep hdeep) hc ht hf⟩

/-! ### What is reachable and what is not -/

section Witnesses

/-- One `uint[]` root. -/
def Words : Contract := contract!{ uint[] xs; }

/-- One `uint[2]` root. -/
def Pairs : Contract := contract!{ uint[2] pair; }

/-- One `bool`-keyed mapping root. -/
def BoolKeyed : Contract := contract!{ mapping(bool => uint) flags; }

/-- One `Token[]` root. -/
def Tokens : Contract := contract!{ Token[] tokens; }

/-- A word past the end of a `uint[]` that is not cleared: canonical, not
reachable, since `pop`, `delete` and a shorter copy clear the words they
leave behind and nothing writes past the end of an array of words. -/
theorem dirty_word_not_reachable :
    CanonStorage Words [("xs", .array [] [.int 5] false)] ∧
      ¬ Reachable Words [("xs", .array [] [.int 5] false)] := by
  refine ⟨⟨rfl, fun r T hr => ?_⟩, fun h => ?_⟩
  · simp only [Words, lookupBy] at hr
    split at hr
    · rename_i he; subst he; cases hr
      exact ⟨_, rfl, rfl, trivial, trivial, trivial⟩
    · exact nomatch hr
  · have ht := reachable_tight (by decide) (by decide) h "xs" _ _ rfl rfl
    have := ht.2.1 rfl (.int 5) (by simp only [List.mem_cons, List.not_mem_nil, or_false])
    simp only [defaultForTy, Semantics.SVal.prim.injEq, PrimVal.int.injEq, Int.reduceEq] at this

/-- A slot past the end of a fixed-size array: canonical, not reachable. -/
theorem fixed_past_end_not_reachable :
    CanonStorage Pairs [("pair", .array [.int 0, .int 0] [.int 0] true)] ∧
      ¬ Reachable Pairs [("pair", .array [.int 0, .int 0] [.int 0] true)] := by
  refine ⟨⟨rfl, fun r T hr => ?_⟩, fun h => ?_⟩
  · simp only [Pairs, lookupBy] at hr
    split at hr
    · rename_i he; subst he; cases hr
      exact ⟨_, rfl, rfl, rfl, ⟨trivial, trivial, trivial⟩, trivial, trivial⟩
    · exact nomatch hr
  · have ht := reachable_tight (by decide) (by decide) h "pair" _ _ rfl rfl
    exact nomatch ht.1

/-- One `uint[2^256 + 1]` root: more slots than a `uint` index reaches
(solc refuses a storage type that large). -/
def Huge : Contract := { vars := [("big", .ref (.fixed .uint (2 ^ 256 + 1)))] }

/-- **Reachable does not imply `FitsStorage`** (decision 77): `Huge`'s
initial storage is reached by the empty program, and its root has
`2^256 + 1` elements, past what `FitsStorage` allows a fixed-size array (the
builder writes each element at a literal index).  So `reachable_iff` keeps
its `FitsStorage` premise: canonical and tight is not enough for this root,
and reachable says nothing about the slot count. -/
theorem huge_reachable_not_fits :
    Reachable Huge Huge.initStorage ∧ ¬ FitsStorage Huge Huge.initStorage := by
  refine ⟨⟨[], .nil, ⟨State.init Huge, List.prefix_refl _⟩, Prog.run_nil _,
    congrArg EState.storage Reachable.init_erase⟩, fun hf => ?_⟩
  have h := hf "big" _ _ rfl rfl
  rw [defaultForTy] at h
  simp only [Semantics.SVal.fits, List.length_replicate] at h
  exact Nat.not_succ_le_self _ h.1

/-- An entry in a `bool`-keyed mapping, at the key `1` that `true` hashes
to (`Value.keyAt`, decisions 10 and 14): reachable, by the builder
(`flags[true] = 3;`). -/
theorem bool_key_reachable :
    Reachable BoolKeyed [("flags", .map [(1, .int 3)] (.int 0))] := by
  refine canon_reachable (by decide) (by decide) ⟨rfl, fun r T hr => ?_⟩ (fun r T v hr hv => ?_)
    fun r T v hr hv => ?_
  · simp only [BoolKeyed, lookupBy] at hr
    split at hr
    · rename_i he; subst he; cases hr
      exact ⟨_, rfl, rfl, ⟨trivial, trivial⟩, defaultForTy_uint.symm, trivial⟩
    · exact nomatch hr
  · simp only [BoolKeyed, lookupBy] at hr
    split at hr
    · rename_i he; subst he; cases hr
      simp only [lookupBy, if_pos] at hv
      cases hv
      exact ⟨(fun h => nomatch h), trivial, trivial⟩
    · exact nomatch hr
  · simp only [BoolKeyed, lookupBy] at hr
    split at hr
    · rename_i he; subst he; cases hr
      simp only [lookupBy, if_pos] at hv
      cases hv
      exact ⟨rfl, rfl, trivial⟩
    · exact nomatch hr

/-- A `Token` past the end of `tokens`, written through a reference taken
before its `pop`: reachable, by the builder. -/
theorem dangling_slot_reachable :
    Reachable Tokens [("tokens", .array [] [.struct [("value", .int 7)]] false)] := by
  refine canon_reachable (by decide) (by decide) ⟨rfl, fun r T hr => ?_⟩ (fun r T v hr hv => ?_)
    fun r T v hr hv => ?_
  · simp only [Tokens, lookupBy] at hr
    split at hr
    · rename_i he; subst he; cases hr
      exact ⟨_, rfl, rfl, trivial, ⟨⟨rfl, trivial, trivial⟩, trivial⟩⟩
    · exact nomatch hr
  · simp only [Tokens, lookupBy] at hr
    split at hr
    · rename_i he; subst he; cases hr
      simp only [lookupBy, if_pos] at hv
      cases hv
      exact ⟨fun h => absurd h (by decide), (fun h => nomatch h), trivial, ⟨⟨trivial, trivial⟩, trivial⟩⟩
    · exact nomatch hr
  · simp only [Tokens, lookupBy] at hr
    split at hr
    · rename_i he; subst he; cases hr
      simp only [lookupBy, if_pos] at hv
      cases hv
      exact ⟨by decide, trivial, ⟨⟨rfl, trivial⟩, trivial⟩⟩
    · exact nomatch hr

end Witnesses

end Exact

end Solidity
