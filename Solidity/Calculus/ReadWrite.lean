import Solidity.Update
import Solidity.Semantics.Properties

/-!
# The untyped heap and storage, read through a copy

What the typed memory laws (`Calculus/TermLaws.lean`, `Calculus/MemRead.lean`,
`Theory/Typed/Mem.lean`) read of the untyped interpreter's copies, through
the erasure of the typed heap: a fresh default object read along a path
(`copyStToM_default_readPath`), a copy read along a member path
(`find_overlay_fields`, `layAt_prim`), and a member of a struct copied
between the two domains (`copyStToM_member`, `copyMem_member`).  The
storage read-after-write part, push and pop, and the transfer frame went
with `sol_close`'s untyped set at W10.5.1 (`docs/intrinsic.md`); the rest
goes when the memory laws read the typed heap (W10.5.4).

This module also registers the closers' simp sets.
-/

/-- The rewrites `sol_close` closes a scoped leaf with
(`Calculus/CloseScoped.lean`): the weakest preconditions and symbols of
`Calculus/CloseLemmas.lean`, the leaf's terms and updates read by position. -/
register_simp_attr close_rw_s

/-- The bare box and diamond, which `sol_close` tries after every lemma of
`close_rw_s`: a `simp` set listed later is consulted later. -/
register_simp_attr close_rw_s_last

/-- The evaluation of the reduced formulas `sol_decide` closes (`Decide.lean`). -/
register_simp_attr decide_eval

/-- The same over free reads, for `sol_decide`'s constraints (`DecideComplete.lean`). -/
register_simp_attr decide_evalA

namespace Solidity

open Semantics SemanticsProperties

theorem Semantics.Res.ok_bind' {α β : Type} (a : α) (f : α → Res β) : ((Except.ok a : Res α) >>= f) = f a := rfl

/-! ## A fresh default object, read along a path

`addM(m, R)` copies the default of `R` into memory (`allocDefault`), so what
a path below the fresh root reads is what the declared type at that path
says (`copyStToM_default_readPath`): a primitive's default, or a reference
the copy allocated, below the counter it leaves.  `Ty.memberTy` is the
declared type at a path; `MVal.readPath` follows a path through memory. -/

/-- The object a memory address is in. -/
def Semantics.Addr.id : Addr → Nat
  | .memoryField id _ | .memoryIndex id _ => id

/-- The address of a path step from the object `id`. -/
def Semantics.Addr.ofSeg (id : Nat) : Seg → Addr
  | .field f => .memoryField id f
  | .at k => .memoryIndex id k

theorem Semantics.State.getObj_heapExt {σ τ : State} (h : σ.HeapExt τ) {id : Nat} (hid : id < σ.nextId) :
    τ.getObj id = σ.getObj id := by
  unfold State.getObj
  rw [h.2 id hid]

/-- An object below the counter reads the same in a heap extension. -/
theorem readAddr_heapExt {σ τ : State} (h : σ.HeapExt τ) {a : Addr} (ha : a.id < σ.nextId) :
    readAddr τ a = readAddr σ a := by
  cases a with
  | memoryField id f => simp only [readAddr, State.getObj_heapExt h (id := id) ha]
  | memoryIndex id i => simp only [readAddr, State.getObj_heapExt h (id := id) ha]

/-- The slot at the end of a path from a memory value: a reference is
followed, a primitive ends it. -/
def Semantics.MVal.readPath (τ : State) : MVal → List Seg → Res MVal
  | mv, [] => .ok mv
  | .ref id, s :: rest => readAddr τ (.ofSeg id s) >>= fun mv => mv.readPath τ rest
  | .prim _, _ :: _ => .error .undef

/-- The slot at the end of a path from the object `id`. -/
def Semantics.State.readPath (τ : State) (id : Nat) (p : List Seg) : Res MVal :=
  MVal.readPath τ (.ref id) p

theorem Semantics.MVal.readPath_snoc (τ : State) : (mv : MVal) → (p : List Seg) → (s : Seg) →
    mv.readPath τ (p ++ [s]) = mv.readPath τ p >>= fun mv' => match mv' with
      | .ref id => readAddr τ (.ofSeg id s)
      | .prim _ => .error .undef
  | .ref id, [], s => by
    simp only [List.nil_append, MVal.readPath, Res.ok_bind']
    cases readAddr τ (.ofSeg id s) <;> rfl
  | .prim _, [], _ => rfl
  | .ref id, s' :: p, s => by
    simp only [List.cons_append, MVal.readPath]
    cases readAddr τ (.ofSeg id s') with
    | error _ => rfl
    | ok mv => simp only [Res.ok_bind', MVal.readPath_snoc τ mv p s]
  | .prim _, _ :: _, _ => rfl

/-- The declared type of a member or a fixed element: a struct's member, a
fixed array's element in range. -/
def Ty.at : Ty → Seg → Option Ty
  | .ref (.struct sn), .field f => lookupBy f (structDef sn)
  | .ref (.fixed E n), .at k => if 0 ≤ k ∧ k < n then some E else none
  | _, _ => none

/-- The declared type at the end of a path, member by member. -/
def Ty.memberTy : Ty → List Seg → Option Ty
  | T, [] => some T
  | T, s :: rest => (T.at s).bind (·.memberTy rest)

/-- The declared type at a path below a reference type. -/
def RefTy.memberTy (R : RefTy) (p : List Seg) : Option Ty := (Ty.ref R).memberTy p

theorem Ty.memberTy_append (T : Ty) : (p q : List Seg) →
    T.memberTy (p ++ q) = (T.memberTy p).bind (·.memberTy q)
  | [], q => rfl
  | s :: p, q => by
    simp only [List.cons_append, Ty.memberTy]
    cases T.at s <;> simp only [Option.bind, Ty.memberTy_append]

theorem Ty.at_prim (q : PrimTy) (s : Seg) : (Ty.prim q).at s = none := by
  cases s <;> rfl

/-- The memory value a default of `T` copies to: the primitive default, or a
reference below the counter `n`. -/
def DefaultMVal : Ty → MVal → Nat → Prop
  | .prim q, mv, _ => mv = (PrimTy.default q).toMVal
  | .ref _, mv, n => ∃ id, mv = .ref id ∧ id < n

theorem DefaultMVal.mono {T : Ty} {mv : MVal} {n n' : Nat} (h : DefaultMVal T mv n) (hn : n ≤ n') :
    DefaultMVal T mv n' := by
  cases T with
  | prim q => exact h
  | ref R =>
    obtain ⟨id, rfl, hid⟩ := h
    exact ⟨id, rfl, Nat.lt_of_lt_of_le hid hn⟩

theorem copyStToM_default_prim {σ τ : State} {q : PrimTy} {mv : MVal}
    (h : copyStToM σ (defaultForTy (.prim q)) = .ok (τ, mv)) :
    τ = σ ∧ mv = (PrimTy.default q).toMVal := by
  cases q <;> simp [defaultForTy] at h <;> obtain ⟨rfl, rfl⟩ := h <;> exact ⟨rfl, rfl⟩

theorem copyStToM_struct_ref {σ τ : State} {fields : List (Name × SVal)} {mv : MVal}
    (h : copyStToM σ (.struct fields) = .ok (τ, mv)) : ∃ id, mv = .ref id := by
  rw [copyStToM] at h
  cases hf : copyStFields σ fields with
  | error e => rw [hf] at h; exact absurd h (by simp [bind, Except.bind])
  | ok tf =>
    obtain ⟨t', mfields⟩ := tf
    rw [hf] at h
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq, State.alloc] at h
    exact ⟨_, h.2.symm⟩

theorem copyStToM_array_ref {σ τ : State} {elems shadow : List SVal} {fx : Bool} {mv : MVal}
    (h : copyStToM σ (.array elems shadow fx) = .ok (τ, mv)) : ∃ id, mv = .ref id := by
  rw [copyStToM] at h
  cases he : copyStElems σ elems with
  | error e => rw [he] at h; exact absurd h (by simp [bind, Except.bind])
  | ok te =>
    obtain ⟨t', melems⟩ := te
    rw [he] at h
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq, State.alloc] at h
    exact ⟨_, h.2.symm⟩

theorem copyStToM_default_ref {σ τ : State} {R : RefTy} {mv : MVal}
    (h : copyStToM σ (defaultForTy (.ref R)) = .ok (τ, mv)) : ∃ id, mv = .ref id ∧ id < τ.nextId := by
  have hr : ∃ id, mv = .ref id := by
    cases R with
    | struct sn => rw [defaultForTy] at h; exact copyStToM_struct_ref h
    | array E => rw [defaultForTy] at h; exact copyStToM_array_ref h
    | fixed E n => rw [defaultForTy] at h; exact copyStToM_array_ref h
    | mapping K V => rw [defaultForTy] at h; simp [copyStToM] at h
  obtain ⟨id, rfl⟩ := hr
  exact ⟨id, rfl, copyStToM_ref_lt h⟩

/-- The members of a struct copy of defaults: each the copy of its member's
default, into a heap the copy of the struct extends. -/
theorem copyStFields_default_lookup :
    ∀ {σ τ : State} {L : List (Name × Ty)} {mfields : List (Name × MVal)},
      copyStFields σ (defaultForFields L) = .ok (τ, mfields) → ∀ f,
        (∀ mv, lookupBy f mfields = some mv → ∃ T σ₁ σ₂, lookupBy f L = some T ∧
          copyStToM σ₁ (defaultForTy T) = .ok (σ₂, mv) ∧ σ₂.HeapExt τ) ∧
        (∀ T, lookupBy f L = some T → ∃ mv σ₁ σ₂, lookupBy f mfields = some mv ∧
          copyStToM σ₁ (defaultForTy T) = .ok (σ₂, mv) ∧ σ₂.HeapExt τ)
  | σ, τ, [], mfields, h, f => by
    rw [defaultForFields] at h
    simp [copyStFields] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun mv hmv => by simp [lookupBy] at hmv, fun T hT => by simp [lookupBy] at hT⟩
  | σ, τ, (n, T) :: L, mfields, h, f => by
    rw [defaultForFields, copyStFields] at h
    cases h1 : copyStToM σ (defaultForTy T) with
    | error e => simp [h1, bind, Except.bind] at h
    | ok p =>
      obtain ⟨σ₁, mv⟩ := p
      cases h2 : copyStFields σ₁ (defaultForFields L) with
      | error e => simp [h1, h2, bind, Except.bind] at h
      | ok q =>
        obtain ⟨σ₂, mrest⟩ := q
        simp only [h1, h2, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hext : σ₁.HeapExt _ := copyStFields_heapExt σ₁ _ _ _ h2
        by_cases hf : f = n
        · subst hf
          simp only [lookupBy, if_true]
          exact ⟨fun mv' hmv' => by cases hmv'; exact ⟨T, σ, σ₁, rfl, h1, hext⟩,
            fun T' hT' => by cases hT'; exact ⟨mv, σ, σ₁, rfl, h1, hext⟩⟩
        · simp only [lookupBy, hf, if_false]
          exact copyStFields_default_lookup h2 f

/-- The elements of a copy of `n` defaults: each the copy of the default. -/
theorem copyStElems_replicate {v : SVal} :
    ∀ {n : Nat} {σ τ : State} {melems : List MVal},
      copyStElems σ (List.replicate n v) = .ok (τ, melems) →
      melems.length = n ∧ ∀ j (hj : j < melems.length), ∃ σ₁ σ₂,
        copyStToM σ₁ v = .ok (σ₂, melems[j]) ∧ σ₂.HeapExt τ
  | 0, σ, τ, melems, h => by
    simp [List.replicate, copyStElems] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun j hj => absurd hj (by simp)⟩
  | n + 1, σ, τ, melems, h => by
    rw [List.replicate_succ, copyStElems] at h
    cases h1 : copyStToM σ v with
    | error e => simp [h1, bind, Except.bind] at h
    | ok p =>
      obtain ⟨σ₁, mv⟩ := p
      cases h2 : copyStElems σ₁ (List.replicate n v) with
      | error e => simp [h1, h2, bind, Except.bind] at h
      | ok q =>
        obtain ⟨σ₂, mrest⟩ := q
        simp only [h1, h2, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hlen, hrest⟩ := copyStElems_replicate h2
        refine ⟨by simp [hlen], fun j hj => ?_⟩
        cases j with
        | zero => exact ⟨σ, σ₁, h1, copyStElems_heapExt σ₁ _ _ _ h2⟩
        | succ j => exact hrest j (by simpa using hj)

/-- **A fresh default object, read along a path**: what is there is what the
declared type at the path says — a primitive's default, or a reference
allocated by the copy — and it is there exactly at the declared paths. -/
theorem copyStToM_default_readPath : (p : List Seg) → ∀ {T : Ty} {σ τ : State} {mv : MVal},
    copyStToM σ (defaultForTy T) = .ok (τ, mv) → ∀ {τ' : State}, τ.HeapExt τ' →
    (∀ mv', mv.readPath τ' p = .ok mv' → ∃ T', T.memberTy p = some T' ∧ DefaultMVal T' mv' τ.nextId) ∧
    (∀ T', T.memberTy p = some T' → ∃ mv', mv.readPath τ' p = .ok mv' ∧ DefaultMVal T' mv' τ.nextId)
  | [], T, σ, τ, mv, h, τ', hext => by
    have hd : DefaultMVal T mv τ.nextId := by
      cases T with
      | prim q => exact (copyStToM_default_prim h).2
      | ref R => exact copyStToM_default_ref h
    exact ⟨fun mv' hmv' => by simp only [MVal.readPath] at hmv'; cases hmv'; exact ⟨T, rfl, hd⟩,
      fun T' hT' => by cases hT'; exact ⟨mv, by simp only [MVal.readPath], hd⟩⟩
  | s :: rest, T, σ, τ, mv, h, τ', hext => by
    cases T with
    | prim q =>
      obtain ⟨rfl, rfl⟩ := copyStToM_default_prim h
      refine ⟨fun mv' hmv' => ?_, fun T' hT' => ?_⟩
      · cases q <;> simp [PrimTy.default, Value.toMVal, MVal.readPath] at hmv'
      · simp [Ty.memberTy, Ty.at_prim] at hT'
    | ref R =>
      cases R with
      | mapping K V => rw [defaultForTy] at h; simp [copyStToM] at h
      | array E =>
        rw [defaultForTy, copyStToM] at h
        simp only [copyStElems, Res.ok_bind', State.alloc, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hobj : τ'.getObj σ.nextId = .ok (.array [] false) := by
          rw [State.getObj_heapExt hext (Nat.lt_succ_self _)]
          exact State.alloc_fresh σ (.array [] false)
        refine ⟨fun mv' hmv' => ?_, fun T' hT' => ?_⟩
        · cases s <;> simp [MVal.readPath, Addr.ofSeg, readAddr, hobj, bind, Except.bind] at hmv'
        · cases s <;> simp [Ty.memberTy, Ty.at] at hT'
      | struct sn =>
        rw [defaultForTy, copyStToM] at h
        cases hf : copyStFields σ (defaultForFields (structDef sn)) with
        | error e => rw [hf] at h; exact absurd h (by simp [bind, Except.bind])
        | ok tf =>
          obtain ⟨τ₁, mfields⟩ := tf
          rw [hf] at h
          simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq, State.alloc] at h
          obtain ⟨rfl, rfl⟩ := h
          have hobj : τ'.getObj τ₁.nextId = .ok (.struct mfields) := by
            rw [State.getObj_heapExt hext (Nat.lt_succ_self _)]
            exact State.alloc_fresh τ₁ (.struct mfields)
          have hext' : ∀ {σ₂ : State}, σ₂.HeapExt τ₁ → σ₂.HeapExt τ' :=
            fun h₂ => h₂.trans ((State.HeapExt.alloc τ₁ (.struct mfields)).trans hext)
          cases s with
          | «at» k =>
            refine ⟨fun mv' hmv' => ?_, fun T' hT' => ?_⟩
            · simp [MVal.readPath, Addr.ofSeg, readAddr, hobj, bind, Except.bind] at hmv'
            · simp [Ty.memberTy, Ty.at] at hT'
          | field f =>
            have hread : readAddr τ' (.ofSeg τ₁.nextId (.field f)) =
                match lookupBy f mfields with | some v => .ok v | none => .error .undef := by
              simp [Addr.ofSeg, readAddr, hobj, bind, Except.bind, pure, Except.pure] <;> rfl
            have hlk := copyStFields_default_lookup hf f
            refine ⟨fun mv' hmv' => ?_, fun T' hT' => ?_⟩
            · simp only [MVal.readPath, hread] at hmv'
              cases hl : lookupBy f mfields with
              | none => simp [hl, bind, Except.bind] at hmv'
              | some mv₁ =>
                simp only [hl, Res.ok_bind'] at hmv'
                obtain ⟨T₁, σ₁, σ₂, hT₁, hc, hext₁⟩ := hlk.1 mv₁ hl
                obtain ⟨T', hT', hd⟩ := (copyStToM_default_readPath rest hc (hext' hext₁)).1 mv' hmv'
                refine ⟨T', ?_, hd.mono (Nat.le_trans hext₁.1 (Nat.le_succ _))⟩
                simp [Ty.memberTy, Ty.at, hT₁, hT']
            · simp only [Ty.memberTy, Ty.at] at hT'
              cases hT₁ : lookupBy f (structDef sn) with
              | none => simp [hT₁] at hT'
              | some T₁ =>
                simp only [hT₁, Option.bind] at hT'
                obtain ⟨mv₁, σ₁, σ₂, hl, hc, hext₁⟩ := hlk.2 T₁ hT₁
                obtain ⟨mv', hmv', hd⟩ := (copyStToM_default_readPath rest hc (hext' hext₁)).2 T' hT'
                refine ⟨mv', ?_, hd.mono (Nat.le_trans hext₁.1 (Nat.le_succ _))⟩
                simp only [MVal.readPath, hread, hl, Res.ok_bind']
                exact hmv'
      | fixed E n =>
        rw [defaultForTy, copyStToM] at h
        cases he : copyStElems σ (List.replicate n (defaultForTy E)) with
        | error e => rw [he] at h; exact absurd h (by simp [bind, Except.bind])
        | ok te =>
          obtain ⟨τ₁, melems⟩ := te
          rw [he] at h
          simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq, State.alloc] at h
          obtain ⟨rfl, rfl⟩ := h
          have hobj : τ'.getObj τ₁.nextId = .ok (.array melems true) := by
            rw [State.getObj_heapExt hext (Nat.lt_succ_self _)]
            exact State.alloc_fresh τ₁ (.array melems true)
          have hext' : ∀ {σ₂ : State}, σ₂.HeapExt τ₁ → σ₂.HeapExt τ' :=
            fun h₂ => h₂.trans ((State.HeapExt.alloc τ₁ (.array melems true)).trans hext)
          obtain ⟨hlen, helems⟩ := copyStElems_replicate he
          cases s with
          | field f =>
            refine ⟨fun mv' hmv' => ?_, fun T' hT' => ?_⟩
            · simp [MVal.readPath, Addr.ofSeg, readAddr, hobj, bind, Except.bind] at hmv'
            · simp [Ty.memberTy, Ty.at] at hT'
          | «at» k =>
            have hread : readAddr τ' (.ofSeg τ₁.nextId (.at k)) =
                if hk : 0 ≤ k ∧ k.toNat < melems.length then .ok melems[k.toNat]
                else .error .revert := by
              simp [Addr.ofSeg, readAddr, hobj, bind, Except.bind, pure, Except.pure]
            refine ⟨fun mv' hmv' => ?_, fun T' hT' => ?_⟩
            · simp only [MVal.readPath, hread] at hmv'
              split at hmv'
              · rename_i hk
                simp only [Res.ok_bind'] at hmv'
                obtain ⟨σ₁, σ₂, hc, hext₁⟩ := helems k.toNat hk.2
                obtain ⟨T', hT', hd⟩ := (copyStToM_default_readPath rest hc (hext' hext₁)).1 mv' hmv'
                refine ⟨T', ?_, hd.mono (Nat.le_trans hext₁.1 (Nat.le_succ _))⟩
                have hk' : 0 ≤ k ∧ k < n := ⟨hk.1, by rw [← hlen]; omega⟩
                simp [Ty.memberTy, Ty.at, hk', hT']
              · simp [bind, Except.bind] at hmv'
            · simp only [Ty.memberTy, Ty.at] at hT'
              split at hT'
              · rename_i hk
                simp only [Option.bind] at hT'
                have hk' : 0 ≤ k ∧ k.toNat < melems.length := ⟨hk.1, by rw [hlen]; omega⟩
                obtain ⟨σ₁, σ₂, hc, hext₁⟩ := helems k.toNat hk'.2
                obtain ⟨mv', hmv', hd⟩ := (copyStToM_default_readPath rest hc (hext' hext₁)).2 T' hT'
                refine ⟨mv', ?_, hd.mono (Nat.le_trans hext₁.1 (Nat.le_succ _))⟩
                simp only [MVal.readPath, hread, hk']
                exact hmv'
              · simp at hT'

namespace Close

/-! ## Storage: reading through a copy

A copy lays the source over the tree there (`SVal.overlay`).  Along members
it is read as the source, laid over what the target held at the same
place: a word read is the source's word. -/

/-- A path of members only: `account.balance`, `tokens.length`. -/
def fieldPath : List Seg → Bool
  | [] => true
  | .field _ :: q => fieldPath q
  | .at _ :: _ => false

@[simp] theorem fieldPath_nil : fieldPath [] = true := rfl
@[simp] theorem fieldPath_field (f : Name) (q : List Seg) :
    fieldPath (.field f :: q) = fieldPath q := rfl
@[simp] theorem fieldPath_at (i : Int) (q : List Seg) : fieldPath (.at i :: q) = false := rfl

/-- What a copy leaves at a member path, given what the source holds there:
the source's value laid over the target's (`layAt_prim`: a word is the
source's word). -/
def layAt : SVal → List Seg → SVal → SVal
  | old, [], v => old.overlay v
  | .struct ofs, .field f :: q, v =>
    match lookupBy f ofs with
    | some o => layAt o q v
    | none => v.strip
  | _, _ :: _, v => v.strip

theorem stripElems_length : ∀ (l : List SVal), (SVal.strip.stripElems l).length = l.length
  | [] => rfl
  | _ :: l => by simp [SVal.strip.stripElems, stripElems_length l]

/-- A word copied is the word: `alice.age` after `alice = bob;` is `bob.age`. -/
@[simp] theorem layAt_prim (old : SVal) (q : List Seg) (p : PrimVal) :
    layAt old q (.prim p) = .prim p := by
  induction q generalizing old with
  | nil => cases old <;> rfl
  | cons s q ih =>
    cases old with
    | struct ofs =>
      cases s with
      | field f =>
        simp only [layAt]
        split
        · exact ih _
        · rfl
      | «at» _ => rfl
    | prim _ => rfl
    | array _ _ _ => rfl
    | map _ _ => rfl

/-- Reading laid-on-fresh-slots values along members: as before, stripped. -/
theorem find_strip_fields : ∀ (v : SVal) (q : List Seg), fieldPath q = true →
    v.strip.find q = v.find q >>= fun w => .ok w.strip
  | v, [], _ => by simp [SVal.find_nil, bind, Except.bind]
  | .prim _, .field _ :: _, _ => by simp [SVal.strip, SVal.find, bind, Except.bind]
  | .struct fields, .field f :: q, hq => by
    simp only [fieldPath_field] at hq
    have hl : ∀ fs : List (Name × SVal), lookupBy f (SVal.strip.stripFields fs) =
        (lookupBy f fs).map SVal.strip := by
      intro fs
      induction fs with
      | nil => rfl
      | cons hd tl ih =>
        obtain ⟨n, w⟩ := hd
        simp only [SVal.strip.stripFields, lookupBy]
        split <;> simp_all
    simp only [SVal.strip, SVal.find, hl fields]
    cases lookupBy f fields with
    | none => rfl
    | some w => exact find_strip_fields w q hq
  | .array elems shadow fx, .field f :: q, hq => by
    by_cases hf : f = "length"
    · subst hf
      have hlen : (SVal.strip.stripElems elems).length = elems.length := by
        induction elems with
        | nil => rfl
        | cons _ _ ih => simp [SVal.strip.stripElems, ih]
      simp only [SVal.strip, SVal.find, hlen]
      cases fx; rotate_left
      · rfl
      cases q with
      | nil => simp [SVal.find_nil, bind, Except.bind, SVal.strip]
      | cons s q => cases s <;> simp [SVal.find, bind, Except.bind]
    · simp [SVal.strip, SVal.find, hf, bind, Except.bind]
  | .map _ _, .field _ :: _, _ => by simp [SVal.strip, SVal.find, bind, Except.bind]
  | _, .at _ :: _, hq => by simp at hq

/-- **A copy read along members** is the source read, laid over the target
(`SVal.overlay`): after `alice = bob;`, `alice.age` reads `bob.age`
(`layAt_prim`). -/
theorem find_overlay_fields : ∀ (old new : SVal) (q : List Seg), fieldPath q = true →
    (old.overlay new).find q = new.find q >>= fun v => .ok (layAt old q v)
  | old, new, [], _ => by simp [SVal.find_nil, bind, Except.bind, layAt]
  | old, new, .field f :: q, hq => by
    simp only [fieldPath_field] at hq
    cases new with
    | prim p => cases old <;> simp [SVal.overlay, SVal.strip, SVal.find, bind, Except.bind]
    | map ne nd => cases old <;> simp [SVal.overlay, SVal.strip, SVal.find, bind, Except.bind]
    | struct nfs =>
      cases old with
      | struct ofs =>
        have hl : ∀ ns : List (Name × SVal), lookupBy f (SVal.overlay.overlayFields ofs ns) =
            (lookupBy f ns).map (fun v => match lookupBy f ofs with
              | some o => o.overlay v
              | none => v.strip) := by
          intro ns
          induction ns with
          | nil => rfl
          | cons hd tl ih =>
            obtain ⟨n, w⟩ := hd
            simp only [SVal.overlay.overlayFields, lookupBy]
            split
            · rename_i hn; subst hn; first | rfl | simp_all
            · exact ih
        simp only [SVal.overlay, SVal.find, hl nfs, layAt]
        cases hn : lookupBy f nfs with
        | none => rfl
        | some w =>
          simp only [Option.map]
          cases ho : lookupBy f ofs with
          | none =>
            simp only
            rw [find_strip_fields w q hq]
          | some o =>
            simp only
            rw [find_overlay_fields o w q hq]
      | prim _ | array _ _ _ | map _ _ =>
        exact (find_strip_fields (.struct nfs) (.field f :: q) (by simpa using hq)).trans rfl
    | array nel nsh nfx =>
      by_cases hf : f = "length"
      · subst hf
        have hlen : ∀ os : List SVal, (SVal.overlay.overlayElems os nel).length = nel.length := by
          intro os
          induction nel generalizing os with
          | nil => cases os <;> rfl
          | cons x xs ih =>
            cases os with
            | nil =>
              simp only [SVal.overlay.overlayElems]
              exact stripElems_length _
            | cons o os => simp [SVal.overlay.overlayElems, ih]
        cases nfx; rotate_left
        · cases old <;> rfl
        cases old with
        | array oel osh ofx =>
          simp only [SVal.overlay, SVal.find, hlen]
          cases q with
          | nil => simp [SVal.find_nil, bind, Except.bind, layAt, SVal.strip]
          | cons s q => cases s <;> simp [SVal.find, bind, Except.bind]
        | prim _ | struct _ | map _ _ =>
          exact (find_strip_fields (.array nel nsh false) (.field "length" :: q) (by simpa using hq)).trans
            (by cases q <;> simp [SVal.find, bind, Except.bind, layAt_prim, SVal.strip])
      · cases old <;> simp [SVal.overlay, SVal.strip, SVal.find, hf, bind, Except.bind]
  | _, _, .at _ :: _, hq => by simp at hq

/-! ## Memory: a value read -/

/-- The value at a memory address: what `read(memory, m.age)` is. -/
def readVal (σ : State) (a : Addr) : Res Value := readAddr σ a >>= MVal.asValue

/-! ## Copies between storage and memory -/

/-- A copy into memory keeps each primitive: the copy of `alice.age` is
`alice.age`, and a nested struct, which becomes a reference, reads as no
value on either side. -/
theorem copyStToM_asValue {σ τ : State} {v : SVal} {mv : MVal}
    (h : copyStToM σ v = .ok (τ, mv)) : mv.asValue = v.asValue := by
  cases v with
  | prim p =>
    cases p <;> simp [copyStToM] at h <;> obtain ⟨rfl, rfl⟩ := h <;> rfl
  | map _ _ => simp [copyStToM] at h
  | struct fields =>
    rw [copyStToM] at h
    cases hc : copyStFields σ fields with
    | error e => simp [hc, bind, Except.bind] at h
    | ok r =>
      simp only [hc, bind, Except.bind, State.alloc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      rfl
  | array elems shadow fx =>
    rw [copyStToM] at h
    cases hc : copyStElems σ elems with
    | error e => simp [hc, bind, Except.bind] at h
    | ok r =>
      simp only [hc, bind, Except.bind, State.alloc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      rfl

/-- The members a struct copy into memory holds: each the copy of the
storage member of the same name. -/
theorem copyStFields_lookup {σ τ : State} :
    ∀ {fields : List (Name × SVal)} {mfields : List (Name × MVal)},
      copyStFields σ fields = .ok (τ, mfields) → ∀ f,
        (match lookupBy f mfields with | some mv => mv.asValue | none => .error .undef) =
          (match lookupBy f fields with | some v => v.asValue | none => .error .undef)
  | [], mfields, h, f => by
    simp [copyStFields] at h
    obtain ⟨_, rfl⟩ := h
    rfl
  | (n, v) :: rest, mfields, h, f => by
    rw [copyStFields] at h
    cases h1 : copyStToM σ v with
    | error e => simp [h1, bind, Except.bind] at h
    | ok p =>
      obtain ⟨σ₁, mv⟩ := p
      cases h2 : copyStFields σ₁ rest with
      | error e => simp [h1, h2, bind, Except.bind] at h
      | ok q =>
        obtain ⟨σ₂, mrest⟩ := q
        simp only [h1, h2, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        by_cases hf : f = n
        · subst hf; simp [lookupBy, copyStToM_asValue h1]
        · simp only [lookupBy, hf, if_false]
          exact copyStFields_lookup h2 f

/-- **A member of a struct copied into memory**: after
`Person memory m = alice;`, `m.age` reads what `alice.age` held. -/
theorem copyStToM_member {σ τ : State} {v : SVal} {id : Nat} {f : Name}
    (h : copyStToM σ v = .ok (τ, .ref id)) (hf : f ≠ "length") :
    readVal τ (.memoryField id f) = v.find [.field f] >>= SVal.asValue := by
  cases v with
  | prim p => cases p <;> simp [copyStToM] at h
  | map _ _ => simp [copyStToM] at h
  | struct fields =>
    rw [copyStToM] at h
    cases hc : copyStFields σ fields with
    | error e => simp [hc, bind, Except.bind] at h
    | ok r =>
      obtain ⟨σ₁, mfields⟩ := r
      simp only [hc, bind, Except.bind, State.alloc, Except.ok.injEq, Prod.mk.injEq,
        MVal.ref.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := copyStFields_lookup hc f
      simp only [readVal, readAddr, State.getObj, lookupBy_setBy_self, SVal.find, bind,
        Except.bind]
      revert this
      cases lookupBy f mfields <;> cases lookupBy f fields <;> simp [pure, Except.pure]
  | array elems shadow fx =>
    rw [copyStToM] at h
    cases hc : copyStElems σ elems with
    | error e => simp [hc, bind, Except.bind] at h
    | ok r =>
      obtain ⟨σ₁, melems⟩ := r
      simp only [hc, bind, Except.bind, State.alloc, Except.ok.injEq, Prod.mk.injEq,
        MVal.ref.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [readVal, readAddr, State.getObj, lookupBy_setBy_self, SVal.find, bind, Except.bind]

/-- A copy out of memory of a primitive: the primitive. -/
theorem copyMToSt_prim (σ : State) (rem : List Nat) (p : PrimVal) :
    copyMToSt σ rem (.prim p) = .ok (.prim p) := by
  cases p <;> rw [copyMToSt.eq_def]

/-- The members a struct copy out of memory holds. -/
theorem copyMFields_lookup {σ : State} {rem : List Nat} :
    ∀ {fields : List (Name × MVal)} {sfields : List (Name × SVal)},
      copyMFields σ rem fields = .ok sfields → ∀ f,
        (match lookupBy f sfields with | some v => .ok v | none => .error .undef) =
          (match lookupBy f fields with
            | some mv => copyMToSt σ rem mv | none => (.error .undef : Res SVal))
  | [], sfields, h, f => by
    rw [copyMFields] at h
    simp only [Except.ok.injEq] at h
    subst h; rfl
  | (n, mv) :: rest, sfields, h, f => by
    rw [copyMFields] at h
    cases h1 : copyMToSt σ rem mv with
    | error e => simp [h1, bind, Except.bind] at h
    | ok v =>
      cases h2 : copyMFields σ rem rest with
      | error e => simp [h1, h2, bind, Except.bind] at h
      | ok srest =>
        simp only [h1, h2, bind, Except.bind, Except.ok.injEq] at h
        subst h
        by_cases hf : f = n
        · subst hf; simp [lookupBy, h1]
        · simp only [lookupBy, hf, if_false]
          exact copyMFields_lookup h2 f

/-- What a member of a memory object copies to, as a storage value: a
primitive itself, a reference the object it points to. -/
def copyLeaf (σ : State) (id : Nat) (mv : MVal) : Res SVal :=
  copyMToSt σ ((σ.heap.map Prod.fst).erase id) mv

/-- A primitive member copies as itself. -/
theorem copyLeaf_prim (σ : State) (id : Nat) (p : PrimVal) :
    copyLeaf σ id (.prim p) = .ok (.prim p) := copyMToSt_prim σ _ p

/-- **A member of a memory struct copied to storage**: after
`alice = m;`, `alice.age` holds what `m.age` held. -/
theorem copyMem_member {σ : State} {id : Nat} {v : SVal} {f : Name}
    (h : copyMem σ (.ref id) = .ok v) (hf : f ≠ "length") :
    v.find [.field f] = readAddr σ (.memoryField id f) >>= copyLeaf σ id := by
  unfold copyMem at h
  rw [copyMToSt.eq_def] at h
  simp only at h
  split at h
  · rename_i hmem
    cases hg : σ.getObj id with
    | error e => simp [hg] at h
    | ok obj =>
      cases obj with
      | struct fields =>
        cases hc : copyMFields σ ((σ.heap.map Prod.fst).erase id) fields with
        | error e => simp [hg, hc, bind, Except.bind] at h
        | ok sfields =>
          simp only [hg, hc, bind, Except.bind, Except.ok.injEq] at h
          subst h
          have := copyMFields_lookup hc f
          simp only [readAddr, hg, SVal.find, copyLeaf, bind, Except.bind]
          revert this
          cases lookupBy f sfields <;> cases lookupBy f fields <;> simp [pure, Except.pure]
      | array elems =>
        cases hc : copyMElems σ ((σ.heap.map Prod.fst).erase id) elems with
        | error e => simp [hg, hc, bind, Except.bind] at h
        | ok selems =>
          simp only [hg, hc, bind, Except.bind, Except.ok.injEq] at h
          subst h
          simp [readAddr, hg, SVal.find, bind, Except.bind]
  · simp at h

/-- `allocDefault` is a copy of the type's default into memory. -/
theorem allocDefault_copy {σ τ : State} {R : RefTy} {id : Nat}
    (h : allocDefault σ R = .ok (τ, id)) : copyStToM σ (defaultForRef R) = .ok (τ, .ref id) := by
  unfold allocDefault at h
  split at h <;> simp_all

end Close

end Solidity
