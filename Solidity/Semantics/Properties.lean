import Solidity.Semantics

/-!
# Algebraic properties of the executable semantics

`Semantics.lean` defines the executable interpreter.  This module records the
state and tree laws needed to reason about executions independently of a
particular rewrite rule: association-list updates, storage read-after-write,
frame properties, and freshness of memory allocation.
-/

namespace Solidity
namespace SemanticsProperties

open Semantics

/-! ## Association-list laws -/

@[simp] theorem lookupBy_setBy_self [DecidableEq κ] (k : κ) (v : α)
    (l : List (κ × α)) : lookupBy k (setBy k v l) = some v := by
  induction l with
  | nil => simp only [setBy, lookupBy, ↓reduceIte]
  | cons hd tl ih =>
      obtain ⟨k', v'⟩ := hd
      by_cases h : k = k' <;> simp only [h, setBy, ↓reduceIte, lookupBy, ih]

theorem lookupBy_setBy_ne [DecidableEq κ] {k k' : κ} (h : k ≠ k')
    (v : α) (l : List (κ × α)) :
    lookupBy k (setBy k' v l) = lookupBy k l := by
  induction l with
  | nil => simp only [setBy, lookupBy, h, ↓reduceIte]
  | cons hd tl ih =>
      obtain ⟨k'', v''⟩ := hd
      by_cases h₂ : k' = k''
      · subst h₂
        simp only [setBy, ↓reduceIte, lookupBy, h]
      · by_cases h₃ : k = k'' <;>
          simp only [h₃, setBy, h₂, ↓reduceIte, lookupBy, ih]

/-! ## A live read is a slot read -/

/-- A read that checks every index against the live length reads, where it
returns, what the slot read does: `persons[0].age` with one person. -/
theorem SVal.find_of_findLive : ∀ {v w : SVal} {p : List Seg}, v.findLive p = .ok w →
    v.find p = .ok w
  | v, w, [], h => by simpa only [SVal.find, Except.ok.injEq, SVal.findLive] using h
  | .prim _, w, a :: p, h => by cases a <;> simp only [SVal.findLive, reduceCtorEq] at h
  | .struct fields, w, .field n :: p, h => by
    simp only [SVal.findLive] at h
    simp only [SVal.find]
    split at h
    · rename_i hl; (try rw [hl]); exact SVal.find_of_findLive h
    · simp only [reduceCtorEq] at h
  | .struct _, w, .at _ :: _, h => by simp only [SVal.findLive, reduceCtorEq] at h
  | .array elems shadow _, w, .at i :: p, h => by
    simp only [SVal.findLive] at h
    split at h
    · rename_i hi
      have hi' : 0 ≤ i ∧ i.toNat < (elems ++ shadow).length := by
        simp only [List.length_append]; omega
      simp only [SVal.find, dif_pos hi']
      rw [List.get_eq_getElem, List.getElem_append_left hi.2]
      exact SVal.find_of_findLive h
    · simp only [reduceCtorEq] at h
  | .array elems shadow fx, w, .field n :: p, h => by
    by_cases hn : n = "length"
    · subst hn; simp only [SVal.findLive] at h; simp only [SVal.find]
      cases fx
      · exact SVal.find_of_findLive h
      · simp only [↓reduceIte, reduceCtorEq] at h
    · simp only [SVal.findLive, reduceCtorEq] at h
  | .map entries dflt, w, .at i :: p, h => by
    simp only [SVal.findLive] at h
    simp only [SVal.find]
    split at h <;> rename_i hl <;> (try rw [hl]) <;> exact SVal.find_of_findLive h
  | .map _ _, w, .field _ :: _, h => by simp only [SVal.findLive, reduceCtorEq] at h

theorem State.findStorage_of_findLive {σ : State} {r : Name} {p : List Seg} {w : SVal}
    (h : σ.findLive r p = .ok w) : σ.findStorage r p = .ok w := by
  unfold State.findLive at h
  unfold State.findStorage
  split at h
  · rename_i hl; (try rw [hl]); exact SVal.find_of_findLive h
  · simp only [reduceCtorEq] at h

/-! ## Storage read-after-write -/

/-- A successful tree update is observable by reading the same path.  This
includes insertion at a previously absent mapping key.

The general form — the read at, below, above and *off* the written path — is
the typed Theory's `Obs.findOnSave`/`findOnSavePrefix`/`findOnSaveFrame`
(`Theory/Typed/Obs.lean`), over solkey's own `save`, and needs no
hypothesis that the write succeeded.
This one is kept because the whole typing layer is stated against it. -/
theorem SVal.find_save_same {old new updated : SVal} {path : List Seg}
    (h : old.save path new = .ok updated) :
    updated.find path = .ok new := by
  induction path generalizing old updated with
  | nil =>
      simp only [SVal.save, Except.ok.injEq] at h
      subst updated
      simp only [SVal.find]
  | cons seg rest ih =>
      cases seg with
      | field name =>
          cases old <;> try { simp only [SVal.save, reduceCtorEq] at h }
          rename_i fields
          cases hv : lookupBy name fields with
          | none => simp only [SVal.save, hv, reduceCtorEq] at h
          | some old =>
              simp only [SVal.save, hv] at h
              cases hs : old.save rest new with
              | error e => rw [hs] at h; contradiction
              | ok child =>
                  rw [hs] at h
                  injection h with h'
                  subst updated
                  simp only [SVal.find, lookupBy_setBy_self, ih hs]
      | «at» i =>
          cases old <;> try { simp only [SVal.save, reduceCtorEq] at h }
          · rename_i elems shadow fx
            simp only [SVal.save] at h
            split at h
            next hb =>
              cases hs :
                  ((elems ++ shadow).get ⟨i.toNat, hb.2⟩).save rest new with
              | error e => rw [hs] at h; contradiction
              | ok child =>
                  rw [hs] at h
                  injection h with h'
                  subst updated
                  simp only [SVal.find, hb, List.take_append_drop, List.length_set,
                      List.length_append, Int.toNat_lt, Int.natCast_add, true_and,
                      List.get_eq_getElem, List.getElem_set_self, ih hs, dite_eq_ite,
                      ite_eq_left_iff, Int.not_lt, reduceCtorEq, imp_false, Int.not_le]
                  simp only [List.length_append] at hb; omega
            next hb => contradiction
          · rename_i entries dflt
            cases hv : lookupBy i entries with
            | none =>
                simp only [SVal.save, hv] at h
                cases hs : dflt.save rest new with
                | error e => rw [hs] at h; contradiction
                | ok child =>
                    rw [hs] at h
                    injection h with h'
                    subst updated
                    simp only [SVal.find, lookupBy_setBy_self, ih hs]
            | some old =>
                simp only [SVal.save, hv] at h
                cases hs : old.save rest new with
                | error e => rw [hs] at h; contradiction
                | ok child =>
                    rw [hs] at h
                    injection h with h'
                    subst updated
                    simp only [SVal.find, lookupBy_setBy_self, ih hs]

/-- A successful storage update changes only the storage component. -/
theorem State.saveStorage_frame {s s' : State} {root : Name}
    {path : List Seg} {new : SVal}
    (h : s.saveStorage root path new = .ok s') :
    s'.heap = s.heap ∧ s'.nextId = s.nextId ∧
      s'.env = s.env ∧ s'.net = s.net ∧ s'.selfBalance = s.selfBalance ∧ s'.tx = s.tx := by
  unfold State.saveStorage at h
  cases hv : lookupBy root s.storage with
  | none => simp only [hv, reduceCtorEq] at h
  | some old =>
      simp only [hv] at h
      cases hs : old.save path new with
      | error e => rw [hs] at h; contradiction
      | ok updated =>
          rw [hs] at h
          injection h with h'
          subst s'
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Allocation and heap freshness -/

/-- All allocated object identifiers are strictly below `nextId`.  Stated in
lookup form, this also rules out duplicate stale entries at future IDs. -/
def HeapWellFormed (s : State) : Prop :=
  ∀ id, s.nextId ≤ id → lookupBy id s.heap = none

/-- The freshly returned identifier reads back the allocated object. -/
@[simp] theorem State.alloc_fresh (s : State) (obj : MObj) :
    (s.alloc obj).1.getObj (s.alloc obj).2 = .ok obj := by
  simp only [State.getObj, State.alloc, lookupBy_setBy_self]

namespace HeapWellFormed

/-- The current `nextId` is genuinely absent from a well-formed heap. -/
theorem nextId_fresh {s : State} (h : HeapWellFormed s) :
    lookupBy s.nextId s.heap = none := h s.nextId (Nat.le_refl _)

/-- Fresh allocation preserves the heap invariant. -/
theorem alloc {s : State} (h : HeapWellFormed s) (obj : MObj) :
    HeapWellFormed (s.alloc obj).1 := by
  intro id hid
  change s.nextId + 1 ≤ id at hid
  have hne : id ≠ s.nextId := by omega
  change lookupBy id (setBy s.nextId obj s.heap) = none
  rw [lookupBy_setBy_ne hne]
  exact h id (by omega)

end HeapWellFormed

/-! ## Immediate cross-domain copy facts -/

@[simp] theorem copyStToM_int (s : State) (v : Int) :
    copyStToM s (.int v) = .ok (s, .int v) := rfl

@[simp] theorem copyStToM_bool (s : State) (v : Bool) :
    copyStToM s (.bool v) = .ok (s, .bool v) := rfl

@[simp] theorem copyStToM_map (s : State)
    (entries : List (Int × SVal)) (dflt : SVal) :
    copyStToM s (.map entries dflt) = .error .undef := rfl

/-! ## Deep-copy frame properties -/

/-- Two states agree on every component that a storage-to-memory copy is not
allowed to change: storage, local bindings, the network ledger and the
contract balance.  The heap and `nextId` are intentionally omitted: deep
copying allocates fresh memory objects. -/
def StateFrame (s t : State) : Prop :=
  t.storage = s.storage ∧ t.env = s.env ∧ t.net = s.net ∧
    t.selfBalance = s.selfBalance ∧ t.tx = s.tx

namespace StateFrame

@[simp] theorem refl (s : State) : StateFrame s s := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem trans {s t u : State} (hst : StateFrame s t)
    (htu : StateFrame t u) : StateFrame s u := by
  rcases hst with ⟨hss, hse, hsn, hsb, hsx⟩
  rcases htu with ⟨hts, hte, htn, htb, htx⟩
  exact ⟨hts.trans hss, hte.trans hse, htn.trans hsn, htb.trans hsb, htx.trans hsx⟩

end StateFrame

/-- A state computation is frame-preserving when every successful result
agrees with its input on storage, local bindings, the network ledger and the
contract balance. -/
def FramePreserving (s : State) (r : Res (State × α)) : Prop :=
  ∀ t a, r = .ok (t, a) → StateFrame s t

namespace FramePreserving

theorem pure (s : State) (a : α) :
    FramePreserving s (.ok (s, a)) := by
  intro t b h
  cases h
  exact StateFrame.refl s

/-- Frame preservation composes through state-and-value computations. -/
theorem bind {s : State} {x : Res (State × α)}
    {f : State × α → Res (State × β)}
    (hx : FramePreserving s x)
    (hf : ∀ t a, StateFrame s t → FramePreserving t (f (t, a))) :
    FramePreserving s (x >>= f) := by
  intro u b h
  cases hxv : x with
  | error e =>
      rw [hxv] at h
      contradiction
  | ok ta =>
      obtain ⟨t, a⟩ := ta
      have hst : StateFrame s t := hx t a hxv
      have hfu : f (t, a) = .ok (u, b) := by
        simpa only [hxv] using h
      exact StateFrame.trans hst (hf t a hst u b hfu)

theorem alloc_ref (s : State) (obj : MObj) :
    FramePreserving s
      (let (t, id) := s.alloc obj
       .ok (t, MVal.ref id)) := by
  simp only [FramePreserving, State.alloc]
  intro t mv h
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end FramePreserving

mutual

/-- A successful storage-to-memory copy changes only the heap and its fresh-ID
counter, including for recursively nested structs and arrays. -/
theorem copyStToM_frame (s : State) (v : SVal) :
    FramePreserving s (copyStToM s v) := by
  cases v with
  | prim p =>
      cases p with
      | int v => exact FramePreserving.pure s (MVal.int v)
      | bool b => exact FramePreserving.pure s (MVal.bool b)
  | map entries dflt =>
      intro t mv h
      simp only [copyStToM, reduceCtorEq] at h
  | struct fields =>
      rw [copyStToM]
      apply FramePreserving.bind (copyStFields_frame s fields)
      intro t mfields _
      exact FramePreserving.alloc_ref t (.struct mfields)
  | array elems _ fx =>
      rw [copyStToM]
      apply FramePreserving.bind (copyStElems_frame s elems)
      intro t melems _
      exact FramePreserving.alloc_ref t (.array melems fx)

theorem copyStFields_frame (s : State)
    (fields : List (Name × SVal)) :
    FramePreserving s (copyStFields s fields) := by
  cases fields with
  | nil =>
      exact FramePreserving.pure s []
  | cons field rest =>
      obtain ⟨name, v⟩ := field
      rw [copyStFields]
      apply FramePreserving.bind (copyStToM_frame s v)
      intro t mv _
      apply FramePreserving.bind (copyStFields_frame t rest)
      intro u mrest _
      exact FramePreserving.pure u ((name, mv) :: mrest)

theorem copyStElems_frame (s : State) (elems : List SVal) :
    FramePreserving s (copyStElems s elems) := by
  cases elems with
  | nil =>
      exact FramePreserving.pure s []
  | cons v rest =>
      rw [copyStElems]
      apply FramePreserving.bind (copyStToM_frame s v)
      intro t mv _
      apply FramePreserving.bind (copyStElems_frame t rest)
      intro u mrest _
      exact FramePreserving.pure u (mv :: mrest)

end

/-! ## The fresh-ID counter only grows

A copy allocates; it never frees, so every identity at or above the *final*
`nextId` was already absent before the copy: solkey's `new(mem, r)`, read
on the interpreter (on the typed heap, `Grown.alloc_fresh`). -/

/-- A state computation only advances the fresh-ID counter. -/
def NextIdGrows (s : State) (r : Res (State × α)) : Prop :=
  ∀ t a, r = .ok (t, a) → s.nextId ≤ t.nextId

namespace NextIdGrows

theorem pure (s : State) (a : α) : NextIdGrows s (.ok (s, a)) := by
  intro t b h; cases h; exact Nat.le_refl _

theorem bind {s : State} {x : Res (State × α)}
    {f : State × α → Res (State × β)}
    (hx : NextIdGrows s x)
    (hf : ∀ t a, NextIdGrows t (f (t, a))) :
    NextIdGrows s (x >>= f) := by
  intro u b h
  cases hxv : x with
  | error e => rw [hxv] at h; contradiction
  | ok ta =>
      obtain ⟨t, a⟩ := ta
      have hfu : f (t, a) = .ok (u, b) := by simpa only [hxv] using h
      exact Nat.le_trans (hx t a hxv) (hf t a u b hfu)

theorem alloc_ref (s : State) (obj : MObj) :
    NextIdGrows s
      (let (t, id) := s.alloc obj
       .ok (t, MVal.ref id)) := by
  simp only [NextIdGrows, State.alloc]
  intro t mv h; cases h; exact Nat.le_succ _

end NextIdGrows

/-! ## State-update algebra (`updateRules.key` analogues)

KeY's update calculus applies parallel updates at the point of use
(`applyOnPV`, `applyOnDifferentPV`) and drops effectless elementaries
(`simplifyUpdate1-3`). The Lean model has no update syntax — state
change is function application — so the semantic content of those rules
is the read-after-write / frame / overwrite-absorption laws below.
Storage instances already exist (`State.saveStorage_frame`); these cover locals (`env`) and the payment
ledger (`net`). The update-monoid normal-form machinery
(`sequentialToParallel*`, `applyOnParallel`, skip elimination) is
function composition and needs no port; `commuteSimpleUpdates` /
`elimSelfUpdate*` are commented out in the KeY source. -/

/-- Overwriting the same key twice keeps only the second write
(assoc-list core of KeY `simplifyUpdate1-3`). -/
theorem setBy_setBy_self [DecidableEq κ] (k : κ) (v v' : α)
    (l : List (κ × α)) : setBy k v' (setBy k v l) = setBy k v' l := by
  induction l with
  | nil => simp only [setBy, ↓reduceIte]
  | cons hd tl ih =>
      obtain ⟨k'', v''⟩ := hd
      by_cases h : k = k'' <;> simp only [h, setBy, ↓reduceIte, ih]

/-! ## Paths, runs and results

The laws the calculus, the typing layer and the EVM compiler all use; kept
here once rather than in each of them. -/

/-- A member that `lookupBy` finds is in the list: `age` is a member of `Person`. -/
theorem lookupBy_eq_some_mem [DecidableEq κ] {k : κ} {v : α} :
    ∀ {l : List (κ × α)}, lookupBy k l = some v → (k, v) ∈ l
  | [], h => by simp only [lookupBy, reduceCtorEq] at h
  | (k', v') :: l, h => by
    simp only [lookupBy] at h
    split at h
    · cases h; rename_i hk; subst hk; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookupBy_eq_some_mem h)

/-- Reading at the empty path reads the whole value: `alice` itself. -/
theorem SVal.find_nil (v : SVal) : v.find [] = .ok v := by cases v <;> rfl

/-- Writing at the empty path replaces the whole value: `alice = …` at `alice`. -/
theorem SVal.save_nil (v new : SVal) : v.save [] new = .ok new := by cases v <;> rfl

@[simp] theorem SVal.findLive_nil (v : SVal) : v.findLive [] = .ok v := by cases v <;> rfl

/-- Reading along `segs ++ rest` is reading `segs`, then `rest` from there:
`alice.account.balance` is `alice.account`, then `.balance`. -/
theorem SVal.find_append : ∀ (v : SVal) (segs rest : List Seg),
    v.find (segs ++ rest) = (v.find segs >>= fun w => w.find rest)
  | v, [], rest => by simp only [List.nil_append, SVal.find_nil]; rfl
  | .prim _, _ :: _, _ => by simp only [List.cons_append, SVal.find]; rfl
  | .struct fields, .field name :: segs, rest => by
    simp only [List.cons_append, SVal.find]
    split
    · exact SVal.find_append _ _ _
    · rfl
  | .struct _, .at _ :: _, _ => by simp only [List.cons_append, SVal.find]; rfl
  | .array elems _ _, .at i :: segs, rest => by
    simp only [List.cons_append, SVal.find]
    split
    · exact SVal.find_append _ _ _
    · rfl
  | .array elems sh fx, .field name :: segs, rest => by
    by_cases h : name = "length"
    · subst h; simp only [List.cons_append, SVal.find]
      cases fx
      · exact SVal.find_append _ _ _
      · rfl
    · have e : ∀ l, SVal.find (.array elems sh fx) (.field name :: l) = .error .undef := by
        intro l; simp only [SVal.find]
      simp only [List.cons_append, e]; rfl
  | .map entries dflt, .at i :: segs, rest => by
    simp only [List.cons_append, SVal.find]
    split
    · exact SVal.find_append _ _ _
    · exact SVal.find_append _ _ _
  | .map _ _, .field _ :: _, _ => by simp only [List.cons_append, SVal.find]; rfl

/-- `SVal.find_append` for the live read. -/
theorem SVal.findLive_append : ∀ (v : SVal) (segs rest : List Seg),
    v.findLive (segs ++ rest) = (v.findLive segs >>= fun w => w.findLive rest)
  | v, [], rest => by simp only [List.nil_append, SVal.findLive_nil]; rfl
  | .prim _, _ :: _, _ => by simp only [List.cons_append, SVal.findLive]; rfl
  | .struct fields, .field name :: segs, rest => by
    simp only [List.cons_append, SVal.findLive]
    split
    · exact SVal.findLive_append _ _ _
    · rfl
  | .struct _, .at _ :: _, _ => by simp only [List.cons_append, SVal.findLive]; rfl
  | .array elems _ _, .at i :: segs, rest => by
    simp only [List.cons_append, SVal.findLive]
    split
    · exact SVal.findLive_append _ _ _
    · rfl
  | .array elems sh fx, .field name :: segs, rest => by
    by_cases h : name = "length"
    · subst h; simp only [List.cons_append, SVal.findLive]
      cases fx
      · exact SVal.findLive_append _ _ _
      · rfl
    · have e : ∀ l, SVal.findLive (.array elems sh fx) (.field name :: l) = .error .undef := by
        intro l; simp only [SVal.findLive]
      simp only [List.cons_append, e]; rfl
  | .map entries dflt, .at i :: segs, rest => by
    simp only [List.cons_append, SVal.findLive]
    split
    · exact SVal.findLive_append _ _ _
    · exact SVal.findLive_append _ _ _
  | .map _ _, .field _ :: _, _ => by simp only [List.cons_append, SVal.findLive]; rfl

/-- A write along `segs ++ rest`, where `segs` reads `sub`, writes `rest` into
`sub` and puts the result back at `segs`: `alice.age = 1;` rebuilds `alice`
with its `age` replaced. -/
theorem SVal.save_append : ∀ (v : SVal) (segs rest : List Seg) (new sub : SVal),
    v.find segs = .ok sub → v.save (segs ++ rest) new = (sub.save rest new >>= v.save segs)
  | v, [], rest, new, sub, h => by
    simp only [SVal.find_nil, Except.ok.injEq] at h; subst h
    simp only [List.nil_append]
    cases v.save rest new with
    | error e => rfl
    | ok a => exact (SVal.save_nil v a).symm
  | .prim _, _ :: _, _, _, _, h => by simp only [SVal.find, reduceCtorEq] at h
  | .struct fields, .field name :: segs, rest, new, sub, h => by
    simp only [List.cons_append, SVal.save]
    simp only [SVal.find] at h
    split
    · rename_i old hold
      rw [hold] at h
      rw [SVal.save_append old segs rest new sub h]
      cases sub.save rest new <;> rfl
    · rename_i hn; rw [hn] at h; cases h
  | .struct _, .at _ :: _, _, _, _, h => by simp only [SVal.find, reduceCtorEq] at h
  | .array elems sh _, .at i :: segs, rest, new, sub, h => by
    simp only [List.cons_append, SVal.save]
    simp only [SVal.find] at h
    split
    · rename_i hb; rw [dif_pos hb] at h; rw [SVal.save_append _ segs rest new sub h]
      cases sub.save rest new <;> rfl
    · rename_i hb; rw [dif_neg hb] at h; cases h
  | .array elems sh fx, .field name :: segs, rest, new, sub, h => by
    by_cases hn : name = "length"
    · subst hn
      cases fx
      · cases segs with
        | nil =>
          simp only [SVal.find, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h; subst h
          cases rest <;> simp only [List.append_nil, SVal.save, List.cons_append,
                             List.nil_append] <;> rfl
        | cons s segs => simp only [SVal.find, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      · simp only [SVal.find, ↓reduceIte, reduceCtorEq] at h
    · simp only [SVal.find, reduceCtorEq] at h
  | .map entries dflt, .at i :: segs, rest, new, sub, h => by
    simp only [List.cons_append, SVal.save]
    simp only [SVal.find] at h
    split
    · rename_i old hold; rw [hold] at h; rw [SVal.save_append _ segs rest new sub h]
      cases sub.save rest new <;> rfl
    · rename_i hold; rw [hold] at h; rw [SVal.save_append _ segs rest new sub h]
      cases sub.save rest new <;> rfl
  | .map _ _, .field _ :: _, _, _, _, h => by simp only [SVal.find, reduceCtorEq] at h

/-- `SVal.find_append` at a root: `folks[7].age` is `folks[7]`, then `.age`. -/
theorem State.findStorage_append (σ : State) (r : Name) (segs rest : List Seg) :
    σ.findStorage r (segs ++ rest) = (σ.findStorage r segs >>= fun w => w.find rest) := by
  unfold State.findStorage
  split
  · exact SVal.find_append _ _ _
  · rfl

/-- `SVal.save_append` at a root: `alice.age = 1;` writes `age` below `alice`. -/
theorem State.saveStorage_append {σ : State} {r : Name} {segs : List Seg} {sub : SVal}
    (h : σ.findStorage r segs = .ok sub) (rest : List Seg) (new : SVal) :
    σ.saveStorage r (segs ++ rest) new = (sub.save rest new >>= σ.saveStorage r segs) := by
  unfold State.findStorage at h
  unfold State.saveStorage
  split
  · rename_i v hv
    rw [hv] at h
    rw [SVal.save_append v segs rest new sub h]
    cases sub.save rest new <;> rfl
  · rename_i hv; rw [hv] at h; cases h

/-- The storage a successful `saveStorage` leaves. -/
def _root_.Solidity.Semantics.State.storeRes (σ : State) (r : Name) (segs : List Seg)
    (x : SVal) : Res (List (Name × SVal)) :=
  match lookupBy r σ.storage with
  | some v => do
    let u ← v.save segs x
    pure (setBy r u σ.storage)
  | none => .error .undef

theorem State.saveStorage_eq (σ : State) (r : Name) (segs : List Seg) (x : SVal) :
    σ.saveStorage r segs x = (do let s ← σ.storeRes r segs x; pure { σ with storage := s }) := by
  unfold State.saveStorage State.storeRes
  cases lookupBy r σ.storage with
  | none => rfl
  | some v => cases h : v.save segs x <;> simp only [bind, Except.bind, h, pure, Except.pure]

/-- A write that returned wrote below a root that was there. -/
theorem State.saveStorage_ok_inv {σ σ' : State} {r : Name} {segs : List Seg} {new : SVal}
    (h : σ.saveStorage r segs new = .ok σ') :
    ∃ V up, lookupBy r σ.storage = some V ∧ V.save segs new = .ok up ∧
      σ' = { σ with storage := setBy r up σ.storage } := by
  unfold State.saveStorage at h
  cases hV : lookupBy r σ.storage with
  | none => simp only [hV, reduceCtorEq] at h
  | some V =>
    simp only [hV] at h
    cases hs : V.save segs new with
    | error e => rw [hs] at h; cases h
    | ok up => rw [hs] at h; cases h; exact ⟨V, up, rfl, hs, rfl⟩

/-- `delete` clears a list of elements one by one. -/
theorem defaultOfElems_eq_map :
    ∀ l : List SVal, SVal.defaultOf.defaultOfElems l = l.map SVal.defaultOf
  | [] => rfl
  | v :: l => by simp only [SVal.defaultOf.defaultOfElems, defaultOfElems_eq_map l, List.map_cons]

/-- A deleted struct's member is the member deleted: `delete alice;` makes `alice.age` `0`. -/
theorem lookupBy_defaultOfFields (n : Name) : ∀ fields : List (Name × SVal),
    lookupBy n (SVal.defaultOf.defaultOfFields fields) = (lookupBy n fields).map SVal.defaultOf
  | [] => rfl
  | (m, v) :: fields => by
    simp only [SVal.defaultOf.defaultOfFields, lookupBy]
    split
    · rfl
    · exact lookupBy_defaultOfFields n fields

/-- A fresh struct's member is its type's default: a fresh `Person`'s `age` is `0`. -/
theorem lookupBy_defaultForFields (n : Name) : ∀ l : List (Name × Ty),
    lookupBy n (defaultForFields l) = (lookupBy n l).map defaultForTy
  | [] => by simp only [defaultForFields, lookupBy, Option.map_none]
  | (m, T) :: l => by
    rw [defaultForFields]
    simp only [lookupBy]
    split
    · rfl
    · exact lookupBy_defaultForFields n l

/-- A run that returned passes its value on. -/
theorem Res.ok_bind {α β : Type} (a : α) (f : α → Res β) :
    (Except.ok a >>= f : Res β) = f a := rfl

/-- A run that halted halts what follows. -/
theorem Res.error_bind {α β : Type} (e : Halt) (f : α → Res β) :
    (Except.error e >>= f : Res β) = .error e := rfl

end SemanticsProperties
end Solidity
