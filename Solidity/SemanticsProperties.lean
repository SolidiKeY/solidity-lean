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
  | nil => simp [setBy, lookupBy]
  | cons hd tl ih =>
      obtain ⟨k', v'⟩ := hd
      by_cases h : k = k' <;> simp [setBy, lookupBy, h, ih]

theorem lookupBy_setBy_ne [DecidableEq κ] {k k' : κ} (h : k ≠ k')
    (v : α) (l : List (κ × α)) :
    lookupBy k (setBy k' v l) = lookupBy k l := by
  induction l with
  | nil => simp [setBy, lookupBy, h]
  | cons hd tl ih =>
      obtain ⟨k'', v''⟩ := hd
      by_cases h₂ : k' = k''
      · subst h₂
        simp [setBy, lookupBy, h]
      · by_cases h₃ : k = k'' <;>
          simp [setBy, lookupBy, h₂, h₃, ih]

/-! ## Storage read-after-write -/

/-- A successful tree update is observable by reading the same path.  This
includes insertion at a previously absent mapping key. -/
theorem SVal.find_save_same {old new updated : SVal} {path : List Seg}
    (h : old.save path new = .ok updated) :
    updated.find path = .ok new := by
  induction path generalizing old updated with
  | nil =>
      simp [SVal.save] at h
      subst updated
      simp [SVal.find]
  | cons seg rest ih =>
      cases seg with
      | field name =>
          cases old <;> try { simp [SVal.save] at h }
          rename_i fields
          cases hv : lookupBy name fields with
          | none => simp [SVal.save, hv] at h
          | some old =>
              simp only [SVal.save, hv] at h
              cases hs : old.save rest new with
              | error e => rw [hs] at h; contradiction
              | ok child =>
                  rw [hs] at h
                  injection h with h'
                  subst updated
                  simp [SVal.find, lookupBy_setBy_self, ih hs]
      | «at» i =>
          cases old <;> try { simp [SVal.save] at h }
          · rename_i elems
            simp only [SVal.save] at h
            split at h
            next hb =>
              cases hs :
                  (elems.get ⟨i.toNat, hb.2⟩).save rest new with
              | error e => rw [hs] at h; contradiction
              | ok child =>
                  rw [hs] at h
                  injection h with h'
                  subst updated
                  simp [SVal.find, hb, ih hs]
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
                    simp [SVal.find, lookupBy_setBy_self, ih hs]
            | some old =>
                simp only [SVal.save, hv] at h
                cases hs : old.save rest new with
                | error e => rw [hs] at h; contradiction
                | ok child =>
                    rw [hs] at h
                    injection h with h'
                    subst updated
                    simp [SVal.find, lookupBy_setBy_self, ih hs]

/-- State-level read-after-write, lifted through the storage-root map. -/
theorem State.findStorage_saveStorage_same {s s' : State} {root : Name}
    {path : List Seg} {new : SVal}
    (h : s.saveStorage root path new = .ok s') :
    s'.findStorage root path = .ok new := by
  unfold State.saveStorage at h
  cases hv : lookupBy root s.storage with
  | none => simp [hv] at h
  | some old =>
      simp only [hv] at h
      cases hs : old.save path new with
      | error e => rw [hs] at h; contradiction
      | ok updated =>
          rw [hs] at h
          injection h with h'
          subst s'
          simp [State.findStorage, lookupBy_setBy_self,
            SVal.find_save_same hs]

/-- A successful storage update changes only the storage component. -/
theorem State.saveStorage_frame {s s' : State} {root : Name}
    {path : List Seg} {new : SVal}
    (h : s.saveStorage root path new = .ok s') :
    s'.heap = s.heap ∧ s'.nextId = s.nextId ∧
      s'.env = s.env ∧ s'.net = s.net ∧ s'.selfBalance = s.selfBalance := by
  unfold State.saveStorage at h
  cases hv : lookupBy root s.storage with
  | none => simp [hv] at h
  | some old =>
      simp only [hv] at h
      cases hs : old.save path new with
      | error e => rw [hs] at h; contradiction
      | ok updated =>
          rw [hs] at h
          injection h with h'
          subst s'
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Allocation and heap freshness -/

/-- All allocated object identifiers are strictly below `nextId`.  Stated in
lookup form, this also rules out duplicate stale entries at future IDs. -/
def HeapWellFormed (s : State) : Prop :=
  ∀ id, s.nextId ≤ id → lookupBy id s.heap = none

/-- Allocation returns the identifier it inserts. -/
@[simp] theorem State.alloc_id (s : State) (obj : MObj) :
    (s.alloc obj).2 = s.nextId := rfl

/-- The next fresh identifier advances exactly once. -/
@[simp] theorem State.alloc_nextId (s : State) (obj : MObj) :
    (s.alloc obj).1.nextId = s.nextId + 1 := rfl

/-- The freshly returned identifier reads back the allocated object. -/
@[simp] theorem State.alloc_fresh (s : State) (obj : MObj) :
    (s.alloc obj).1.getObj (s.alloc obj).2 = .ok obj := by
  simp [State.alloc, State.getObj, lookupBy_setBy_self]

/-- Allocation leaves every other heap lookup unchanged. -/
theorem State.alloc_preserves_getObj {s : State} {obj : MObj} {id : Nat}
    (hne : id ≠ s.nextId) :
    (s.alloc obj).1.getObj id = s.getObj id := by
  simp [State.alloc, State.getObj, lookupBy_setBy_ne hne]

/-- Allocation does not change storage, local bindings, the network
ledger, or the contract balance. -/
theorem State.alloc_frame (s : State) (obj : MObj) :
    (s.alloc obj).1.storage = s.storage ∧
      (s.alloc obj).1.env = s.env ∧
      (s.alloc obj).1.net = s.net ∧
      (s.alloc obj).1.selfBalance = s.selfBalance :=
  ⟨rfl, rfl, rfl, rfl⟩

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
    copyStToM s (.map entries dflt) = .error .stuck := rfl

/-! ## Deep-copy frame properties -/

/-- Two states agree on every component that a storage-to-memory copy is not
allowed to change: storage, local bindings, the network ledger and the
contract balance.  The heap and `nextId` are intentionally omitted: deep
copying allocates fresh memory objects. -/
def StateFrame (s t : State) : Prop :=
  t.storage = s.storage ∧ t.env = s.env ∧ t.net = s.net ∧
    t.selfBalance = s.selfBalance

namespace StateFrame

@[simp] theorem refl (s : State) : StateFrame s s := ⟨rfl, rfl, rfl, rfl⟩

theorem trans {s t u : State} (hst : StateFrame s t)
    (htu : StateFrame t u) : StateFrame s u := by
  rcases hst with ⟨hss, hse, hsn, hsb⟩
  rcases htu with ⟨hts, hte, htn, htb⟩
  exact ⟨hts.trans hss, hte.trans hse, htn.trans hsn, htb.trans hsb⟩

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
        simpa [hxv] using h
      exact StateFrame.trans hst (hf t a hst u b hfu)

theorem alloc_ref (s : State) (obj : MObj) :
    FramePreserving s
      (let (t, id) := s.alloc obj
       .ok (t, MVal.ref id)) := by
  simp only [FramePreserving, State.alloc]
  intro t mv h
  cases h
  exact ⟨rfl, rfl, rfl, rfl⟩

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
      simp [copyStToM] at h
  | struct fields =>
      rw [copyStToM]
      apply FramePreserving.bind (copyStFields_frame s fields)
      intro t mfields _
      exact FramePreserving.alloc_ref t (.struct mfields)
  | array elems =>
      rw [copyStToM]
      apply FramePreserving.bind (copyStElems_frame s elems)
      intro t melems _
      exact FramePreserving.alloc_ref t (.array melems)

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

/-! ## State-update algebra (`updateRules.key` analogues)

KeY's update calculus applies parallel updates at the point of use
(`applyOnPV`, `applyOnDifferentPV`) and drops effectless elementaries
(`simplifyUpdate1-3`). The Lean model has no update syntax — state
change is function application — so the semantic content of those rules
is the read-after-write / frame / overwrite-absorption laws below.
Storage instances already exist (`State.findStorage_saveStorage_same`,
`State.saveStorage_frame`); these cover locals (`env`) and the payment
ledger (`net`). The update-monoid normal-form machinery
(`sequentialToParallel*`, `applyOnParallel`, skip elimination) is
function composition and needs no port; `commuteSimpleUpdates` /
`elimSelfUpdate*` are commented out in the KeY source. -/

/-- Overwriting the same key twice keeps only the second write
(assoc-list core of KeY `simplifyUpdate1-3`). -/
theorem setBy_setBy_self [DecidableEq κ] (k : κ) (v v' : α)
    (l : List (κ × α)) : setBy k v' (setBy k v l) = setBy k v' l := by
  induction l with
  | nil => simp [setBy]
  | cons hd tl ih =>
      obtain ⟨k'', v''⟩ := hd
      by_cases h : k = k'' <;> simp [setBy, h, ih]

/-- KeY `applyOnPV`/`applyOnPVLastInParallel` for locals: read after
write at the point of application. -/
@[simp] theorem State.getEnv_setEnv_self (s : State) (n : Name)
    (b : Binding) : (s.setEnv n b).getEnv n = .ok b := by
  simp [State.getEnv, State.setEnv]

/-- KeY `applyOnDifferentPV` for locals: a write to a different name
frames. -/
theorem State.getEnv_setEnv_ne {n n' : Name} (h : n' ≠ n) (s : State)
    (b : Binding) : (s.setEnv n b).getEnv n' = s.getEnv n' := by
  simp [State.getEnv, State.setEnv, lookupBy_setBy_ne h]

/-- KeY `simplifyUpdate1-3` (semantic core): the later write to the same
local absorbs the earlier one. -/
theorem State.setEnv_setEnv_absorb (s : State) (n : Name)
    (b b' : Binding) : (s.setEnv n b).setEnv n b' = s.setEnv n b' := by
  simp [State.setEnv, setBy_setBy_self]

/-- Ledger instance of `applyOnPV`: read after transfer booking. -/
@[simp] theorem State.getNet_setNet_self (s : State) (a v : Int) :
    (s.setNet a v).getNet a = v := by
  simp [State.getNet, State.setNet]

/-- Ledger instance of `applyOnDifferentPV`. -/
theorem State.getNet_setNet_ne {a a' : Int} (h : a' ≠ a) (s : State)
    (v : Int) : (s.setNet a v).getNet a' = s.getNet a' := by
  simp [State.getNet, State.setNet, lookupBy_setBy_ne h]

/-- Ledger overwrite absorption. -/
theorem State.setNet_setNet_absorb (s : State) (a : Int) (v v' : Int) :
    (s.setNet a v).setNet a v' = s.setNet a v' := by
  simp [State.setNet, setBy_setBy_self]

end SemanticsProperties
end Solidity
