import Solidity.Yul.Views.RetainedSourceTrace

namespace Solidity.Yul.Views

def valueStoragePathsM {D : Source.Layout} {σ : Source.STy} (v : Source.Val D σ) : List Source.SPath := by
  cases v with
  | storRef _ p => exact [p]
  | udvt v => exact valueStoragePathsM v
  | int | bool | address | fixedBytes | fixed | enum | contract | internalFn | externalFn | memRef | cdRef => exact []
termination_by structural v

/-- Syntactic reference collection from actual typed values. No current-length
or historical index-formation assertion is made. UDVT payloads are traversed:
valid frontends restrict them further, but arbitrary Layout does not. -/
@[implemented_by valueStoragePathsM]
def valueStoragePaths {D : Source.Layout} : {σ : Source.STy} → Source.Val D σ → List Source.SPath := by
  intro σ v
  induction v with
  | storRef _ p => exact [p]
  | udvt _ ih => exact ih
  | int | bool | address | fixedBytes | fixed | enum | contract | internalFn | externalFn | memRef | cdRef => exact []

theorem valueStoragePaths_eq_M {D σ} (v : Source.Val D σ) : valueStoragePaths v=valueStoragePathsM v := by
  induction v with
  | udvt v ih => exact ih
  | int | bool | address | fixedBytes | fixed | enum | contract | internalFn | externalFn | memRef | storRef | cdRef => rfl

def localStoragePathsM {D : Source.Layout} {Γ : Source.RCtx} (locals : Source.Locals D Γ) : List Source.SPath := by
  cases locals with
  | nil => exact []
  | cons value rest => exact valueStoragePaths value ++ localStoragePathsM rest
termination_by structural locals

@[implemented_by localStoragePathsM]
def localStoragePaths {D : Source.Layout} : {Γ : Source.RCtx} → Source.Locals D Γ → List Source.SPath := by
  intro Γ locals
  induction locals with
  | nil => exact []
  | cons value rest ih => exact valueStoragePaths value ++ ih

theorem localStoragePaths_eq_M {D Γ} (locals : Source.Locals D Γ) : localStoragePaths locals=localStoragePathsM locals := by
  induction locals with
  | nil => rfl
  | cons value rest ih => exact congrArg (valueStoragePaths value ++ ·) ih

def returnStoragePathsM {D : Source.Layout} {types : List Source.STy} (values : Source.Vals D types) : List Source.SPath := by
  cases values with
  | nil => exact []
  | cons value rest => exact valueStoragePaths value ++ returnStoragePathsM rest
termination_by structural values

@[implemented_by returnStoragePathsM]
def returnStoragePaths {D : Source.Layout} : {types : List Source.STy} → Source.Vals D types → List Source.SPath := by
  intro types values
  induction values with
  | nil => exact []
  | cons value rest ih => exact valueStoragePaths value ++ ih

theorem returnStoragePaths_eq_M {D types} (values : Source.Vals D types) : returnStoragePaths values=returnStoragePathsM values := by
  induction values with
  | nil => rfl
  | cons value rest ih => exact congrArg (valueStoragePaths value ++ ·) ih

theorem localStoragePaths_get {D Γ σ} (locals : Source.Locals D Γ) (i : Source.Idx Γ σ)
    (p : Source.SPath) (inside : p ∈ valueStoragePaths (locals.get i)) : p ∈ localStoragePaths locals := by
  induction i with
  | here => cases locals with | cons v rest => exact List.mem_append_left _ inside
  | there i ih => cases locals with | cons v rest => exact List.mem_append_right _ (ih rest inside)

/-- Genuine owner typing at an actual local storRef. RefOK imposes pathTy,
not current ancestor bounds or historical reachability. UDVT recursive path
collection is intentionally not claimed to inherit this lemma automatically. -/
theorem typedEntryReference {E Γ σ} (H : Source.HeapTy) (locals : Source.Locals E.layout Γ)
    (i : Source.Idx Γ σ) (location : σ.loc?=some .storage) (p : Source.SPath)
    (found : locals.get i=Source.Val.storRef location p) (ok : Source.LocalsOK E H locals) :
    E.pathTy p=some σ ∧ p ∈ localStoragePaths locals := by
  have typed := Source.LocalsOK.get locals i ok
  rw [found] at typed
  refine ⟨typed,localStoragePaths_get locals i p ?_⟩
  rw [found]
  exact List.mem_cons_self

/-- Exact root/first-index prefix, including descendants. Merely finding this
prefix does not prove pathTy, RefOK, reachability, or a successful index event. -/
def entryPathIndex (root : Source.DeclName) (p : Source.SPath) : Option Nat :=
  if p.root=root then match p.steps with | .index i :: _ => some i | _ => none else none

def entryPathIndices (root : Source.DeclName) (paths : List Source.SPath) : List Nat :=
  paths.filterMap (entryPathIndex root)

theorem entryPathIndices_member (root : Source.DeclName) (paths : List Source.SPath) (i : Nat) :
    i ∈ entryPathIndices root paths ↔ ∃ p ∈ paths, entryPathIndex root p=some i := by
  exact List.mem_filterMap

/-- Account-tagged endpoint provenance. Paths have no embedded address; this
carrier prevents an implicit reinterpretation under a different frame. It is
a ghost observation, not another source state or a historical event. -/
structure EntryReferenceScope (E : Source.Env) where
  account : Roadmap.Address
  paths : List Source.SPath

def entryLocalScope {E Γ} (F : Source.Fr) (locals : Source.Locals E.layout Γ) : EntryReferenceScope E :=
  ⟨F.this,localStoragePaths locals⟩

def entryReturnScope {E types} (F : Source.Fr) (values : Source.Vals E.layout types) : EntryReferenceScope E :=
  ⟨F.this,returnStoragePaths values⟩

def scopedEntryIndices {E τ b child active a} (layout : @RetainedArrayLayout E τ b child active a)
    (scopes : List (EntryReferenceScope E)) : List Nat :=
  scopes.flatMap fun scope => if scope.account=a then entryPathIndices layout.root scope.paths else []

/-- Monotone finite visit union. Live indices, real formation events, and entry
observations stay separate inputs; no fabricated formation witness is needed. -/
def capturedVisitIndices {E τ b child active a} (layout : @RetainedArrayLayout E τ b child active a)
    (history : RetainedIndexHistory layout) (scopes : List (EntryReferenceScope E)) (length : Nat) : List Nat :=
  uniqueVisitIndices [] (List.range length ++ history.map RetainedIndexEvent.index ++ scopedEntryIndices layout scopes)

theorem capturedVisitIndices_mem {E τ b child active a} (layout : @RetainedArrayLayout E τ b child active a)
    (history : RetainedIndexHistory layout) (scopes : List (EntryReferenceScope E)) (length i : Nat) :
    i ∈ capturedVisitIndices layout history scopes length ↔
      i<length ∨ (∃ event ∈ history, event.index=i) ∨ i ∈ scopedEntryIndices layout scopes := by
  simp only [capturedVisitIndices,uniqueVisitIndices_mem,List.not_mem_nil,not_false_eq_true,and_true,List.mem_append,List.mem_range,List.mem_map]
  exact or_assoc

theorem capturedVisitIndices_unique {E τ b child active a} (layout : @RetainedArrayLayout E τ b child active a)
    (history : RetainedIndexHistory layout) (scopes : List (EntryReferenceScope E)) (length : Nat) :
    (capturedVisitIndices layout history scopes length).Nodup := uniqueVisitIndices_nodup _ _

end Solidity.Yul.Views
