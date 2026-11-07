import Solidity.Backend.StorageOps.OperationFamilies
import Solidity.Storage.HashedLayout

/-! Finite access adapters for the published word-layout interface. Requests
contain only existing layout paths and in-place offsets, not a new source AST.
Every request is checked; invalid paths/offsets fail the entire resolution.
STy retains its existing word-granularity/lmax restrictions. This module neither
adds an admitted-source cap nor bridges recursive graph values to that layout. -/
namespace Solidity.Backend.StorageOps.LayoutAccess
open Solidity.Storage Solidity.Hash

/-- Resolve an existing layout path and check an actual word inside its endpoint. -/
def resolve (ty : STy) (base : Solidity.Storage.Loc)
    (path : List Solidity.Storage.Step) (offset : Nat) : Option Solidity.Storage.Loc := do
  let (endpoint, address) ← ty.locate base path
  if offset < endpoint.size then some (address.add offset) else none

theorem resolve_bounded {L R : Nat} {ty : STy} {base address : Solidity.Storage.Loc}
    {path : List Solidity.Storage.Step} {offset : Nat}
    (fits : ty.Fits L) (placed : Placed L R ty base)
    (accepted : resolve ty base path offset = some address) : address.Bounded L R := by
  unfold resolve at accepted
  simp only [Option.bind_eq_bind] at accepted
  cases located : ty.locate base path with
  | none => simp only [located, Option.bind_none] at accepted; cases accepted
  | some pair =>
    obtain ⟨endpoint, first⟩ := pair
    simp only [located, Option.bind_some] at accepted
    split at accepted
    · rename_i inside
      have equal := Option.some.inj accepted
      subst address
      exact (STy.locate_bounded ty base path fits placed located).2 offset inside
    · cases accepted

/-- All-or-failure traversal retains order and repeated requests. It never
silently drops an invalid request via filterMap. -/
def resolveMany (ty : STy) (base : Solidity.Storage.Loc) :
    List (List Solidity.Storage.Step × Nat) → Option (List Solidity.Storage.Loc)
  | [] => some []
  | (path, offset) :: rest => do
    let address ← resolve ty base path offset
    let addresses ← resolveMany ty base rest
    some (address :: addresses)

theorem resolveMany_length {ty : STy} {base : Solidity.Storage.Loc}
    (requests : List (List Solidity.Storage.Step × Nat)) (addresses : List Solidity.Storage.Loc)
    (accepted : resolveMany ty base requests = some addresses) : addresses.length = requests.length := by
  induction requests generalizing addresses with
  | nil => cases accepted; rfl
  | cons request rest ih =>
    obtain ⟨path, offset⟩ := request
    simp only [resolveMany, Option.bind_eq_bind] at accepted
    cases first : resolve ty base path offset with
    | none => simp only [first, Option.bind_none] at accepted; cases accepted
    | some address =>
      cases remaining : resolveMany ty base rest with
      | none => simp only [first, remaining, Option.bind_some, Option.bind_none] at accepted; cases accepted
      | some tail =>
        simp only [first, remaining, Option.bind_some, Option.some.injEq] at accepted
        subst addresses
        exact congrArg Nat.succ (ih tail remaining)

theorem resolveMany_bounded {L R : Nat} {ty : STy} {base : Solidity.Storage.Loc}
    (fits : ty.Fits L) (placed : Placed L R ty base)
    (requests : List (List Solidity.Storage.Step × Nat)) (addresses : List Solidity.Storage.Loc)
    (accepted : resolveMany ty base requests = some addresses) :
    ∀ address ∈ addresses, address.Bounded L R := by
  induction requests generalizing addresses with
  | nil => cases accepted; intro address member; cases member
  | cons request rest ih =>
    obtain ⟨path, offset⟩ := request
    simp only [resolveMany, Option.bind_eq_bind] at accepted
    cases first : resolve ty base path offset with
    | none => simp only [first, Option.bind_none] at accepted; cases accepted
    | some address =>
      cases remaining : resolveMany ty base rest with
      | none => simp only [first, remaining, Option.bind_some, Option.bind_none] at accepted; cases accepted
      | some tail =>
        simp only [first, remaining, Option.bind_some, Option.some.injEq] at accepted
        subst addresses
        intro query member
        rcases List.mem_cons.mp member with equal | later
        · subst query; exact resolve_bounded fits placed first
        · exact ih tail remaining query later

/-- All recursive hash preimages of these resolved accesses, in occurrence
order. Duplicates are allowed; the run premise must hold for this complete list. -/
def runPreimages (N : Nat) (hash : Pre → Nat) (addresses : List Solidity.Storage.Loc) : List Pre :=
  addresses.flatMap (Solidity.Storage.Loc.pres N hash)

theorem mem_runPreimages {N : Nat} {hash : Pre → Nat}
    {addresses : List Solidity.Storage.Loc} {address : Solidity.Storage.Loc} {pre : Pre}
    (access : address ∈ addresses) (hashed : pre ∈ address.pres N hash) :
    pre ∈ runPreimages N hash addresses :=
  List.mem_flatMap.mpr ⟨address, access, hashed⟩

/-- Resolved operation families commute under one complete finite per-run
premise. Resolution discharges access bounds, not symbolic disjointness or the
link between actual emitted accesses and requests. Effects use only their own
value and fixed captured parameters, as in modifyMany. -/
theorem resolved_families_commute {n N L R : Nat} {G : TypeGraph.Schema n}
    {E : TypeGraph.Ty n} {hash : Pre → Nat} {ty : STy} {base : Solidity.Storage.Loc}
    (hH : ∀ p, hash p < N) (hL : L ≤ N) (hR : R ≤ N)
    (fits : ty.Fits L) (placed : Placed L R ty base)
    (left right : List (List Solidity.Storage.Step × Nat))
    (a b : List Solidity.Storage.Loc)
    (leftAccepted : resolveMany ty base left = some a)
    (rightAccepted : resolveMany ty base right = some b)
    (regions : RegionsDisjoint N L hash (List.range R) (runPreimages N hash (a ++ b)))
    (separate : ∀ x ∈ a, ∀ y ∈ b, x ≠ y)
    (slots : Nat → TypeGraph.Slot G E)
    (f g : Nat → TypeGraph.Value G E → Option (TypeGraph.Value G E)) :
    (modifyMany f (a.map (Solidity.Storage.Loc.word N hash)) slots).bind
      (modifyMany g (b.map (Solidity.Storage.Loc.word N hash))) =
    (modifyMany g (b.map (Solidity.Storage.Loc.word N hash)) slots).bind
      (modifyMany f (a.map (Solidity.Storage.Loc.word N hash))) := by
  apply modifyMany_commute
  intro x hx y hy
  obtain ⟨sx, hsx, rfl⟩ := List.mem_map.mp hx
  obtain ⟨sy, hsy, rfl⟩ := List.mem_map.mp hy
  intro equal
  have same := Solidity.Storage.Loc.word_inj hH hL hR regions sx sy
    (resolveMany_bounded fits placed left a leftAccepted sx hsx)
    (resolveMany_bounded fits placed right b rightAccepted sy hsy)
    (fun p hp => mem_runPreimages (List.mem_append_left b hsx) hp)
    (fun p hp => mem_runPreimages (List.mem_append_right a hsy) hp) equal
  exact separate sx hsx sy hsy same

/-- Exact finite footprint transport for checked operation paths. Repeated
accesses and aliases are retained; only this run's bounded recursive preimages
are used. No distinction between live and retained aliases is erased. -/
theorem resolved_word_membership {N L R : Nat} {hash : Pre → Nat}
    {ty : STy} {base : Solidity.Storage.Loc}
    (hH : ∀ p, hash p < N) (hL : L ≤ N) (hR : R ≤ N)
    (fits : ty.Fits L) (placed : Placed L R ty base)
    (requests : List (List Solidity.Storage.Step × Nat)) (addresses : List Solidity.Storage.Loc)
    (accepted : resolveMany ty base requests = some addresses)
    (queryPath : List Solidity.Storage.Step) (queryOffset : Nat) (query : Solidity.Storage.Loc)
    (queryAccepted : resolve ty base queryPath queryOffset = some query)
    (regions : RegionsDisjoint N L hash (List.range R) (runPreimages N hash (addresses ++ [query]))) :
    query.word N hash ∈ addresses.map (Solidity.Storage.Loc.word N hash) ↔ query ∈ addresses := by
  constructor
  · intro member
    obtain ⟨address, access, equal⟩ := List.mem_map.mp member
    have same := Solidity.Storage.Loc.word_inj hH hL hR regions address query
      (resolveMany_bounded fits placed requests addresses accepted address access)
      (resolve_bounded fits placed queryAccepted)
      (fun p hp => mem_runPreimages (List.mem_append_left [query] access) hp)
      (fun p hp => mem_runPreimages (List.mem_append_right addresses (List.mem_singleton_self query)) hp)
      equal
    exact same ▸ access
  · intro member
    exact List.mem_map.mpr ⟨query, member, rfl⟩

/-- A separately resolved outside query remains unchanged by a successful
family. Its preimages are included in the same run premise automatically. -/
theorem resolved_family_outside {n N L R : Nat} {G : TypeGraph.Schema n}
    {E : TypeGraph.Ty n} {hash : Pre → Nat} {ty : STy} {base : Solidity.Storage.Loc}
    (hH : ∀ p, hash p < N) (hL : L ≤ N) (hR : R ≤ N)
    (fits : ty.Fits L) (placed : Placed L R ty base)
    (requests : List (List Solidity.Storage.Step × Nat)) (addresses : List Solidity.Storage.Loc)
    (accepted : resolveMany ty base requests = some addresses)
    (queryPath : List Solidity.Storage.Step) (queryOffset : Nat) (query : Solidity.Storage.Loc)
    (queryAccepted : resolve ty base queryPath queryOffset = some query)
    (regions : RegionsDisjoint N L hash (List.range R) (runPreimages N hash (addresses ++ [query])))
    (outside : query ∉ addresses)
    (slots result : Nat → TypeGraph.Slot G E)
    (effect : Nat → TypeGraph.Value G E → Option (TypeGraph.Value G E))
    (performed : modifyMany effect (addresses.map (Solidity.Storage.Loc.word N hash)) slots = some result) :
    result (query.word N hash) = slots (query.word N hash) := by
  apply modifyMany_outside effect _ slots result (query.word N hash) _ performed
  intro member
  exact outside ((resolved_word_membership hH hL hR fits placed requests addresses accepted
    queryPath queryOffset query queryAccepted regions).mp member)

/-- info: 'Solidity.Backend.StorageOps.LayoutAccess.resolved_word_membership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_word_membership
end Solidity.Backend.StorageOps.LayoutAccess
