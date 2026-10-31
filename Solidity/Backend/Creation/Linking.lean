import Solidity.Backend.Creation.Regions
import Solidity.Backend.Creation.Execution

/-! Certified runtime library locations and reuse of the existing assembler/linker.
These are internal session-produced addresses, not an admitted external link map. -/
namespace Solidity.Backend.Creation

structure LinkSite (total : Nat) (Lib : Type) where
  location : Location total 20
  library : Lib

/-- The absolute assembler references must agree exactly with typed local sites. -/
structure LinkTable (a : Artifact Lib) where
  sites : List (LinkSite a.runtime.length Lib)
  origin : a.runtimeLinks = sites.map (fun s => (a.linkBase + s.location.offset, s.library))
  disjoint : sites.Pairwise (fun s t => s.location.Disjoint t.location)

def localRefs (sites : List (LinkSite total Lib)) : List (Nat × Lib) :=
  sites.map (fun s => (s.location.offset, s.library))

theorem linkSites_length (sites : List (LinkSite total Lib)) (code : List UInt8)
    (hcode : code.length = total) (addresses : Lib → Vector UInt8 20) :
    (linkBytes code (localRefs sites) addresses).length = total := by
  induction sites generalizing code with
  | nil => simpa only [localRefs, List.map_nil, linkBytes, List.foldl_nil] using hcode
  | cons s rest ih =>
    have hbound : s.location.offset + (addresses s.library).toList.length ≤ code.length := by
      rw [Vector.length_toList, hcode]
      exact s.location.bounds
    have hpatch : (patchAt code s.location.offset (addresses s.library).toList).length = total := by
      rw [patchAt_length _ _ _ hbound, hcode]
    exact ih _ hpatch

def linkedArtifact (a : Artifact Lib) (table : LinkTable a)
    (addresses : Lib → Vector UInt8 20) : Artifact Lib where
  runtime := linkBytes a.runtime (localRefs table.sites) addresses
  args := a.args
  runtimeFits := by rw [linkSites_length _ _ rfl]; exact a.runtimeFits
  linkBase := 0
  runtimeLinks := []

theorem linked_args (a : Artifact Lib) (table : LinkTable a) (addresses : Lib → Vector UInt8 20) :
    (linkedArtifact a table addresses).args = a.args := rfl

theorem linked_installs (a : Artifact Lib) (table : LinkTable a) (addresses : Lib → Vector UInt8 20) :
    let b := linkedArtifact a table addresses
    Exec b.payload b.payload [] [] (.returned (linkBytes a.runtime (localRefs table.sites) addresses)) :=
  installs_runtime _

/-- This deployment gate refuses unresolved placeholders. Raw bytes remain data. -/
def deployable (a : Artifact Lib) : Option (List UInt8) :=
  if a.runtimeLinks.isEmpty then some a.payload else none

theorem unresolved_refused (a : Artifact Lib) (h : a.runtimeLinks ≠ []) : deployable a = none := by
  simp only [deployable, List.isEmpty_iff, h, if_false]

theorem linked_deployable (a : Artifact Lib) (table : LinkTable a) (addresses : Lib → Vector UInt8 20) :
    deployable (linkedArtifact a table addresses) = some (linkedArtifact a table addresses).payload := rfl

/-- Completion refuses a missing address before changing any bytes. -/
def resolve (sites : List (LinkSite total Lib)) (addresses : Lib → Option (Vector UInt8 20)) :
    Option (List (Vector UInt8 20)) :=
  match sites with
  | [] => some []
  | s :: rest => do
    let address ← addresses s.library
    let tail ← resolve rest addresses
    pure (address :: tail)

theorem resolve_missing (sites : List (LinkSite total Lib)) (addresses : Lib → Option (Vector UInt8 20))
    (s : LinkSite total Lib) (hs : s ∈ sites) (missing : addresses s.library = none) :
    resolve sites addresses = none := by
  induction sites with
  | nil => cases hs
  | cons t rest ih =>
    rcases List.mem_cons.mp hs with he | hr
    · subst t
      simp only [resolve, missing]
      rfl
    · simp only [resolve]
      rw [ih hr]
      cases addresses t.library <;> rfl

theorem link_payload_bounds (a : Artifact Lib) (_table : LinkTable a)
    (s : LinkSite a.runtime.length Lib) :
    a.runtimeStart ≤ a.runtimeStart + s.location.offset ∧
      a.runtimeStart + s.location.offset + 20 ≤ a.argsStart := by
  have hb : s.location.offset + 20 ≤ a.runtime.length := s.location.bounds
  unfold Artifact.argsStart
  omega

/-- Argument length validation is separate from bytecode/linking; no ABI decoder
is claimed here. A caller supplies the exact encoded argument length. -/
def checkedArguments (a : Artifact Lib) (expected : Nat) : Option (List UInt8) :=
  if a.args.length = expected then some a.args else none

theorem truncated_arguments_refused (a : Artifact Lib) (expected : Nat)
    (h : a.args.length < expected) : checkedArguments a expected = none := by
  simp only [checkedArguments, Nat.ne_of_lt h, if_false]

theorem two_links_commute (code : List UInt8) (a b : LinkSite code.length Lib)
    (disjoint : a.location.Disjoint b.location) (addresses : Lib → Vector UInt8 20) :
    linkBytes code [(a.location.offset, a.library), (b.location.offset, b.library)] addresses =
      linkBytes code [(b.location.offset, b.library), (a.location.offset, a.library)] addresses := by
  simp only [linkBytes, List.foldl_cons, List.foldl_nil]
  apply patchAt_commute
  · simpa only [Vector.length_toList] using a.location.bounds
  · simpa only [Vector.length_toList] using b.location.bounds
  · simpa only [Vector.length_toList] using disjoint

/-- Existing assembler correctness supplies byte equality through arbitrary
prefix and constructor arguments. No relocation/fixpoint algorithm is duplicated. -/
theorem assembler_link_wrapper [DecidableEq L]
    {base : Nat} {link : Lib → Option (Vector UInt8 20)} {items : List (Item L Lib)}
    {out : Assembled Lib} (addresses : Lib → Vector UInt8 20)
    (h : assemble base link items = some out) (n : Immediate)
    (alignment : size (wrapper n) = base) (args : List UInt8) :
    ∃ out', assemble base (fillLink link addresses) items = some out' ∧ out'.linkRefs = [] ∧
      linkBytes (encode (wrapper n) ++ encode out.code ++ args) out.linkRefs addresses =
        encode (wrapper n) ++ encode out'.code ++ args ∧
      (encode out'.code).length = (encode out.code).length := by
  obtain ⟨out', hout, href, hbytes, _, _⟩ := link_patch addresses h
  refine ⟨out', hout, href, hbytes (wrapper n) args alignment, ?_⟩
  rw [length_encode, length_encode, (assemble_layout hout).2.2, (assemble_layout h).2.2]

end Solidity.Backend.Creation
