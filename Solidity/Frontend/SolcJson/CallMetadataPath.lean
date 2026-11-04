import Solidity.Frontend.SolcJson.CallMetadataSound

/-! Total paths attach supplied metadata inputs to one analysed AST. This is
structural attachment only: no table completeness, authentication or execution
adequacy follows from a path. Core call syntax and semantics are unchanged. -/
namespace Solidity.Frontend.CallMetadata
open Lean (Json)

inductive Edge where
  | field (name : String)
  | index (position : Nat)
  deriving DecidableEq, Repr

abbrev Path := List Edge

def walk (root : Json) : Path → Option Json
  | [] => some root
  | .field name :: rest => (root.getObjVal? name).toOption.bind (walk · rest)
  | .index position :: rest => root.getArr?.toOption.bind fun xs =>
      (xs[position]?).bind (walk · rest)

/-- Transport a path relative to a subtree into its original root. -/
theorem walk_append (root : Json) (headPath tailPath : Path) :
    walk root (headPath ++ tailPath) = (walk root headPath).bind (walk · tailPath) := by
  induction headPath generalizing root with
  | nil => rfl
  | cons edge rest ih =>
    cases edge <;> simp only [List.cons_append, walk, ih, Option.bind_assoc]

/-- A node reached from this exact root, without partial traversal or fuel. -/
structure Located (root : Json) where
  path : Path
  node : Json
  reached : walk root path = some node

def locate (root : Json) (path : Path) : Option (Located root) :=
  match h : walk root path with
  | none => none
  | some node => some ⟨path, node, h⟩

/-- Resolve a relative path while retaining the original AST root. -/
def Located.descend {root : Json} (parent : Located root) (relative : Path) :
    Option (Located root) :=
  match h : walk parent.node relative with
  | none => none
  | some node => some ⟨parent.path ++ relative, node, by
      simp only [walk_append, parent.reached, Option.bind_some, h]⟩

theorem Located.descend_exact {root : Json} (parent child : Located root)
    (relative : Path) (accepted : parent.descend relative = some child) :
    child.path = parent.path ++ relative ∧ walk parent.node relative = some child.node := by
  unfold Located.descend at accepted
  split at accepted
  next h => cases accepted
  next node h =>
    cases Option.some.inj accepted
    exact ⟨rfl, h⟩

/-- Root and path determine the exact payload, independently of witness proofs. -/
theorem Located.node_unique {root : Json} (one two : Located root)
    (same : one.path = two.path) : one.node = two.node := by
  have reached : some one.node = some two.node :=
    one.reached.symm.trans (same ▸ two.reached)
  exact Option.some.inj reached

/-- All inputs are attached to the same accepted profile AST. This does not
assert the supplied declaration list is complete. -/
structure Attached (profile : Profile) where
  declarations : List (Located profile.ast)
  call : Located profile.ast
  checked : Checked (some profile) (declarations.map Located.node) call.node

def attach (profile : Profile) (declarations : List (Located profile.ast))
    (call : Located profile.ast) : Except Refusal (Attached profile) := do
  let checked ← check (some profile) (declarations.map Located.node) call.node
  return ⟨declarations, call, checked⟩

inductive AttachmentRefusal where
  | declarationPath (path : Path)
  | callPath (path : Path)
  | metadata (reason : Refusal)

def locateDeclarations (root : Json) : List Path →
    Except AttachmentRefusal (List (Located root))
  | [] => .ok []
  | path :: rest => do
      let some node := locate root path | throw (.declarationPath path)
      let tail ← locateDeclarations root rest
      return node :: tail

/-- Resolve all inputs from this profile AST before checking metadata. The
caller supplies paths, never substitute node payloads. -/
def attachPaths (profile : Profile) (declarations : List Path) (call : Path) :
    Except AttachmentRefusal (Attached profile) := do
  let ds ← locateDeclarations profile.ast declarations
  let some node := locate profile.ast call | throw (.callPath call)
  match attach profile ds node with
  | .ok attached => return attached
  | .error reason => throw (.metadata reason)

/-- Same checker inputs determine all returned metadata, not just its mode. -/
theorem checked_unique {p : Option Profile} {ds : List Json} {call : Json}
    (one two : Checked p ds call) : one.info = two.info := by
  exact Except.ok.inj (one.accepted.symm.trans two.accepted)

theorem Attached.info_unique {p : Profile} (one two : Attached p)
    (table : one.declarations.map Located.node = two.declarations.map Located.node)
    (site : one.call.path = two.call.path) : one.checked.info = two.checked.info := by
  have call : one.call.node = two.call.node := one.call.node_unique two.call site
  have accepted : inspect (some p) (one.declarations.map Located.node) one.call.node =
      .ok two.checked.info := by
    simp only [table, call]
    exact two.checked.accepted
  exact Except.ok.inj (one.checked.accepted.symm.trans accepted)

theorem Attached.call_at {p : Profile} (a : Attached p) :
    walk p.ast a.call.path = some a.checked.info.call := by
  simp only [checked_call_exact a.checked]
  exact a.call.reached

/-- The actually selected declaration, not merely the supplied table, is
reached in the accepted profile AST. No table completeness is needed. -/
theorem Attached.declaration_at {p : Profile} (a : Attached p) :
    ∃ path, walk p.ast path = some a.checked.info.declaration := by
  have hm : a.checked.info.declaration ∈ a.declarations.map Located.node :=
    inspect_declaration_member a.checked.accepted
  rcases List.mem_map.mp hm with ⟨d, _, hd⟩
  refine ⟨d.path, ?_⟩
  simpa only [hd] using d.reached

/-- info: 'Solidity.Frontend.CallMetadata.Attached.declaration_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Attached.declaration_at
/-- info: 'Solidity.Frontend.CallMetadata.Attached.call_at' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Attached.call_at
/-- info: 'Solidity.Frontend.CallMetadata.walk_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walk_append
/-- info: 'Solidity.Frontend.CallMetadata.Located.descend_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Located.descend_exact
/-- info: 'Solidity.Frontend.CallMetadata.Located.node_unique' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Located.node_unique
/-- info: 'Solidity.Frontend.CallMetadata.checked_unique' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms checked_unique
/-- info: 'Solidity.Frontend.CallMetadata.Attached.info_unique' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Attached.info_unique
end Solidity.Frontend.CallMetadata
