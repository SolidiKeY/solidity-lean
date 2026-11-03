import Solidity.Frontend.SolcJson.YulTypedChildren
/-! Concrete JSON prefix transport over existing occurrence metadata.
Routes preserve inherited/reset read-write roles and actual raw ordinals.
They do not introduce a syntax/state/value representation or reverse coverage. -/
namespace Solidity.Frontend.YulJson.Prefix
open Lean (Json)
open Occurrences
open Solidity.Yul
/-- A chain of ACTUAL schema-selected child positions. -/
inductive Route : Json → Bool → Json → Bool → List Edge → Prop where
  | here (node : Json) (role : Bool) : Route node role node role []
  | array {values : Array Json} {start node role path} (index : Fin values.size)
      (inside : Route values[index] start node role path) :
      Route (.arr values) start node role (.array index.val::path)
  | object {fields : Std.TreeMap.Raw String Json} {start node role path}
      (index : Fin fields.toList.length)
      (notIdentifier : isIdentifier (.obj fields) = false)
      (included : includeField (.obj fields) fields.toList[index].1 = true)
      (inside : Route fields.toList[index].2
        (fieldRole (.obj fields) fields.toList[index].1) node role path) :
      Route (.obj fields) start node role (.field fields.toList[index].1 index.val::path)

theorem Route.lift {root start node role routePath}
    (route : Route root start node role routePath) {path write found}
    (inside : OccurrenceD node role path write found) :
    OccurrenceD root start (routePath++path) write found := by
  induction route with
  | here => exact inside
  | array index route ih => exact .array index (ih inside)
  | object index notIdentifier included route ih =>
      exact .object index notIdentifier included (ih inside)

theorem Route.comp {root start middle middleRole first}
    (one : Route root start middle middleRole first) {node role second}
    (two : Route middle middleRole node role second) :
    Route root start node role (first++second) := by
  induction one with
  | here => exact two
  | array index route ih => exact .array index (ih two)
  | object index notIdentifier included route ih =>
      exact .object index notIdentifier included (ih two)

/-- The supplied ordinal selects an ACTUAL raw key/value pair. No object
WF or reverse lookup law is assumed or needed. -/
theorem selected_field {root : Json} {fields : Std.TreeMap.Raw String Json}
    {start key child} (index : Fin fields.toList.length)
    (rootEq : root = .obj fields) (pairEq : fields.toList[index] = (key,child))
    (notIdentifier : isIdentifier root = false)
    (included : includeField root key = true) :
    Route root start child (fieldRole root key) [.field key index.val] := by
  cases rootEq
  have selected : includeField (.obj fields) fields.toList[index].1 = true := by
    simpa only [pairEq] using included
  have childRoute : Route fields.toList[index].2
      (fieldRole (.obj fields) fields.toList[index].1) child
      (fieldRole (.obj fields) key) [] := by
    simpa only [pairEq] using Route.here child (fieldRole (.obj fields) key)
  have actual := Route.object (start := start) index notIdentifier selected childRoute
  simpa only [pairEq] using actual

theorem array_entry (values : Array Json) (start : Bool) (index : Fin values.size) :
    Route (.arr values) start values[index] start [.array index.val] :=
  .array index (.here values[index] start)

/-- Exact direct-block prefix uses the ORIGINAL witness field ordinal and
statement index; arbitrary raw maps do not gain a uniqueness/WF premise. -/
theorem block_statement {fuel node entry} (actual : BlockPath.Witness fuel node entry) :
    Route node false actual.values[actual.index] false actual.path := by
  have kindEq := ObjectLookup.kind_of_string actual.kind
  have notIdentifier : isIdentifier node = false := by
    simp only [isIdentifier,kindEq]
    decide +kernel
  have included : includeField node "statements" = true := by
    simp only [includeField,kindEq,childKeys]
    decide +kernel
  have role : fieldRole node "statements" = false := by
    simp only [fieldRole,kindEq]
    decide +kernel
  have outer := selected_field (start := false) actual.fieldIndex
    actual.root actual.selected notIdentifier included
  have exactRole : Route node false (.arr actual.values) false
      [.field "statements" actual.fieldIndex.val] := by
    simpa only [role] using outer
  exact exactRole.comp (array_entry actual.values false actual.index)

/-- Any occurrence under the actual statement now has its exact block-root
prefix. This keeps the final write role and found JSON node unchanged. -/
theorem block_occurrence {fuel node entry} (actual : BlockPath.Witness fuel node entry)
    {path write found}
    (inside : OccurrenceD actual.values[actual.index] false path write found) :
    OccurrenceD node false (actual.path++path) write found :=
  (block_statement actual).lift inside

structure AssignmentRead {fuel node statement F X n E}
    (actual : BlockPath.Witness fuel node statement)
    (leaf : TypingLeaves.Path × @TypingLeaves.ReadLeaf F X n E) where
  inner : AssignmentPath.Witness actual.values[actual.index] leaf
  occurrence : OccurrenceD node false (actual.path++inner.path) false inner.found

structure AssignmentTarget {fuel node statement X n E}
    (actual : BlockPath.Witness fuel node statement)
    (leaf : TypingLeaves.Path × @TypingLeaves.WriteLeaf X n E) where
  inner : TargetPath.Witness actual.values[actual.index] leaf
  occurrence : OccurrenceD node false (actual.path++inner.path) true inner.found

/-- Assignment leaves from the supplied item's ORIGINAL StatementD.
This helper preserves its context/certificate; decoded_assignment below
additionally supplies membership in the SAME original root BlockD. -/
theorem block_assignment {fuel node statement first rest rhs}
    (actual : BlockPath.Witness fuel node statement)
    (shape : statement.2.tree = .yulAssign first rest rhs) :
    ∃ child : BlockScope.AssignmentD statement.2.scope statement.2.environment (first::rest) rhs,
      HEq statement.2.typed (ScopedBlockTyping.StatementD.assignment (c := statement.2.control) child) ∧
      TypingLeaves.All (fun path leaf => Nonempty (AssignmentRead actual (path,leaf)))
        (TypingLeaves.reads (TypingLeaves.assignmentReads statement.2.scope statement.2.environment child) []) ∧
      TypingLeaves.All (fun path leaf => Nonempty (AssignmentTarget actual (path,leaf)))
        (TypingLeaves.targets (TypingLeaves.assignmentTargets statement.2.scope statement.2.environment child) []) := by
  rcases statement with ⟨ordinal,item⟩
  rcases item with ⟨X,scope,F,n,m,E,c,tree,final,typed⟩
  cases shape
  cases typed with
  | assignment original =>
      obtain ⟨child,parentEq,reads,targets⟩ :=
        TypedChildren.assignment_positions actual.childFuel actual.decoded (.assignment (c := c) original)
      refine ⟨child,heq_of_eq parentEq,?_,?_⟩
      · intro entry present
        obtain ⟨inside⟩ := reads entry present
        exact ⟨⟨inside,block_occurrence actual inside.occurrence⟩⟩
      · intro entry present
        obtain ⟨inside⟩ := targets entry present
        exact ⟨⟨inside,block_occurrence actual inside.occurrence⟩⟩

/-- Concrete root decoder + ORIGINAL BlockD composition. Membership carries
the full item (scope, both environments and original StatementD), so no
caller-prepared context or independent witness can replace the root's context. -/
theorem decoded_assignment {X scope F n E c body first rest rhs}
    (fuel : Nat) {node}
    (parsed : blockAux fuel node = .ok body)
    (typed : @ScopedBlockTyping.BlockD X scope F n E c body)
    (statement : Nat × TypingStatements.Item)
    (member : statement ∈ TypingStatements.block typed)
    (shape : statement.2.tree = .yulAssign first rest rhs) :
    ∃ actual : BlockPath.Witness fuel node statement,
    ∃ child : BlockScope.AssignmentD statement.2.scope statement.2.environment (first::rest) rhs,
      HEq statement.2.typed
        (ScopedBlockTyping.StatementD.assignment (c := statement.2.control) child) ∧
      TypingLeaves.All (fun path leaf => Nonempty (AssignmentRead actual (path,leaf)))
        (TypingLeaves.reads (TypingLeaves.assignmentReads statement.2.scope statement.2.environment child) []) ∧
      TypingLeaves.All (fun path leaf => Nonempty (AssignmentTarget actual (path,leaf)))
        (TypingLeaves.targets (TypingLeaves.assignmentTargets statement.2.scope statement.2.environment child) []) := by
  obtain ⟨actual⟩ := BlockPath.decoded_block fuel parsed typed statement member
  obtain ⟨child,original,reads,targets⟩ := block_assignment actual shape
  exact ⟨actual,child,original,reads,targets⟩

theorem Route.empty {root start node role} (route : Route root start node role []) :
    node = root ∧ role = start := by
  cases route
  exact ⟨rfl,rfl⟩

theorem Route.field_selected {root start node role key ordinal path}
    (route : Route root start node role (.field key ordinal::path)) :
    includeField root key = true := by
  cases route with
  | object index notIdentifier included inside => exact included

theorem Route.array_bound {values start node role ordinal path}
    (route : Route (.arr values) start node role (.array ordinal::path)) :
    ordinal < values.size := by
  cases route with
  | array index inside => exact index.isLt

/-- Different direct statement ordinals keep ALL prefixed suffixes distinct,
even when every identifier node and local suffix is structurally identical. -/
theorem block_prefix_distinct {fuel node first second}
    (one : BlockPath.Witness fuel node first) (two : BlockPath.Witness fuel node second)
    (different : first.1 ≠ second.1) (left right : List Edge) :
    one.path++left ≠ two.path++right := by
  intro same
  have indices := congrArg (fun path : List Edge =>
    match path with | _::.array index::_ => some index | _ => none) same
  change some one.index.val = some two.index.val at indices
  exact different (one.position.trans ((Option.some.inj indices).trans two.position.symm))

end Solidity.Frontend.YulJson.Prefix
