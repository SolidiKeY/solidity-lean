import Solidity.Frontend.SolcJson.YulReferenceAttachment

/-! Positions/roles in the EXTRACTED Yul AST JSON value, not InlineAssembly.
This is metadata, not another program AST. Schema-selected fields follow the
existing pinned decoder; the semantic valid-Yul boundary still requires its
actual ShapedBlock certificate. Array and object positions remain explicit,
even for structurally identical identifier nodes. Source namespace/reference
accounting and admission are not supplied by these position certificates. -/
namespace Solidity.Frontend.YulJson.Occurrences
open Lean (Json)

def kind (node : Json) : String :=
  ((string node "nodeType").toOption).getD ""

def childKeys : String → List String
  | "YulBlock" => ["statements"]
  | "YulAssignment" => ["variableNames","value"]
  | "YulFunctionCall" => ["arguments"]
  | "YulIf" => ["condition","body"]
  | "YulForLoop" => ["pre","condition","post","body"]
  | "YulSwitch" => ["expression","cases"]
  | "YulCase" => ["value","body"]
  | "YulFunctionDefinition" => ["body"]
  | "YulVariableDeclaration" => ["value"]
  | "YulExpressionStatement" => ["expression"]
  | _ => []

def isIdentifier (node : Json) : Bool := kind node == "YulIdentifier"
def includeField (node : Json) (key : String) : Bool := (childKeys (kind node)).contains key
def fieldRole (node : Json) (key : String) : Bool :=
  kind node == "YulAssignment" && key == "variableNames"

inductive Edge where
  | array (index : Nat)
  | field (key : String) (ordinal : Nat)
  deriving Repr, DecidableEq

/-- Actual JSON positions with inherited array roles and reset object roles.
Malformed case values do not acquire valid-Yul meaning from this relation. -/
inductive OccurrenceD : Json → Bool → List Edge → Bool → Json → Prop where
  | identifier {node start} : isIdentifier node = true →
      OccurrenceD node start [] start node
  | array {values : Array Json} {start path role node} (index : Fin values.size) :
      OccurrenceD values[index] start path role node →
      OccurrenceD (.arr values) start (.array index.val::path) role node
  | object {fields : Std.TreeMap.Raw String Json} {start path role node}
      (index : Fin fields.toList.length) :
      isIdentifier (.obj fields) = false →
      includeField (.obj fields) fields.toList[index].1 = true →
      OccurrenceD fields.toList[index].2
        (fieldRole (.obj fields) fields.toList[index].1) path role node →
      OccurrenceD (.obj fields) start
        (.field fields.toList[index].1 index.val::path) role node

structure Occurrence (root : Json) (start : Bool) where
  path : List Edge
  write : Bool
  node : Json
  derivation : OccurrenceD root start path write node

structure Child (root : Json) (start : Bool) where
  edge : Edge
  node : Json
  role : Bool
  lift : ∀ {path write found}, OccurrenceD node role path write found →
    OccurrenceD root start (edge::path) write found

def Child.liftOccurrence {root start} (child : Child root start)
    (occurrence : Occurrence child.node child.role) : Occurrence root start :=
  ⟨child.edge::occurrence.path,occurrence.write,occurrence.node,child.lift occurrence.derivation⟩

/-- Every selected occurrence under this non-identifier parent comes from an
ACTUAL child position. This is a real proof field, supplied concretely below. -/
structure Children (root : Json) (start : Bool) where
  entries : List (Child root start)
  cover : ∀ {path write node}, OccurrenceD root start path write node →
    ∃ child ∈ entries, ∃ rest, path = child.edge::rest ∧
      OccurrenceD child.node child.role rest write node

theorem finRange_member {n : Nat} (index : Fin n) : index ∈ List.finRange n :=
  List.mem_ofFn.mpr ⟨index,rfl⟩

def arrayChild (values : Array Json) (start : Bool) (index : Fin values.size) :
    Child (.arr values) start :=
  ⟨.array index.val,values[index],start,fun occurrence => .array index occurrence⟩

def arrayChildren (values : Array Json) (start : Bool) : Children (.arr values) start :=
  ⟨(List.finRange values.size).map (arrayChild values start),by
    intro path write node occurrence
    cases occurrence with
    | identifier yes => cases (show false = true from yes)
    | array index inside =>
        exact ⟨arrayChild values start index,
          List.mem_map.mpr ⟨index,finRange_member index,rfl⟩,_,rfl,inside⟩⟩

def objectChild (fields : Std.TreeMap.Raw String Json) (start : Bool)
    (notIdentifier : isIdentifier (.obj fields) = false)
    (index : Fin fields.toList.length)
    (selected : includeField (.obj fields) fields.toList[index].1 = true) :
    Child (.obj fields) start :=
  ⟨.field fields.toList[index].1 index.val,fields.toList[index].2,
    fieldRole (.obj fields) fields.toList[index].1,
    fun occurrence => .object index notIdentifier selected occurrence⟩

def objectEntries (fields : Std.TreeMap.Raw String Json) (start : Bool)
    (notIdentifier : isIdentifier (.obj fields) = false) : List (Child (.obj fields) start) :=
  (List.finRange fields.toList.length).filterMap (fun index =>
    if selected : includeField (.obj fields) fields.toList[index].1 = true then
      some (objectChild fields start notIdentifier index selected) else none)

def objectChildren (fields : Std.TreeMap.Raw String Json) (start : Bool)
    (notIdentifier : isIdentifier (.obj fields) = false) : Children (.obj fields) start :=
  ⟨objectEntries fields start notIdentifier,by
    intro path write node occurrence
    cases occurrence with
    | identifier yes => cases (notIdentifier.symm.trans yes)
    | object index _ selected inside =>
        refine ⟨objectChild fields start notIdentifier index selected,?_,_,rfl,inside⟩
        exact List.mem_filterMap.mpr
          ⟨index,finRange_member index,dif_pos selected⟩⟩

/-- A position fixes both the actual identifier node and its access role.
This is why matching by positions does not conflate equal-looking nodes. -/
theorem OccurrenceD.deterministic {root start path write node}
    (one : OccurrenceD root start path write node) :
    ∀ {otherPath otherWrite otherNode}, OccurrenceD root start otherPath otherWrite otherNode →
      path = otherPath → write = otherWrite ∧ node = otherNode := by
  induction one with
  | identifier identifier =>
      intro otherPath otherWrite otherNode two same
      cases two with
      | identifier _ => exact ⟨rfl,rfl⟩
      | array index inside => cases same
      | object index _ _ inside => cases same
  | @array values start path write node index inside ih =>
      intro otherPath otherWrite otherNode two same
      cases two with
      | identifier _ => cases same
      | array otherIndex other =>
          have positions := (List.cons.inj same).1
          have indices : index = otherIndex := Fin.ext (Edge.array.inj positions)
          cases indices
          exact ih other (List.cons.inj same).2
  | @object fields start path write node index notIdentifier selected inside ih =>
      intro otherPath otherWrite otherNode two same
      cases two with
      | identifier _ => cases same
      | object otherIndex _ _ other =>
          have positions := (List.cons.inj same).1
          have indices : index = otherIndex := Fin.ext (Edge.field.inj positions).2
          cases indices
          exact ih other (List.cons.inj same).2

theorem Occurrence.eq_of_path_eq {root start} (one two : Occurrence root start)
    (same : one.path = two.path) : one = two := by
  have unique := one.derivation.deterministic two.derivation same
  cases one with
  | mk path write node derivation =>
      cases two with
      | mk otherPath otherWrite otherNode otherDerivation =>
          dsimp only at same unique
          rcases unique with ⟨sameWrite,sameNode⟩
          cases same
          cases sameWrite
          cases sameNode
          rfl

/-- Executable equality compares actual position paths. Distinct positions stay
distinct even if identifier spelling, JSON and source span are identical. -/
instance {root start} : DecidableEq (Occurrence root start) := fun one two =>
  if same : one.path = two.path then isTrue (one.eq_of_path_eq two same)
  else isFalse (fun equal => same (congrArg Occurrence.path equal))

end Solidity.Frontend.YulJson.Occurrences
