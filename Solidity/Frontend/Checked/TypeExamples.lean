import Solidity.Frontend.Checked.Check
import Solidity.Frontend.Checked.Render
import Solidity.Source.Ctor
import Solidity.Source.Decls

/-!
# Type and declaration controls (G09)

Kernel-checked witnesses for the parse of type names and declarations:
trees (`rfl`), attribute orders as layouts, recursive declaration
references through S00's declaration graph, printing round trips, the
constructor coverage of the type and declaration constructors, and negative
controls.
-/

namespace Solidity.Frontend.Checked

open Solidity.Source

/-- A checked type name of a string. -/
def ty (s : String) : Except Error (Syn .typeName) := parseType (ascii s)

/-- `u` read with layout `L` is the tree `t`: the same nodes (constructors in
pre-order) and the same yield.  A decidable stand-in for equality, since
`Syn` has no `DecidableEq`. -/
def sameTree {c : Cat} (u : Syn c) (L : List Choice) (t : Syn c) : Bool :=
  u.nodes == t.nodes && u.toks L == t.toks L && (u.toks L).isSome

/-- The checked parse of `s` in a category is the tree `t`. -/
def parsesTo {c : Cat} (p : Nat → P (Syn c)) (s : String) (t : Syn c) : Bool :=
  match parseCat p (ascii s) with
  | .ok (u, L) => sameTree u L t
  | .error _ => false

theorem type_array_of_array :
    parsesTo typeName "uint[2][]" (.array (.array (.elem (.int false 256 (by decide)))
      (.some (.lit (.num (.dec 2 0 0))))) .none) = true := by decide +kernel

theorem type_mapping_named :
    parsesTo typeName "mapping(address owner => mapping(bytes32 => bool) ok)"
      (.mapping (.elem .address (by decide)) (some "owner")
        (.mapping (.elem (.fixedBytes 32 (by decide)) (by decide)) none (.elem .bool) none)
        (some "ok")) = true := by decide +kernel

theorem type_function :
    parsesTo typeName "function (uint8 a) external view returns (bool)"
      (.fnType (.cons (.param (.elem (.int false 8 (by decide))) none (some "a")) .nil)
        (some .external) (some .view)
        (.cons (.param (.elem .bool) none none) .nil)) = true := by decide +kernel

theorem type_payable_path :
    parsesTo typeName "address payable" (.elem .addressPayable) &&
    parsesTo typeName "a.b.C[]" (.array (.userType ⟨"a", ["b", "C"]⟩) .none) &&
    parsesTo typeName "fixed128x18" (.elem (.fixed true (some ⟨128, 18, by decide⟩)))
      = true := by decide +kernel

/-- Function type attributes in either order: one tree, two layouts. -/
theorem type_attr_order :
    parsesTo typeName "function () view external"
      (.fnType .nil (some .external) (some .view) .nil) = true ∧
    ((parseCat typeName (ascii "function () view external")).toOption.map (·.2)) =
      some [.attrs [.mutab, .vis]] ∧
    ((parseCat typeName (ascii "function () external view")).toOption.map (·.2)) =
      some [.attrs [.vis, .mutab]] := by
  decide +kernel

/-! ## Negative controls -/

def tyErr (s : String) : Option String :=
  match ty s with
  | .error e => some e.msg
  | .ok _ => none

/-- A second visibility ends a function type's attributes (it belongs to the
state variable); a second mutability is refused. -/
theorem type_second_visibility :
    parsesTo sourceUnit "contract C { function () internal public f; }"
      (.unit (.cons (.contract false "C" .none .nil
        (.cons (.stateVar (.fnType .nil (some .internal) none .nil) (some .pub) none none false "f"
          .none) .nil)) .nil)) = true := by decide +kernel

theorem type_refused :
    tyErr "mapping(address payable => uint)" = some "expected '=>'" ∧
    tyErr "uint[" = some "expected an expression" ∧
    tyErr "function () public external" = some "unexpected token" ∧
    tyErr "mapping(uint => )" = some "expected a type name" ∧
    tyErr "function () returns ()" = some "empty returns list" ∧
    tyErr "uint x" = some "unexpected token" ∧
    tyErr "function () view pure" = some "repeated function type attribute" := by decide +kernel

/-! ## Declarations -/

/-- The constructors of a checked unit's tree (empty if refused). -/
def ctorsOf (s : String) : List Ctor :=
  match parse (ascii s) with
  | .ok u => u.nodes.map Node.ctor
  | .error _ => []

def unitErr (s : String) : Option (Nat × String) :=
  match parse (ascii s) with
  | .error e => some (e.pos, e.msg)
  | .ok _ => none

/-- The type and declaration programs of the G09 corpus. -/
def declCorpus : List String := [
  "struct S { uint a; S[] kids; mapping(uint => S) next; }
   enum E { A, B, C }
   type T is address payable;
   uint constant K = 1;
   error Bad(uint code, string);
   event Ev(uint indexed a, bytes b) anonymous;
   using L for T global;
   using {add as +, L.sub} for T;
   using L for *;",
  "contract C {
     uint public constant x = 1;
     bytes32 immutable private h;
     mapping(address => uint) internal transient t;
     uint transient;
     function (uint) external returns (bool) public f;
     uint[] override(A, B) public xs;
     struct P { string s; }
     event Q();
     error R();
     function(bytes memory) external public c3;
     function () internal internal transient fiit;
     mapping(a.K key => S) byKey;
     function f(uint[] memory a, S storage s, bytes calldata c) internal {}
   }"]

theorem declCorpus_accepted : declCorpus.all (fun s => !(ctorsOf s).isEmpty) = true := by
  decide +kernel

/-- The type and declaration constructors (G09). -/
def declCtors : List Ctor :=
  [.elem, .fnType, .mapping, .userType, .array, .param, .struct, .structMember, .enum, .udvt,
    .stateVar, .constant, .event, .eventParam, .error, .errorParam, .usingPart, .usingPath,
    .usingAliases, .usingAlias, .topPart]

/-- **Acceptance coverage (G09)**: every type and declaration constructor is
produced by an accepted program of the corpus. -/
theorem declCtors_covered :
    declCtors.all (fun c => declCorpus.any fun s => (ctorsOf s).contains c) = true := by
  decide +kernel

/-- The corpus is in the profile: no syntax-level rejection. -/
theorem declCorpus_in_profile :
    declCorpus.all (fun s => match parse (ascii s) with
      | .ok u => u.rejections.isEmpty | .error _ => false) = true := by decide +kernel

/-- **A recursive declaration reference**: struct `S` mentions itself, an
edge of S00's declaration graph. -/
theorem recursive_struct :
    (match parse (ascii "struct S { S[] kids; mapping(uint => S) next; }") with
      | .ok u => (Syn.decls u).map fun (d : Decl) => (d.name, d.refs)
      | .error _ => []) = [("S", [(.use, ⟨"S", []⟩), (.use, ⟨"S", []⟩)])] := by
  decide +kernel

/-- A decidable fingerprint of a tree: its nodes (constructors, pre-order)
and its tokens under the canonical-order layout it was read with. -/
def fingerprint (r : Except Error (Syn .unit × List Choice)) : Option (List Node × Option (List Tok)) :=
  r.toOption.map fun (u, L) => (u.nodes, u.toks L)

/-- Mutually recursive declarations: each struct's edge names the other. -/
theorem mutual_structs :
    (match parse (ascii "struct A { B[] b; } struct B { A a; }") with
      | .ok u => (Syn.decls u).map fun (d : Decl) => (d.name, d.refs)
      | .error _ => []) = [("A", [(.use, ⟨"B", []⟩)]), ("B", [(.use, ⟨"A", []⟩)])] := by
  decide +kernel

/-- An empty import path is refused (`NonEmptyStringLiteral`). -/
theorem import_empty_refused :
    unitErr "import \"\";" = some (7, "empty import path") := by decide +kernel

/-- State variable attributes in any order: the same nodes and tokens up to
the attribute run, different layouts. -/
theorem stateVar_attr_order :
    ((parseWithLayout (ascii "contract C { uint constant public x = 1; }")).toOption.map
      fun (u, _) => u.nodes) =
    ((parseWithLayout (ascii "contract C { uint public constant x = 1; }")).toOption.map
      fun (u, _) => u.nodes) ∧
    ((parseWithLayout (ascii "contract C { uint constant public x = 1; }")).toOption.map (·.2)) =
      some [.attrs [.const, .vis]] := by decide +kernel

/-- `transient` is an attribute before a name and a name before `;`. -/
theorem transient_soft :
    parsesTo sourceUnit "contract C { uint transient t; uint transient; }"
      (.unit (.cons (.contract false "C" .none .nil
        (.cons (.stateVar (.elem (.int false 256 (by decide))) none none none true "t" .none)
        (.cons (.stateVar (.elem (.int false 256 (by decide))) none none none false "transient" .none)
          .nil))) .nil)) = true := by decide +kernel

theorem decl_refused :
    unitErr "contract C { uint public public x; }" = some (32, "repeated state variable attribute") ∧
    unitErr "struct S { }" = some (12, "empty struct") ∧
    unitErr "enum E { }" = some (9, "expected an identifier") ∧
    unitErr "uint constant K;" = some (15, "expected '='") ∧
    unitErr "type T is S;" = some (10, "expected an elementary type name") ∧
    unitErr "using {f as !} for T;" = some (12, "expected a user-definable operator") := by
  decide +kernel

/-! ## Printing -/

theorem print_text :
    (match parseWithLayout (ascii "contract C{uint constant public x=0x01;string s='a\\n';}") with
      | .ok (u, L) => (u.print L).map Bytes.str
      | .error _ => none) =
      some "contract C { uint256 constant public x = 0x01 ; string s = \"a\\x0a\" ; }" := by
  decide +kernel

/-- Parse, print, parse again: the fingerprint of the second parse. -/
def reprintFingerprint (s : String) : Option (List Node × Option (List Tok)) :=
  match parseWithLayout (ascii s) with
  | .ok (u, L) => match u.print L with
    | some b => fingerprint (parseWithLayout b)
    | none => none
  | .error _ => none

/-- **Round trip**: the printed text parses to a tree with the same nodes
and tokens. -/
theorem print_roundtrip :
    declCorpus.all (fun s => reprintFingerprint s == fingerprint (parseWithLayout (ascii s)) &&
      (reprintFingerprint s).isSome) = true := by
  decide +kernel

/-- A 40-digit hex literal whose lowercase spelling is its checksum, spelled
otherwise, keeps its cleared flag through printing. -/
theorem print_checksum_flag :
    (reprintFingerprint "contract C { address a = 0x000000000000000000000000000000000000000B; }") ==
      fingerprint (parseWithLayout (ascii
        "contract C { address a = 0x000000000000000000000000000000000000000B; }")) &&
    (reprintFingerprint "contract C { string s = unicode\"\\u2028\\u202e\\u202c\"; }").isSome
      = true := by
  decide +kernel

end Solidity.Frontend.Checked

/-- info: 'Solidity.Frontend.Checked.parseType_derives' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.Checked.parseType_derives
/-- info: 'Solidity.Frontend.Checked.declCtors_covered' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.Checked.declCtors_covered
