import Solidity.Frontend.Checked.Check
import Solidity.Frontend.Checked.Render
import Solidity.Source.Ctor
import Solidity.Source.Decls

/-! Performance-only G09 type/declaration control split; public declarations and kernel budgets are unchanged. -/

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

def tyErr (s : String) : Option String :=
  match ty s with
  | .error e => some e.msg
  | .ok _ => none

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

/-- The type and declaration constructors (G09). -/
def declCtors : List Ctor :=
  [.elem, .fnType, .mapping, .userType, .array, .param, .struct, .structMember, .enum, .udvt,
    .stateVar, .constant, .event, .eventParam, .error, .errorParam, .usingPart, .usingPath,
    .usingAliases, .usingAlias, .topPart]

/-- A decidable fingerprint of a tree: its nodes (constructors, pre-order)
and its tokens under the canonical-order layout it was read with. -/
def fingerprint (r : Except Error (Syn .unit × List Choice)) : Option (List Node × Option (List Tok)) :=
  r.toOption.map fun (u, L) => (u.nodes, u.toks L)

/-- Parse, print, parse again: the fingerprint of the second parse. -/
def reprintFingerprint (s : String) : Option (List Node × Option (List Tok)) :=
  match parseWithLayout (ascii s) with
  | .ok (u, L) => match u.print L with
    | some b => fingerprint (parseWithLayout b)
    | none => none
  | .error _ => none

end Solidity.Frontend.Checked
