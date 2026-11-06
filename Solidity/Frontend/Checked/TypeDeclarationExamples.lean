import Solidity.Frontend.Checked.TypeExampleCore

/-! Performance-only G09 type/declaration control split; public declarations and kernel budgets are unchanged. -/

namespace Solidity.Frontend.Checked

open Solidity.Source

/-- **A recursive declaration reference**: struct `S` mentions itself, an
edge of S00's declaration graph. -/
theorem recursive_struct :
    (match parse (ascii "struct S { S[] kids; mapping(uint => S) next; }") with
      | .ok u => (Syn.decls u).map fun (d : Decl) => (d.name, d.refs)
      | .error _ => []) = [("S", [(.use, ⟨"S", []⟩), (.use, ⟨"S", []⟩)])] := by
  decide +kernel

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

end Solidity.Frontend.Checked
