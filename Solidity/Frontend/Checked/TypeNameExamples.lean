import Solidity.Frontend.Checked.TypeExampleCore

/-! Performance-only G09 type/declaration control split; public declarations and kernel budgets are unchanged. -/

namespace Solidity.Frontend.Checked

open Solidity.Source

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

end Solidity.Frontend.Checked
