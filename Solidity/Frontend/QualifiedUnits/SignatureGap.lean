import Solidity.Frontend.QualifiedUnits.Checked
import Solidity.Frontend.QualifiedUnits.Controls

/-!
# Preserved inherited-overload counterexample (QN-SIG)

These theorems witness a remaining required-gate failure, not correct
Solidity candidate collection. The current nearest-name graph drops a base
function with a different parameter type. Compiler fixtures independently
accept that overload, including when parameter types have same spelling in
different units. Full acceptance must fail until this gap is resolved.
-/
namespace Solidity.Frontend.QualifiedUnits.SignatureGap
open Solidity.Source Controls

def uintTy : Syn .typeName := .elem (.int false 256 (by decide))

def functionOf (ty : Syn .typeName) (result : Nat) : Syn (.part false) :=
  .function (.ident "f") (.cons (.param ty none none) .nil) (some .internal) (some .pure)
    .nil false none (.cons (.param uintTy none none) .nil)
    (.some (.block (.cons (.stmtItem (.returnStmt (.some (.lit (.num (.dec result 0 0)))))) .nil)))

def program : UnitSet := ⟨[("A", unitOf [
  .contract false "B" .none .nil (.cons (functionOf uintTy 1) .nil),
  .contract false "D" .none (.cons (.inherit ⟨"B", []⟩ .none) .nil)
    (.cons (functionOf (.elem .bool) 2) .nil)])]⟩

/-- Counterexample observation: the required base overload is currently lost. -/
theorem current_overload_gap :
    resolve program [] "A" (some ⟨"A", 2⟩) [] ⟨"f", []⟩ = .ok [.decl ⟨"A", 3⟩] := by
  rfl

/-- The lost declaration exists at its original identity. -/
theorem base_overload_exists :
    (program.decl? ⟨"A", 1⟩).map Decl.kind = some .function := by
  rfl

end Solidity.Frontend.QualifiedUnits.SignatureGap
