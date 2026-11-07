import Solidity.Yul.ReservedNames
import Lean

/-! H69 reservation-policy separation. SLOTNUM is deliberately absent from the
pinned inline-Yul reservation table. Assuming its membership contradicts the
unchanged public theorem; this is not a success contract or a new exclusion.
The ordinary count theorem remains a separate statement.
-/
namespace H62.AuditYul.ReservedRefutation

theorem slotnum_not_reserved : "slotnum" ∉ Solidity.Yul.reservedNames :=
  Solidity.Yul.slotnum_not_reserved

open Lean Elab Command in
run_cmd do
  let source ← getConstInfo `Solidity.Yul.slotnum_not_reserved
  let audit ← getConstInfo `H62.AuditYul.ReservedRefutation.slotnum_not_reserved
  unless source.type == audit.type && source.levelParams == audit.levelParams do
    throwError "reserved-name refutation statement changed"
  let axioms ← liftTermElabM (collectAxioms `H62.AuditYul.ReservedRefutation.slotnum_not_reserved)
  unless axioms.all (fun n => [``propext, ``Classical.choice, ``Quot.sound].contains n) do
    throwError "unapproved refutation axioms {axioms}"
  logInfo "RESERVED_REFUTATION_FIDELITY_PASS: unchanged full type and universes"

#print axioms slotnum_not_reserved
end H62.AuditYul.ReservedRefutation
