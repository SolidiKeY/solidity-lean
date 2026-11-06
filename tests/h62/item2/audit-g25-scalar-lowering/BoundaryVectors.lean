import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Lean

/-! Audit-only exporter. VM evaluation generates external-test inputs, never
proofs. The two segment identities are separately kernel checked. -/
namespace Solidity.Backend.Scalar.H62Audit.BoundaryVectors
open Solidity Solidity.Backend Solidity.Backend.Scalar

def negationBytes : List UInt8 :=
  (negatedTrue (C := default) (Γ := [])).bytes

def pushZeroBytes : List UInt8 :=
  Backend.encode [Environment.constant 0 ⟨0, by decide⟩]

theorem negation_bytes : negationBytes = 0x7f :: (List.replicate 31 0 ++ [1, 0x15]) :=
  negatedTrue_bytes

theorem push_zero_bytes : pushZeroBytes = [0x5f] := rfl

#eval do
  let bytes (xs : List UInt8) : Lean.Json := Lean.toJson (xs.map UInt8.toNat)
  IO.FS.writeFile "/workspace/h62-audit-g25-artifacts/evidence/boundary-vectors.json"
    ((Lean.Json.mkObj [("negatedTrue", bytes negationBytes),
      ("metadataPushZero", bytes pushZeroBytes)]).compress ++ "\n")

end Solidity.Backend.Scalar.H62Audit.BoundaryVectors
