import Solidity.Correctness.Lowering.Total.Versions.Primitive
import Solidity.Correctness.Lowering.Total.Decode.Spelling

namespace Solidity.Examples.Goals.LoopsDecode

open Solidity.Correctness.Lowering.Total

/-- The landed decoder table, retained from the producer examples. -/
example : Decode.tables1 = ⟨Decode.typeName, Decode.localTy, Decode.unit, Decode.env⟩ := rfl

/-- The bridge: the generic decoder at the landed tables preserves every request. -/
example (r : Request) : Decode.tables1.decode r = Decode.decode r := Decode.decode_tables1 r

/-- The retained width table configuration. -/
example : Decode.tablesW = ⟨Decode.typeNameW, Decode.localTyW, Decode.unitW, Decode.env⟩ := rfl

/-- Retained width probes use an empty contract and two narrow integer locals. -/
def narrowRequest (raw : List RawStmt) : Request :=
  ⟨{ vars := [] }, ⟨FreshNames.ofPrefixes "se" "sp" "ie" "mv", none, raw,
    { funs := [] }, ⟨([("n", .val .uint 8), ("k", .val .uint 16)], 1), {}⟩⟩, none⟩

example : (Decode.tablesW.decode (narrowRequest [.assign (.name "k") (.name "n")])).isSome =
    true := rfl
example : Decode.tablesW.decode (narrowRequest [.assign (.name "n") (.name "k")]) = none := rfl
example : (Decode.tablesW.decode (narrowRequest [.assign (.name "n") (.num 255)])).isSome =
    true := rfl
example : Decode.tablesW.decode (narrowRequest [.assign (.name "n") (.num 256)]) = none := rfl
example : Decode.decode (narrowRequest [.assign (.name "k") (.name "n")]) = none := rfl

example : (Decode.tablesW.decode { narrowRequest [.assign (.name "s") (.num 255)] with
    contract := { vars := [("s", .prim .uint)], widths := [("s", 8)] } }).isSome = true := rfl
example : Decode.tablesW.decode { narrowRequest [.assign (.name "s") (.num 256)] with
    contract := { vars := [("s", .prim .uint)], widths := [("s", 8)] } } = none := rfl
example : Decode.tablesW.decode { narrowRequest [] with
    contract := { vars := [("s", .prim .uint)], widths := [("s#address", 20)] } } = none := rfl

-- Declaration-name parsing checks are executable guards, not semantic faithfulness proofs.
#guard (Decode.tablesW.decode
  (narrowRequest [.decl (.named "uint8") "m" (some (.name "n"))])).isSome
#guard (Decode.tablesW.decode
  (narrowRequest [.decl (.named "uint8") "m" (some (.name "k"))])).isNone

/-- Type representation only; the version's simulation remains a separate obligation. -/
example {p : PrimTy} {bits : Nat} {τ : Source.STy}
    (h : Decode.primTy p bits = some τ) : Version.Prim p τ := Version.prim_of_primTy h

/-- Retained spelling checks preserve the Source inference completeness premise. -/
example {T : Decode.Tables} (complete : InferCompleteT T) {r : Request} {s : SourceProgram} :
    T.decode r = some s ↔ SpellsT T r s := ⟨decode_spellsT, SpellsT.decode complete⟩
example {r : Request} {s : SourceProgram} : SpellsT Decode.tables1 r s ↔ Spells r s :=
  spellsT_tables1

end Solidity.Examples.Goals.LoopsDecode
