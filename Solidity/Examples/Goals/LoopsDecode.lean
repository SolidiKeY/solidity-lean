import Solidity.Correctness.Lowering.Total.Versions.Marked
import Solidity.Correctness.Lowering.Total.Decode.Spelling
import Solidity.Correctness.Lowering.Total.Decode.Marked

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

/-! ### The address-aware decoder version

`Decode.tablesA` reads an erased `address` where the model marks one. -/

example : Decode.tablesA = ⟨Decode.typeNameA, Decode.localTyA, Decode.unitA, Decode.env⟩ := rfl
/-- Over `address a; address b; uint n`: `a = b` types, and neither `a = n`
nor `n = a` does, so the marker is read as a Source `address`. -/
def addressRequest (raw : List RawStmt) : Request :=
  ⟨{ vars := [] }, ⟨(.ofPrefixes "se" "sp" "ie" "mv"), none, raw, { funs := [] },
    ⟨([("a", .val .uint 256 Decode.addressShape), ("b", .val .uint 256 Decode.addressShape),
       ("n", .val .uint)], 1), {}⟩⟩, none⟩
example : (Decode.tablesA.decode (addressRequest [.assign (.name "a") (.name "b")])).isSome =
    true := rfl
example : Decode.tablesA.decode (addressRequest [.assign (.name "a") (.name "n")]) = none := rfl
example : Decode.tablesA.decode (addressRequest [.assign (.name "n") (.name "a")]) = none := rfl
/-- Equality of two addresses is spelled and typed; an address against a `uint`
or a numeric literal is not; a marker on a `bool`, or a doubled marker (a
captured address), is a gap. -/
example : (Decode.tablesA.decode
    (addressRequest [.require (.binop .eqB (.name "a") (.name "b"))])).isSome = true := rfl
example : Decode.tablesA.decode
    (addressRequest [.require (.binop .eqB (.name "a") (.name "n"))]) = none := rfl
example : Decode.tablesA.decode
    (addressRequest [.require (.binop .eqB (.name "a") (.num 0))]) = none := rfl
example : Decode.tablesA.decode { addressRequest [] with
    input := { (addressRequest []).input with
      before := ⟨([("f", .val .bool 256 Decode.addressShape)], 1), {}⟩ } } = none := rfl
example : Decode.tablesA.decode { addressRequest [] with
    input := { (addressRequest []).input with
      before := ⟨([("c", .val .uint 256 [("#address", 20), ("#address", 20)])], 1), {}⟩ } } =
    none := rfl
/-! A declaration by the name `address` decodes (evaluated, not kernel-checked:
names are read by string functions). -/
#guard (Decode.tablesA.decode
  (addressRequest [.decl (.named "address") "m" (some (.name "a"))])).isSome
#guard (Decode.tablesA.decode
  (addressRequest [.decl (.named "address") "m" (some (.name "n"))])).isNone
/-- The width-aware version has no type for a marked local. -/
example : Decode.tablesW.decode (addressRequest [.assign (.name "a") (.name "b")]) = none := rfl
/-- An address state variable (`owner#address ↦ 20`) is read; assigning it to
a `uint` does not type; a marker on a variable with its own width row, on an
`int`, or with another size is a gap. -/
def ownerContract : Contract :=
  { vars := [("owner", .prim .uint), ("total", .prim .uint)], widths := [("owner#address", 20)] }
example : (Decode.tablesA.decode { addressRequest [.assign (.name "owner") (.name "a")] with
    contract := ownerContract }).isSome = true := rfl
example : Decode.tablesA.decode { addressRequest [.assign (.name "total") (.name "owner")] with
    contract := ownerContract } = none := rfl
example : Decode.tablesA.decode { addressRequest [] with
    contract := { vars := [("o", .prim .uint)], widths := [("o", 8), ("o#address", 20)] } } =
    none := rfl
example : Decode.tablesA.decode { addressRequest [] with
    contract := { vars := [("o", .prim .int)], widths := [("o#address", 20)] } } = none := rfl
example : Decode.tablesA.decode { addressRequest [] with
    contract := { vars := [("o", .prim .uint)], widths := [("o#address", 32)] } } = none := rfl
/-- On requests with no address the version agrees with the width-aware one. -/
example : Decode.tablesA.decode (narrowRequest [.assign (.name "k") (.name "n")]) =
    Decode.tablesW.decode (narrowRequest [.assign (.name "k") (.name "n")]) := rfl
/-- Its decoder is sound for its spelling relation, as every version's is. -/
example {r : Request} {s : SourceProgram} (h : Decode.tablesA.decode r = some s) :
    SpellsT Decode.tablesA r s := decode_spellsT h

/-! ### The bytes-aware decoder version

`Decode.tablesB` reads an erased `bytesN` where the model marks one. -/

example : Decode.tablesB = ⟨Decode.typeNameB, Decode.localTyB, Decode.unitB, Decode.env⟩ := rfl
/-- Over `bytes1 x; bytes1 y; uint8 n`: `x = y` types and neither `x = n` nor
`n = x` does, so the marker is read as `bytes1`, not `uint8`. A marker whose
size does not match the width is a gap. -/
def bytesRequest (raw : List RawStmt) : Request :=
  ⟨{ vars := [] }, ⟨(.ofPrefixes "se" "sp" "ie" "mv"), none, raw, { funs := [] },
    ⟨([("x", .val .uint 8 [("#bytes", 1)]), ("y", .val .uint 8 [("#bytes", 1)]),
       ("n", .val .uint 8)], 1), {}⟩⟩, none⟩
example : (Decode.tablesB.decode (bytesRequest [.assign (.name "x") (.name "y")])).isSome =
    true := rfl
example : Decode.tablesB.decode (bytesRequest [.assign (.name "x") (.name "n")]) = none := rfl
example : Decode.tablesB.decode (bytesRequest [.assign (.name "n") (.name "x")]) = none := rfl
example : Decode.tablesB.decode { bytesRequest [] with
    input := { (bytesRequest []).input with
      before := ⟨([("z", .val .uint 16 [("#bytes", 1)])], 1), {}⟩ } } = none := rfl
/-- The address-aware version has no type for a bytes-marked local. -/
example : Decode.tablesA.decode (bytesRequest [.assign (.name "x") (.name "y")]) = none := rfl
/-- State variables: `bytes1 s` (rows `s ↦ 8`, `s#bytes ↦ 1`) and `bytes32 h`
(row `h#bytes ↦ 32` only) are read; `s = x` types, and neither `s = n` nor the
narrowing `x = h` does; a
marker that does not match the width, or beside an address marker, is a gap. -/
def bytesContract : Contract :=
  { vars := [("s", .prim .uint), ("h", .prim .uint)],
    widths := [("s", 8), ("s#bytes", 1), ("h#bytes", 32)] }
example : (Decode.tablesB.decode { bytesRequest [.assign (.name "s") (.name "x")] with
    contract := bytesContract }).isSome = true := rfl
example : Decode.tablesB.decode { bytesRequest [.assign (.name "s") (.name "n")] with
    contract := bytesContract } = none := rfl
example : Decode.tablesB.decode { bytesRequest [.assign (.name "x") (.name "h")] with
    contract := bytesContract } = none := rfl
example : Decode.tablesB.decode { bytesRequest [] with
    contract := { vars := [("s", .prim .uint)], widths := [("s", 16), ("s#bytes", 1)] } } =
    none := rfl
example : Decode.tablesB.decode { bytesRequest [] with
    contract := { vars := [("s", .prim .uint)],
                  widths := [("s#bytes", 32), ("s#address", 20)] } } = none := rfl
/-- Probes of what is in the fragment between marked operands. -/
example : (Decode.tablesB.decode { bytesRequest [.assign (.name "h") (.name "x")] with
    contract := bytesContract }).isSome = true := rfl
example : (Decode.tablesB.decode
    (bytesRequest [.assign (.name "y") (.index (.name "x") (.num 0))])).isSome = true := rfl
example : (Decode.tablesB.decode
    (bytesRequest [.assign (.name "n") (.field (.name "x") "length")])).isSome = true := rfl
example : (Decode.tablesB.decode
    (bytesRequest [.assign (.name "x") (.binop .band (.name "x") (.name "y"))])).isSome =
    true := rfl
example : (Decode.tablesB.decode
    (bytesRequest [.require (.binop .lt (.name "x") (.name "y"))])).isSome = true := rfl
example : Decode.tablesB.decode
    (bytesRequest [.assign (.name "x") (.call "bytes1" [.name "n"])]) = none := rfl
/-! A declaration by the name `bytes1` decodes (evaluated, not kernel-checked). -/
#guard (Decode.tablesB.decode
  (bytesRequest [.decl (.named "bytes1") "m" (some (.name "x"))])).isSome
#guard (Decode.tablesB.decode
  (bytesRequest [.decl (.named "bytes1") "m" (some (.name "n"))])).isNone
/-! ### The caller-aware decoder version

`Decode.tablesS` reads `msg.sender` as a Source address. -/

/-- `a = msg.sender` types for an address `a` and not for a `uint`; the
bytes-aware version has no reading of `msg.sender`. -/
example : (Decode.Tables.decode Decode.tablesS (addressRequest [.assign (.name "a") (.env .msgSender)])).isSome =
    true := rfl
example : Decode.tablesS.decode (addressRequest [.assign (.name "n") (.env .msgSender)]) =
    none := rfl
example : Decode.tablesB.decode (addressRequest [.assign (.name "a") (.env .msgSender)]) =
    none := rfl
example : (Decode.tablesS.decode
    (addressRequest [.require (.binop .eqB (.env .msgSender) (.name "a"))])).isSome = true := rfl
example : Decode.tablesS.decode (addressRequest [.assign (.name "a") (.env .selfAddress)]) =
    none := rfl
/-- `envS` reads exactly `msg.sender`, as the Source `msg.sender`. -/
example : Decode.envS .msgSender = some (.member (.ident "msg") "sender") := rfl
example : Decode.envS .selfAddress = Decode.env .selfAddress := rfl
/-- Retained initial matching runs from Source states to model states. -/
example : Simulation.InitialMatching Version.rel Decode.tablesW.decode := Version.initialMatching
/-- Related globals preserve the caller value. -/
example {E : Source.Env} {C : Contract} {G : Source.Glob E} {F : Source.Fr} {st : Source.St E}
    {σ : State C []} (h : (Version.rel E C).glob G F st σ) :
    σ.tx.msgSender.1 = (F.sender.val : Int) := h.2.2.2.1

/-- Retained marked-type matching statements keep the same one-way relation. -/
example : Simulation.InitialMatching Version.rel Decode.tablesA.decode :=
  Version.initialMatchingAt Version.soundA
example : Simulation.InitialMatching Version.rel Decode.tablesB.decode :=
  Version.initialMatchingAt Version.soundB

end Solidity.Examples.Goals.LoopsDecode
