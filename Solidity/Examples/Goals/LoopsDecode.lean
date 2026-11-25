import Solidity.Correctness.Lowering.Total.Versions.CalleeBinding.Frame
import Solidity.Correctness.Lowering.Total.Versions.CalleeBinding.Functions
import Solidity.Correctness.Lowering.Total.Decode.Callee.Units
import Solidity.Correctness.Lowering.Total.Decode.Callee.Declarations
import Solidity.Correctness.Lowering.Total.Decode.Callee.Metadata
import Solidity.Correctness.Lowering.Total.Versions.CalleeBinding.Resolved
import Solidity.Source.Elaborate
import Solidity.Correctness.Lowering.Total.Versions.Self
import Solidity.Correctness.Lowering.Total.Decode.BytesLiteral.Evaluation
import Solidity.Correctness.Lowering.Total.Decode.WithExpr
import Solidity.Correctness.Lowering.Total.Decode.Callee.Functions

namespace Solidity.Examples.Goals.LoopsDecode

open Solidity.Correctness.Lowering Solidity.Correctness.Lowering.Total
open Solidity.Correctness.Lowering.Checker

/-- The decoder reads neither the fresh-name scheme nor the counter. -/
def sampleNames : FreshNames := (.ofPrefixes "se" "sp" "ie" "mv")

def sampleRequest (raw : List RawStmt) : Request :=
  ⟨IntrinsicProbe.C, ⟨sampleNames, none, raw, RawProbe.scope, ⟨(RawProbe.inputLocals, 1), {}⟩⟩,
    none⟩

/-! ### The width-aware decoder version (H1258, additive)

`Decode.tablesW.decode` reads primitives at their declared widths; the landed
decoder is unchanged. -/

/-- Over `uint8 n; uint16 k`: widening `k = n` types, narrowing `n = k` does
not; `n = 255` fits and `n = 256` does not. So the widths are read. -/
def narrowRequest (raw : List RawStmt) : Request :=
  ⟨IntrinsicProbe.C, ⟨sampleNames, none, raw, RawProbe.scope,
    ⟨([("n", .val .uint 8), ("k", .val .uint 16)], 1), {}⟩⟩, none⟩
example : (Decode.tablesW.decode (narrowRequest [.assign (.name "k") (.name "n")])).isSome =
    true := rfl
example : Decode.tablesW.decode (narrowRequest [.assign (.name "n") (.name "k")]) = none := rfl
example : (Decode.tablesW.decode (narrowRequest [.assign (.name "n") (.num 255)])).isSome =
    true := rfl
example : Decode.tablesW.decode (narrowRequest [.assign (.name "n") (.num 256)]) = none := rfl
/-- The landed decoder has no type for a narrow local. -/
example : Decode.decode (narrowRequest [.assign (.name "k") (.name "n")]) = none := rfl
/-- A narrow state variable is read at its row; a marker row, a variable named
like one, and a local marked as an erased `address` are gaps. -/
example : (Decode.tablesW.decode { sampleRequest [.assign (.name "s") (.num 255)] with
    contract := { vars := [("s", .prim .uint)], widths := [("s", 8)] } }).isSome = true := rfl
example : Decode.tablesW.decode { sampleRequest [.assign (.name "s") (.num 256)] with
    contract := { vars := [("s", .prim .uint)], widths := [("s", 8)] } } = none := rfl
example : Decode.tablesW.decode { sampleRequest [] with
    contract := { vars := [("s", .prim .uint)], widths := [("s#address", 20)] } } = none := rfl
example : Decode.tablesW.decode { sampleRequest [] with
    contract := { vars := [("x", .prim .uint), ("x#bytes", .prim .uint)] } } = none := rfl
/-- A `bytes1` state variable (`x ↦ 8` and the marker `x#bytes ↦ 1`) is a gap,
not a `uint8`; so is a `bool` with a width row. A row that names no state
variable is not read. -/
example : Decode.tablesW.decode { sampleRequest [] with
    contract := { vars := [("x", .prim .uint)], widths := [("x", 8), ("x#bytes", 1)] } } =
    none := rfl
example : Decode.tablesW.decode { sampleRequest [] with
    contract := { vars := [("b", .prim .bool)], widths := [("b", 8)] } } = none := rfl
example : (Decode.tablesW.decode { sampleRequest [.assign (.name "s") (.num 256)] with
    contract := { vars := [("s", .prim .uint)], widths := [("t", 8)] } }).isSome = true := rfl
/-! Declarations by name: `uint8 m = n` types over `uint8 n`, `uint8 m = k` does
not over `uint16 k`, and `address`/`bytes1` names are gaps. Names are read by
string functions, so these are evaluated, not kernel-checked. -/
#guard (Decode.tablesW.decode
  (narrowRequest [.decl (.named "uint8") "m" (some (.name "n"))])).isSome
#guard (Decode.tablesW.decode
  (narrowRequest [.decl (.named "uint8") "m" (some (.name "k"))])).isNone
#guard (Decode.tablesW.decode (narrowRequest [.decl (.named "address") "m" none])).isNone
#guard (Decode.tablesW.decode (narrowRequest [.decl (.named "bytes1") "m" none])).isNone
example : Decode.tablesW.decode { narrowRequest [] with
    input := { (narrowRequest []).input with
      before := ⟨([("a", .val .uint 256 [("#address", 20)])], 1), {}⟩ } } = none := rfl
/-- The tables of the landed decoder and of the width-aware version. -/
example : Decode.tables1 = ⟨Decode.typeName, Decode.localTy, Decode.unit, Decode.env⟩ := rfl
example : Decode.tablesW = ⟨Decode.typeNameW, Decode.localTyW, Decode.unitW, Decode.env⟩ := rfl
/-- The bridge: at the landed tables the generic decoder is the landed decoder
and the version's spelling relation is the landed one. -/
example (r : Request) : Decode.tables1.decode r = Decode.decode r := Decode.decode_tables1 r
example {r : Request} {s : SourceProgram} : SpellsT Decode.tables1 r s ↔ Spells r s :=
  spellsT_tables1
/-- On the e1 sample the width-aware version agrees with the landed decoder. -/
example : Decode.tablesW.decode (sampleRequest RawProbe.input) =
    Decode.decode (sampleRequest RawProbe.input) := rfl
/-- A version's decoder against its spelling relation: sound, unique, and
complete if Source inference is. -/
example {T : Decode.Tables} {r : Request} {s : SourceProgram} (h : T.decode r = some s) :
    SpellsT T r s := decode_spellsT h
example {T : Decode.Tables} (complete : InferCompleteT T) {r : Request} {s : SourceProgram} :
    T.decode r = some s ↔ SpellsT T r s := ⟨decode_spellsT, SpellsT.decode complete⟩
example {T : Decode.Tables} {r : Request} {s s' : SourceProgram} (h : SpellsT T r s)
    (h' : SpellsT T r s') : s = s' := h.unique h'

/-! ### The address-aware decoder version

`Decode.tablesA` reads an erased `address` where the model marks one. Its
boundary is pinned further down. -/

example : Decode.tablesA = ⟨Decode.typeNameA, Decode.localTyA, Decode.unitA, Decode.env⟩ := rfl
/-- Over `address a; address b; uint n`: `a = b` types, and neither `a = n`
nor `n = a` does, so the marker is read as a Source `address`. -/
def addressRequest (raw : List RawStmt) : Request :=
  ⟨IntrinsicProbe.C, ⟨sampleNames, none, raw, RawProbe.scope,
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

/-! ### The width-aware version's boundary (`Total.Versions`) -/

/-- Its value relation: a model `uint` holding 200 is related to the Source
`uint8` 200; a model `uint` is related to no signed Source integer. -/
example (D : Source.Layout) (h : Source.IntTy.u8.lo ≤ 200 ∧ 200 ≤ Source.IntTy.u8.hi)
    (x : PrimTy.uint.Denote) (same : x.1 = 200) :
    Version.Relation.ValRel D (.int Source.IntTy.u8) .uint (.int 200 h) x :=
  .uint Source.IntTy.u8 rfl 200 h x same
example (D : Source.Layout) (t : Source.IntTy) (signed : t.signed = true)
    (v : Source.Val D (.int t)) (x : PrimTy.uint.Denote) :
    ¬ Version.Relation.ValRel D (.int t) .uint v x :=
  fun h => by cases h with | uint _ unsigned => rw [signed] at unsigned; cases unsigned
/-- Total initial matching is a theorem for the version (Source to model). -/
example : Simulation.InitialMatching Version.rel Decode.tablesW.decode := Version.initialMatching
/-- The version's boundary admits every request whose pipeline succeeds. -/
example : FullDomain Version.boundary := Version.boundaryAt_fullDomain _ _
/-- What the contract, and its version 2, ask at the version's boundary. -/
example :
    LowerLoopsCorrectContract Version.boundary Version.boundary.reference
        Decode.tablesW.decode →
      ∀ r : Request, r.Succeeds → ∃ s, Decode.tablesW.decode r = some s :=
  fun h => (Iff.mp Version.residual_iff h).1
example :
    LowerLoopsCorrectContractV2 Version.rel Version.boundary Version.boundary.reference
        Decode.tablesW.decode → Simulation.Bound Version.rel Decode.tablesW.decode :=
  fun h => (Iff.mp Version.contractV2_iff h).2.2.2.2

/-! ### The address-aware version's boundary -/

/-- A model `uint` and the Source address with the same number are related. -/
example (D : Source.Layout) (a : Solidity.Roadmap.Address) (x : PrimTy.uint.Denote)
    (same : x.1 = (a.val : Int)) :
    Version.Relation.ValRel D (.address false) .uint (.address a) x :=
  .address false a x same
/-- A model `uint` of `2^160` or more is related to no Source address. -/
example (D : Source.Layout) (p : Bool) (v : Source.Val D (.address p)) (x : PrimTy.uint.Denote)
    (big : (2 : Int) ^ 160 ≤ x.1) : ¬ Version.Relation.ValRel D (.address p) .uint v x :=
  fun h => by
    cases h with
    | address _ a _ same =>
      have bound : ((a.val : Nat) : Int) < (2 : Int) ^ 160 := by
        have := a.isLt
        exact_mod_cast this
      omega
/-- The address-aware tables are sound, so total initial matching holds for
them, and version 2 of the contract at their boundary is five obligations. -/
example : Version.Sound Decode.tablesA := Version.soundA
example : Simulation.InitialMatching Version.rel Decode.tablesA.decode :=
  Version.initialMatchingAt Version.soundA
example :
    LowerLoopsCorrectContractV2 Version.rel Version.boundaryA Version.boundaryA.reference
        Decode.tablesA.decode → Simulation.Bound Version.rel Decode.tablesA.decode :=
  fun h => (Iff.mp (Version.contractV2At_iff Version.soundA) h).2.2.2.2
example : FullDomain Version.boundaryA := Version.boundaryAt_fullDomain _ _

/-! ### The bytes-aware decoder version and its boundary

`Decode.tablesB` reads an erased `bytesN` where the model marks one. -/

example : Decode.tablesB = ⟨Decode.typeNameB, Decode.localTyB, Decode.unitB, Decode.env⟩ := rfl
/-- Over `bytes1 x; bytes1 y; uint8 n`: `x = y` types and neither `x = n` nor
`n = x` does, so the marker is read as `bytes1`, not `uint8`. A marker whose
size does not match the width is a gap. -/
def bytesRequest (raw : List RawStmt) : Request :=
  ⟨IntrinsicProbe.C, ⟨sampleNames, none, raw, RawProbe.scope,
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
/-- A model `uint` and the Source `bytesN` with that big-endian value are
related: the two bytes `0x01 0x02` and the number 258 (not 513). -/
example (D : Source.Layout) (x : PrimTy.uint.Denote) (same : x.1 = 258) :
    Version.Relation.ValRel D (.fixedBytes 2 (by decide)) .uint (.fixedBytes [1, 2] rfl) x :=
  .bytes 2 (by decide) [1, 2] rfl x (same.trans (by decide))
example : Source.bytesNat [1, 2] = 258 := by decide
/-- A `bytes32` local is read; a marker of 0 or 33 bytes, a marker on an
`int`, and a doubled marker (a captured value) are gaps. -/
example : (Decode.tablesB.decode { bytesRequest [.assign (.name "w") (.name "w")] with
    input := { (bytesRequest [.assign (.name "w") (.name "w")]).input with
      before := ⟨([("w", .val .uint 256 [("#bytes", 32)])], 1), {}⟩ } }).isSome = true := rfl
example : Decode.tablesB.decode { bytesRequest [] with
    input := { (bytesRequest []).input with
      before := ⟨([("w", .val .uint 0 [("#bytes", 0)])], 1), {}⟩ } } = none := rfl
example : Decode.tablesB.decode { bytesRequest [] with
    input := { (bytesRequest []).input with
      before := ⟨([("w", .val .uint 264 [("#bytes", 33)])], 1), {}⟩ } } = none := rfl
example : Decode.tablesB.decode { bytesRequest [] with
    input := { (bytesRequest []).input with
      before := ⟨([("w", .val .int 8 [("#bytes", 1)])], 1), {}⟩ } } = none := rfl
example : Decode.tablesB.decode { bytesRequest [] with
    input := { (bytesRequest []).input with
      before := ⟨([("w", .val .uint 8 [("#bytes", 1), ("#bytes", 1)])], 1), {}⟩ } } =
    none := rfl
/-- The bytes-aware tables are sound, so total initial matching holds for
them, and version 2 of the contract at their boundary is five obligations. -/
example : Version.Sound Decode.tablesB := Version.soundB
example : Simulation.InitialMatching Version.rel Decode.tablesB.decode :=
  Version.initialMatchingAt Version.soundB
example :
    LowerLoopsCorrectContractV2 Version.rel Version.boundaryB Version.boundaryB.reference
        Decode.tablesB.decode → Simulation.Bound Version.rel Decode.tablesB.decode :=
  fun h => (Iff.mp (Version.contractV2At_iff Version.soundB) h).2.2.2.2

/-! ### The caller-aware decoder version

`Decode.tablesS` reads `msg.sender`; the state relation relates the caller. -/

/-- `a = msg.sender` types for an address `a` and not for a `uint`; the
bytes-aware version has no reading of `msg.sender`. -/
example : (Decode.tablesS.decode (addressRequest [.assign (.name "a") (.env .msgSender)])).isSome =
    true := rfl
example : Decode.tablesS.decode (addressRequest [.assign (.name "n") (.env .msgSender)]) =
    none := rfl
example : Decode.tablesB.decode (addressRequest [.assign (.name "a") (.env .msgSender)]) =
    none := rfl
example : (Decode.tablesS.decode
    (addressRequest [.require (.binop .eqB (.env .msgSender) (.name "a"))])).isSome = true := rfl
example : Decode.tablesS.decode (addressRequest [.assign (.name "a") (.env .selfAddress)]) =
    none := rfl
/-- Related globals have the model's caller equal to the Source sender. -/
example {E : Source.Env} {C : Contract} {G : Source.Glob E} {F : Source.Fr} {st : Source.St E}
    {σ : State C []} (h : (Version.rel E C).glob G F st σ) :
    σ.tx.msgSender.1 = (F.sender.val : Int) := h.2.2.2.1
/-- `envS` reads exactly `msg.sender`, as the Source `msg.sender`. -/
example : Decode.envS .msgSender = some (.member (.ident "msg") "sender") := rfl
example : Decode.envS .selfAddress = Decode.env .selfAddress := rfl
/-- The caller-aware tables are sound; total initial matching holds for them. -/
example : Version.Sound Decode.tablesS := Version.soundS
example : Simulation.InitialMatching Version.rel Decode.tablesS.decode :=
  Version.initialMatchingAt Version.soundS
example : FullDomain Version.boundaryS := Version.boundaryAt_fullDomain _ _

/-! ### The self-aware decoder version

`Decode.tablesT` reads `address(this)` and its balance; the state relation
relates the running account's address and observed balance. -/

/-- `a = address(this)` types for an address `a` and not for a `uint`;
`n = address(this).balance` types for a `uint` `n` and not for an address. The
caller-aware version reads neither. -/
example : (Decode.tablesT.decode
    (addressRequest [.assign (.name "a") (.env .selfAddress)])).isSome = true := rfl
example : Decode.tablesT.decode (addressRequest [.assign (.name "n") (.env .selfAddress)]) =
    none := rfl
example : (Decode.tablesT.decode
    (addressRequest [.assign (.name "n") (.env .selfBalance)])).isSome = true := rfl
example : Decode.tablesT.decode (addressRequest [.assign (.name "a") (.env .selfBalance)]) =
    none := rfl
example : Decode.tablesS.decode (addressRequest [.assign (.name "n") (.env .selfBalance)]) =
    none := rfl
/-- Both reads inside a loop condition and a comparison with the caller. -/
example : (Decode.tablesT.decode (addressRequest
    [.whileLoop {} (.binop .lt (.name "n") (.env .selfBalance))
      [.require (.binop .neB (.env .msgSender) (.env .selfAddress)),
       .incDec .postInc (.name "n")]])).isSome = true := rfl
/-- The environment table has no gap left, and is the caller-aware one elsewhere. -/
example (k : EnvKey) : (Decode.envT k).isSome = true := Decode.envT_total k
example : Decode.envT .msgSender = Decode.envS .msgSender := rfl
example : Decode.envT .selfAddress = some Decode.thisAddress := rfl
/-- Related globals relate both reads to the Source frame's own account. -/
example {E : Source.Env} {C : Contract} {G : Source.Glob E} {F : Source.Fr} {st : Source.St E}
    {σ : State C []} (h : (Version.rel E C).glob G F st σ) :
    σ.tx.selfAddress.1 = (F.this.val : Int) ∧
      σ.selfBalance.1 = ((Version.Relation.ownBalance G F st).val : Int) :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩
/-- The self-aware tables are sound; total initial matching holds for them. -/
example : Version.Sound Decode.tablesT := Version.soundT
example : Simulation.InitialMatching Version.rel Decode.tablesT.decode :=
  Version.initialMatchingAt Version.soundT
example : FullDomain Version.boundaryT := Version.boundaryAt_fullDomain _ _


/-- Supplementary primitive representation check; simulation is separate. -/
example {p : PrimTy} {bits : Nat} {τ : Source.STy}
    (h : Decode.primTy p bits = some τ) : Version.Prim p τ := Version.prim_of_primTy h

/-- The state-variable width checks also hold beside narrow locals. -/
example : (Decode.tablesW.decode { narrowRequest [.assign (.name "s") (.num 255)] with
    contract := { vars := [("s", .prim .uint)], widths := [("s", 8)] } }).isSome = true := rfl
example : Decode.tablesW.decode { narrowRequest [.assign (.name "s") (.num 256)] with
    contract := { vars := [("s", .prim .uint)], widths := [("s", 8)] } } = none := rfl

/-- Full-width matching does not imply converse matching at a narrow width:
300 has a related uint256 value but no related uint8 value. -/
example (E : Source.Env) (C : Contract) (H : HTy) :
    (∃ v, Version.Relation.val E C H (Source.Agreement.sourceTy .uint) (.val .uint) v
      (⟨300, by decide⟩ : PrimTy.uint.Denote)) ∧
    ¬ ∃ v, Version.Relation.val E C H (.int Source.IntTy.u8) (.val .uint) v
      (⟨300, by decide⟩ : PrimTy.uint.Denote) := by
  constructor
  · exact Version.Relation.val_total E C H .uint _
  · rintro ⟨v, h⟩
    cases h
    rename_i n unsigned bounds same
    have upper : n ≤ 255 := bounds.2
    change 300 = n at same
    omega

/-! Fixed-bytes literal components are folded before byte normalization. These
checks exercise the literal helper; the shared call decoder is not extended yet. -/
example : Decode.BytesLiteral.decode (.bytesLit [0, 256]) =
    some (.lit (.hexStr [1, 0])) := rfl
example : Decode.BytesLiteral.decode (.bytesLit [222, 173]) =
    some (.lit (.hexStr [222, 173])) := rfl
example : Decode.BytesLiteral.decode (.call bytesLitName [.bool true]) = none := rfl
example (Γ : Source.Ctx) :
    Source.Typed Γ (Decode.BytesLiteral.spelling [0, 256]) (.stringLit [1, 0]) := .hexStr _
/-- Padding carries the folded value, rather than truncating the second component. -/
example : Source.bytesNat (Source.fitBytes 4 (Decode.BytesLiteral.bytes [0, 256])) =
    16777216 := Decode.BytesLiteral.faithful rfl (by decide)
example : Source.bytesNat (Source.fitBytes 0 (Decode.BytesLiteral.bytes [])) = 0 :=
  Decode.BytesLiteral.faithful rfl (by decide)
/-- A one-component overflow does not satisfy the model target-width check. -/
example : bytesAlign 1 [256] = .ok 256 ∧ ¬ 256 < 256 ^ 1 := ⟨rfl, by decide⟩

/-- Contextual conversion and the actual checks justify the carry-and-padding value. -/
example (C : Contract) (Γ : ECtx) (Δ : NCtx) :
    Source.bytesNat (Source.fitBytes 4 (Decode.BytesLiteral.bytes [0, 256])) =
      16777216 := by
  letI : FreshNames := sampleNames
  exact Decode.BytesLiteral.faithful_checked C Γ Δ (o := .bytesLit [0, 256])
    (e := .num 0) (by decide) rfl rfl rfl (by
      simp only [check]
      rfl)

/-- At bytes32, fitCheck alone accepts an overflowing word; the numeric checker
rejects it. Both checks in faithful_checked are therefore material. -/
example (C : Contract) (Γ : ECtx) (Δ : NCtx) :
    letI : FreshNames := sampleNames
    fitCheck C Γ .uint 256 (.num (2 ^ 256)) = .ok () ∧
      (check C Δ .uint (.num (2 ^ 256))).isOk = false := by
  constructor
  · rfl
  · simp only [check]
    rfl

/-- The full-word branch also proves faithfulness for a padded single byte. -/
example (C : Contract) (Γ : ECtx) (Δ : NCtx) :
    Source.bytesNat (Source.fitBytes 32 (Decode.BytesLiteral.bytes [1])) =
      256 ^ 31 := by
  letI : FreshNames := sampleNames
  exact Decode.BytesLiteral.faithful_checked C Γ Δ (o := .bytesLit [1])
    (e := .num 0) (by decide) rfl rfl rfl (by
      simp only [check]
      rfl)

/-- Source resolution and execution preserve the carry-normalized bytes4
value, at every horizon sufficient for a literal plus its conversion. -/
example (Γ : Source.Ctx) (G : Source.Glob Γ.env) (F : Source.Fr) (k : Nat) :
    Source.evalE G F (k + 2)
        (Decode.BytesLiteral.resolved Γ [0, 256] (n := 4) (by decide) rfl) =
      pure (.val (Source.mkBytes (n := 4) (h := by decide) [1, 0])) :=
  Decode.BytesLiteral.eval_resolved Γ G F k _ _ _

/-- The same resolved expression times out when its child has horizon zero;
the sufficient-horizon theorem does not silently alter Source's timeout. -/
example (Γ : Source.Ctx) (G : Source.Glob Γ.env) (F : Source.Fr) :
    Source.evalE G F 1
        (Decode.BytesLiteral.resolved Γ [0, 256] (n := 4) (by decide) rfl) =
      Source.EM.halt .timeout := by
  simp only [Decode.BytesLiteral.resolved, Decode.BytesLiteral.typed,
    Source.Typed.toR, Source.evalE]
  rfl

/-- The evaluator's fixed-bytes value exposes the same numeric value as the
model's checked contextual conversion. -/
example (C : Contract) (Γ : ECtx) (Δ : NCtx) (D : Source.Layout) :
    (Source.mkBytes (D := D) (n := 4) (h := by decide) [1, 0]).key =
      some (16777216 : Int) := by
  letI : FreshNames := sampleNames
  exact Decode.BytesLiteral.evaluated_value C Γ Δ (o := .bytesLit [0, 256])
    (e := .num 0) (by decide) rfl rfl rfl (by simp only [check]; rfl) D

/-! The additive call registry is honored inside ordinary call arguments and
operators, and a malformed claimed call never falls back to a user call. -/
example : Decode.Calls.expr Decode.tablesB CallSpellExt.registry1
    (.call "f" [.bytesLit [0, 256]]) = some
      (.call (.ident "f") (.positional (.cons (.lit (.hexStr [1, 0])) .nil))) := rfl
example : Decode.Calls.expr Decode.tablesB CallSpellExt.registry1
    (.binop .eqB (.bytesLit [1]) (.bytesLit [1])) = some
      (.equality .eq (.lit (.hexStr [1])) (.lit (.hexStr [1]))) := rfl
example : Decode.Calls.expr Decode.tablesB CallSpellExt.registry1
    (.call "f" [.call bytesLitName [.bool true]]) = none := rfl
example : Decode.Calls.expr Decode.tablesB CallSpellExt.registry1
    (.call "#other" [.num 1]) = Decode.tablesB.expr (.call "#other" [.num 1]) := rfl

/-- Both directions of the registered spelling contract hold, and they force
unique results and compatibility with v1 wherever no registered call occurs. -/
example (T : Decode.Tables) (R : CallSpellExt.Registry) :
    CallSpellExt.ConformsX T R (Decode.Calls.expr T R) := Decode.Calls.conformsX
example : CallSpellExt.conformsX_conforms_statement := Decode.Calls.conformsX_conforms
example : CallSpellExt.exprX_unclaimed_statement := Decode.Calls.unclaimed_spelling
example : CallSpellExt.exprX_nil_statement := Decode.Calls.empty_spelling
example (T : Decode.Tables) (R : CallSpellExt.Registry) (e : RawExpr)
    (a b : Source.Syn .expr) (ha : CallSpellExt.ExprX T R e a)
    (hb : CallSpellExt.ExprX T R e b) : a = b := Decode.Calls.unique ha hb

/-! Registered literals now reach Source statement inference through the
complete request decoder; the old decoder and its guard remain unchanged. -/
example : (Decode.Calls.decode Decode.tablesB CallSpellExt.registry1
    (bytesRequest [.assign (.name "x") (.bytesLit [1])])).isSome = true := rfl
example : Decode.tablesB.decode
    (bytesRequest [.assign (.name "x") (.bytesLit [1])]) = none := rfl
example : (Decode.Calls.decode Decode.tablesB CallSpellExt.registry1
    (bytesRequest [.block [.assign (.name "x") (.bytesLit [1])]])).isSome = true := rfl
example : (Decode.Calls.decode Decode.tablesB CallSpellExt.registry1
    (bytesRequest [.unchecked [.assign (.name "x") (.bytesLit [1])]])).isSome = true := rfl
example : Decode.Calls.decode Decode.tablesB CallSpellExt.registry1
    (bytesRequest [.assign (.name "x") (.call bytesLitName [.bool true])]) = none := rfl
example : Decode.Calls.decode Decode.tablesB CallSpellExt.registry1
    (bytesRequest [.assign (.name "x") (.bytesLit [1, 2])]) = none := rfl
/-- The complete old decoder is recovered for every request and table, not
only for the positive literal examples. -/
example (T : Decode.Tables) (r : Request) : Decode.Calls.decode T [] r = T.decode r :=
  Decode.Calls.decode_empty T r

example (T : Decode.Tables) (R : CallSpellExt.Registry) (r : Request) (s : SourceProgram)
    (h : Decode.Calls.decode T R r = some s) : Decode.plain r = true :=
  Decode.WithExpr.decode_guard T (Decode.Calls.expr T R) h

/-! Callee headers reach the real Source frame constructor. -/
private def calleeHeader : FunDecl :=
  { params := [("small", .prim .uint), ("who", .prim .uint), ("tag", .prim .uint)]
    rets := [("ok", .prim .bool), ("out", .prim .int)]
    widths := [("small", 8), ("who#address", 20), ("tag", 32), ("tag#bytes", 4), ("out", 16)]
    body := [] }

example : (do
    let (ps, rs) ← Decode.Callee.signature calleeHeader
    let f ← Source.Frame.mk? { decls := [] } none ps rs .nil true false
    pure (f.locals.map Prod.fst)) = some ["out", "ok", "tag", "who", "small"] := rfl

example : (do
    let (ps, rs) ← Decode.Callee.signature calleeHeader
    let f ← Source.Frame.mk? { decls := [] } none ps rs .nil true false
    pure (f.ps, f.rs)) = some
      ([.int ⟨false, 8, by decide⟩, .address false, .fixedBytes 4 (by decide)],
       [.bool, .int ⟨true, 16, by decide⟩]) := rfl

/-- Consume the general certificate at the heterogeneous concrete header:
all parameter/return slots retain their exact width/marker-table decisions. -/
example : ∃ f,
    (do
      let (ps, rs) ← Decode.Callee.signature calleeHeader
      Source.Frame.mk? { decls := [] } none ps rs .nil true false) = some f ∧
    f.names = [some "small", some "who", some "tag"] ∧
    f.rnames = [some "ok", some "out"] ∧
    Decode.Callee.Slots calleeHeader.widths calleeHeader.params f.ps ∧
    Decode.Callee.Slots calleeHeader.widths calleeHeader.rets f.rs := by
  obtain ⟨⟨ps, rs⟩, hs⟩ : ∃ sig, Decode.Callee.signature calleeHeader = some sig := ⟨_, rfl⟩
  obtain ⟨f, hf, pn, rn, pts, rts, _⟩ :=
    Decode.Callee.signature_frame hs { decls := [] } none .nil true false
  refine ⟨f, ?_, pn, rn, pts, rts⟩
  simp [hs, hf]

/-- Repeated names are preserved, not silently removed or renamed. -/
example : (Decode.Callee.parameters [] [("x", .prim .bool), ("x", .prim .bool)]).map
    Source.Syn.paramNames = some [some "x", some "x"] := rfl
example : Decode.Callee.parameters [("x", 7)] [("x", .prim .uint)] = none := rfl
example : Decode.Callee.parameters [("x", 32), ("x#bytes", 4), ("x#address", 20)]
    [("x", .prim .uint)] = none := rfl
/-- Reference parameters remain an explicit implementation gap. -/
example : Decode.Callee.parameters [] [("xs", .ref (.array (.prim .uint)))] = none := rfl

/-! Original ordinary function bodies reach Source elaboration. These are
component checks, not complete unit or callee-pipeline coverage. -/
private def identityCallee : FunDecl :=
  { params := [("x", .prim .uint)], rets := [("r", .prim .uint)]
    widths := [("x", 8), ("r", 8)], body := [.ret (some (.name "x"))] }

private def identityDecl := Decode.Callee.functionDecl Decode.tablesB
  CallSpellExt.registry1 "C" "identity" (some .internal) none identityCallee

-- Executable Source elaboration checks; the general frame certificate below
-- is kernel-proved separately.
#guard_msgs in
#eval (show IO Unit from do
  let actual := do
    let d ← identityDecl
    let b ← Source.elabBody { decls := [d] } d
    pure (b.val.ps.length, b.val.rs.length)
  unless actual == some (1, 1) do
    throw (IO.userError "identity callee failed Source body elaboration"))

/-- The assembly certificate connects this original declaration to its actual
Source frame, including the narrow parameter and return-slot correspondence. -/
example : ∃ d f, identityDecl = some d ∧
    d.frame? { decls := [d] } = some f ∧
    f.names = [some "x"] ∧ f.rnames = [some "r"] ∧
    Decode.Callee.Slots identityCallee.widths identityCallee.params f.ps ∧
    Decode.Callee.Slots identityCallee.widths identityCallee.rets f.rs := by
  obtain ⟨d, hd⟩ : ∃ d, identityDecl = some d := ⟨_, rfl⟩
  obtain ⟨_, _, _, _, f, _, _, _, _, hf, hn, hr, hp, hs, _⟩ :=
    Decode.Callee.functionDecl_faithful _ _ _ _ _ _ _ d hd { decls := [d] }
  exact ⟨d, f, hd, hf, hn, hr, hp, hs⟩

private def guardedCallee : FunDecl :=
  { identityCallee with mods :=
    [{ name := "first", params := [], args := [.bytesLit [1]], body := [] },
     { name := "second", params := [], args := [], body := [] }] }

example : (Decode.Callee.modifiers Decode.tablesB CallSpellExt.registry1
    guardedCallee.mods).map (fun ms => ms.invList.map (fun m => m.1.head)) =
    some ["first", "second"] := by
  change (some (.cons (.modInv ⟨"first", []⟩ (.some (.positional
    (.cons (.lit (.hexStr [1])) .nil))))
    (.cons (.modInv ⟨"second", []⟩ (.some (.positional .nil))) .nil)) :
      Option (Source.Syn (.list .modInv))).map _ = _
  simp [Source.Syn.invList]

-- Missing modifier definitions are rejected by Source elaboration; assembly
-- cannot silently erase them to make a body elaborate.
#guard_msgs in
#eval (show IO Unit from do
  let actual := do
    let d ← Decode.Callee.functionDecl Decode.tablesB CallSpellExt.registry1
      "C" "identity" (some .internal) none guardedCallee
    pure (Source.elabBody { decls := [d] } d).isSome
  unless actual == some false do
    throw (IO.userError "unresolved callee modifiers were not rejected"))

/-! Bind the translated function to its complete elaborated Source unit. -/
private def identityResolution : Source.Resolution :=
  let d := identityDecl.get (by rfl)
  Source.resolveUnit { pipeline := .legacy }
    (.unit (.cons (.contract false "C" .none .nil (.cons d.node .nil)) .nil))

#guard_msgs in
#eval (show IO Unit from do
  let d := identityDecl.get (by rfl)
  let actual := Version.CalleeBinding.fromResolution identityResolution d
  unless actual.isSome do
    throw (IO.userError "translated identity unit failed resolved-body binding"))

/-- The general binding certificate identifies the actual program body for
this translated declaration, rather than an independently chosen derivation. -/
example {s : Version.CalleeBinding.Output}
    (h : Version.CalleeBinding.fromResolution identityResolution
      (identityDecl.get (by rfl)) = some s) :
    s.source.prog.body (identityDecl.get (by rfl)) = some s.body :=
  (Version.CalleeBinding.fromResolution_bound h).2.2.2.2.1

#guard_msgs in
#eval (show IO Unit from do
  let actual := Version.CalleeBinding.fromResolutionAt identityResolution 1
  unless actual.map (fun s => s.declaration.name) == some "identity" do
    throw (IO.userError "indexed callee selection failed")
  unless (Version.CalleeBinding.fromResolutionAt identityResolution 0).isNone do
    throw (IO.userError "bodyless contract declaration was bound as a function")
  unless (Version.CalleeBinding.fromResolutionAt identityResolution 2).isNone do
    throw (IO.userError "out-of-range callee selection succeeded"))

example {s : Version.CalleeBinding.Output}
    (h : Version.CalleeBinding.fromResolutionAt identityResolution 1 = some s) :
    s.declaration ∈ s.source.res.env.decls :=
  (Version.CalleeBinding.fromResolutionAt_member h).2.1

/-! Retained ordinary headers supply source identity and call flags. -/
private def importedCallee : FunDecl :=
  let source : SourceFunction :=
    { name := "sourceIdentity", mutability := .viewFn,
      callable := .abi .externalFn .selected none }
  { identityCallee with sourceDecl := some source }

example : (Decode.Callee.fromMetadata Decode.tablesB CallSpellExt.registry1
    "C" importedCallee).map (fun d => d.name) = some "sourceIdentity" := rfl
example : (do
    let d ← Decode.Callee.fromMetadata Decode.tablesB CallSpellExt.registry1 "C" importedCallee
    let f ← d.frame? { decls := [d] }
    pure f.msgValue) = some false := rfl

example {d : Source.Decl}
    (h : Decode.Callee.fromMetadata Decode.tablesB CallSpellExt.registry1
      "C" importedCallee = some d) : d.name = "sourceIdentity" := by
  obtain ⟨source, _, hs, _, _, hn, _⟩ := Decode.Callee.fromMetadata_header h
  cases hs
  exact hn

#guard_msgs in
#eval (show IO Unit from do
  let d := (Decode.Callee.fromMetadata Decode.tablesB CallSpellExt.registry1
    "C" importedCallee).get (by rfl)
  let res := Source.resolveUnit { pipeline := .legacy }
    (.unit (.cons (.contract false "C" .none .nil (.cons d.node .nil)) .nil))
  unless (Version.CalleeBinding.fromResolution res d).isSome do
    throw (IO.userError "retained metadata function failed Source binding"))

example : Decode.Callee.fromMetadata Decode.tablesB CallSpellExt.registry1
    "C" identityCallee = none := rfl
example : Decode.Callee.ordinaryVisibility (.local .freeFn) = none := rfl
example : Decode.Callee.ordinaryVisibility (.abi .publicFn .retained none) = none := rfl
example : Decode.Callee.ordinaryVisibility .constructor = none := rfl
example : [SourceMutability.nonpayable, .pureFn, .viewFn, .payable].map
    Decode.Callee.sourceMutability = [none, some .pure, some .view, some .payable] := rfl

/-! The complete function-entry list is assembled in its original order. -/
private def secondImportedCallee : FunDecl :=
  let source : SourceFunction :=
    { name := "secondIdentity", callable := .local .internalFn }
  { identityCallee with sourceDecl := some source }
private def importedFunctions : List (Name × FunDecl) :=
  [("modelAlias1", importedCallee), ("modelAlias2", secondImportedCallee)]

#guard_msgs in
#eval (show IO Unit from do
  let actual := do
    let parts ← Decode.Callee.functionParts Decode.tablesB CallSpellExt.registry1 "C" importedFunctions
    let res := Source.resolveUnit { pipeline := .legacy }
      (.unit (.cons (.contract false "C" .none .nil parts) .nil))
    let first ← Version.CalleeBinding.fromResolutionAt res 1
    let second ← Version.CalleeBinding.fromResolutionAt res 2
    pure (first.declaration.name, second.declaration.name)
  unless actual == some ("sourceIdentity", "secondIdentity") do
    throw (IO.userError "function-list assembly lost source identity or order"))

example {parts : Source.Syn (.list (.part false))}
    (h : Decode.Callee.functionParts Decode.tablesB CallSpellExt.registry1
      "C" importedFunctions = some parts) :
    (parts.collect (some "C")).map some =
      importedFunctions.map (fun f =>
        Decode.Callee.fromMetadata Decode.tablesB CallSpellExt.registry1 "C" f.2) ∧
    (parts.collect (some "C")).length = 2 :=
  ⟨Decode.Callee.functionParts_faithful _ _ _ _ _ h,
    Decode.Callee.functionParts_length h⟩

/-- A missing-metadata entry between valid functions fails the entire list. -/
example : Decode.Callee.functionParts Decode.tablesB CallSpellExt.registry1 "C"
    [("first", importedCallee), ("unsupported", identityCallee),
      ("second", secondImportedCallee)] = none := rfl

/-! Supplied state syntax is retained before translated functions. -/
private def statePrefix : Source.Syn (.list (.part false)) :=
  .cons (.stateVar (.elem Decode.uintElem) none none none false "stored" .none) .nil
private def stateReader : FunDecl :=
  { importedCallee with
    params := []
    rets := [("r", .prim .uint)]
    widths := []
    body := [.ret (some (.name "stored"))] }

#guard_msgs in
#eval (show IO Unit from do
  let actual := do
    let u ← Decode.Callee.withFunctions Decode.tablesB CallSpellExt.registry1 "C"
      statePrefix [("modelReader", stateReader)]
    let res := Source.resolveUnit { pipeline := .legacy } u
    let bound ← Version.CalleeBinding.fromResolutionAt res 2
    pure (res.env.decls.map (fun d => d.name), bound.body.ps.length, bound.body.rs.length)
  unless actual == some (["C", "stored", "sourceIdentity"], 0, 1) do
    throw (IO.userError "unit assembly lost state prefix or state-reading function"))

/-- The declaration-table suffix is exactly the original function list's
translation; the offset counts the contract and all supplied declarations. -/
example {u : Source.Syn .unit}
    (h : Decode.Callee.withFunctions Decode.tablesB CallSpellExt.registry1 "C"
      statePrefix [("modelReader", stateReader)] = some u) :
    (u.decls.drop (1 + (statePrefix.collect (some "C")).length)).map some =
      [Decode.Callee.fromMetadata Decode.tablesB CallSpellExt.registry1 "C" stateReader] :=
  Decode.Callee.withFunctions_tail h

/-! Relative function selection skips the complete supplied declaration prefix. -/
#guard_msgs in
#eval (show IO Unit from do
  let bind := Version.CalleeBinding.fromFunctions Decode.tablesB CallSpellExt.registry1
    { pipeline := .legacy } "C" statePrefix [("modelReader", stateReader)]
  let actual := (bind 0).map fun s => (s.declaration.name, s.body.ps.length, s.body.rs.length)
  unless actual == some ("sourceIdentity", 0, 1) do
    throw (IO.userError "relative function selection did not bind the translated model entry")
  unless (bind 1).isNone do
    throw (IO.userError "out-of-range relative function selection succeeded"))

example {s : Version.CalleeBinding.Output}
    (h : Version.CalleeBinding.fromFunctions Decode.tablesB CallSpellExt.registry1
      { pipeline := .legacy } "C" statePrefix [("modelReader", stateReader)] 0 = some s) :
    Decode.Callee.fromMetadata Decode.tablesB CallSpellExt.registry1 "C" stateReader =
      some s.declaration := by
  obtain ⟨_, _, _, hd, _, _⟩ := Version.CalleeBinding.fromFunctions_bound h (by rfl)
  exact hd

/-- The selected frame retains the model declaration's original return name,
not the model alias or a name inferred from the Source body. -/
example {s : Version.CalleeBinding.Output}
    (h : Version.CalleeBinding.fromFunctions Decode.tablesB CallSpellExt.registry1
      { pipeline := .legacy } "C" statePrefix [("modelReader", stateReader)] 0 = some s) :
    s.frame.names = [] ∧ s.frame.rnames = [some "r"] ∧ s.frame.inModifier = false := by
  obtain ⟨_, _, _, _, _, _, _, hn, hr, _, _, _, hm⟩ :=
    Version.CalleeBinding.fromFunctions_frame h (by rfl)
  exact ⟨hn, hr, hm⟩

end Solidity.Examples.Goals.LoopsDecode
