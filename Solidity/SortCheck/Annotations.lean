import Solidity.Calculus.Rules

/-!
# Sort annotations of the solkey taclets

A machine-checked transcription of the *read-sort annotations* carried
by the read-bearing taclets of solkey's `solidityProgramRules.key`
(transcribed at solkey commit `8c5c69ca25`: 310 taclets, 110 of them
read-bearing, one row each). The sort-relevant history is
`12e72a1b4b` "removed find<int> to be more generic", `52c9c2477a`
"removed valAt", `0f9b99ad55` "removed different fields" (which
dropped the `Field[primitive]`/`Field[reference]` schema sorts in favour
of `\hasFieldSort`/`\hasMemoryFieldSort` bounds), `444f029579` (the
memory arithmetic families `memoryField*`/`memoryIndexArray*`) and
`29c44e225b` "fixed some rules", which merged the `_root`/`_decompose`
twins into one taclet each, split `storageIndex{Op}Assign` and
`storageIndex{Pre,Post}{in,de}crement[Assignment]` into a `Mapping` and
an `Array` taclet, and replaced the last two `find<[Struct]>` copy reads
(`storageFieldWriteCopySource`, `storagePushValueCopySource`) by the
sort-free `find<[StValue]>` — closing the two open findings this table
used to carry. Each `TacletReadAnn` row records, per KeY taclet, the
multiset of read operations its `\replacewith`/`\add` skeleton performs
and the KeY sort each read declares.

Two consumers keep this table honest from both sides:

- `SolkeyCheck` (`lake exe solkeycheck`) parses the live `.key` file and
  cross-checks it against `tacletReadAnns` — the **text ↔ table** edge.
  Any upstream drift (say, a reintroduced `find<[int]>` on a copy rule)
  fails the check.
- `Faithfulness.lean` proves the table's sort claims against the
  Lean interpreter — the **table ↔ semantics** edge. Updating the table
  to match a buggy taclet makes `sortFaithful_all` unprovable (see
  `Counterexamples/PreFixSortAnnotations.lean` for the exact bug the
  `12e72a1b4b` fix removed).

This file is deliberately proof-free data so the checker executable can
import it cheaply.
-/

namespace Solidity
namespace TacletAnnotations

/-- The `\has*Sort` varcond family that resolves a generic sort
(`alphaPrim`, `alpha`, `alphaMem`) at taclet-match time. -/
inductive SortVarcond where
  | hasSort
  | hasFieldSort
  | hasElementSort
  | hasMemoryFieldSort
  | hasMemoryElementSort
  deriving DecidableEq, Repr

/-- The sort a single read operation declares.

- `fixed s` — a sort of the lattice (`KeySort`), written into the
  taclet: `find<[int]>`, `find<[Struct]>`, `read<[Identity]>`,
  `read<[int]>`, `selectSt<[int]>` — and the sort-free reads
  `find<[StValue]>` (formerly `valAt(storage, p)`), which are
  `fixed .stValue`: `StValue` is the supersort of every storage value
  (`SVal.keySort_le_stValue`), so such a read claims nothing and the
  sort is recovered later by the cast `selectOnStore` inserts on the
  read side. The pre-fix bug of solkey `12e72a1b4b` was exactly a
  `fixed .int` where values of other sorts could flow.
- `generic vc` — schema-generic sort resolved by the varcond `vc`:
  `find<[alphaPrim]>` under `\hasSort`/`\hasFieldSort`/
  `\hasElementSort`, `read<[alpha]>`/`defaultValue<[alphaMem]>` under
  the memory varconds. -/
inductive ReadSort where
  | fixed (s : KeySort)
  | generic (vc : SortVarcond)
  deriving DecidableEq, Repr

/-- Which state component the read touches (classified by the read
symbol's first argument in the taclet text). -/
inductive ReadDomain where
  | storage
  | memory
  | net
  deriving DecidableEq, Repr

/-- What the read denotes inside the matched statement.

- `value` — the payload read the rule copies/tests (the RHS of a copy,
  the current value of a compound assignment or `++`/`--` target, the
  pushed element). `SortFaithfulness.ReadSite.expr?` maps it back to a
  Lean expression.
- `length` — an `.. size` cell read (`find<[int]>(storage,
  consr(sp, size))`, `read<[int]>(memory, mp, size)`): array-length
  bookkeeping, always int-sorted. The Lean model has no `size` cell, so
  these are token-checked only.
- `net` — a payment-ledger read `selectSt<[int]>(net, at(a))`.
- `dflt` — a `defaultValue<[..]>` write payload (`delete` rules). -/
inductive ReadSite where
  | value
  | length
  | net
  | dflt
  deriving DecidableEq, Repr

structure TacletRead where
  domain : ReadDomain
  site : ReadSite
  sort : ReadSort
  deriving DecidableEq, Repr

/-- Sort annotations of one KeY taclet: its exact name in
`solidityProgramRules.key`, the Lean rule it is mapped to in
`docs/lean-key-rule-map.md` (a representative when the map is
one-to-many, `none` for taclets outside the Lean rule set), and the
multiset of reads its skeleton performs, in file order. -/
structure TacletReadAnn where
  keyName : String
  leanRule : Option RuleName
  reads : List TacletRead
  deriving Repr, DecidableEq

/-! ## Row builders -/

private def sread (site : ReadSite) (sort : ReadSort) : TacletRead :=
  ⟨.storage, site, sort⟩

private def mread (site : ReadSite) (sort : ReadSort) : TacletRead :=
  ⟨.memory, site, sort⟩

private def slen : TacletRead := sread .length (.fixed .int)
private def mlen : TacletRead := mread .length (.fixed .int)

/-- The int-sorted read of an arithmetic target cell:
`find<[int]>(storage, ..)` / `read<[int]>(memory, ..)`. -/
private def sint : TacletRead := sread .value (.fixed .int)
private def mint : TacletRead := mread .value (.fixed .int)

/-! ### Compound assignment (`+=` .. `%=`)

Every arithmetic taclet reads its target cell int-sorted in the
`save`/`write`; the array forms bracket it with the bounds check's two
`size` reads (`\replacewith` and the `\add`ed "in bounds" premise, or
the memory `\add`s), in the order the taclet text has them. The former
`#inBounds*` premise, which re-read the cell, is gone with
`InBoundsTacletGenerator`. -/

/-- KeY compound-assignment taclet name fragment per operator. -/
def compoundOpName : BinOp -> String
  | .add => "Add"
  | .sub => "Sub"
  | .mul => "Mul"
  | .div => "Div"
  | .mod => "Mod"
  | _ => "?"

/-- The compound-assignment ops with KeY taclets (`+=` .. `%=`). -/
def compoundOps : List BinOp := [.add, .sub, .mul, .div, .mod]

private def compoundRows : List TacletReadAnn :=
  compoundOps.flatMap fun op =>
    [ { keyName := s!"storageRoot{compoundOpName op}Assign"
        leanRule := some (.storageRootOpAssign op)
        reads := [sint] },
      { keyName := s!"storageField{compoundOpName op}Assign"
        leanRule := some (.storageFieldOpAssign op)
        reads := [sint] },
      { keyName := s!"storageIndexMapping{compoundOpName op}Assign"
        leanRule := some (.storageIndexMappingOpAssign op)
        reads := [sint] },
      { keyName := s!"storageIndexArray{compoundOpName op}Assign"
        leanRule := some (.storageIndexArrayOpAssign op)
        reads := [slen, sint, slen] },
      { keyName := s!"memoryField{compoundOpName op}Assign"
        leanRule := some (.memoryFieldOpAssign op)
        reads := [mint] },
      { keyName := s!"memoryIndexArray{compoundOpName op}Assign"
        leanRule := some (.memoryIndexArrayOpAssign op)
        reads := [mint, mlen, mlen] } ]

/-! ### Increment / decrement

Statement forms (`sp.fld++;`) read the target cell once; the
`..Assignment` forms (`v = sp.fld++;`) read it a second time for the
captured old/new value. The storage index forms are split by receiver
kind upstream (`storageIndexMapping*` / `storageIndexArray*`), both
mapped to the one Lean `storageIndexIncrement[Assignment]`, whose
`KeyOrigin` is the merge of the two. -/

/-- KeY `Pre/Post` × `in/de` taclet name fragment per `IncDec` op. -/
def incDecOpName : IncDec -> String
  | .preInc => "Preincrement"
  | .preDec => "Predecrement"
  | .postInc => "Postincrement"
  | .postDec => "Postdecrement"

def incDecOps : List IncDec := [.preInc, .preDec, .postInc, .postDec]

private def incDecRows : List TacletReadAnn :=
  incDecOps.flatMap fun op =>
    [ { keyName := s!"storageRoot{incDecOpName op}"
        leanRule := some (.storageRootIncrement op)
        reads := [sint] },
      { keyName := s!"storageField{incDecOpName op}"
        leanRule := some (.storageFieldIncrement op)
        reads := [sint] },
      { keyName := s!"storageIndexMapping{incDecOpName op}"
        leanRule := some (.storageIndexIncrement op)
        reads := [sint] },
      { keyName := s!"storageIndexArray{incDecOpName op}"
        leanRule := some (.storageIndexIncrement op)
        reads := [slen, sint, slen] },
      { keyName := s!"storageRoot{incDecOpName op}Assignment"
        leanRule := some (.storageRootIncrementAssignment op)
        reads := [sint, sint] },
      { keyName := s!"storageField{incDecOpName op}Assignment"
        leanRule := some (.storageFieldIncrementAssignment op)
        reads := [sint, sint] },
      { keyName := s!"storageIndexMapping{incDecOpName op}Assignment"
        leanRule := some (.storageIndexIncrementAssignment op)
        reads := [sint, sint] },
      { keyName := s!"storageIndexArray{incDecOpName op}Assignment"
        leanRule := some (.storageIndexIncrementAssignment op)
        reads := [slen, sint, sint, slen] },
      { keyName := s!"memoryField{incDecOpName op}"
        leanRule := some (.memoryFieldIncrement op)
        reads := [mint] },
      { keyName := s!"memoryIndexArray{incDecOpName op}"
        leanRule := some (.memoryIndexArrayIncrement op)
        reads := [mint, mlen, mlen] },
      { keyName := s!"memoryField{incDecOpName op}Assignment"
        leanRule := some (.memoryFieldIncrementAssignment op)
        reads := [mint, mint] },
      { keyName := s!"memoryIndexArray{incDecOpName op}Assignment"
        leanRule := some (.memoryIndexArrayIncrementAssignment op)
        reads := [mint, mint, mlen, mlen] } ]

/-! ## The table -/

/-- Sort annotations of every read-bearing taclet in
`solidityProgramRules.key`, keyed by exact taclet name. `solkeycheck`
fails on any read-bearing taclet missing from this table
(`UNANNOTATED READS`), so coverage is enforced, not assumed. -/
def tacletReadAnns : List TacletReadAnn :=
  [ -- Storage root copies and reads.
    { keyName := "storageRootWriteCopySource"
      leanRule := some .storageRootWriteCopySource
      reads := [sread .value (.fixed .stValue)] },
    { keyName := "storageRootReadSelect"
      leanRule := some .storageRootReadSelect
      reads := [sread .value (.generic .hasSort)] },
    -- Field copies and reads.
    { keyName := "storageFieldWriteCopySource"
      leanRule := some .storageFieldWriteCopySource
      -- Sort-free since `29c44e225b`; was `find<[Struct]>` on a
      -- `Path[storage,simple]` source that may be primitive-typed — the
      -- open finding `Counterexamples/PreFixSortAnnotations.lean` refutes.
      reads := [sread .value (.fixed .stValue)] },
    { keyName := "storageFieldReadFind"
      leanRule := some .storageFieldReadFind
      reads := [sread .value (.generic .hasFieldSort)] },
    { keyName := "storageFieldReadStoreRoot"
      leanRule := some .storageFieldReadStoreRoot
      reads := [sread .value (.fixed .stValue)] },
    -- Mapping index rules.
    { keyName := "storageIndexReadMappingFind"
      leanRule := some .storageIndexReadMappingFind
      reads := [sread .value (.generic .hasElementSort)] },
    { keyName := "storageIndexReadMappingStoreRoot"
      leanRule := some .storageIndexReadMappingStoreRoot
      reads := [sread .value (.fixed .stValue)] },
    { keyName := "storageIndexWriteMappingCopySource"
      leanRule := some .storageIndexWriteMappingCopySource
      reads := [sread .value (.fixed .stValue)] },
    -- Array index rules (Lean splits by modality; the box rule is the
    -- representative). The bounds check reads `size` twice: once in
    -- the in-bounds `\replacewith`, once in the out-of-bounds one.
    { keyName := "storageIndexWriteArraySave"
      leanRule := some .storageIndexWriteArraySaveBox
      reads := [slen, slen] },
    { keyName := "storageIndexReadArrayFind"
      leanRule := some .storageIndexReadArrayFindBox
      reads := [slen, sread .value (.generic .hasElementSort), slen] },
    { keyName := "storageIndexReadArrayBindLocalRoot"
      leanRule := some .storageIndexReadArrayBindLocalRootBox
      reads := [slen, slen] },
    { keyName := "storageIndexReadArrayStoreRoot"
      leanRule := some .storageIndexReadArrayStoreRootBox
      reads := [slen, sread .value (.fixed .stValue), slen] },
    { keyName := "storageIndexWriteArrayCopySource"
      leanRule := some .storageIndexWriteArrayCopySourceBox
      reads := [slen, sread .value (.fixed .stValue), slen] },
    { keyName := "memoryToStorageIndexArrayCopyRoot"
      leanRule := some .memoryToStorageIndexArrayCopyRootBox
      reads := [slen, slen] },
    -- Push / pop.
    { keyName := "storagePushValueSave"
      leanRule := some .storagePushValueSave
      reads := [slen, slen] },
    { keyName := "storagePushValueCopySource"
      leanRule := some .storagePushValueCopySource
      -- Sort-free since `29c44e225b`; the second former `find<[Struct]>`
      -- open finding (see `storageFieldWriteCopySource`).
      reads := [slen, sread .value (.fixed .stValue), slen] },
    { keyName := "storagePushLengthSave"
      leanRule := some .storagePushLengthSave
      reads := [slen, slen] },
    { keyName := "storageLocalRootPushBind"
      leanRule := some .storageLocalRootPushBind
      reads := [slen, slen] },
    { keyName := "storagePopSave"
      leanRule := some .storagePopSaveBox
      reads := [slen, slen, slen, slen] },
    -- Cross-domain copies.
    { keyName := "memoryStorageCopy"
      leanRule := some .memoryStorageCopy
      -- The one surviving `find<[Struct]>`: its target is
      -- `Variable[memory]`, which Solidity types as a reference —
      -- provably faithful (`ruleRefTarget`).
      reads := [sread .value (.fixed .struct)] },
    { keyName := "memoryToStorageFieldCopyField"
      leanRule := some .memoryToStorageFieldCopyRoot
      reads := [mread .value (.fixed .identity)] },
    -- Memory reads. `memoryFieldRead` is the merge of the former
    -- `memoryFieldReadValue` (`Field[primitive]`) and `memoryFieldReadMemory`
    -- (`Field[reference]`, `read<[Identity]>`): one rule over a bare `Field`,
    -- its result sort resolved by `\hasMemoryFieldSort(a, \sort(alpha))` —
    -- which is what the Lean rule modelled all along.
    { keyName := "memoryFieldRead"
      leanRule := some .memoryFieldReadHeap
      reads := [mread .value (.generic .hasMemoryFieldSort)] },
    { keyName := "memoryIndexWriteArray"
      leanRule := some .memoryIndexWriteStoreBox
      reads := [mlen, mlen] },
    { keyName := "memoryIndexReadArrayValue"
      leanRule := some .memoryIndexReadHeapBox
      reads := [mread .value (.generic .hasMemoryElementSort), mlen,
        mlen] },
    { keyName := "memoryIndexReadArrayMemory"
      leanRule := some .memoryIndexReadHeapBox
      reads := [mread .value (.fixed .identity), mlen, mlen] },
    -- Memory deletes.
    { keyName := "memoryFieldDeletePrimitive"
      leanRule := some .memoryFieldDeletePrimitive
      reads := [mread .dflt (.generic .hasMemoryFieldSort)] },
    { keyName := "memoryIndexDeletePrimitive"
      leanRule := some .memoryIndexDeletePrimitiveBox
      reads := [mlen, mlen] },
    { keyName := "memoryIndexDeleteReference"
      leanRule := some .memoryIndexDeleteReferenceBox
      reads := [mlen, mlen] },
    -- Payments. solkey `333cc7b353` split each rule by modality: the box
    -- rule books the debit unconditionally, the diamond rule additionally
    -- owes the EVM funding check as a "sufficient funds" goal. The ledger
    -- read is the same `selectSt<[int]>(net, at(a))` in all four.
    { keyName := "transferNoCallbackBox"
      leanRule := some .transferNoCallbackBox
      reads := [⟨.net, .net, .fixed .int⟩] },
    { keyName := "transferNoCallbackDiamond"
      leanRule := some .transferNoCallbackDiamond
      reads := [⟨.net, .net, .fixed .int⟩] },
    { keyName := "transferWithCallbackBox"
      leanRule := some .transferWithCallback
      reads := [⟨.net, .net, .fixed .int⟩] },
    { keyName := "transferWithCallbackDiamond"
      leanRule := some .transferWithCallback
      reads := [⟨.net, .net, .fixed .int⟩] } ]
  ++ compoundRows ++ incDecRows

/-! ## The pre-fix annotations (solkey `12e72a1b4b^`)

The annotations the fixed commit removed, kept as data so
`Counterexamples/PreFixSortAnnotations.lean` can prove they are *not*
sort-faithful — i.e. that this layer catches the bug that slipped
through. The `_root` taclets of that era are the merged taclets of
today; the rows keep the names of their day. -/

/-- Pre-fix `storageRootWriteCopySource`: `find<[int]>(storage, sp)` on
a `Path[storage,simple]` source — mis-sorts `flag = flag2` on bools. -/
def preFixStorageRootWriteCopySource : TacletReadAnn :=
  { keyName := "storageRootWriteCopySource"
    leanRule := some .storageRootWriteCopySource
    reads := [sread .value (.fixed .int)] }

/-- Pre-fix `storageRootWriteCopySource_struct` (deleted by the fix):
the struct half of the duplicated rule pair. -/
def preFixStorageRootWriteCopySourceStruct : TacletReadAnn :=
  { keyName := "storageRootWriteCopySource_struct"
    leanRule := some .storageRootWriteCopySource
    reads := [sread .value (.fixed .struct)] }

/-- Pre-fix `storageRootReadSelect`: `find<[int]>` with no varcond. -/
def preFixStorageRootReadSelect : TacletReadAnn :=
  { keyName := "storageRootReadSelect"
    leanRule := some .storageRootReadSelect
    reads := [sread .value (.fixed .int)] }

/-- All pre-fix rows of the five taclets `12e72a1b4b` changed. -/
def preFixTacletReadAnns : List TacletReadAnn :=
  [ preFixStorageRootWriteCopySource,
    preFixStorageRootWriteCopySourceStruct,
    preFixStorageRootReadSelect,
    { keyName := "storageFieldReadFind"
      leanRule := some .storageFieldReadFind
      reads := [sread .value (.fixed .int)] },
    { keyName := "storageFieldReadStoreRoot"
      leanRule := some .storageFieldReadStoreRoot
      reads := [sread .value (.fixed .int)] },
    { keyName := "storageIndexReadMappingFind_root"
      leanRule := some .storageIndexReadMappingFind
      reads := [sread .value (.fixed .int)] },
    { keyName := "storageIndexReadMappingFind_decompose"
      leanRule := some .storageIndexReadMappingFind
      reads := [sread .value (.fixed .int)] },
    { keyName := "storageIndexReadMappingStoreRoot"
      leanRule := some .storageIndexReadMappingStoreRoot
      reads := [sread .value (.fixed .int)] },
    { keyName := "storageIndexReadArrayFind_root"
      leanRule := some .storageIndexReadArrayFindBox
      reads := [slen, sread .value (.fixed .int)] },
    { keyName := "storageIndexReadArrayFind_decompose"
      leanRule := some .storageIndexReadArrayFindBox
      reads := [slen, sread .value (.fixed .int)] },
    { keyName := "storageIndexReadArrayStoreRoot"
      leanRule := some .storageIndexReadArrayStoreRootBox
      reads := [slen, sread .value (.fixed .int)] } ]

-- Taclet names must be unique, and the table has one row per
-- read-bearing taclet of the pinned file.
#guard (tacletReadAnns.map (·.keyName)).Nodup
#guard tacletReadAnns.length = 110

end TacletAnnotations
end Solidity
