import Solidity.Rules

/-!
# Sort annotations of the solkey taclets

A machine-checked transcription of the *read-sort annotations* carried
by the read-bearing taclets of solkey's `solidityProgramRules.key`
(transcribed at solkey commit `0f9b99ad55` and unchanged at `e67a0d7c48` —
that commit touches
only `structRules.key`; the sort-relevant history is
`12e72a1b4b` "removed find<int> to be more generic", `52c9c2477a`
"removed valAt", and `0f9b99ad55` "removed different fields", which
dropped the `Field[primitive]`/`Field[reference]` schema sorts in favour
of `\hasFieldSort`/`\hasMemoryFieldSort` bounds). Each `TacletReadAnn`
row records, per KeY taclet, the
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

/-- `storage{Root,Field,Index}{Add..Mod}Assign` read the target cell
int-sorted in the `save` (the former `#inBounds*` premise, which
re-read the cell, was dropped together with `InBoundsTacletGenerator`). -/
private def compoundReads (_op : BinOp) : List TacletRead :=
  [sread .value (.fixed .int)]

private def compoundRows : List TacletReadAnn :=
  compoundOps.flatMap fun op =>
    [ { keyName := s!"storageRoot{compoundOpName op}Assign"
        leanRule := some (.storageRootCompoundAssign op)
        reads := compoundReads op },
      { keyName := s!"storageField{compoundOpName op}Assign"
        leanRule := some (.storageFieldCompoundAssign op)
        reads := compoundReads op },
      { keyName := s!"storageIndex{compoundOpName op}Assign"
        leanRule := some (.storageIndexCompoundAssign op)
        reads := compoundReads op } ]

/-- KeY `Pre/Post` × `in/de` taclet name fragment per `IncDec` op. -/
def incDecOpName : IncDec -> String
  | .preInc => "Preincrement"
  | .preDec => "Predecrement"
  | .postInc => "Postincrement"
  | .postDec => "Postdecrement"

def incDecOps : List IncDec := [.preInc, .preDec, .postInc, .postDec]

/-- Statement-form `storage{Root,Field,Index}{Pre,Post}{in,de}crement`:
one int read of the target cell in the `save`. -/
private def incDecReads : List TacletRead :=
  [sread .value (.fixed .int)]

/-- Assignment-form `..Assignment` variants additionally read the cell
for the captured old/new value. -/
private def incDecAssignReads : List TacletRead :=
  [sread .value (.fixed .int), sread .value (.fixed .int)]

private def incDecRows : List TacletReadAnn :=
  incDecOps.flatMap fun op =>
    [ { keyName := s!"storageRoot{incDecOpName op}"
        leanRule := some (.storageRootIncDec op)
        reads := incDecReads },
      { keyName := s!"storageField{incDecOpName op}"
        leanRule := some (.storageFieldIncDec op)
        reads := incDecReads },
      { keyName := s!"storageIndex{incDecOpName op}"
        leanRule := some (.storageIndexIncDec op)
        reads := incDecReads },
      { keyName := s!"storageRoot{incDecOpName op}Assignment"
        leanRule := some (.storageRootIncDecAssignment op)
        reads := incDecAssignReads },
      { keyName := s!"storageField{incDecOpName op}Assignment"
        leanRule := some (.storageFieldIncDecAssignment op)
        reads := incDecAssignReads },
      { keyName := s!"storageIndex{incDecOpName op}Assignment"
        leanRule := some (.storageIndexIncDecAssignment op)
        reads := incDecAssignReads } ]

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
      -- `find<[Struct]>(storage, sp2)` on a `Path[storage,simple]`
      -- source: NOT sort-faithful for primitive-typed sources — an
      -- `openFindings` entry, see `Faithfulness.lean`.
      reads := [sread .value (.fixed .struct)] },
    { keyName := "storageFieldReadFind"
      leanRule := some .storageFieldReadFind
      reads := [sread .value (.generic .hasFieldSort)] },
    { keyName := "storageFieldReadStoreRoot"
      leanRule := some .storageFieldReadStoreRoot
      reads := [sread .value (.fixed .stValue)] },
    -- Mapping index rules.
    { keyName := "storageIndexReadMappingFind_root"
      leanRule := some .storageIndexReadMappingFind
      reads := [sread .value (.generic .hasElementSort)] },
    { keyName := "storageIndexReadMappingFind_decompose"
      leanRule := some .storageIndexReadMappingFind
      reads := [sread .value (.generic .hasElementSort)] },
    { keyName := "storageIndexReadMappingStoreRoot"
      leanRule := some .storageIndexReadMappingStoreRoot
      reads := [sread .value (.fixed .stValue)] },
    { keyName := "storageIndexWriteMappingCopySource"
      leanRule := some .storageIndexWriteMappingCopySource
      reads := [sread .value (.fixed .stValue)] },
    -- Array index rules (Lean splits by modality; the box rule is the
    -- representative).
    { keyName := "storageIndexWriteArraySave_root"
      leanRule := some .storageIndexWriteArraySaveBox
      reads := [slen, slen] },
    { keyName := "storageIndexWriteArraySave_decompose"
      leanRule := some .storageIndexWriteArraySaveBox
      reads := [slen, slen] },
    { keyName := "storageIndexReadArrayFind_root"
      leanRule := some .storageIndexReadArrayFindBox
      reads := [slen, sread .value (.generic .hasElementSort)] },
    { keyName := "storageIndexReadArrayFind_decompose"
      leanRule := some .storageIndexReadArrayFindBox
      reads := [slen, sread .value (.generic .hasElementSort)] },
    { keyName := "storageIndexReadArrayBindLocalRoot"
      leanRule := some .storageIndexReadArrayBindLocalRootBox
      reads := [slen] },
    { keyName := "storageIndexReadArrayStoreRoot"
      leanRule := some .storageIndexReadArrayStoreRootBox
      reads := [slen, sread .value (.fixed .stValue)] },
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
      -- `find<[Struct]>(storage, sp2)` on the pushed source: NOT
      -- sort-faithful for primitive element types — `openFindings`.
      reads := [slen, sread .value (.fixed .struct), slen] },
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
      -- `find<[Struct]>` too, but the target is `Variable[memory]`,
      -- which Solidity types as a reference — provably faithful.
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
      leanRule := some .memoryDeleteSimpleTarget
      reads := [mread .dflt (.generic .hasMemoryFieldSort)] },
    { keyName := "memoryIndexDeletePrimitive"
      leanRule := some .memoryDeleteSimpleTarget
      reads := [mlen, mlen] },
    { keyName := "memoryIndexDeleteReference"
      leanRule := some .memoryDeleteSimpleTarget
      reads := [mlen, mlen] },
    -- Payments. solkey `333cc7b353` split each rule by modality: the box
    -- rule books the debit unconditionally, the diamond rule additionally
    -- owes the EVM funding check as a "sufficient funds" goal. The ledger
    -- read is the same `selectSt<[int]>(net, at(a))` in all four.
    { keyName := "transferNoCallbackBox"
      leanRule := some .transferNoCallback
      reads := [⟨.net, .net, .fixed .int⟩] },
    { keyName := "transferNoCallbackDiamond"
      leanRule := some .transferNoCallback
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
through. -/

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

-- Taclet names must be unique (`_root`/`_decompose` variants are
-- distinct taclets).
#guard (tacletReadAnns.map (·.keyName)).Nodup

end TacletAnnotations
end Solidity
