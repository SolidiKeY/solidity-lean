import Solidity.Typing.Storage
import Solidity.SortCheck.Annotations

/-!
# Sort-faithfulness of the taclet annotations

The semantic side of the conformance loop: every read-sort annotation in
`TacletAnnotations.tacletReadAnns` is proved *faithful* — for every
well-typed statement the mapped Lean rule matches, the sort a taclet
read declares agrees with the storage value the interpreter actually
finds at the read path (`SortFaithful`). The claims per `ReadSort`:

- `fixed s` claims the value's runtime sort (`SVal.keySort`) lies below
  `s` in the lattice (`KeySort.le`): `fixed .stValue` claims nothing,
  since every storage value is an `StValue` (this is why the
  `12e72a1b4b` fix — sort-free `valAt`/`find<[StValue]>` on the copy
  rules — is trivially faithful); `fixed .int` claims an int value,
  `fixed .struct` a tree node, `fixed .identity` never holds in storage;
- `generic vc` claims the value inhabits the read expression's static
  type (the varcond resolves the schema sort to exactly that type).

`sortFaithful_all` discharges every row; `openFindings` is empty since
solkey `29c44e225b` replaced the last two `find<[Struct]>` reads on
possibly-primitive sources (`storageFieldWriteCopySource`,
`storagePushValueCopySource`) — the same family as the fixed bug, and
this table's two open findings until then — by sort-free
`find<[StValue]>`. `Counterexamples/PreFixSortAnnotations.lean` proves
the pre-fix annotations are *not* faithful (the caught bug) and keeps
the refutation of the two former findings' `find<[Struct]>` rows.

Scope: storage-domain `value`-site reads carry the semantic content;
`length`/`net`/`dflt` sites and memory-domain reads have no Lean-model
counterpart here and are token-checked by `solkeycheck` only (see the
module docstring of `Annotations.lean`).
-/

namespace Solidity
namespace SortFaithfulness

open Semantics
open TacletAnnotations

/-! ## What a declared read sort claims -/

/-- The value a `value`-site read denotes inside a matched statement:
the RHS of an assignment (or the `++`/`--` target when the RHS is an
inc/dec), the current value of a compound assignment, the pushed
element. -/
def valueExpr? : Stmt -> Option WrappedExpr
  | Stmt.assign _ (WrappedExpr.incDec _ target) => some target
  | Stmt.assign _ rhs => some rhs
  | Stmt.compoundAssign _ lhs _ => some lhs.expr
  | Stmt.expr (WrappedExpr.incDec _ target) => some target
  | Stmt.push _ (some v) => some v
  | Stmt.pushAssign _ v => some v
  | _ => none

/-- The expression a read site denotes. Non-`value` sites (`length`
cells, the `net` ledger, `delete` defaults) have no Lean-model
counterpart: faithfulness is vacuous there. -/
def ReadSite.expr? : ReadSite -> Stmt -> Option WrappedExpr
  | .value, stmt => valueExpr? stmt
  | _, _ => none

/-- What the declared sort claims about the value found at the read
path, given the read expression's static type. -/
def readSortOkB : ReadSort -> Ty -> SVal -> Bool
  | ReadSort.generic _, ty, v => v.hasTy ty
  | ReadSort.fixed s, _, v => (v.keySort).le s

/-- Sort-faithfulness of one annotated taclet: in every well-typed
state, for every well-typed statement the mapped Lean rule matches,
every declared storage read sort agrees with the value the interpreter
actually finds at the read path. -/
def SortFaithful (ann : TacletReadAnn) : Prop :=
  ∀ (L : Layout) (s : State) (stmt : Stmt) (rule : RuleName),
    ann.leanRule = some rule ->
    wellTypedStorageB L s.storage = true ->
    stmtTypingOk stmt = true ->
    (Rules.ruleEffect rule).cond stmt ->
    ∀ r ∈ ann.reads, r.domain = ReadDomain.storage ->
      ∀ e, ReadSite.expr? r.site stmt = some e ->
        wtStorageExpr L s.env e = true ->
        ∀ s' root segs v,
          resolveS s e = Except.ok (s', root, segs) ->
          State.findStorage s' root segs = Except.ok v ->
          readSortOkB r.sort e.ty v = true

/-! ## Statement-shape facts per rule

`fixed`-sorted value reads need a fact about the read expression's
static type that only the matched statement's shape (plus Solidity
typing, `stmtTypingOk`) provides: compound-assignment and `++`/`--`
targets are numeric; `memoryStorageCopy`'s source shares the
reference-typed memory target's type. -/

/-- Rules whose `value` read is a numeric-typed target: the
compound-assignment and inc/dec taclet families. -/
def ruleNumericTarget : RuleName -> Bool
  | .storageRootOpAssign _ => true
  | .storageFieldOpAssign _ => true
  | .storageIndexMappingOpAssign _ => true
  | .storageIndexArrayOpAssign _ => true
  | .storageRootIncrement _ => true
  | .storageFieldIncrement _ => true
  | .storageIndexIncrement _ => true
  | .storageRootIncrementAssignment _ => true
  | .storageFieldIncrementAssignment _ => true
  | .storageIndexIncrementAssignment _ => true
  | _ => false

/-- Rules whose `value` read is a reference-typed source:
`memoryStorageCopy` (the memory target types the storage source). -/
def ruleRefTarget : RuleName -> Bool
  | .memoryStorageCopy => true
  | _ => false

theorem numericTarget_sound {rule : RuleName}
    (hcls : ruleNumericTarget rule = true) :
    ∀ stmt, (Rules.ruleEffect rule).cond stmt ->
      stmtTypingOk stmt = true ->
      ∀ e, valueExpr? stmt = some e -> isNumericTy e.ty = true := by
  cases rule <;> try exact Bool.noConfusion hcls
  -- Compound assignments: the read target is the (numeric) LHS.
  case storageRootOpAssign op =>
    intro stmt hcond hty e hexpr
    cases stmt <;> try exact hcond.elim
    case compoundAssign op' lhs rhs =>
      simp only [valueExpr?] at hexpr
      cases hexpr
      simpa [stmtTypingOk] using hty
  case storageFieldOpAssign op =>
    intro stmt hcond hty e hexpr
    cases stmt <;> try exact hcond.elim
    case compoundAssign op' lhs rhs =>
      simp only [valueExpr?] at hexpr
      cases hexpr
      simpa [stmtTypingOk] using hty
  case storageIndexMappingOpAssign op =>
    intro stmt hcond hty e hexpr
    cases stmt <;> try exact hcond.elim
    case compoundAssign op' lhs rhs =>
      simp only [valueExpr?] at hexpr
      cases hexpr
      simpa [stmtTypingOk] using hty
  case storageIndexArrayOpAssign op =>
    intro stmt hcond hty e hexpr
    cases stmt <;> try exact hcond.elim
    case compoundAssign op' lhs rhs =>
      simp only [valueExpr?] at hexpr
      cases hexpr
      simpa [stmtTypingOk] using hty
  -- Statement-form `++`/`--`: the read target is the (numeric) operand.
  case storageRootIncrement op =>
    intro stmt hcond hty e hexpr
    cases stmt <;> try exact hcond.elim
    case expr e0 =>
      cases e0 <;> try exact hcond.elim
      case mkIncDec op' target =>
        simp only [valueExpr?] at hexpr
        cases hexpr
        simpa [stmtTypingOk] using hty
  case storageFieldIncrement op =>
    intro stmt hcond hty e hexpr
    cases stmt <;> try exact hcond.elim
    case expr e0 =>
      cases e0 <;> try exact hcond.elim
      case mkIncDec op' target =>
        simp only [valueExpr?] at hexpr
        cases hexpr
        simpa [stmtTypingOk] using hty
  case storageIndexIncrement op =>
    intro stmt hcond hty e hexpr
    cases stmt <;> try exact hcond.elim
    case expr e0 =>
      cases e0 <;> try exact hcond.elim
      case mkIncDec op' target =>
        simp only [valueExpr?] at hexpr
        cases hexpr
        simpa [stmtTypingOk] using hty
  -- Assignment-form `v = x++`: the read target is the inc/dec operand.
  case storageRootIncrementAssignment op =>
    intro stmt hcond hty e hexpr
    cases stmt <;> try exact hcond.elim
    case assign lhs rhs =>
      cases rhs <;> try exact hcond.elim
      case mkIncDec op' target =>
        simp only [valueExpr?] at hexpr
        cases hexpr
        simp only [stmtTypingOk, Bool.and_eq_true] at hty
        exact hty.2
  case storageFieldIncrementAssignment op =>
    intro stmt hcond hty e hexpr
    cases stmt <;> try exact hcond.elim
    case assign lhs rhs =>
      cases rhs <;> try exact hcond.elim
      case mkIncDec op' target =>
        simp only [valueExpr?] at hexpr
        cases hexpr
        simp only [stmtTypingOk, Bool.and_eq_true] at hty
        exact hty.2
  case storageIndexIncrementAssignment op =>
    intro stmt hcond hty e hexpr
    cases stmt <;> try exact hcond.elim
    case assign lhs rhs =>
      cases rhs <;> try exact hcond.elim
      case mkIncDec op' target =>
        simp only [valueExpr?] at hexpr
        cases hexpr
        simp only [stmtTypingOk, Bool.and_eq_true] at hty
        exact hty.2

/-- On an assignment whose RHS is storage-kind, the value read is the
RHS itself (an inc/dec RHS is stack-kind, so the first `valueExpr?` arm
cannot fire). -/
private theorem valueExpr?_assign_storage {lhs : PlaceExpr}
    {rhs e : WrappedExpr} (hsto : Typed.WrappedExpr.isStorage rhs = true)
    (hexpr : valueExpr? (Stmt.assign lhs rhs) = some e) : e = rhs := by
  cases rhs <;> first
    | exact Bool.noConfusion hsto
    | (simp only [valueExpr?] at hexpr; exact (Option.some.inj hexpr).symm)

theorem refTarget_sound {rule : RuleName}
    (hcls : ruleRefTarget rule = true) :
    ∀ stmt, (Rules.ruleEffect rule).cond stmt ->
      stmtTypingOk stmt = true ->
      ∀ e, valueExpr? stmt = some e -> e.ty.isReference = true := by
  cases rule <;> try exact Bool.noConfusion hcls
  case memoryStorageCopy =>
    intro stmt hcond hty e hexpr
    cases stmt <;> try exact hcond.elim
    case assign lhs rhs =>
      obtain ⟨hmemk, _, hsto, _⟩ := hcond
      cases valueExpr?_assign_storage hsto hexpr
      simp only [stmtTypingOk, Bool.and_eq_true] at hty
      obtain ⟨⟨⟨hteq, href⟩, _⟩, _⟩ := hty
      have hmemb : lhs.expr.isMemory = true := by
        simp [WrappedExpr.isMemory, Typed.WrappedExpr.isMemory]
        exact hmemk
      rw [<- show lhs.expr.ty = e.ty from by simpa [beq_iff_eq] using hteq]
      simpa [hmemb] using href

/-! ## The faithfulness dispatcher -/

/-- Decidable per-read check: is this read's claim in the proved
fragment for the given rule? -/
def valueReadOkB (rule : RuleName) (r : TacletRead) : Bool :=
  match r.sort with
  | .generic _ => true
  | .fixed .stValue => true
  | .fixed .int => ruleNumericTarget rule
  | .fixed .struct => ruleRefTarget rule
  | .fixed _ => false

/-- Decidable per-row check: every storage `value` read is in the
proved fragment. `sortFaithful_of_annOkB` turns this Bool into
`SortFaithful`, so the whole table is discharged by evaluation. -/
def annOkB (ann : TacletReadAnn) : Bool :=
  match ann.leanRule with
  | none => true
  | some rule =>
      ann.reads.all fun r =>
        !(r.domain == ReadDomain.storage && r.site == ReadSite.value) ||
          valueReadOkB rule r

theorem sortFaithful_of_annOkB (ann : TacletReadAnn)
    (hok : annOkB ann = true) : SortFaithful ann := by
  intro L s stmt rule hrule hst hty hcond r hmem hdom e hexpr hwt
    s' root segs v hres hfind
  simp only [annOkB, hrule] at hok
  have hr := List.all_eq_true.mp hok r hmem
  cases hsite : r.site
  case length => rw [hsite] at hexpr; simp [ReadSite.expr?] at hexpr
  case net => rw [hsite] at hexpr; simp [ReadSite.expr?] at hexpr
  case dflt => rw [hsite] at hexpr; simp [ReadSite.expr?] at hexpr
  case value =>
  rw [hsite] at hexpr
  simp only [ReadSite.expr?] at hexpr
  simp only [hdom, hsite, beq_self_eq_true, Bool.and_self,
    Bool.not_true, Bool.false_or] at hr
  have hhasTy : v.hasTy e.ty = true :=
    generic_read_hasTy hst hwt hres hfind
  cases hsort : r.sort
  case generic vc => simpa [readSortOkB] using hhasTy
  case fixed ks =>
    -- Every fixed sort outside the proved fragment has `hr : false = true`,
    -- which the `simp` closes; three arms remain.
    cases ks <;> simp only [valueReadOkB, hsort] at hr <;> try exact Bool.noConfusion hr
    case stValue =>
      show (v.keySort).le KeySort.stValue = true
      exact SVal.keySort_le_stValue v
    case int =>
      have hnum := numericTarget_sound hr stmt hcond hty e hexpr
      obtain ⟨n, hn⟩ := hasTy_numeric hnum hhasTy
      subst hn
      show (KeySort.int).le KeySort.int = true
      exact KeySort.le_refl _
    case struct =>
      have href := refTarget_sound hr stmt hcond hty e hexpr
      have hks := (SVal.isRefVal_iff_keySort_struct v).mp (hasTy_isRefVal href hhasTy)
      show (v.keySort).le KeySort.struct = true
      rw [hks]
      exact KeySort.le_refl _

/-! ## The aggregate theorem -/

/-- Annotation rows whose faithfulness FAILS in the Lean model. Empty at
solkey `8c5c69ca25`: the two entries this list carried —
`storageFieldWriteCopySource` and `storagePushValueCopySource`, whose
`find<[Struct]>` read of a `Path[storage,simple]` source failed on a
primitive-typed source, the bug family of `12e72a1b4b` — were fixed
upstream by `29c44e225b` (sort-free `find<[StValue]>`).
`Counterexamples/PreFixSortAnnotations.lean` keeps their refutations. A
row lands here when an upstream taclet declares a sort the interpreter
contradicts; it stays in the table so `solkeycheck` pins the text. -/
def openFindings : List String := []

def tacletReadAnnsProven : List TacletReadAnn :=
  tacletReadAnns.filter fun ann => !openFindings.contains ann.keyName

/-- Every annotation row outside `openFindings` is sort-faithful. -/
theorem sortFaithful_all : ∀ ann ∈ tacletReadAnnsProven, SortFaithful ann := by
  intro ann hmem
  refine sortFaithful_of_annOkB ann (List.all_eq_true.mp ?_ ann hmem)
  native_decide

-- No silent third bucket: every table row is either in the proved
-- fragment or explicitly listed as an open finding.
example :
    tacletReadAnns.all (fun ann =>
      annOkB ann || openFindings.contains ann.keyName) = true := by
  native_decide

-- The two former open findings are now in the proved fragment: their
-- storage value read is the claim-free `find<[StValue]>`.
example :
    (tacletReadAnns.filter (fun ann =>
        ann.keyName == "storageFieldWriteCopySource" ||
        ann.keyName == "storagePushValueCopySource")).map
      (fun ann => (ann.reads.filter (·.site == ReadSite.value), annOkB ann)) =
      [([⟨.storage, .value, .fixed .stValue⟩], true),
        ([⟨.storage, .value, .fixed .stValue⟩], true)] := by
  native_decide

-- The pre-fix annotations of the five changed taclets all fall outside
-- the proved fragment — their unprovability is made concrete in
-- `Counterexamples/PreFixSortAnnotations.lean`.
example : preFixTacletReadAnns.all (fun ann => !annOkB ann) = true := by
  native_decide

/-! ## Row accounting — what `sortFaithful_all` actually claims

`SortFaithful` bites only on storage-domain `value`-site reads
(`ReadSite.expr?` is `none` elsewhere), and a `fixed .stValue` read claims
nothing (`StValue` is every storage value's supersort).  The counts below
are decided against the table, so the headline's real content is
visible: of the 110 rows, 45 are vacuous for `SortFaithful` (memory,
`net`, `length`/`dflt`-only rows — token-checked by `solkeycheck` only;
26 of them the memory arithmetic families), 8 carry only claim-free
`find<[StValue]>` reads, and 57 carry a content-bearing sort claim
(`fixed .int`/`.struct`/… or a varcond-generic sort; 52 of them the
storage arithmetic families' `find<[int]>` target reads). -/

/-- A storage-domain `value`-site read. -/
def storageValueRead (r : TacletRead) : Bool :=
  decide (r.domain = ReadDomain.storage) && decide (r.site = ReadSite.value)

/-- A row with at least one storage `value` read whose declared sort says
something (is not `fixed .stValue`). -/
def contentBearing (ann : TacletReadAnn) : Bool :=
  ann.reads.any fun r =>
    storageValueRead r && !decide (r.sort = ReadSort.fixed KeySort.stValue)

/-- A row whose storage `value` reads are all `fixed .stValue`. -/
def claimFree (ann : TacletReadAnn) : Bool :=
  ann.reads.any storageValueRead && !contentBearing ann

/-- A row with no storage `value` read at all: `SortFaithful` is vacuous. -/
def vacuousRow (ann : TacletReadAnn) : Bool :=
  !ann.reads.any storageValueRead

theorem rows_accounting :
    tacletReadAnns.length = 110 ∧
    (tacletReadAnns.filter contentBearing).length = 57 ∧
    (tacletReadAnns.filter claimFree).length = 8 ∧
    (tacletReadAnns.filter vacuousRow).length = 45 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end SortFaithfulness
end Solidity
