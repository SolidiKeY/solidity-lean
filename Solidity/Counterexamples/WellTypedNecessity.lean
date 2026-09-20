import Solidity.SortCheck.Faithfulness

/-!
# Storage well-typedness is exactly what the sort claims stand on

Answers "does `find(st, p)` on an int-declared field really need a
storage well-typedness invariant to return an int?" — split by what the
question is about:

- **In the KeY calculus: no.** `find<[int]>(storage, p)` is int-sorted
  by construction, and on a mismatching store every read degrades to an
  underspecified cast: `selectOnStore` yields `cast<[alpha]>(v)`,
  `castDel` only deletes the cast when the argument's *static* sort
  already fits, and `cast.key` gives the mismatch case no axioms at
  all. An underspecified value cannot prove anything false, so the
  calculus is sort-sound with **no** wellformedness predicate — it is
  merely incomplete about paths the proof never wrote (which is what a
  symbolic initial storage should be anyway).

- **As a statement about the values the interpreter actually finds:
  yes, it is indispensable.** `SortFaithfulUntyped` below is
  `SortFaithful` with the `wellTypedStorageB` hypothesis dropped, and
  `readSelect_not_faithful_untyped` refutes it for a row that
  `sortFaithful_all` *proves* with the hypothesis — the same
  `storageRootReadSelect` row, verbatim from the live table. The
  witness is the minimal ill-typed store: layout says `total : uint`,
  the store holds `SVal.bool true` there, and the varcond-resolved read
  finds a bool where its schema sort promises `Prim`-below-`uint`. So
  `wellTypedStorageB` is precisely the boundary: with it every
  non-open-finding row is proved, without it the very same row is
  refutable.

The upstream reading: solkey needs no wellformedness axiom for its
sorts to be *sound* — but any claim that a sorted read denotes the
value really stored (and any completeness argument that needs, e.g.,
`find<[int]>(storage, consr(sp, size)) >= 0` for `pop`'s non-revert
branch or array bounds on a symbolic initial storage) needs a
`wellFormed(storage)` assumption in the proof obligation plus its
preservation by every `save` the rules emit — the calculus-side twin of
`wellTypedStorageB`. That preservation theorem is now proved:
`TypeSoundness.execStmt_sound`/`execBlock_sound` (via
`StoragePreservation.save_hasTy` and the `StateTyping` invariants),
with the one-hypothesis-dropped refutations in
`Counterexamples/PreservationNecessity.lean`.
-/

namespace Solidity
namespace Counterexamples
namespace WellTypedNecessity

open Semantics
open TacletAnnotations
open SortFaithfulness

/-- `SortFaithful` with the `wellTypedStorageB` hypothesis dropped:
the state's storage may disagree with the layout. -/
def SortFaithfulUntyped (ann : TacletReadAnn) : Prop :=
  ∀ (L : Layout) (s : State) (stmt : Stmt) (rule : RuleName),
    ann.leanRule = some rule ->
    stmtTypingOk stmt = true ->
    (Rules.ruleEffect rule).cond stmt ->
    ∀ r ∈ ann.reads, r.domain = ReadDomain.storage ->
      ∀ e, ReadSite.expr? r.site stmt = some e ->
        wtStorageExpr L s.env e = true ->
        ∀ s' root segs v,
          resolveS s e = Except.ok (s', root, segs) ->
          State.findStorage s' root segs = Except.ok v ->
          readSortOkB r.sort e.ty v = true

/-- Dropping a hypothesis only strengthens the claim. -/
theorem sortFaithful_of_untyped {ann : TacletReadAnn}
    (h : SortFaithfulUntyped ann) : SortFaithful ann :=
  fun L s stmt rule hrule _hst hty hcond r hmem hdom e hexpr hwt =>
    h L s stmt rule hrule hty hcond r hmem hdom e hexpr hwt

/-! ## The witness: layout `total : uint`, store `total ↦ bool` -/

def untypedLayout : Layout := ⟨[("total", Ty.uint)]⟩

/-- The minimal ill-typed store: the declared-`uint` root holds a
bool. Not reachable from a well-typed initial store by a well-typed
program — which is exactly the invariant (`wellTypedStorageB`
preservation) this module shows cannot be skipped. -/
def illState : State :=
  { storage := [("total", SVal.bool true)] }

def totalExpr : WrappedExpr :=
  WrappedExpr.var Kind.storage Ty.uint
    (Field.primitive "total" Ty.uint (some StorageOrigin.global))

def resultPlace : PlaceExpr :=
  PlaceExpr.var Kind.stack Ty.uint (Field.primitive "result" Ty.uint)

theorem resolveS_total_ill :
    resolveS illState totalExpr =
      Except.ok (illState, "total", ([] : List Seg)) := by
  show resolveS illState
    (WrappedExpr.var Kind.storage Ty.uint
      (Field.primitive "total" Ty.uint (some StorageOrigin.global))) = _
  rw [resolveS]
  rfl

/-- The live table's `storageRootReadSelect` row (checked below). -/
def readSelectRow : TacletReadAnn :=
  { keyName := "storageRootReadSelect"
    leanRule := some .storageRootReadSelect
    reads := [⟨.storage, .value, .generic .hasSort⟩] }

-- The row refuted is the row `solkeycheck` pins, not a strawman…
example : readSelectRow ∈ tacletReadAnns := by native_decide

-- …and with the well-typedness hypothesis that very row is PROVED.
example : SortFaithful readSelectRow :=
  sortFaithful_all readSelectRow (by native_decide)

/-- Without it, the same row is refutable: on `result = total` over the
ill-typed store, the interpreter finds `SVal.bool true` where the
`\hasSort`-resolved read promises the place's `uint` type. -/
theorem readSelect_not_faithful_untyped :
    ¬ SortFaithfulUntyped readSelectRow := by
  intro h
  have hclaim := h untypedLayout illState
    (Stmt.assign resultPlace totalExpr)
    .storageRootReadSelect rfl
    (by native_decide)
    ⟨rfl, rfl, rfl⟩
    ⟨.storage, .value, .generic .hasSort⟩ (List.Mem.head _) rfl
    totalExpr rfl (by native_decide)
    illState "total" [] (SVal.bool true) resolveS_total_ill rfl
  exact Bool.noConfusion hclaim

end WellTypedNecessity
end Counterexamples
end Solidity
