import Solidity.KeySort

/-!
# The pre-`e67a0d7c48` delete fallthroughs were inconsistent

solkey `0f9b99ad55` ("removed different fields") moved field-kind
discrimination out of the schema-variable sorts (`Field[primitive]` /
`Field[reference]`) and into generic-sort *upper bounds*. An upper
bound admits every sort below it — it does not partition. At that
commit the delete-family fallthroughs of `structRules.key` were bounded
by `alphaSt \extends StValue`, and `Struct \extends StValue`, so each
fallthrough instance at `alphaSt := Struct` coexisted with the
dedicated `Struct` rule for the *same term* — rewriting it to a
different result:

- `delValueStruct`:  `delValue<[Struct]>(st) ⇝ delNode(st)`
  `delValueDefault`: `delValue<[alphaSt]>(x) ⇝ defaultValue<[alphaSt]>`
  (at `alphaSt := Struct`, with `defaultValueStruct`: `⇝ mtSt`);
- `selectStDelNodeMap`:     `selectSt<[Struct]>(delNode(st), mf) ⇝ selectSt<[Struct]>(st, mf)`
  `selectStDelNodeDefault`: `selectSt<[alphaSt]>(delNode(st), a) ⇝ defaultValue<[alphaSt]>`
  (at `alphaSt := Struct`, `a := mf` — a `\term Field` schema variable
  matches a `MapField`-sorted term, `MapField \extends Field`).

Every taclet is a standalone lemma: an overlapping pair with different
right-hand sides asserts both results equal, so the taclet *set* had no
model. The two theorems below transcribe each pair (plus the
equal-field branch of `selectOnStore` and `castDel` on statically
well-sorted arguments — nothing else) as hypotheses over abstract
carriers and derive `False`, via `5 = 7` on a stored int. The
derivation is fully first-order: no storage typing, no wellformedness —
the inconsistency was in the rules themselves. Nor was it latent:
`delete s.member;` introduces `delAt(storage, …)`, and any later
`Struct`-sorted read reaches `selectOnDelAtCons`, whose `isEmpty`
branch emits `delValue<[Struct]>(selectSt<[Struct]>(st, a1))` — the
overlapped term. Semantically the `Default` rules at `Struct` were the
wrong side: `delete` must *preserve* mapping members (`delNode` +
`selectStDelNodeMap`), while `defaultValue<[Struct]> = mtSt` wipes
them.

solkey `e67a0d7c48` fixes both overlaps exactly the way the memory side
always did (`memoryRules.key`'s `\generic prim \extends Prim`): the
fallthroughs are re-bounded by `alphaPrim \extends Prim` — which
excludes `Struct` (`struct ≰ prim` below) — and the array-element case
the narrowing uncovered gets its own `selectStDelNodeIndexStruct`.

What the fix leaves open (an incompleteness, not an inconsistency):
`delValue` and `selectSt`-over-`delNode` now have rules at `Struct` and
below `Prim` only, but `selectOnDelAtCons` instantiates at whatever
sort the outer read used — and the copy taclets read `find<[StValue]>`.
On `delete s.p; x = s.p;` (struct-typed `p`, root target `x`,
`storageRootWriteCopySource`) the unfolding reaches
`delValue<[StValue]>(selectSt<[StValue]>(node, p))`, and `StValue` is
neither `Struct` nor below `Prim` (checked below): the term is stuck,
and no later cast can revive it (`findStValueCast` matches
`find<[StValue]>` under a cast, not a bare `delValue<[StValue]>` inside
a `save`). Delete-then-copy therefore fails to symbolically execute.

Recorded in `docs/solkey-feedback.md`; the matcher-admissibility claims
(`alphaSt := Struct`; `Field` schema variable matching a `MapField`
term) are transcriptions of standard KeY generic-sort/subsort matching
and are checked against the shared `KeySort` lattice below.
-/

namespace Solidity
namespace Counterexamples
namespace DeleteFamilyGenericOverlap

/-! ## The lattice facts the story rests on -/

-- The pre-fix bound admitted `Struct`: `alphaSt \extends StValue`…
example : KeySort.struct.le KeySort.stValue = true := by decide
-- …the fix's bound `alphaPrim \extends Prim` does not, …
example : KeySort.struct.le KeySort.prim = false := by decide
-- …and a `\term Field a` schema variable matches a `MapField` term.
example : KeySort.mapField.le KeySort.field = true := by decide
-- The remaining gap: an `StValue`-instantiated delete read fits
-- neither the `Struct` rules nor the `Prim`-bounded fallthroughs.
example : KeySort.stValue.le KeySort.prim = false := by decide
example : KeySort.stValue = KeySort.struct <-> False := by decide

/-! ## Inconsistency of the pre-fix overlapping pairs

Carriers are abstract (`St` for `Struct`-sorted values, `SV` for
`StValue`, `Fld` for fields); each hypothesis is one taclet instance at
`0f9b99ad55`, named after it. `mf` is a `MapField` constant (any
program with a mapping-typed struct member has one), `at0` stands for
`at(0)`. -/

/-- `delValueStruct` vs. pre-fix `delValueDefault` at
`alphaSt := Struct`: together they force `delNode(st) = mtSt`, and with
`selectStDelNodeMap` a stored value becomes independent of what was
stored — `5 = 7`. -/
theorem delValue_overlap_inconsistent
    {St SV Fld : Type}
    (injS : St -> SV) (injI : Int -> SV)
    (mt : St)
    (delValueS : St -> St)             -- delValue<[Struct]>
    (delNode : St -> St)
    (dvStruct : St)                    -- defaultValue<[Struct]>
    (selS : St -> Fld -> St)           -- selectSt<[Struct]>
    (selI : St -> Fld -> Int)          -- selectSt<[int]>
    (storeSt : St -> Fld -> SV -> St)
    (castS : SV -> St) (castI : SV -> Int)
    (mf at0 : Fld)
    -- delValueStruct
    (hDelStruct : ∀ st, delValueS st = delNode st)
    -- pre-fix delValueDefault at alphaSt := Struct
    (hDelDefault : ∀ st, delValueS st = dvStruct)
    -- defaultValueStruct
    (hDv : dvStruct = mt)
    -- selectStDelNodeMap at a MapField constant
    (hMap : ∀ st, selS (delNode st) mf = selS st mf)
    -- selectOnStore, equal-field branch, at Struct and at int
    (hStoreS : ∀ st f v, selS (storeSt st f v) f = castS v)
    (hStoreI : ∀ st f v, selI (storeSt st f v) f = castI v)
    -- castDel on statically well-sorted arguments
    (hCastS : ∀ s, castS (injS s) = s)
    (hCastI : ∀ n, castI (injI n) = n) : False := by
  have hdn : ∀ st, delNode st = mt := fun st =>
    (hDelStruct st).symm.trans ((hDelDefault st).trans hDv)
  have hconst : ∀ st, selS st mf = selS mt mf := by
    intro st
    have h := hMap st
    rw [hdn st] at h
    exact h.symm
  have habs : ∀ s : St, s = selS mt mf := by
    intro s
    have h := hconst (storeSt mt mf (injS s))
    rw [hStoreS, hCastS] at h
    exact h
  have hcollapse : storeSt mt at0 (injI 5) = storeSt mt at0 (injI 7) :=
    (habs _).trans (habs _).symm
  have : (5 : Int) = 7 := by
    have h := congrArg (fun st => selI st at0) hcollapse
    simpa [hStoreI, hCastI] using h
  omega

/-- `selectStDelNodeMap` vs. pre-fix `selectStDelNodeDefault` at
`alphaSt := Struct`, `a := mf`: the mapping member of a deleted node is
both preserved and wiped, so again `5 = 7`. Independent of the
`delValue` pair — fixing one overlap would not have closed the
other. -/
theorem selectStDelNode_overlap_inconsistent
    {St SV Fld : Type}
    (injS : St -> SV) (injI : Int -> SV)
    (mt : St)
    (delNode : St -> St)
    (dvStruct : St)
    (selS : St -> Fld -> St)
    (selI : St -> Fld -> Int)
    (storeSt : St -> Fld -> SV -> St)
    (castS : SV -> St) (castI : SV -> Int)
    (mf at0 : Fld)
    -- pre-fix selectStDelNodeDefault at alphaSt := Struct, a := mf
    (hDefault : ∀ st, selS (delNode st) mf = dvStruct)
    -- defaultValueStruct
    (hDv : dvStruct = mt)
    -- selectStDelNodeMap
    (hMap : ∀ st, selS (delNode st) mf = selS st mf)
    -- selectOnStore, equal-field branch, at Struct and at int
    (hStoreS : ∀ st f v, selS (storeSt st f v) f = castS v)
    (hStoreI : ∀ st f v, selI (storeSt st f v) f = castI v)
    -- castDel on statically well-sorted arguments
    (hCastS : ∀ s, castS (injS s) = s)
    (hCastI : ∀ n, castI (injI n) = n) : False := by
  have hconst : ∀ st, selS st mf = mt := fun st =>
    (hMap st).symm.trans ((hDefault st).trans hDv)
  have habs : ∀ s : St, s = mt := by
    intro s
    have h := hconst (storeSt mt mf (injS s))
    rw [hStoreS, hCastS] at h
    exact h
  have hcollapse : storeSt mt at0 (injI 5) = storeSt mt at0 (injI 7) :=
    (habs _).trans (habs _).symm
  have : (5 : Int) = 7 := by
    have h := congrArg (fun st => selI st at0) hcollapse
    simpa [hStoreI, hCastI] using h
  omega

end DeleteFamilyGenericOverlap
end Counterexamples
end Solidity
