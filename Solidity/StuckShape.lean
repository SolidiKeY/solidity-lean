import Solidity.SemanticsProperties

/-!
# `StuckShape` — the interpreter's "no case is left", as a theorem

`Coverage.lean` does this for the *rules*: `ResidueShape` lists, one
documented constructor per family, exactly the statements no rule of the calculus
covers, and `coverage_residue` proves the list is complete. This module
is the interpreter's counterpart.

There is one honest difference, and it decides the design. Residue is a
property of *syntax*, so `Coverage.lean` has to hand-write a Boolean
mirror (`residueShapeB`) to decide it. Stuckness depends on the **state**
and already has a decision procedure — the interpreter itself. So there
is deliberately **no** `stuckShapeB` here: nothing would be gained by
writing a second interpreter. What the development buys is the
*classification*. A `native_decide` fact like
`Counterexamples/ErrorOrder.lean`'s `execStmt store prog = .error .stuck`
says only "something went wrong"; a `StmtStuck` derivation names which of
the listed families it belongs to, and `StuckCause` is the list.

`Semantics.lean` no longer hides a stuck case behind a wildcard — every
`| _ => .error .stuck` there has been expanded into explicit
per-constructor arms — so this table can be read off the interpreter arm
by arm, and a new constructor is a compile error there before it can be a
missing row here.

## Layering

1. **Leaves** (this file): `SVal.find`/`SVal.save`, the cross-domain
   copies, `readLoc`/`writeLoc`. State-free or one lookup deep, and they
   carry the halt taxonomy the rest of the development leans on.
2. Expression layer (`resolveS`/`resolveMBase`/`readM`/`resolveLoc`/
   `evalValue`) — a five-member mutual family.
3. Statement layer (`execStmt`/`execBlock`) and `exec_trichotomy`.
-/

namespace Solidity
namespace StuckShape

open Semantics

/-! ## The stuck causes

The complete list of reasons the interpreter answers `.error .stuck`,
one constructor per family, no catch-all. The relations below are
*indexed* by a cause, so a derivation names the family it belongs to the
way a `ResidueShape` constructor names an uncovered cell. -/

inductive StuckCause where
  /-- A name the environment does not bind. -/
  | unboundName (name : Name)
  /-- A bound name whose binding is not the stack value the reader
  wanted (`readLoc`, `evalValue`'s stack arm). -/
  | bindingNotValue (name : Name) (b : Binding)
  /-- …not the storage path `resolveS` wanted. -/
  | bindingNotPath (name : Name) (b : Binding)
  /-- …not the memory reference `resolveMBase`/`readM` wanted. -/
  | bindingNotRef (name : Name) (b : Binding)
  /-- A storage root absent from `s.storage`. -/
  | missingStorageRoot (root : Name)
  /-- A path segment applied to a node of the wrong shape: a primitive
  under any selector, a struct under `at`, an array under a field other
  than `length`, a mapping under a field. -/
  | segmentShapeMismatch (v : SVal) (seg : Seg)
  /-- A struct field the node does not carry. -/
  | missingStructField (name : Name)
  /-- A heap identity that is absent. -/
  | heapObjectMissing (id : Nat)
  /-- …present but not a struct, where a field was selected. -/
  | heapObjectNotStruct (id : Nat)
  /-- …present but not an array, where an index was selected. -/
  | heapObjectNotArray (id : Nat)
  /-- A memory member that is not a reference (`resolveMBase`). -/
  | memberNotReference (fld : Name)
  /-- A value that is not an `Int` (`Value.asInt`). -/
  | valueNotInt (v : Value)
  /-- …not a `Bool` (`Value.asBool`, the `if`/`assert`/`require`/ternary
  conditions). -/
  | valueNotBool (v : Value)
  /-- A storage node that is not primitive (`SVal.asValue`). -/
  | svalNotPrimitive (v : SVal)
  /-- A memory slot that is not primitive (`MVal.asValue`). -/
  | mvalNotPrimitive (mv : MVal)
  /-- A mapping reaching memory (`copyStToM`): mappings have no memory
  representation. -/
  | mappingIntoMemory
  /-- `copyMem` ran out of unvisited identities — a heap cycle. -/
  | copyCycle (id : Nat)
  /-- `**` with a negative exponent. -/
  | negativeExponent (base exponent : Int)
  /-- An alias root used as an l-value target (`Loc.storageLocal` /
  `Loc.memoryRoot` in `readLoc`/`writeLoc`): those bind references, not
  primitives. -/
  | aliasRootAsTarget (name : Name)
  /-- A stack-kind field or index place — kind confusion `wtExpr` does
  not pin, the run-time face of `ResidueShape.assignStackPlace`. -/
  | stackPlace
  /-- A memory root read as a value (`evalValue`). -/
  | memoryRootAsValue (name : Name)
  /-- A non-place expression where a place was required. -/
  | nonPlaceExpression
  /-- A storage-to-storage copy of a mapping-carrying type — the solc
  ≥ 0.7 compile error, mirrored by `tyHasMapping`. -/
  | mappingStorageCopy (ty : Ty)
  /-- A non-primitive right-hand side of stack kind; notably a ternary,
  whose `WrappedExpr.kind` is always `.stack`. -/
  | referenceRhsOfStackKind
  /-- A memory declaration of non-reference type. -/
  | memoryDeclNonReference (ty : Ty)
  /-- `push` on a node that is not an array. -/
  | pushOnNonArray (v : SVal)
  /-- `push` on a target whose type is not an array reference. -/
  | pushTargetTypeNotArray (ty : Ty)
  /-- `pop` on a node that is not an array. -/
  | popOnNonArray (v : SVal)
  /-- `transfer` of a negative amount — an untypable program. -/
  | negativeTransfer (amount : Int)
  /-- A call reaching the interpreter: meaning comes from inlining
  (`SoliditySyntax.inlineBlock`), as in KeY, where `functionBodyExpand`
  is the only rule for a `FunctionBodyStatement`. -/
  | callNotInlined (fn : Name)
  /-- A call that is not `net`, or `net` at the wrong arity. -/
  | unknownCall (fn : Name)
  deriving Repr

/-! ## The halt taxonomy

Which of the two halts each part of the interpreter can produce. These
are the facts the rest of the development leans on to avoid carrying a
`.revert` case it can never reach — and the first of them is what makes
`allocDefault`'s masking arm safe to unmask. -/

/-- The storage→memory copy never reverts: its single failure arm is the
mapping one, and `SVal.find`-style index checks never run inside it.

This is the fact `allocDefault` needs. Its `| .error _ => .error .stuck`
arm maps a propagated halt to `.stuck`, which is exact only because this
theorem holds; without it that arm would be masking a revert. -/
theorem copyStToM_never_reverts (s : State) (v : SVal) :
    copyStToM s v ≠ .error Halt.revert := by
  induction s, v using copyStToM.induct
    (motive_2 := fun s l => copyStElems s l ≠ .error Halt.revert)
    (motive_3 := fun s l => copyStFields s l ≠ .error Halt.revert) with
  | case1 s v => simp [copyStToM]
  | case2 s b => simp [copyStToM]
  | case3 s fields ih =>
      simp only [copyStToM, bind, Except.bind]
      cases h : copyStFields s fields with
      | error e => rw [h] at ih; simpa using ih
      | ok x => simp
  | case4 s elems shadow ih =>
      simp only [copyStToM, bind, Except.bind]
      cases h : copyStElems s elems with
      | error e => rw [h] at ih; simpa using ih
      | ok x => simp
  | case5 s entries dflt => simp [copyStToM]
  | case6 s => simp [copyStFields]
  | case7 s name v rest ihv ihrest =>
      simp only [copyStFields, bind, Except.bind]
      cases h : copyStToM s v with
      | error e => rw [h] at ihv; simpa using ihv
      | ok x =>
          simp only []
          have ih2 := ihrest x.1
          cases h2 : copyStFields x.1 rest with
          | error e => rw [h2] at ih2; simpa using ih2
          | ok y => simp
  | case8 s => simp [copyStElems]
  | case9 s v rest ihv ihrest =>
      simp only [copyStElems, bind, Except.bind]
      cases h : copyStToM s v with
      | error e => rw [h] at ihv; simpa using ihv
      | ok x =>
          simp only []
          have ih2 := ihrest x.1
          cases h2 : copyStElems x.1 rest with
          | error e => rw [h2] at ih2; simpa using ih2
          | ok y => simp

/-- A missing heap identity is stuck, never a revert. -/
theorem getObj_never_reverts {s : State} {id : Nat} :
    s.getObj id ≠ .error Halt.revert := by
  simp only [State.getObj]
  cases lookupBy id s.heap <;> simp

/-- The memory→storage copy never reverts either: it fails only on a
missing identity or on a cycle (`rem` exhausted). -/
theorem copyMToSt_never_reverts (s : State) (rem : List Nat) (mv : MVal) :
    copyMToSt s rem mv ≠ .error Halt.revert := by
  induction rem, mv using copyMToSt.induct (s := s)
    (motive2 := fun rem l => copyMElems s rem l ≠ .error Halt.revert)
    (motive3 := fun rem l => copyMFields s rem l ≠ .error Halt.revert) with
  | case1 rem v => simp [copyMToSt]
  | case2 rem b => simp [copyMToSt]
  | case3 rem id hmem fields hobj ih =>
      simp only [copyMToSt, hmem, dif_pos, hobj, bind, Except.bind]
      cases h : copyMFields s (rem.erase id) fields with
      | error e => rw [h] at ih; simpa using ih
      | ok x => simp
  | case4 rem id hmem elems hobj ih =>
      simp only [copyMToSt, hmem, dif_pos, hobj, bind, Except.bind]
      cases h : copyMElems s (rem.erase id) elems with
      | error e => rw [h] at ih; simpa using ih
      | ok x => simp
  | case5 rem id hmem e hobj =>
      simp only [copyMToSt, hmem, dif_pos, hobj]
      intro hc
      exact getObj_never_reverts (hobj.trans (by simpa using hc))
  | case6 rem id hmem => simp [copyMToSt, hmem]
  | case7 rem => simp [copyMElems]
  | case8 rem v rest ihv ihrest =>
      simp only [copyMElems, bind, Except.bind]
      cases h : copyMToSt s rem v with
      | error e => rw [h] at ihv; simpa using ihv
      | ok x =>
          simp only []
          cases h2 : copyMElems s rem rest with
          | error e => rw [h2] at ihrest; simpa using ihrest
          | ok y => simp
  | case9 rem => simp [copyMFields]
  | case10 rem name v rest ihv ihrest =>
      simp only [copyMFields, bind, Except.bind]
      cases h : copyMToSt s rem v with
      | error e => rw [h] at ihv; simpa using ihv
      | ok x =>
          simp only []
          cases h2 : copyMFields s rem rest with
          | error e => rw [h2] at ihrest; simpa using ihrest
          | ok y => simp

/-- `copyMem` never reverts. -/
theorem copyMem_never_reverts {s : State} {mv : MVal} :
    copyMem s mv ≠ .error Halt.revert :=
  copyMToSt_never_reverts s _ mv

/-! ## `SVal.find`: the first stuck characterization

`Semantics.SVal.find` has twelve arms since the wildcard expansion, and
`SVal.find.induct` therefore *is* the case table — one hypothesis per
arm, including the `name = "length" → False` side condition that keeps
the array-field arm apart from the `length` one. `FindStuck` names the
four shape mismatches and the missing field, and propagates through the
five recursive arms. -/

inductive FindStuck : SVal -> List Seg -> StuckCause -> Prop where
  /-- A struct that does not carry the selected field. -/
  | structMissing {fields name rest}
      (h : lookupBy name fields = none) :
      FindStuck (SVal.struct fields) (Seg.field name :: rest)
        (.missingStructField name)
  /-- …and the recursive arm through the field it does carry. -/
  | structStep {fields name rest v c}
      (h : lookupBy name fields = some v) (hrec : FindStuck v rest c) :
      FindStuck (SVal.struct fields) (Seg.field name :: rest) c
  /-- An in-range array index. Out of range is a *revert*, not stuck, so
  it has no constructor here. -/
  | arrayStep {elems i rest c} (h : 0 ≤ i ∧ i.toNat < elems.length)
      (hrec : FindStuck (elems.get ⟨i.toNat, h.2⟩) rest c) :
      FindStuck (SVal.array elems sh) (Seg.at i :: rest) c
  /-- `a.length` continues into the length as a primitive. -/
  | arrayLengthStep {elems rest c}
      (hrec : FindStuck (SVal.int elems.length) rest c) :
      FindStuck (SVal.array elems sh) (Seg.field "length" :: rest) c
  /-- A mapping key that is present. -/
  | mapStep {entries dflt i rest v c}
      (h : lookupBy i entries = some v) (hrec : FindStuck v rest c) :
      FindStuck (SVal.map entries dflt) (Seg.at i :: rest) c
  /-- …and an absent one, which reads through to the default. -/
  | mapDefaultStep {entries dflt i rest c}
      (h : lookupBy i entries = none) (hrec : FindStuck dflt rest c) :
      FindStuck (SVal.map entries dflt) (Seg.at i :: rest) c
  /-- A primitive under any selector. -/
  | primSelector {p seg rest} :
      FindStuck (SVal.prim p) (seg :: rest)
        (.segmentShapeMismatch (SVal.prim p) seg)
  /-- A struct under `at`. -/
  | structAt {fields i rest} :
      FindStuck (SVal.struct fields) (Seg.at i :: rest)
        (.segmentShapeMismatch (SVal.struct fields) (Seg.at i))
  /-- An array under a field other than `length`. -/
  | arrayField {elems name rest} (h : name ≠ "length") :
      FindStuck (SVal.array elems sh) (Seg.field name :: rest)
        (.segmentShapeMismatch (SVal.array elems sh) (Seg.field name))
  /-- A mapping under a field. -/
  | mapField {entries dflt name rest} :
      FindStuck (SVal.map entries dflt) (Seg.field name :: rest)
        (.segmentShapeMismatch (SVal.map entries dflt) (Seg.field name))

/-- Soundness: every `FindStuck` derivation really is a stuck `find`. -/
theorem FindStuck.sound {v : SVal} {segs : List Seg} {c : StuckCause}
    (h : FindStuck v segs c) : v.find segs = .error Halt.stuck := by
  induction h with
  | structMissing h => simp [SVal.find, h]
  | structStep h _ ih => simp [SVal.find, h, ih]
  | arrayStep h _ ih => rw [SVal.find, dif_pos h]; exact ih
  | arrayLengthStep _ ih => simp [SVal.find, ih]
  | mapStep h _ ih => simp [SVal.find, h, ih]
  | mapDefaultStep h _ ih => simp [SVal.find, h, ih]
  | primSelector => simp [SVal.find]
  | structAt => simp [SVal.find]
  | arrayField _ => simp [SVal.find]
  | mapField => simp [SVal.find]

/-- Completeness: a stuck `find` has a named cause. Read off
`SVal.find.induct`, one case per interpreter arm — the empty-path and
out-of-range arms discharge because they do not answer `.stuck`. -/
theorem find_stuck_of {v : SVal} {segs : List Seg}
    (h : v.find segs = .error Halt.stuck) : ∃ c, FindStuck v segs c := by
  induction v, segs using SVal.find.induct with
  | case1 v => simp [SVal.find] at h
  | case2 fields name rest v hlook ih =>
      rw [SVal.find, hlook] at h
      exact (ih h).imp fun _ hc => .structStep hlook hc
  | case3 fields name rest hlook => exact ⟨_, .structMissing hlook⟩
  | case4 elems shadow i rest hr ih =>
      rw [SVal.find, dif_pos hr] at h
      exact (ih h).imp fun _ hc => .arrayStep hr hc
  | case5 elems shadow i rest hr => rw [SVal.find, dif_neg hr] at h; simp at h
  | case6 elems shadow rest ih =>
      rw [SVal.find] at h
      exact (ih h).imp fun _ hc => .arrayLengthStep hc
  | case7 entries dflt i rest v hlook ih =>
      rw [SVal.find, hlook] at h
      exact (ih h).imp fun _ hc => .mapStep hlook hc
  | case8 entries dflt i rest hlook ih =>
      rw [SVal.find, hlook] at h
      exact (ih h).imp fun _ hc => .mapDefaultStep hlook hc
  | case9 p head tail => exact ⟨_, .primSelector⟩
  | case10 fields i tail => exact ⟨_, .structAt⟩
  | case11 elems shadow name tail hname => exact ⟨_, .arrayField hname⟩
  | case12 entries dflt name tail => exact ⟨_, .mapField⟩

/-- **The leaf characterization.** `find` is stuck exactly on the listed
families. -/
theorem find_stuck_iff {v : SVal} {segs : List Seg} :
    v.find segs = .error Halt.stuck ↔ ∃ c, FindStuck v segs c :=
  ⟨find_stuck_of, fun ⟨_, hc⟩ => hc.sound⟩

end StuckShape
end Solidity
