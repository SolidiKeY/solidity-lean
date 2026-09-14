import Solidity.TypeSoundness
import Solidity.DecEq

/-!
# "You can only prove these cases with wellformed"

Each refutation weakens a type-soundness statement by exactly one
invariant conjunct or side condition and exhibits a concrete witness
where the conclusion fails; next to it sits a positive twin discharged
*by* the statement, so the boundary is sharp.  R1, R2, R3, R5, R6, R7 and
R9 refute the headline `execStmt_sound` itself; R4 and R8 refute the
*fixed-typing lemmas* `saveStorage_wellTyped` and `setObjField_wt`, and
for R8 the headline is in fact provable without the conjunct
(`execStmt_sound_dupHeapTy` below): `HeapTy.Extends` reads through
`lookupBy`, which never sees a duplicated row.

- **R1** — entry storage well-typedness: `delete total;` from an
  ill-typed store executes fine and stays ill-typed. The invariant is
  inductive, not free.
- **R2** — env typing: `total = x;` with a stack binding that lies
  about its annotation writes a bool into the `uint` root from a
  perfectly well-typed *storage*. Program-variable typing is part of
  wellformedness (the calculus-side lesson: KeY's program-variable
  sorts carry this).
- **R3** — the `defaultOk` no-duplicate-row condition: `xs.push()` on an
  array whose element type declares one field name twice pushes an
  ill-typed default.
- **R4** — `nodupKeysB L.globals`, for the lemma `saveStorage_wellTyped`
  (the headline fixes `L`, so it fails there for the same reason): a
  layout with a duplicated root checks one stored value against two
  types; a save satisfying the first breaks the second.
- **R5** — heap typing: reading a memory field whose object lies about
  its store-typing claim writes a bool into a `uint` root.
- **R6** — `op.isArith` in `compoundAssign`: `total <= 3;` as a
  compound assignment slips a bool through `checkArith` (which passes
  non-int values untouched) into the `uint` root.
- **R7** — `nodupKeysB Γ`: a duplicated context row is shadowed by
  `setBy`, so a stack re-declaration leaves a binding the hidden row
  rejects — the env conjunct is not inductive without it.
- **R8** — `nodupKeysB H`, for the fixed-`H` lemma `setObjField_wt`:
  two claims on one identity are both met by an empty struct; a field
  write satisfying the first breaks the second.  The headline does not
  need this conjunct — it may pick a deduplicated `H'`.
- **R9** — `HeapWellFormed`: a stale counter makes a fresh allocation
  overwrite a live, claimed object; no store typing extending `H` can
  type the result.
-/

namespace Solidity
namespace Counterexamples
namespace PreservationNecessity

open Semantics
open SemanticsProperties (HeapWellFormed)


/-! ## Shared witnesses -/

def uintLayout : Layout := ⟨[("total", Ty.uint)]⟩

def totalFld : Field :=
  Field.primitive "total" Ty.uint (some StorageOrigin.global)

def totalPlace : PlaceExpr := PlaceExpr.var Kind.storage Ty.uint totalFld

def goodState : State := { storage := [("total", SVal.int 0)] }

def illState : State := { storage := [("total", SVal.bool true)] }

theorem goodState_wt : StateWT [] [] uintLayout goodState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | native_decide
    | exact fun i _ => rfl

/-! ## R1 — entry storage well-typedness is indispensable -/

def deleteTotal : Stmt := Stmt.delete totalPlace

/-- The headline minus the storage-well-typedness conjunct. -/
def PreservationUntypedStorage (L : Layout) (stmt : Stmt) : Prop :=
  ∀ (Γ Γ' : Ctx) (H : HeapTy) (s s' : State),
    nodupKeysB L.globals = true -> nodupKeysB Γ = true ->
    nodupKeysB H = true ->
    envTypedB Γ L H s.env = true -> heapTypedB H s.heap = true ->
    HeapWellFormed s ->
    stmtWt Γ L stmt = some Γ' ->
    execStmt s stmt = Except.ok s' ->
    wellTypedStorageB L s'.storage = true

/-- `delete` on the ill-typed store succeeds (a bool's `defaultOf` is
`bool false`) and the result is still ill-typed: preservation cannot
be proved without the entry hypothesis. -/
theorem delete_not_preserving_untyped :
    ¬ PreservationUntypedStorage uintLayout deleteTotal := by
  intro h
  have hexec : execStmt illState deleteTotal =
      Except.ok { storage := [("total", SVal.bool false)] } := by
    native_decide
  have := h [] [] [] illState _
    (by native_decide) rfl rfl (by native_decide) rfl
    (fun i _ => rfl) (by native_decide) hexec
  exact absurd this (by native_decide)

/-- Positive twin: the very same statement from the well-typed twin
state, discharged by the headline. -/
theorem delete_preserves_from_good :
    ∀ s', execStmt goodState deleteTotal = Except.ok s' ->
      wellTypedStorageB uintLayout s'.storage = true := by
  intro s' hexec
  obtain ⟨H', _, hwt'⟩ := execStmt_sound (Γ' := []) deleteTotal
    goodState_wt (by native_decide) hexec
  exact hwt'.storage

/-! ## R2 — env typing is load-bearing -/

def xStackFld : Field := Field.primitive "x" Ty.uint

def assignTotalX : Stmt :=
  Stmt.assign totalPlace (WrappedExpr.var Kind.stack Ty.uint xStackFld)

/-- The headline minus the env-typing conjunct. -/
def PreservationUntypedEnv (L : Layout) (stmt : Stmt) : Prop :=
  ∀ (Γ Γ' : Ctx) (H : HeapTy) (s s' : State),
    nodupKeysB L.globals = true -> nodupKeysB Γ = true ->
    nodupKeysB H = true ->
    wellTypedStorageB L s.storage = true ->
    heapTypedB H s.heap = true -> HeapWellFormed s ->
    stmtWt Γ L stmt = some Γ' ->
    execStmt s stmt = Except.ok s' ->
    wellTypedStorageB L s'.storage = true

/-- A stack binding lying about its `uint` annotation: `total = x;`
from a well-typed *storage* writes `bool true` into the `uint` root.
The storage invariant alone cannot carry itself — the env typing is
part of wellformedness. -/
theorem assign_not_preserving_untyped_env :
    ¬ PreservationUntypedEnv uintLayout assignTotalX := by
  intro h
  have hexec : execStmt
      { storage := [("total", SVal.int 0)],
        env := [("x", Binding.val (Value.bool true))] } assignTotalX =
      Except.ok
        { storage := [("total", SVal.bool true)],
          env := [("x", Binding.val (Value.bool true))] } := by
    native_decide
  have := h [("x", BTy.stack Ty.uint)] [("x", BTy.stack Ty.uint)] [] _ _
    (by native_decide) (by native_decide) rfl (by native_decide) rfl
    (fun i _ => rfl) (by native_decide) hexec
  exact absurd this (by native_decide)

/-! ## R3 — the `defaultOk` side condition is real -/

/-- `BadDup` declares the field name `a` twice, at two different types
(`Semantics.structDef`). `defaultForTy` builds both rows, so the second
carries a `bool` where `"a"` looks up to `uint`. -/
def dupFieldTy : Ty := Ty.ref (RefTy.struct "BadDup")

def dupArrayTy : Ty := Ty.ref (RefTy.array dupFieldTy)

def dupLayoutR3 : Layout := ⟨[("xs", dupArrayTy)]⟩

def xsFld : Field :=
  { name := "xs", ty := dupArrayTy, origin := some StorageOrigin.global }

def xsPlace : PlaceExpr := PlaceExpr.var Kind.storage dupArrayTy xsFld

def dupState : State := { storage := [("xs", SVal.array [])] }

/-- Push preservation with the `defaultOk` side condition dropped
(`wtExpr` on the target is kept — the condition lives in `stmtWt`'s push
arm, which is exactly what this refutes). -/
def PushPreservationNoDefaultOk (L : Layout) (target : PlaceExpr) : Prop :=
  ∀ (Γ : Ctx) (H : HeapTy) (s s' : State),
    StateWT Γ H L s ->
    wtExpr Γ L target.expr = true ->
    execStmt s (Stmt.push target none) = Except.ok s' ->
    wellTypedStorageB L s'.storage = true

/-- The duplicate row is what makes the pushed default ill-typed.

This used to be a *depth* counterexample: nine nested mappings outran
`defaultForTyFuel`'s hardcoded fuel of eight, and the default bottomed
out at `SVal.int 0`. `defaultForTy` is fuel-free now and correct at every
depth (`Semantics.structDef_rank_lt`), so that reading of R3 is simply
true and no longer a counterexample. What survives — and what
`defaultOk` still has to check — is the no-duplicate-row condition. -/
theorem push_not_preserving_without_defaultOk :
    ¬ PushPreservationNoDefaultOk dupLayoutR3 xsPlace := by
  intro h
  have hwt : StateWT [] [] dupLayoutR3 dupState := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
      | native_decide
      | exact fun i _ => rfl
  have hbad : (match execStmt dupState (Stmt.push xsPlace none) with
      | Except.ok t => wellTypedStorageB dupLayoutR3 t.storage
      | Except.error _ => true) = false := by native_decide
  cases hE : execStmt dupState (Stmt.push xsPlace none) with
  | error e => rw [hE] at hbad; try dsimp only at hbad; exact Bool.noConfusion hbad
  | ok s' =>
      rw [hE] at hbad
      try dsimp only at hbad
      rw [h [] [] dupState s' hwt (by native_decide) hE] at hbad
      exact Bool.noConfusion hbad

-- …and the side condition is what `stmtWt` demands: the duplicate-row
-- push is rejected, an ordinary one accepted.
example : stmtWt [] dupLayoutR3 (Stmt.push xsPlace none) = none := by
  native_decide
example :
    (stmtWt [] ⟨[("ys", Ty.ref (RefTy.array Ty.uint))]⟩
      (Stmt.push (PlaceExpr.var Kind.storage
        (Ty.ref (RefTy.array Ty.uint))
        { name := "ys", ty := Ty.ref (RefTy.array Ty.uint),
          origin := some StorageOrigin.global }) none)).isSome = true := by
  native_decide

/-! ## R4 — duplicate layout keys break save-preservation -/

def dupLayout : Layout :=
  ⟨[("x", Ty.ref (RefTy.struct "Token")),
    ("x", Ty.ref (RefTy.struct "Triple"))]⟩

/-- `saveStorage_wellTyped` minus `nodupKeysB L.globals`. -/
def SavePreservationNoNodup (L : Layout) : Prop :=
  ∀ (s s' : State) (root : Name) (segs : List Seg) (ty' : Ty)
    (new : SVal),
    wellTypedStorageB L s.storage = true ->
    L.tyAt root segs = some ty' -> new.hasTy ty' = true ->
    s.saveStorage root segs new = Except.ok s' ->
    wellTypedStorageB L s'.storage = true

/-- An empty struct inhabits both `Token` and `Triple`, so the
duplicated layout is satisfiable — but a save that satisfies the
first row (`lookupBy` sees only that one) breaks the second. -/
theorem save_not_preserving_dup_layout :
    ¬ SavePreservationNoNodup dupLayout := by
  intro h
  have hsave : State.saveStorage { storage := [("x", SVal.struct [])] }
      "x" [] (SVal.struct [("value", SVal.int 0)]) =
      Except.ok { storage :=
        [("x", SVal.struct [("value", SVal.int 0)])] } := by
    native_decide
  have := h _ _ "x" [] (Ty.ref (RefTy.struct "Token"))
    (SVal.struct [("value", SVal.int 0)])
    (by native_decide) (by native_decide) (by native_decide) hsave
  exact absurd this (by native_decide)

/-! ## R5 — heap typing is load-bearing -/

def mFld : Field :=
  Field.identity "m" (RefTy.struct "S")

def readMemField : Stmt :=
  Stmt.assign totalPlace
    (WrappedExpr.field Kind.memory Ty.uint
      (WrappedExpr.var Kind.memory (Ty.ref (RefTy.struct "S")) mFld)
      (Field.primitive "a" Ty.uint))

/-- The headline minus the heap-typing conjunct. -/
def PreservationUntypedHeap (L : Layout) (stmt : Stmt) : Prop :=
  ∀ (Γ Γ' : Ctx) (H : HeapTy) (s s' : State),
    nodupKeysB L.globals = true -> nodupKeysB Γ = true ->
    nodupKeysB H = true ->
    wellTypedStorageB L s.storage = true ->
    envTypedB Γ L H s.env = true -> HeapWellFormed s ->
    stmtWt Γ L stmt = some Γ' ->
    execStmt s stmt = Except.ok s' ->
    wellTypedStorageB L s'.storage = true

/-- A heap object lying about its claim (`S.a : uint` holding a bool):
`total = m.a;` writes the bool into the `uint` root, with storage and
env typing intact. -/
theorem read_not_preserving_untyped_heap :
    ¬ PreservationUntypedHeap uintLayout readMemField := by
  intro h
  have hexec : execStmt
      { storage := [("total", SVal.int 0)],
        heap := [(0, MObj.struct [("a", MVal.bool true)])],
        nextId := 1,
        env := [("m", Binding.mref 0)] } readMemField =
      Except.ok
        { storage := [("total", SVal.bool true)],
          heap := [(0, MObj.struct [("a", MVal.bool true)])],
          nextId := 1,
          env := [("m", Binding.mref 0)] } := by
    native_decide
  have := h [("m", BTy.mem (Ty.ref (RefTy.struct "S")))]
    [("m", BTy.mem (Ty.ref (RefTy.struct "S")))]
    [(0, Ty.ref (RefTy.struct "S"))]
    { storage := [("total", SVal.int 0)],
      heap := [(0, MObj.struct [("a", MVal.bool true)])],
      nextId := 1,
      env := [("m", Binding.mref 0)] } _
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by intro i hi
        have hi' : 1 ≤ i := hi
        have hne : i ≠ 0 := by omega
        simp [lookupBy, hne])
    (by native_decide) hexec
  exact absurd this (by native_decide)

/-! ## R6 — `op.isArith` in `compoundAssign` -/

def leAssign : Stmt :=
  Stmt.compoundAssign BinOp.le totalPlace
    (WrappedExpr.intLit Ty.uint 3)

/-- Compound-assignment preservation with `op.isArith` dropped. -/
def CompoundPreservationNoArith (L : Layout) (stmt : Stmt) : Prop :=
  ∀ (Γ : Ctx) (H : HeapTy) (s s' : State),
    StateWT Γ H L s ->
    (match stmt with
     | Stmt.compoundAssign _ lhs rhs =>
         wtExpr Γ L lhs.expr = true ∧ wtExpr Γ L rhs = true
     | _ => False) ->
    execStmt s stmt = Except.ok s' ->
    wellTypedStorageB L s'.storage = true

/-- `total <= 3;` as a compound assignment: `applyBinOp .le` returns a
bool, `checkArith` passes non-int values untouched, and the bool lands
in the `uint` root — from a fully well-typed state. The `op.isArith`
condition in `stmtWt` is what keeps this out. -/
theorem compound_not_preserving_nonarith :
    ¬ CompoundPreservationNoArith uintLayout leAssign := by
  intro h
  have hbad : (match execStmt goodState leAssign with
      | Except.ok t => wellTypedStorageB uintLayout t.storage
      | Except.error _ => true) = false := by native_decide
  cases hE : execStmt goodState leAssign with
  | error e => rw [hE] at hbad; try dsimp only at hbad; exact Bool.noConfusion hbad
  | ok s' =>
      rw [hE] at hbad
      try dsimp only at hbad
      rw [h [] [] goodState s' goodState_wt
        ⟨by native_decide, by native_decide⟩ hE] at hbad
      exact Bool.noConfusion hbad

-- …and `stmtWt` indeed rejects it while accepting the arithmetic twin.
example : stmtWt [] uintLayout leAssign = none := by native_decide
example :
    (stmtWt [] uintLayout
      (Stmt.compoundAssign BinOp.add totalPlace
        (WrappedExpr.intLit Ty.uint 3))).isSome = true := by
  native_decide

/-! ## R7 — duplicate context keys break env-typing preservation -/

/-- Γ with a duplicated key: `x` as `uint` *and* as `int`, both
satisfied by one int-valued binding — so the entry state is env-typed
even though Γ is not nodup. -/
def dupCtx : Ctx := [("x", BTy.stack Ty.uint), ("x", BTy.stack Ty.int)]

def dupCtxState : State :=
  { storage := [("total", SVal.int 0)],
    env := [("x", Binding.val (Value.int 0))] }

/-- `bool x = true;` re-declaring the duplicated name. -/
def redeclX : Stmt :=
  Stmt.stackDecl Ty.bool "x" (some (WrappedExpr.bool true))

/-- The headline minus `nodupKeysB Γ`, read on the env conjunct of the
conclusion (a stack re-declaration touches neither storage nor heap,
so the store typing is fixed). -/
def PreservationDupCtx (L : Layout) (stmt : Stmt) : Prop :=
  ∀ (Γ Γ' : Ctx) (H : HeapTy) (s s' : State),
    nodupKeysB L.globals = true -> nodupKeysB H = true ->
    wellTypedStorageB L s.storage = true ->
    envTypedB Γ L H s.env = true -> heapTypedB H s.heap = true ->
    HeapWellFormed s ->
    stmtWt Γ L stmt = some Γ' ->
    execStmt s stmt = Except.ok s' ->
    envTypedB Γ' L H s'.env = true

/-- `setBy` re-types only the *first* `x` row; the shadowed second row
still demands an int, and the new bool binding fails it. The
invariant is not inductive on a duplicated context. -/
theorem redecl_not_preserving_dup_ctx :
    ¬ PreservationDupCtx uintLayout redeclX := by
  intro h
  have hexec : execStmt dupCtxState redeclX =
      Except.ok { storage := [("total", SVal.int 0)],
                  env := [("x", Binding.val (Value.bool true))] } := by
    native_decide
  have := h dupCtx [("x", BTy.stack Ty.bool), ("x", BTy.stack Ty.int)] []
    dupCtxState _ (by native_decide) rfl (by native_decide)
    (by native_decide) rfl (fun i _ => rfl) (by native_decide) hexec
  exact absurd this (by native_decide)

/-- Positive twin: the same re-declaration from the nodup context is
discharged by the headline. -/
theorem redecl_preserves_nodup_ctx :
    ∀ s', execStmt dupCtxState redeclX = Except.ok s' ->
      ∃ H', StateWT [("x", BTy.stack Ty.bool)] H' uintLayout s' := by
  intro s' hexec
  obtain ⟨H', _, hwt'⟩ := execStmt_sound
    (Γ := [("x", BTy.stack Ty.uint)]) (Γ' := [("x", BTy.stack Ty.bool)])
    (H := []) (L := uintLayout)
    redeclX (StateWT.ofB (by native_decide)) (by native_decide) hexec
  exact ⟨H', hwt'⟩

/-! ## R8 — duplicate store-typing keys break heap-typing preservation -/

/-- `H` claiming identity `0` twice, as `Token` and as `Account`. An
empty struct object satisfies both claims. -/
def dupHeapTy : HeapTy :=
  [(0, Ty.ref (RefTy.struct "Token")), (0, Ty.ref (RefTy.struct "Account"))]

/-- `setObjField_wt` minus `nodupKeysB H` (its store typing is fixed —
a field write allocates nothing). -/
def SetObjFieldPreservationDupHeapTy (L : Layout) : Prop :=
  ∀ (Γ : Ctx) (H : HeapTy) (s : State) (id : Nat) (fld str : Name)
    (ty : Ty) (mv : MVal) (fields : List (Name × MVal)),
    nodupKeysB L.globals = true -> nodupKeysB Γ = true ->
    wellTypedStorageB L s.storage = true ->
    envTypedB Γ L H s.env = true -> heapTypedB H s.heap = true ->
    HeapWellFormed s ->
    lookupBy id H = some (Ty.ref (RefTy.struct str)) ->
    lookupBy fld (structDef str) = some ty ->
    MVal.hasTyH H mv ty = true ->
    lookupBy id s.heap = some (MObj.struct fields) ->
    heapTypedB H (s.setObj id (MObj.struct (setBy fld mv fields))).heap
      = true

/-- Writing `value` (a `Token` member) into the object satisfies the
first claim and breaks the second: `Account` has no `value` field. -/
theorem setObjField_not_preserving_dup_heapTy :
    ¬ SetObjFieldPreservationDupHeapTy uintLayout := by
  intro h
  have := h [] dupHeapTy
    { storage := [("total", SVal.int 0)],
      heap := [(0, MObj.struct [])], nextId := 1 }
    0 "value" "Token" Ty.uint (MVal.int 1) []
    (by native_decide) rfl (by native_decide) rfl (by native_decide)
    (by intro i hi
        have hi' : 1 ≤ i := hi
        have hne : i ≠ 0 := by omega
        simp [lookupBy, hne])
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  exact absurd this (by native_decide)

/-- Positive twin: under a nodup store typing the same write is
discharged by `setObjField_wt`. -/
theorem setObjField_preserves_nodup_heapTy :
    StateWT [] [(0, Ty.ref (RefTy.struct "Token"))] uintLayout
      (State.setObj
        { storage := [("total", SVal.int 0)],
          heap := [(0, MObj.struct [])], nextId := 1 }
        0 (MObj.struct (setBy "value" (MVal.int 1) []))) :=
  setObjField_wt (Γ := []) (H := [(0, Ty.ref (RefTy.struct "Token"))])
    (L := uintLayout)
    (s := { storage := [("total", SVal.int 0)],
            heap := [(0, MObj.struct [])], nextId := 1 })
    (id := 0) (fld := "value") (str := "Token") (ty := Ty.uint)
    (mv := MVal.int 1) (fields := [])
    (StateWT.ofB (by native_decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)

/-! ### R8, revisited: the headline does not need `nodupKeysB H`

`setObjField_wt` keeps `H` fixed, so a duplicated claim is fatal there.
The headline `execStmt_sound` returns *some* `H'` extending `H`, and
`HeapTy.Extends` is `lookupBy`-based: a hidden second row is invisible to
it.  So the headline minus `heapTyNodup` is provable — deduplicate `H`
(`dedupKeys`, StateTyping.lean), which changes no lookup, and run the
headline on the deduplicated typing. -/

/-- `StateWT` without the `heapTyNodup` conjunct. -/
structure StateWTDupHeapTy (Γ : Ctx) (H : HeapTy) (L : Layout) (s : State) :
    Prop where
  layoutNodup : nodupKeysB L.globals = true
  ctxNodup : nodupKeysB Γ = true
  storage : wellTypedStorageB L s.storage = true
  env : envTypedB Γ L H s.env = true
  heap : heapTypedB H s.heap = true
  heapWf : HeapWellFormed s

/-- The type-soundness headline with `heapTyNodup` dropped. -/
theorem execStmt_sound_dupHeapTy {Γ Γ' : Ctx} {H : HeapTy} {L : Layout}
    {s s' : State} (stmt : Stmt)
    (hwt : StateWTDupHeapTy Γ H L s) (hstmt : stmtWt Γ L stmt = some Γ')
    (hexec : execStmt s stmt = Except.ok s') :
    ∃ H', H.Extends H' ∧ StateWT Γ' H' L s' := by
  have hwt' : StateWT Γ (dedupKeys H) L s :=
    ⟨hwt.layoutNodup, hwt.ctxNodup, nodupKeysB_dedupKeys H, hwt.storage,
      envTypedB_mono (HeapTy.extends_dedup H) hwt.env,
      heapTypedB_dedup hwt.heap, hwt.heapWf⟩
  obtain ⟨H', hext, hwt''⟩ := execStmt_sound stmt hwt' hstmt hexec
  exact ⟨H', (HeapTy.extends_dedup H).trans hext, hwt''⟩

/-- The R8 witness, run through the headline: the duplicated typing is
accepted and the write is typed under the deduplicated claim. -/
example :
    ∃ H', dupHeapTy.Extends H' ∧
      StateWT [] H' uintLayout
        (State.setObj
          { storage := [("total", SVal.int 0)],
            heap := [(0, MObj.struct [])], nextId := 1 }
          0 (MObj.struct (setBy "value" (MVal.int 1) []))) :=
  ⟨dedupKeys dupHeapTy, HeapTy.extends_dedup _, by
    have h := setObjField_preserves_nodup_heapTy
    exact h⟩

/-! ## R9 — heap freshness is load-bearing -/

/-- A stale allocation counter: identity `0` is live (claimed as
`Token`, bound to `m`) but `nextId` is still `0`. -/
def staleState : State :=
  { storage := [("total", SVal.int 0)],
    heap := [(0, MObj.struct [("value", MVal.int 0)])],
    nextId := 0,
    env := [("m", Binding.mref 0)] }

def tokenTy : Ty := Ty.ref (RefTy.struct "Token")

/-- `uint[] memory n;` — a fresh default allocation. -/
def declArr : Stmt :=
  Stmt.memoryDecl (Ty.ref (RefTy.array Ty.uint)) "n" none

/-- The headline minus `HeapWellFormed s` — the full conclusion,
existential store typing included. -/
def PreservationStaleCounter (L : Layout) (stmt : Stmt) : Prop :=
  ∀ (Γ Γ' : Ctx) (H : HeapTy) (s s' : State),
    nodupKeysB L.globals = true -> nodupKeysB Γ = true ->
    nodupKeysB H = true ->
    wellTypedStorageB L s.storage = true ->
    envTypedB Γ L H s.env = true -> heapTypedB H s.heap = true ->
    stmtWt Γ L stmt = some Γ' ->
    execStmt s stmt = Except.ok s' ->
    ∃ H', H.Extends H' ∧ StateWT Γ' H' L s'

/-- The allocation lands on the live identity `0` and overwrites the
`Token` object with an array. Any extension `H'` still claims `0` as
`Token`, so no store typing can type the result. -/
theorem decl_not_preserving_stale_counter :
    ¬ PreservationStaleCounter uintLayout declArr := by
  intro h
  have hexec : execStmt staleState declArr =
      Except.ok { storage := [("total", SVal.int 0)],
                  heap := [(0, MObj.array [])],
                  nextId := 1,
                  env := [("m", Binding.mref 0), ("n", Binding.mref 0)] } := by
    native_decide
  obtain ⟨H', hext, hwt'⟩ := h [("m", BTy.mem tokenTy)]
    [("m", BTy.mem tokenTy), ("n", BTy.mem (Ty.ref (RefTy.array Ty.uint)))]
    [(0, tokenTy)] staleState _
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) hexec
  have hclaim : lookupBy 0 H' = some tokenTy := hext 0 _ (by native_decide)
  have hrow := List.all_eq_true.mp hwt'.heap _ (lookupBy_eq_some_mem hclaim)
  simp [lookupBy, MObj.hasTyH, tokenTy] at hrow

/-- Positive twin: with the counter past the live identity, the
headline allocates fresh and types the result. -/
theorem decl_preserves_fresh_counter :
    ∀ s', execStmt { staleState with nextId := 1 } declArr = Except.ok s' ->
      ∃ H', HeapTy.Extends [(0, tokenTy)] H' ∧
        StateWT [("m", BTy.mem tokenTy),
                 ("n", BTy.mem (Ty.ref (RefTy.array Ty.uint)))]
          H' uintLayout s' := by
  intro s' hexec
  exact execStmt_sound
    (Γ := [("m", BTy.mem tokenTy)])
    (Γ' := [("m", BTy.mem tokenTy),
            ("n", BTy.mem (Ty.ref (RefTy.array Ty.uint)))])
    (H := [(0, tokenTy)]) (L := uintLayout)
    declArr (StateWT.ofB (by native_decide)) (by native_decide) hexec

/-! ## The headline is not vacuous

A concrete well-typed program (write, compound-add, push, read) runs
through `execBlock_sound`, and the corollary `run_then_find_int`
recovers an int at the declared-`uint` path with no per-state
assumption. -/

def demoLayout : Layout :=
  ⟨[("total", Ty.uint), ("values", Ty.ref (RefTy.array Ty.uint))]⟩

def demoState : State :=
  { storage := [("total", SVal.int 40), ("values", SVal.array [])] }

def valuesPlace : PlaceExpr :=
  PlaceExpr.var Kind.storage (Ty.ref (RefTy.array Ty.uint))
    { name := "values", ty := Ty.ref (RefTy.array Ty.uint),
      origin := some StorageOrigin.global }

def demoProg : List Stmt :=
  [Stmt.compoundAssign BinOp.add totalPlace (WrappedExpr.intLit Ty.uint 2),
   Stmt.push valuesPlace
     (some (WrappedExpr.var Kind.storage Ty.uint totalFld))]

theorem demoState_wt : StateWT [] [] demoLayout demoState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | native_decide
    | exact fun i _ => rfl

example :
    ∀ s' v, execBlock demoState demoProg = Except.ok s' ->
      s'.findStorage "values" [Seg.at 0] = Except.ok v ->
      ∃ n, v = SVal.int n := by
  intro s' v hexec hfind
  exact run_then_find_int (Γ' := []) (ty := Ty.uint) demoState_wt
    (by native_decide) hexec (by native_decide) rfl hfind

-- The demo program actually runs and stores 42.
example :
    execBlock demoState demoProg =
      Except.ok { storage :=
        [("total", SVal.int 42),
         ("values", SVal.array [SVal.int 42])] } := by
  native_decide

end PreservationNecessity
end Counterexamples
end Solidity
