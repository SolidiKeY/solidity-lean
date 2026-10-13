import Solidity.Typing.State

/-!
# Type soundness: the layout, the typed values, the invariants' shape

The typed syntax rules out every *static* mismatch: a member exists, an
operator takes its operand, a copy holds no mapping, a pushed default is
well-formed, and, since the scoped syntax (`Syntax/Scoped.lean`), a local is a
position in a context `Γ`, read and written at the type `Γ` gives it.  The
typed run (`Semantics/Run.lean`) rules out the dynamic ones: its states
hold values of their types, so their erasure's global part is well-typed by
construction (`State.glob_wt`, `Typing/TypedWT.lean`).

Here: `C`'s layout, the value and heap lemmas the invariants read
(`StateWT`, `Typing/State.lean`: storage inhabits `C`'s layout, the heap
the store typing `H`, the allocation counter is fresh), a local of its type
(`LTy.WT`), and `RunInv`, the shape of an invariant with a part on the
global state and one on each local, which `Typing/TypedRunInv.lean` carries
along the typed run and `Reachability.lean` and `Constructibility.lean`
instantiate.
-/

namespace Solidity

open Semantics
open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne HeapWellFormed
  lookupBy_eq_some_mem)

variable {C : Contract}

/-! ## The layout a contract declares -/

/-- The storage layout of `C`: its roots at their declared types.  A root's
type is `C.rootType`, and one step down is `segTy`, which reads the same
`structDef` as `C.fieldType`. -/
def Contract.layout (C : Contract) : Layout := ⟨C.vars⟩

/-! ## Value and heap lemmas -/

section Lemmas

variable {H : HeapTy}

/-- A reference slot typed at a reference type is the store typing's claim. -/
theorem Semantics.MVal.hasTyH_ref {id : Nat} {R : RefTy} :
    MVal.hasTyH H (.ref id) (.ref R) = true ↔ lookupBy id H = some (.ref R) := by
  simp [MVal.hasTyH]

/-- The object at a claimed identity exists and has the claimed type. -/
theorem heapTypedB_obj {heap : List (Nat × MObj)} {id : Nat} {ty : Ty}
    (hheap : heapTypedB H heap = true) (h : lookupBy id H = some ty) :
    ∃ obj, lookupBy id heap = some obj ∧ obj.hasTyH H ty = true := by
  have := List.all_eq_true.mp hheap _ (lookupBy_eq_some_mem h)
  revert this
  cases hl : lookupBy id heap with
  | none => intro h; exact absurd h (by simp)
  | some obj => intro h; exact ⟨obj, rfl, h⟩

/-- An integer is a value of every numeric type. -/
theorem int_toSVal_hasTy {p : PrimTy} (hp : p.isNumeric = true) (n : Int) :
    (Value.toSVal (.int n)).hasTy (.prim p) = true := by
  cases p <;> simp_all [PrimTy.isNumeric, Value.toSVal, SVal.hasTy]

end Lemmas

/-! ## The values the statements write are typed -/

section Effects

variable {H : HeapTy} {σ σ' : State}

theorem arith_new_wt {op : BinOp} {p : PrimTy} {old v n₁ n₂ : Value}
    (hop : op.isArith = true) (hp : p.isNumeric = true)
    (h₁ : applyBinOp op old v = .ok n₁) (h₂ : checkArith (.prim p) n₁ = .ok n₂) :
    (Value.toSVal n₂).hasTy (.prim p) = true := by
  rw [checkArith_ok_eq h₂]
  obtain ⟨n, rfl⟩ := applyBinOp_arith_int hop h₁
  exact int_toSVal_hasTy hp n

/-- `x++` stores and yields numbers of `x`'s type. -/
theorem bump_new_wt {p : PrimTy} {m : Int} {n : Value} (hp : p.isNumeric = true)
    (h : checkArith (.prim p) (.int m) = .ok n) : (Value.toSVal n).hasTy (.prim p) = true := by
  rw [checkArith_ok_eq h]; exact int_toSVal_hasTy hp m

end Effects

/-! ## Where a run starts -/

theorem Semantics.lookupBy_map_snd {k : Name} {f : Ty → SVal} :
    ∀ l : List (Name × Ty), lookupBy k (l.map fun (n, T) => (n, f T)) = (lookupBy k l).map f
  | [] => rfl
  | (n, T) :: rest => by
    by_cases h : k = n
    · simp [lookupBy, h]
    · simp [lookupBy, h, lookupBy_map_snd rest]

/-- A contract starts well-typed: each root at its type's default, an empty
heap.  `StandardExample` starts in `State.exampleStore`
(`exampleStore_wt`). -/
theorem Semantics.StateWT.init {σ : State} (hnd : nodupKeysB C.vars = true)
    (hst : σ.storage = C.initStorage) (hheap : σ.heap = []) : StateWT [] C.layout σ where
  layoutNodup := hnd
  heapTyNodup := rfl
  storage := by
    rw [hst]
    refine List.all_eq_true.mpr fun g hg => ?_
    show (match lookupBy g.1 C.initStorage with
      | some v => v.hasTy g.2
      | none => false) = true
    simp only [Contract.initStorage, lookupBy_map_snd, lookupBy_eq_of_nodup hnd hg, Option.map]
    exact defaultForTy_hasTy
  heap := rfl
  heapWf := fun i _ => by rw [hheap]; rfl

/-- `StandardExample`'s store is well-typed. -/
theorem exampleStore_wt : StateWT [] StandardExample.layout State.exampleStore :=
  StateWT.init (by decide) initStorage_standardExample.symm rfl

end Solidity

/-! # Over the scoped syntax

A local, erased, is typed by its context (`LTy.WT`); `TEnv.All`
(`Typing/TypedRunInv.lean`) reads it of every local of a typed state. -/

namespace Solidity

open Semantics hiding State
open SemanticsProperties (HeapWellFormed)

variable {C : Contract}

/-! ## Invariants of runs

What a run keeps is a part on the global state and a part on each local,
the latter kept as the store typing grows (`Typing/TypedRunInv.lean` carries
it along the typed run). -/

/-- An invariant of runs: a part on the global state, a part on each
local, kept as the store typing `H` grows. -/
structure RunInv (C : Contract) where
  glob : HeapTy → Semantics.State → Prop
  loc : HeapTy → (t : LTy) → t.Denote C → Prop
  loc_mono : ∀ {H H' : HeapTy} {t : LTy} {v : t.Denote C}, H.Extends H' → loc H t v →
    loc H' t v

/-! ## The typed locals -/

/-- A local's value is of its type: a value of its primitive type, an alias
bound (if at all) to a path the layout types at its type, a memory local,
if set at all, an identity the store typing claims at its type (an unset
one, decision 17', reads as a revert). -/
def LTy.WT (C : Contract) (H : HeapTy) : (t : LTy) → t.Denote C → Prop
  | .val p, v => (Value.toSVal v).hasTy (.prim p) = true
  | .alias R, o => ∀ r segs, o = some (r, segs) → C.layout.tyAt r segs = some (.ref R)
  | .mem R, o => ∀ id, o = some id → MVal.hasTyH H (.ref id) (.ref R) = true
  | .old, _ => True
  | .oldNet, _ => True
  | .kint, _ => True

theorem LTy.WT.mono {H H' : HeapTy} (hext : H.Extends H') :
    {t : LTy} → {v : t.Denote C} → LTy.WT C H t v → LTy.WT C H' t v
  | .val _, _, h => h
  | .alias _, _, h => h
  | .mem _, _, h => fun id hid => MVal.hasTyH_mono hext (h id hid)
  | .old, _, h => h
  | .oldNet, _, h => h
  | .kint, _, h => h

theorem LTy.WT.default (p : PrimTy) : LTy.WT C H (.val p) (PrimTy.default p) := by
  cases p <;> rfl

end Solidity
