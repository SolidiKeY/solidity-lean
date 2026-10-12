import Solidity.Typing.State
import Solidity.Semantics.Erased

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

/-- The element type of an array type of either kind: `uint` of `uint[]` and
of `uint[3]`. -/
def RefTy.arrElem? : RefTy → Option Ty
  | .array E | .fixed E _ => some E
  | _ => none

theorem ArrTy.arrElem {R : RefTy} {E : Ty} : ArrTy R E → R.arrElem? = some E
  | .dyn | .fixed => rfl

/-- A primitive slot read out is a stack value of the slot's type. -/
theorem Semantics.MVal.asValue_hasTy {mv : MVal} {ty : Ty} {v : Value}
    (h : MVal.hasTyH H mv ty = true) (hval : mv.asValue = .ok v) :
    (Value.toSVal v).hasTy ty = true := by
  cases mv with
  | prim p =>
      cases p <;> simp only [MVal.asValue] at hval <;> cases hval <;>
        cases ty with
        | prim pt => cases pt <;> simp_all [MVal.hasTyH, Value.toSVal, SVal.hasTy]
        | ref r => simp [MVal.hasTyH] at h
  | ref id => exact nomatch hval

/-- A stored primitive read out is a stack value of its type. -/
theorem Semantics.SVal.asValue_hasTy {sv : SVal} {ty : Ty} {v : Value}
    (h : sv.hasTy ty = true) (hval : sv.asValue = .ok v) : (Value.toSVal v).hasTy ty = true := by
  rw [SVal.asValue_toSVal hval]; exact h

/-- An integer is a value of every numeric type. -/
theorem int_toSVal_hasTy {p : PrimTy} (hp : p.isNumeric = true) (n : Int) :
    (Value.toSVal (.int n)).hasTy (.prim p) = true := by
  cases p <;> simp_all [PrimTy.isNumeric, Value.toSVal, SVal.hasTy]

end Lemmas

/-! ## Operators -/

/-! ## The global invariant along an allocation -/

namespace Semantics.StateWT

variable {H : HeapTy} {σ σ' : State}

end Semantics.StateWT

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

The locals are typed by their context: `Env.All (LTy.WT C H) σ.env` says each
local holds what its type says. -/

namespace Solidity

open Semantics hiding State
open SemanticsProperties (HeapWellFormed)

variable {C : Contract}

/-! ## Results -/

/-! ## Locals that satisfy a predicate -/

/-- Every local of `e` satisfies `P` at its type. -/
def Env.All (P : (t : LTy) → t.Denote C → Prop) : {Γ : Ctx} → Env C Γ → Prop
  | [], _ => True
  | _ :: _, e => P _ e.1 ∧ Env.All P e.2

namespace Env.All

variable {P Q : (t : LTy) → t.Denote C → Prop}

theorem get : {Γ : Ctx} → {t : LTy} → (i : Idx Γ t) → {e : Env C Γ} → Env.All P e →
    P t (Env.get i e) := by
  intro Γ t i
  induction i with
  | here => intro e h; exact h.1
  | there i ih => intro e h; exact ih h.2

theorem set : {Γ : Ctx} → {t : LTy} → (i : Idx Γ t) → {e : Env C Γ} → {v : t.Denote C} →
    Env.All P e → P t v → Env.All P (Env.set i v e) := by
  intro Γ t i
  induction i with
  | here => intro e v h hv; exact ⟨hv, h.2⟩
  | there i ih => intro e v h hv; exact ⟨h.1, ih h.2 hv⟩

theorem drop {Γ : Ctx} : {Δ : Ctx} → (h : Ext Γ Δ) → {e : Env C Δ} → Env.All P e →
    Env.All P (Env.drop h e) := by
  intro Δ h
  induction h with
  | refl => intro e he; exact he
  | push h ih => intro e he; exact ih he.2

theorem append {Γ : Ctx} : (ρ : Ctx) → {r : Env C ρ} → {e : Env C Γ} → Env.All P r →
    Env.All P e → Env.All P (Env.append ρ r e)
  | [], _, _, _, he => he
  | _ :: ρ, _, _, hr, he => ⟨hr.1, append ρ hr.2 he⟩

theorem take {Γ : Ctx} : (ρ : Ctx) → {e : Env C (ρ ++ Γ)} → Env.All P e → Env.All P (Env.take ρ e)
  | [], _, _ => trivial
  | _ :: ρ, _, he => ⟨he.1, take ρ he.2⟩

theorem mono (hPQ : ∀ t v, P t v → Q t v) : {Γ : Ctx} → {e : Env C Γ} → Env.All P e →
    Env.All Q e
  | [], _, _ => trivial
  | _ :: _, _, he => ⟨hPQ _ _ he.1, mono hPQ he.2⟩

theorem and : {Γ : Ctx} → {e : Env C Γ} → Env.All P e → Env.All Q e →
    Env.All (fun t v => P t v ∧ Q t v) e
  | [], _, _, _ => trivial
  | _ :: _, _, hp, hq => ⟨⟨hp.1, hq.1⟩, and hp.2 hq.2⟩

end Env.All

/-! ## Invariants of runs

What a run keeps is a part on the global state and a part on each local,
the latter kept as the store typing grows (`Typing/TypedRunInv.lean` carries
it along the typed run). -/

/-- An invariant of runs: a part on the global state, a part on each
local, kept as the store typing `H` grows, and blind to the locals. -/
structure RunInv (C : Contract) where
  glob : HeapTy → Semantics.State → Prop
  loc : HeapTy → (t : LTy) → t.Denote C → Prop
  loc_mono : ∀ {H H' : HeapTy} {t : LTy} {v : t.Denote C}, H.Extends H' → loc H t v →
    loc H' t v
  reglob : ∀ {H : HeapTy} {τ : Semantics.State} {Γ : Ctx} (e : Env C Γ), glob H τ →
    glob H (EState.ofGlob τ e).glob

namespace RunInv

variable {I : RunInv C}

theorem env_mono {Γ : Ctx} {H H' : HeapTy} (hext : H.Extends H') {e : Env C Γ}
    (h : Env.All (I.loc H) e) : Env.All (I.loc H') e :=
  Env.All.mono (fun _ _ => I.loc_mono hext) h

end RunInv

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

theorem LTy.WT.mono {H H' : HeapTy} (hext : H.Extends H') :
    {t : LTy} → {v : t.Denote C} → LTy.WT C H t v → LTy.WT C H' t v
  | .val _, _, h => h
  | .alias _, _, h => h
  | .mem _, _, h => fun id hid => MVal.hasTyH_mono hext (h id hid)
  | .old, _, h => h
  | .oldNet, _, h => h

theorem LTy.WT.default (p : PrimTy) : LTy.WT C H (.val p) (PrimTy.default p) := by
  cases p <;> rfl

/-- A storage-and-heap invariant is blind to the locals. -/
theorem _root_.Solidity.Semantics.StateWT.reglob {H : HeapTy} {L : Layout} {τ : Semantics.State}
    {Γ : Ctx} (h : StateWT H L τ) (e : Env C Γ) : StateWT H L (EState.ofGlob τ e).glob :=
  ⟨h.1, h.2, h.3, h.4, h.5⟩

end Solidity
