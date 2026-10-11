import Solidity.Typing.State
import Solidity.Semantics.Erased

/-!
# Type soundness on the erasure: the evaluators are typed

The typed syntax rules out every *static* mismatch: a member exists, an
operator takes its operand, a copy holds no mapping, a pushed default is
well-formed, and, since the scoped syntax (`Syntax/Scoped.lean`), a local is a
position in a context `Γ`, read and written at the type `Γ` gives it.  The
typed run (`Semantics/Run.lean`) rules out the dynamic ones: its
states hold values of their types, so their erasure is well-typed by
construction (`State.erase_wt`, `Typing/TypedWT.lean`).

`RunWT C H σ` is that invariant on an erased state: the global part
`StateWT` (`Typing/State.lean`: storage inhabits `C`'s layout, the heap the
store typing `H`, the allocation counter is fresh) and every local of its
type (`LTy.WT`: a number in a `uint` local, a path the layout types at an
alias's type, an identity `H` claims at a memory local's type).  What is
proved here is what the closer and the other invariants read of it: the
erasure's evaluators (`Semantics/Erased.lean`) find values of their types —
the paths resolve to a place the layout types at the path's type
(`Loc.resolve_wt`), the memory reads find a slot of the path's type
(`MLoc.read_wt`), a value evaluates to one of its type (`Val.eval_wt`).
`RunInv` is the shape of an invariant with a part on the global state and
one on each local, which `Typing/TypedRunInv.lean` carries along the typed
run and `Reachability.lean` and `Constructibility.lean` instantiate.
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

/-- `alice` in `StandardExample` has type `Person` in the layout, as
declared. -/
theorem Contract.layout_tyAt_root {C : Contract} {r : Name} {T : Ty}
    (h : C.rootType r = some T) : C.layout.tyAt r [] = some T := by
  simp only [Layout.tyAt, Contract.layout]
  rw [show lookupBy r C.vars = some T from h]
  rfl

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

/-- A member of a typed memory struct has its declared type: `m.age` a `uint`. -/
theorem mHasTyHFields_lookup {str : Name} {fields : List (Name × MVal)} {n : Name} {v : MVal}
    (hwt : MObj.hasTyH.hasTyHFields H str fields = true)
    (hlook : lookupBy n fields = some v) :
    ∃ ty, lookupBy n (structDef str) = some ty ∧ MVal.hasTyH H v ty = true := by
  induction fields with
  | nil => simp [lookupBy] at hlook
  | cons p rest ih =>
      obtain ⟨n', v'⟩ := p
      simp only [MObj.hasTyH.hasTyHFields, Bool.and_eq_true] at hwt
      by_cases hn : n = n'
      · subst hn
        simp [lookupBy] at hlook
        subst hlook
        cases hdef : lookupBy n (structDef str) with
        | none => rw [hdef] at hwt; exact Bool.noConfusion hwt.1
        | some ty =>
            rw [hdef] at hwt
            exact ⟨ty, rfl, hwt.1⟩
      · simp [lookupBy, hn] at hlook
        exact ih hwt.2 hlook

/-- An element of a typed memory array has the element type: `ns[i]` a `uint`. -/
theorem mHasTyHElems_mem {elem : Ty} {elems : List MVal} {v : MVal}
    (hwt : MObj.hasTyH.hasTyHElems H elem elems = true) (hmem : v ∈ elems) :
    MVal.hasTyH H v elem = true := by
  induction elems with
  | nil => cases hmem
  | cons w rest ih =>
      simp only [MObj.hasTyH.hasTyHElems, Bool.and_eq_true] at hwt
      cases hmem with
      | head => exact hwt.1
      | tail _ hmem => exact ih hwt.2 hmem

/-- The element type of an array type of either kind: `uint` of `uint[]` and
of `uint[3]`. -/
def RefTy.arrElem? : RefTy → Option Ty
  | .array E | .fixed E _ => some E
  | _ => none

theorem ArrTy.arrElem {R : RefTy} {E : Ty} : ArrTy R E → R.arrElem? = some E
  | .dyn | .fixed => rfl

/-- An object typed at an array type is an array of the element type. -/
theorem Semantics.MObj.hasTyH_arrElem {R : RefTy} {E : Ty} {obj : MObj} (hR : R.arrElem? = some E)
    (h : MObj.hasTyH H obj (.ref R) = true) :
    ∃ elems fx, obj = .array elems fx ∧ MObj.hasTyH.hasTyHElems H E elems = true := by
  cases R <;> simp only [RefTy.arrElem?, Option.some.injEq, reduceCtorEq] at hR <;> subst hR <;>
    cases obj <;> simp_all [MObj.hasTyH]

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

/-- A typed stack value stored in memory is a typed slot. -/
theorem Semantics.Value.toMVal_hasTyH {v : Value} {ty : Ty}
    (h : (Value.toSVal v).hasTy ty = true) : MVal.hasTyH H v.toMVal ty = true := by
  cases v <;> cases ty with
  | prim pt => cases pt <;> simp_all [Value.toSVal, SVal.hasTy, Value.toMVal, MVal.hasTyH]
  | ref r => simp [Value.toSVal, SVal.hasTy] at h

/-- A stored primitive read out is a stack value of its type. -/
theorem Semantics.SVal.asValue_hasTy {sv : SVal} {ty : Ty} {v : Value}
    (h : sv.hasTy ty = true) (hval : sv.asValue = .ok v) : (Value.toSVal v).hasTy ty = true := by
  rw [SVal.asValue_toSVal hval]; exact h

/-- A slot read as an object is a reference: `m` in `m.age`. -/
theorem Semantics.MVal.asRef_ok {mv : MVal} {id : Nat} (h : mv.asRef = .ok id) : mv = .ref id := by
  cases mv with
  | ref i => cases h; rfl
  | prim _ => exact nomatch h

/-- An integer is a value of every numeric type. -/
theorem int_toSVal_hasTy {p : PrimTy} (hp : p.isNumeric = true) (n : Int) :
    (Value.toSVal (.int n)).hasTy (.prim p) = true := by
  cases p <;> simp_all [PrimTy.isNumeric, Value.toSVal, SVal.hasTy]

/-- Comparisons and connectives produce booleans. -/
theorem applyBinOp_nonarith_bool {op : BinOp} {l r v : Value}
    (hop : op.isArith = false) (h : applyBinOp op l r = .ok v) : ∃ b, v = .bool b := by
  cases op <;> simp only [BinOp.isArith] at hop <;> try exact Bool.noConfusion hop
  all_goals simp only [applyBinOp, bind, Except.bind] at h
  all_goals repeat' split at h
  all_goals first
    | exact ⟨_, (Except.ok.inj h).symm⟩
    | exact nomatch h

end Lemmas

/-! ## Operators -/

/-- `a ⊕ b` evaluates to a value of the type `⊕` returns: `a + b` at `uint`
is a number, `a < b` a boolean, whatever the operands held. -/
theorem evalBinop_wt {op : BinOp} {p q : PrimTy} {lv : Value} {rb : Res Value} {w : Value}
    (hacc : op.accepts p = true) (hq : op.ret p = q) (h : evalBinop op p lv rb = .ok w) :
    (Value.toSVal w).hasTy (.prim q) = true := by
  subst hq
  unfold evalBinop at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · obtain ⟨rv, _, h⟩ := bind_ok_inv h
    obtain ⟨v', hv', h⟩ := bind_ok_inv h
    have hw := checkArith_ok_eq h
    subst hw
    cases hA : op.isArith
    · obtain ⟨b, rfl⟩ := applyBinOp_nonarith_bool hA hv'
      simp [BinOp.ret, hA, Value.toSVal, SVal.hasTy]
    · obtain ⟨n, rfl⟩ := applyBinOp_arith_int hA hv'
      have hnum : p.isNumeric = true := by
        cases op <;> simp_all [BinOp.isArith, BinOp.accepts, PrimTy.isNumeric]
      simp only [BinOp.ret, hA, if_true]
      exact int_toSVal_hasTy hnum n

/-- `-a`, `!a` and `~a` evaluate to a value of the type they return. -/
theorem evalUnop_wt {op : UnOp} {p q : PrimTy} {v w : Value}
    (hacc : op.accepts p = true) (hq : op.ret p = q)
    (h : (do unopCheck op p (← applyUnOp op v)) = (.ok w : Res Value)) :
    (Value.toSVal w).hasTy (.prim q) = true := by
  subst hq
  obtain ⟨u, hu, h⟩ := bind_ok_inv h
  have hw : w = u := by
    unfold unopCheck at h
    split at h
    · exact checkArith_ok_eq h
    · cases h; rfl
  subst hw
  cases op with
  | neg =>
    simp only [applyUnOp, bind, Except.bind] at hu
    split at hu
    · exact nomatch hu
    · cases hu
      obtain rfl : p = .int := by simpa only [UnOp.accepts, beq_iff_eq] using hacc
      exact int_toSVal_hasTy rfl _
  | not =>
    simp only [applyUnOp, bind, Except.bind] at hu
    split at hu
    · exact nomatch hu
    · cases hu; rfl
  | bnot =>
    simp only [applyUnOp, bind, Except.bind] at hu
    split at hu
    · exact nomatch hu
    · cases hu; exact int_toSVal_hasTy (by simp_all [UnOp.accepts, UnOp.ret, PrimTy.isNumeric]) _

/-! ## The global invariant along an allocation -/

namespace Semantics.StateWT

variable {H : HeapTy} {σ σ' : State}

/-- Along an allocation (a storage→memory copy, a fresh default) the
store typing grows and everything typed stays typed. -/
theorem ofCopyOut {H' : HeapTy} (hwt : StateWT H C.layout σ) (hout : CopyOut H σ H' σ') :
    StateWT H' C.layout σ' where
  layoutNodup := hwt.layoutNodup
  heapTyNodup := hout.nodup
  storage := by rw [hout.storage]; exact hwt.storage
  heap := hout.heap
  heapWf := hout.heapWf

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

/-- `+=` .. `%=` are arithmetic, so `x += 1` writes a number. -/
theorem compound_isArith {op : BinOp} (h : op.hasCompoundAssign = true) : op.isArith = true := by
  cases op <;> simp_all [BinOp.hasCompoundAssign, BinOp.isArith]

/-- `new uint[](n)` copies in a value of its type: `n` well-formed defaults. -/
theorem newArrVal_hasTy {R : RefTy} (h : R.newArrOk = true) (n : Int) :
    (newArrVal R n).hasTy (.ref R) = true := by
  cases R with
  | array E =>
    simp only [RefTy.newArrOk, Bool.and_eq_true] at h
    have hE := defaultForTy_hasTy (ty := E)
    simp only [newArrVal, SVal.hasTy, SVal.hasTy.hasTyElems, Bool.and_true, Bool.not_false,
      Bool.true_and]
    induction n.toNat with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, SVal.hasTy.hasTyElems, hE, ih]
  | struct _ => simp [RefTy.newArrOk] at h
  | fixed _ _ => simp [RefTy.newArrOk] at h
  | mapping _ _ => simp [RefTy.newArrOk] at h

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
local holds what its type says, and `RunWT` adds the global part. -/

namespace Solidity

open Semantics hiding State
open SemanticsProperties (HeapWellFormed)

variable {C : Contract}

/-! ## Results -/

theorem map_ok_inv {α β : Type} {f : α → β} {x : Res α} {b : β} (h : f <$> x = .ok b) :
    ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

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

/-- Leaving a call keeps every local satisfying `P` when the caller's and the
frame's return variables do. -/
theorem CallRet.leave_all {P : (t : LTy) → t.Denote C → Prop} {Γ rs Γ' : Ctx}
    (ret : CallRet Γ rs Γ') {e : Env C Γ} {r : Env C rs} (he : Env.All P e) (hr : Env.All P r) :
    Env.All P (ret.leave e r) := by
  cases ret with
  | none => exact he
  | val p x res =>
    cases res with
    | none => exact he
    | some i => exact Env.All.set i he hr.1
  | rets bs => exact Env.All.append _ hr he
  | mem R x hd hm => exact ⟨hr.1, he⟩

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

variable (I : RunInv C)

/-- The invariant holds of a state under the store typing `H`. -/
def Holds {Γ : Ctx} (H : HeapTy) (σ : EState C Γ) : Prop :=
  I.glob H σ.glob ∧ Env.All (I.loc H) σ.env

variable {I}

theorem env_mono {Γ : Ctx} {H H' : HeapTy} (hext : H.Extends H') {e : Env C Γ}
    (h : Env.All (I.loc H) e) : Env.All (I.loc H') e :=
  Env.All.mono (fun _ _ => I.loc_mono hext) h

theorem Holds.withEnv {Γ Δ : Ctx} {H : HeapTy} {σ : EState C Γ} (h : I.Holds H σ) {e : Env C Δ}
    (he : Env.All (I.loc H) e) : I.Holds H (σ.withEnv e) :=
  ⟨h.1, he⟩

theorem Holds.drop {Γ Δ : Ctx} {H : HeapTy} {σ : EState C Δ} (h : I.Holds H σ) (x : Ext Γ Δ) :
    I.Holds H (σ.drop x) :=
  ⟨h.1, Env.All.drop x h.2⟩

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

/-- A memory local set to an identity of its type. -/
theorem LTy.WT.mem_some {H : HeapTy} {R : RefTy} {id : Nat}
    (h : MVal.hasTyH H (.ref id) (.ref R) = true) : LTy.WT C H (.mem R) (some id) :=
  fun _ e => Option.some.inj e ▸ h

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

/-- Type soundness's invariant: the global part well-typed, every local of
its type. -/
def wtInv (C : Contract) : RunInv C where
  glob H τ := StateWT H C.layout τ
  loc := LTy.WT C
  loc_mono hext h := LTy.WT.mono hext h
  reglob e h := h.reglob e

/-- The state invariant over a context: the global part well-typed under
`C`'s layout and the store typing `H`, each local of its type. -/
abbrev RunWT (C : Contract) {Γ : Ctx} (H : HeapTy) (σ : EState C Γ) : Prop := (wtInv C).Holds H σ

namespace RunWT

variable {Γ : Ctx} {H : HeapTy} {σ : EState C Γ}

theorem glob (hwt : RunWT C H σ) : StateWT H C.layout σ.glob := hwt.1

theorem env (hwt : RunWT C H σ) : Env.All (LTy.WT C H) σ.env := hwt.2

/-- The global part replaced by a well-typed one under a grown store
typing. -/
theorem withGlob {H' : HeapTy} (hwt : RunWT C H σ) (hext : H.Extends H') {τ : Semantics.State}
    (hτ : StateWT H' C.layout τ) : RunWT C H' (σ.withGlob τ) :=
  ⟨hτ.reglob σ.env, Env.All.mono (fun _ _ => LTy.WT.mono hext) hwt.env⟩

theorem setLocal (hwt : RunWT C H σ) {t : LTy} (i : Idx Γ t) {v : t.Denote C}
    (hv : LTy.WT C H t v) : RunWT C H (σ.setLocal i v) :=
  ⟨hwt.glob, Env.All.set i hwt.env hv⟩

theorem push (hwt : RunWT C H σ) {t : LTy} {v : t.Denote C} (hv : LTy.WT C H t v) :
    RunWT C H (σ.push v) :=
  ⟨hwt.glob, hv, hwt.env⟩

end RunWT

/-! ## The evaluators are typed

Each mirrors `Semantics.lean`'s evaluator's typing, a local read where the
old one looked a name up.  `H` is fixed here: nothing an expression does
allocates. -/

section Eval

variable {Γ : Ctx} {H : HeapTy} {σ : EState C Γ}

/-- A simple value is of its type: the local `x : uint` holds a number. -/
theorem Simple.eval_wt (hwt : RunWT C H σ) {p : PrimTy} {s : Simple C Γ p} {w : Value}
    (h : s.eval σ = .ok w) : (Value.toSVal w).hasTy (.prim p) = true := by
  cases s with
  | lit n hn => cases h; exact int_toSVal_hasTy (PrimTy.isNumeric_of_inRange hn) n
  | bool b => cases h; rfl
  | «local» i => cases h; exact hwt.env.get i
  | env k hp => subst hp; cases h; rfl

/-- An alias is bound to a path the layout types at its type. -/
theorem aliasPath_wt (hwt : RunWT C H σ) {R : RefTy} (i : Idx Γ (.alias R)) {r : Name}
    {segs : List Seg} (h : aliasPath σ i = .ok (r, segs)) :
    C.layout.tyAt r segs = some (.ref R) := by
  have hi : LTy.WT C H (.alias R) (Env.get i σ.env) := hwt.env.get i
  unfold aliasPath at h
  split at h
  · rename_i p hp
    cases h
    exact hi _ _ hp
  · exact nomatch h

mutual

/-- A storage path resolves to a place the layout types at the path's type:
`p.age`, with `p : Person storage`, at `uint`. -/
theorem SPath.resolve_wt (hwt : RunWT C H σ) :
    ∀ {T : Ty} (p : SPath C Γ T) {r : Name} {segs : List Seg},
      p.resolve σ = .ok (r, segs) → C.layout.tyAt r segs = some T
  | _, .alias i, _, _, h => aliasPath_wt hwt i h
  | _, .loc l, _, _, h => Loc.resolve_wt hwt l h

/-- `alice.age` resolves to `(alice, [age])`, which the layout types `uint`. -/
theorem Loc.resolve_wt (hwt : RunWT C H σ) :
    ∀ {T : Ty} (l : Loc C Γ T) {r : Name} {segs : List Seg},
      l.resolve σ = .ok (r, segs) → C.layout.tyAt r segs = some T
  | _, .root r' hr, r, segs, h => by
    cases h
    exact Contract.layout_tyAt_root hr
  | _, .field b f hf, r, segs, h => by
    obtain ⟨⟨r0, s0⟩, h0, h⟩ := bind_ok_inv h
    cases h
    exact tyAt_append_seg (SPath.resolve_wt hwt b h0) hf
  | _, .index it b i, r, segs, h => by
    obtain ⟨⟨r0, s0⟩, h0, h⟩ := bind_ok_inv h
    obtain ⟨k, _, h⟩ := bind_ok_inv h
    obtain ⟨iv, _, h⟩ := bind_ok_inv h
    bind_inv h
    cases h
    have hb := SPath.resolve_wt hwt b h0
    cases it with
    | map => exact tyAt_append_seg hb rfl
    | arr a => cases a <;> exact tyAt_append_seg hb rfl

end

mutual

/-- A memory path holds a slot of its type: `m`, with `m : Person memory`,
an identity the store typing claims at `Person`. -/
theorem MPath.mval_wt (hwt : RunWT C H σ) :
    ∀ {T : Ty} (p : MPath C Γ T) {mv : MVal}, p.mval σ = .ok mv → MVal.hasTyH H mv T = true
  | _, .var i _, mv, h => by
    simp only [MPath.mval, memRef] at h
    split at h
    · cases h; exact hwt.env.get i _ ‹_›
    · cases h
  | _, .loc l, mv, h => MLoc.read_wt hwt l h

/-- `m.age` reads a slot the heap types `uint`. -/
theorem MLoc.read_wt (hwt : RunWT C H σ) :
    ∀ {T : Ty} (l : MLoc C Γ T) {mv : MVal}, l.read σ = .ok mv → MVal.hasTyH H mv T = true
  | _, @MLoc.field _ _ s _ b f hf, mv, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    obtain ⟨obj, hobj, hty⟩ := heapTypedB_obj hwt.glob.heap hb
    obtain ⟨o, ho, h⟩ := bind_ok_inv h
    simp only [Semantics.State.getObj, hobj] at ho
    cases ho
    cases obj with
    | struct fields =>
      simp only at h
      split at h
      · rename_i v hv
        cases h
        obtain ⟨ty, hdef, hv⟩ := mHasTyHFields_lookup (by simpa [MObj.hasTyH] using hty) hv
        have : ty = _ := Option.some.inj (hdef.symm.trans hf)
        subst this
        exact hv
      · exact nomatch h
    | array _ => exact nomatch h
  | _, @MLoc.index _ _ _ E a b i, mv, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    obtain ⟨obj, hobj, hty⟩ := heapTypedB_obj hwt.glob.heap hb
    obtain ⟨elems, fx, rfl, hel⟩ := MObj.hasTyH_arrElem a.arrElem hty
    bind_inv h
    obtain ⟨iv, _, h⟩ := bind_ok_inv h
    obtain ⟨o, ho, h⟩ := bind_ok_inv h
    simp only [Semantics.State.getObj, hobj] at ho
    cases ho
    simp only at h
    split at h
    · cases h
      exact mHasTyHElems_mem hel (List.get_mem _ _)
    · exact nomatch h

end

/-- A value evaluates to a value of its type: `alice.age + 1` to a number,
`x < y` to a boolean. -/
theorem Val.eval_wt (hwt : RunWT C H σ) :
    ∀ {p : PrimTy} (v : Val C Γ p) {w : Value}, v.eval σ = .ok w →
      (Value.toSVal w).hasTy (.prim p) = true
  | _, .simple s, w, h => Simple.eval_wt hwt h
  | _, .read l, w, h => by
    obtain ⟨⟨r, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
    exact SVal.asValue_hasTy
      (findStorage_hasTy hwt.glob.storage (Loc.resolve_wt hwt l hr) hsv) h
  | _, .binop op hacc hq a b, w, h => by
    obtain ⟨lv, _, h⟩ := bind_ok_inv h
    exact evalBinop_wt hacc hq h
  | _, .unop op hacc hq a, w, h => by
    obtain ⟨av, _, h⟩ := bind_ok_inv h
    exact evalUnop_wt hacc hq h
  | _, .ternary c a b, w, h => by
    obtain ⟨cv, _, h⟩ := bind_ok_inv h
    unfold pickBranch at h
    split at h
    · exact Val.eval_wt hwt a h
    · exact Val.eval_wt hwt b h
    · exact nomatch h
  | _, .readMem l, w, h => by
    obtain ⟨mv, hmv, h⟩ := bind_ok_inv h
    exact MVal.asValue_hasTy (MLoc.read_wt hwt l hmv) h
  | _, .len b hp, w, h => by
    subst hp
    bind_inv h
    obtain ⟨sv, _, h⟩ := bind_ok_inv h
    split at h
    · cases h; rfl
    all_goals exact nomatch h
  | _, .mlen b hp, w, h => by
    subst hp
    iterate 2 bind_inv h
    obtain ⟨o, _, h⟩ := bind_ok_inv h
    split at h
    · cases h; rfl
    all_goals exact nomatch h

end Eval

/-! ## Return variables -/

section Effects

variable {H : HeapTy}

/-- The return variables at their defaults are of their types. -/
theorem Binders.defaults_wt : {ρ : Ctx} → (bs : Binders ρ) →
    Env.All (LTy.WT C H) (Binders.defaults (C := C) bs)
  | _, .nil => trivial
  | _, .snoc bs p _ => ⟨LTy.WT.default p, Binders.defaults_wt bs⟩

end Effects

/-! ## Where a run starts -/

/-- A contract starts well-typed: each root at its type's default, no
locals, an empty heap. -/
theorem RunWT.init {σ : EState C []} (hnd : nodupKeysB C.vars = true)
    (hst : σ.storage = C.initStorage) (hheap : σ.heap = []) : RunWT C [] σ :=
  ⟨StateWT.init (σ := σ.glob) hnd hst hheap, trivial⟩

end Solidity
