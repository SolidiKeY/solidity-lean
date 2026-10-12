import Solidity.Calculus.Logic
import Solidity.Calculus.Lower
import Solidity.Semantics.TypedErase

/-!
# A lowered expression reads what the typed run evaluates

The typed run's evaluators (`Semantics/Run.lean`: `Val.evalT`,
`Loc.resolveT`, `MLoc.addrT`, …) against the terms the rules lower their
expressions to (`Calculus/Lower.lean`), read on the typed state
(`Tm.evalT`, `Calculus/Lands.lean`): the same value erased, the same
`revert` or `panic` (`TRes.Agrees`).  One lemma per evaluator, by
induction on the syntax, from the value-level erasure lemmas
(`Semantics/StorageErase.lean`, `Semantics/HeapErase.lean`); these are what
the update arms' soundness (`Calculus/SoundArms.lean`) composes.
-/

namespace Solidity
open Solidity (Op0 Op3 evalBinop)
open Semantics (Value Seg Res)

variable {C : Contract} {Γ : Ctx} (σ : State C Γ)

theorem Simple.lower_evalT {p : PrimTy} (s : Simple C Γ p) :
    s.lower.evalT σ = .ok (PrimTy.erase (s.evalT σ)) := by
  cases s with
  | lit n h => cases p <;> first | rfl | simp only [PrimTy.inRange, Bool.false_eq_true] at h
  | bool b => rfl
  | «local» i => rfl
  | env k hp => subst hp; cases k <;> rfl

/-- A simple value denotes its typed value. -/
theorem Simple.denote_lowerT {p : PrimTy} (s : Simple C Γ p) :
    s.lower.denoteT σ = .prim (PrimTy.erase (s.evalT σ)) := by
  cases s with
  | lit n h => cases p <;> first | rfl | simp only [PrimTy.inRange, Bool.false_eq_true] at h
  | bool b => rfl
  | «local» i => rfl
  | env k hp => subst hp; cases k <;> rfl

/-- The slot at an address, on the erased global part (`Update.lean`'s
`readAddr`). -/
theorem readAddr_erase {T : Ty} (a : MAddr σ.H T) :
    readAddr σ.globE a.erase = toRes (MVal.erase T) (σ.heap.readAddr a) := by
  cases a with
  | field r h => exact Heap.readField_erase (σ := σ.globE) rfl r h
  | index r a i => exact Heap.readIndex_erase (σ := σ.globE) rfl r a i

mutual

theorem SPath.lower_resolveT : {T : Ty} → (b : SPath C Γ T) →
    TRes.Agrees SRef.erase (b.resolveT σ) (b.lower.evalT σ)
  | _, .alias i => by
    show TRes.Agrees SRef.erase
      (match (TEnv.get i σ.env : Option (SRef C _)) with
        | some r => .ok r
        | none => .error .revert)
      (σ.aliasPathT i)
    unfold State.aliasPathT
    cases (TEnv.get i σ.env : Option (SRef C _)) <;> rfl
  | _, .loc l => Loc.lower_resolveT l

theorem Loc.lower_resolveT : {T : Ty} → (l : Loc C Γ T) →
    TRes.Agrees SRef.erase (l.resolveT σ) (l.lower.evalT σ)
  | _, .root r h => rfl
  | _, .field b f h => by
    refine TRes.Agrees.bind (SPath.lower_resolveT b) fun r => ?_
    exact TRes.Agrees.of_eq (congrArg Except.ok (SRef.erase_field r h).symm)
  | _, .index (k := k) it b i => by
    refine TRes.Agrees.bind (SPath.lower_resolveT b) fun r => ?_
    show TRes.Agrees SRef.erase
      (do
        let k ← i.evalT σ
        TRes.ofOpt (σ.storage.checkIndex r it (PrimTy.key k))
        pure (r.atKey it k))
      (do
        let i ← (← (Tm.keyAt k i.lower).evalT σ).asInt
        σ.globE.checkIndex r.root r.path.erase i
        pure (r.root, r.path.erase ++ [.at i]))
    have hk : ∀ {β : Type} (g : Int → Res β),
        ((Tm.keyAt k i.lower).evalT σ >>= fun v => v.asInt >>= g) =
          (i.lower.evalT σ >>= fun v => v.keyAt k >>= g) := fun g => by
      cases k with
      | uint | int => rfl
      | bool =>
        simp only [Tm.keyAt, Tm.evalT, Op3.eval, Op0.eval]
        cases i.lower.evalT σ with
        | error _ => rfl
        | ok v => cases v with
          | int _ => rfl
          | bool b => cases b <;> rfl
    rw [hk]
    refine TRes.Agrees.bind (Val.lower_evalT i) fun x => ?_
    rw [PrimTy.keyAt_erase_key, ok_bind,
      Storage.checkIndex_erase (σ := σ.globE) rfl r it]
    refine TRes.Agrees.bind (TRes.Agrees.ofOpt _) fun _ => ?_
    exact TRes.Agrees.of_eq (congrArg Except.ok (SRef.erase_index r it _).symm)

theorem MPath.lower_mvalT : {R : RefTy} → (b : MPath C Γ (.ref R)) →
    TRes.Agrees (fun r : HRef σ.H R => r.id) (b.mvalT σ) (b.lower.evalT σ)
  | _, .var i _ => by
    simp only [MPath.mvalT, MPath.lower, Tm.evalT, State.memRefT]
    cases (TEnv.get i σ.env : Option (HRef σ.H _)) <;> rfl
  | _, .loc l => by
    show TRes.Agrees _ (do TRes.ofOpt (σ.heap.readAddr (← l.addrT σ)))
      (do
        let τ ← pure σ.globE
        (← readAddr τ (← l.lower.evalT σ)).asRef)
    simp only [pure_bind]
    refine TRes.Agrees.bind (MLoc.lower_addrT l) fun a => ?_
    rw [readAddr_erase]
    cases σ.heap.readAddr a <;> rfl

theorem MLoc.lower_addrT : {T : Ty} → (l : MLoc C Γ T) →
    TRes.Agrees MAddr.erase (l.addrT σ) (l.lower.evalT σ)
  | _, .field b f _ => by
    show TRes.Agrees _ (do let r ← b.mvalT σ; pure (MAddr.field r _))
      (do pure (Semantics.Addr.memoryField (← b.lower.evalT σ) f))
    exact TRes.Agrees.bind (MPath.lower_mvalT b) fun _ => rfl
  | _, .index a b i => by
    show TRes.Agrees _ (do let r ← b.mvalT σ; let k ← i.evalT σ; pure (MAddr.index r a k.1))
      (do
        let id ← b.lower.evalT σ
        pure (Semantics.Addr.memoryIndex id (← (← i.lower.evalT σ).asInt)))
    refine TRes.Agrees.bind (MPath.lower_mvalT b) fun _ => ?_
    exact TRes.Agrees.bind (Val.lower_evalT i) fun _ => rfl

theorem Val.lower_evalT : {p : PrimTy} → (v : Val C Γ p) →
    TRes.Agrees PrimTy.erase (v.evalT σ) (v.lower.evalT σ)
  | _, .simple s => TRes.Agrees.of_eq (Simple.lower_evalT σ s)
  | _, .read l => by
    show TRes.Agrees _ (do
        let r ← l.resolveT σ
        let v ← TRes.ofOpt (σ.storage.find r)
        pure (SVal.view v))
      (do
        let τ ← pure σ.globE
        let (r, segs) ← l.lower.evalT σ
        (← τ.findStorage r segs).asValue)
    simp only [pure_bind]
    refine TRes.Agrees.bind (Loc.lower_resolveT l) fun r => ?_
    show TRes.Agrees _ (do let v ← TRes.ofOpt (σ.storage.find r); pure (SVal.view v))
      (do let v ← σ.globE.findStorage r.root r.path.erase; v.asValue)
    rw [Storage.findStorage_erase (σ := σ.globE) rfl r]
    exact TRes.Agrees.bind (TRes.Agrees.ofOpt _) fun v =>
      TRes.Agrees.of_eq (SVal.asValue_erase_prim v)
  | _, .binop op h hq a b => by
    subst hq
    show TRes.Agrees _ _ (do evalBinop op _ (← a.lower.evalT σ) (b.lower.evalT σ))
    refine TRes.Agrees.bind (Val.lower_evalT a) fun x => ?_
    show TRes.Agrees _ (match op.shortT x with
      | some y => pure y
      | none => do
        let y ← b.evalT σ
        TRes.ofOpt (op.evalT x y)) (evalBinop op _ (PrimTy.erase x) (b.lower.evalT σ))
    cases hs : op.shortT x with
    | some y => rw [evalBinop_short hs]; rfl
    | none =>
      rw [evalBinop_long hs]
      refine TRes.Agrees.bind (Val.lower_evalT b) fun y => ?_
      rw [BinOp.evalT_erase op h x y]
      exact TRes.Agrees.ofOpt _
  | _, .unop op h hq a => by
    subst hq
    show TRes.Agrees _ _
      (do unopCheck op _ (← Semantics.applyUnOp op (← a.lower.evalT σ)))
    refine TRes.Agrees.bind (Val.lower_evalT a) fun x => ?_
    show TRes.Agrees _ (TRes.ofOpt (op.evalT x)) _
    rw [UnOp.evalT_erase op h x]
    exact TRes.Agrees.ofOpt _
  | _, .ternary c a b => by
    show TRes.Agrees _ _ (do
      pickBranch (← c.lower.evalT σ) (a.lower.evalT σ)
        (b.lower.evalT σ))
    refine TRes.Agrees.bind (Val.lower_evalT c) fun x => ?_
    cases x
    · exact Val.lower_evalT b
    · exact Val.lower_evalT a
  | _, .readMem l => by
    show TRes.Agrees _ (do TRes.ofOpt (σ.heap.readAddr (← l.addrT σ)))
      (do
        let τ ← pure σ.globE
        (← readAddr τ (← l.lower.evalT σ)).asValue)
    simp only [pure_bind]
    refine TRes.Agrees.bind (MLoc.lower_addrT l) fun a => ?_
    rw [readAddr_erase]
    cases σ.heap.readAddr a with
    | none => rfl
    | some x => exact MVal.asValue_erase_prim x
  | _, .len b hp => by
    subst hp
    show TRes.Agrees _ _ (do
      let τ ← pure σ.globE
      let (r, segs) ← b.lower.evalT σ
      arrayLen τ r segs)
    simp only [pure_bind]
    refine TRes.Agrees.bind (SPath.lower_resolveT b) fun r => ?_
    show TRes.Agrees _ (do let n ← TRes.ofOpt (σ.storage.len r); pure n)
      (arrayLen σ.globE r.root r.path.erase)
    rw [Storage.arrayLen_erase (σ := σ.globE) rfl r]
    cases σ.storage.len r <;> rfl
  | _, .mlen b hp => by
    subst hp
    show TRes.Agrees _ _ (do
      let τ ← pure σ.globE
      memArrayLen τ (← b.lower.evalT σ))
    simp only [pure_bind]
    refine TRes.Agrees.bind (MPath.lower_mvalT b) fun r => ?_
    show TRes.Agrees _ (.ok (σ.heap.lenU r)) (memArrayLen σ.globE r.id)
    rw [Heap.memArrayLen_erase (σ := σ.globE) rfl r .dyn]
    rfl

end

/-- A storage write's source. -/
theorem Src.lower_valueT {T : Ty} (r : Src C Γ T) :
    TRes.Agrees SVal.erase (r.valueT σ) (r.lower.evalT σ) := by
  cases r with
  | val v =>
    show TRes.Agrees _ _ (do pure (← v.lower.evalT σ).toSVal)
    exact TRes.Agrees.bind (Val.lower_evalT σ v) fun x =>
      TRes.Agrees.of_eq (congrArg Except.ok (Value.toSVal_erase x))
  | copy p _ =>
    show TRes.Agrees _ _ (do
      let τ ← pure σ.globE
      let (r, segs) ← p.lower.evalT σ
      τ.findStorage r segs)
    simp only [pure_bind]
    refine TRes.Agrees.bind (SPath.lower_resolveT σ p) fun r => ?_
    show TRes.Agrees _ (TRes.ofOpt (σ.storage.find r))
      (σ.globE.findStorage r.root r.path.erase)
    rw [Storage.findStorage_erase (σ := σ.globE) rfl r]
    exact TRes.Agrees.ofOpt _

/-- A memory write's source. -/
theorem MSrc.lower_mvalT {T : Ty} (r : MSrc C Γ T) :
    TRes.Agrees (MVal.erase T) (r.mvalT σ) (r.lower.evalT σ) := by
  cases r with
  | val v =>
    show TRes.Agrees _ _ (do pure (← v.lower.evalT σ).toMVal)
    exact TRes.Agrees.bind_pure (Val.lower_evalT σ v) fun x =>
      congrArg Except.ok (Value.toMVal_erase x)
  | ref p =>
    show TRes.Agrees _ _ (do pure (Semantics.MVal.ref (← p.lower.evalT σ)))
    exact TRes.Agrees.bind_pure (MPath.lower_mvalT σ p) fun _ => rfl

end Solidity
