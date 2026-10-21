import Solidity.Calculus.Logic
import Solidity.Calculus.Lower

/-!
# A lowered expression evaluates as the typed run evaluates

The typed run's evaluators (`Semantics/Run.lean`: `Val.evalT`,
`Loc.resolveT`, `MLoc.addrT`, …) against the terms the rules lower their
expressions to (`Calculus/Lower.lean`), read on the typed state
(`Tm.eval`, `Calculus/TermEval.lean`): the same typed value, `none` where
the run reverts (`TRes.AgreesO`).  Nothing is erased (W9.8.3): a term reads
the typed operations the run does, so each lemma is one induction on the
syntax; these are what the update arms' soundness
(`Calculus/SoundArms.lean`) composes.
-/

namespace Solidity

variable {C : Contract}

/-! ## A typed result against a term's reading -/

/-- A typed result against an `Option` reading: the value through `f`,
`none` for a `revert`; a `panic` against nothing; a `diverge` or an
`exhausted` against anything. -/
def TRes.AgreesO {α β : Type} (f : α → β) : TRes α → Option β → Prop
  | .ok a, u => u = some (f a)
  | .error .revert, u => u = none
  | .error .panic, _ => False
  | .error .diverge, _ => True
  | .error .exhausted, _ => True

namespace TRes.AgreesO

variable {α β γ δ : Type} {f : α → β} {g : γ → δ}

theorem pure (a : α) : TRes.AgreesO f (.ok a) (some (f a)) := rfl

theorem bind {t : TRes α} {u : Option β} (h : TRes.AgreesO f t u) {k : α → TRes γ}
    {k' : β → Option δ} (hk : ∀ a, TRes.AgreesO g (k a) (k' (f a))) :
    TRes.AgreesO g (t >>= k) (u.bind k') := by
  match t, h with
  | .ok a, h => subst h; exact hk a
  | .error .revert, h => subst h; rfl
  | .error .diverge, _ => trivial
  | .error .exhausted, _ => trivial

theorem map {t : TRes α} {u : Option β} (h : TRes.AgreesO f t u) {k : α → γ} {k' : β → δ}
    (hk : ∀ a, k' (f a) = g (k a)) : TRes.AgreesO g (k <$> t) (u.map k') := by
  match t, h with
  | .ok a, h => subst h; exact congrArg some (hk a)
  | .error .revert, h => subst h; rfl
  | .error .diverge, _ => trivial
  | .error .exhausted, _ => trivial

theorem ofOpt (x : Option α) : TRes.AgreesO f (TRes.ofOpt x) (x.map f) := by
  cases x <;> rfl

theorem ofOpt_id (x : Option α) : TRes.AgreesO id (TRes.ofOpt x) x := by
  cases x <;> rfl

theorem of_eq {a : α} {u : Option β} (h : u = some (f a)) : TRes.AgreesO f (.ok a) u := h

theorem congr {f' : α → β} {t : TRes α} {u : Option β} (h : TRes.AgreesO f t u)
    (hf : ∀ a, f a = f' a) : TRes.AgreesO f' t u := by
  match t, h with
  | .ok a, h => subst h; exact congrArg some (hf a)
  | .error .revert, h => exact h
  | .error .diverge, _ => trivial
  | .error .exhausted, _ => trivial

end TRes.AgreesO

/-! ## Addresses -/

/-- A typed address with its identity bare (`MAddrT`). -/
def MAddr.toT {H : HTy} {T : Ty} : MAddr H T → MAddrT T
  | .field r h => .field r.id h
  | .index r a i => .index r.id a i

theorem HRef.ofId?_id {H : HTy} {R : RefTy} (r : HRef H R) : HRef.ofId? H R r.id = some r := by
  unfold HRef.ofId?
  rw [dif_pos r.get?]

/-- A bare address resolves back in its heap typing. -/
theorem MAddr.resolve_toT {H : HTy} {T : Ty} (a : MAddr H T) : a.toT.resolve H = some a := by
  rw [MAddrT.resolve_eq_resolveM]
  cases a <;> simp only [MAddr.toT, MAddrT.resolveM, HRef.ofId?_id, Option.map_some]

/-! ## Expressions -/

variable {Γ : Ctx} (σ : State C Γ)

theorem Simple.lower_evalT {p : PrimTy} (s : Simple C Γ p) :
    s.lower.eval σ = some (s.evalT σ) := by
  cases s with
  | lit n h => rfl
  | bool b => rfl
  | «local» i => rfl
  | env k hp => subst hp; rfl

/-- A simple value denotes its typed value. -/
theorem Simple.denote_lowerT {p : PrimTy} (s : Simple C Γ p) :
    s.lower.denote σ = some (s.evalT σ) :=
  Tm.denote_eval σ s.lower _ (Simple.lower_evalT σ s)

mutual

theorem SPath.lower_resolveT : {T : Ty} → (b : SPath C Γ T) →
    TRes.AgreesO id (b.resolveT σ) (b.lower.eval σ)
  | _, .alias i => by
    show TRes.AgreesO id
      (match (TEnv.get i σ.env : Option (SRef C _)) with
        | some r => .ok r
        | none => .error .revert)
      (TEnv.get i σ.env)
    cases (TEnv.get i σ.env : Option (SRef C _)) <;> rfl
  | _, .loc l => Loc.lower_resolveT l

theorem Loc.lower_resolveT : {T : Ty} → (l : Loc C Γ T) →
    TRes.AgreesO id (l.resolveT σ) (l.lower.eval σ)
  | _, .root r h => rfl
  | _, .field b f h => by
    show TRes.AgreesO id ((fun r => r.field h) <$> b.resolveT σ) ((b.lower.eval σ).map (·.field h))
    exact TRes.AgreesO.map (SPath.lower_resolveT b) fun _ => rfl
  | _, .index (k := k) it b i => by
    show TRes.AgreesO id _ ((Tm.app2 (.at it) b.lower i.lower).eval σ)
    rw [Tm.eval_app2, Op2.eval_eq_evalM]
    show TRes.AgreesO id _ ((b.lower.eval σ).bind fun r =>
      (i.lower.eval σ).bind fun y => σ.storage.atT it r y)
    refine TRes.AgreesO.bind (SPath.lower_resolveT b) fun r => ?_
    refine TRes.AgreesO.bind (Val.lower_evalT i) fun x => ?_
    show TRes.AgreesO id (TRes.ofOpt (σ.storage.checkIndex r it x) >>= fun _ =>
      pure (r.index it x)) (σ.storage.atT it r x)
    simp only [Storage.atT]
    cases σ.storage.checkIndex r it x <;> rfl

theorem MPath.lower_mvalT : {R : RefTy} → (b : MPath C Γ (.ref R)) →
    TRes.AgreesO (fun r : HRef σ.H R => r.id) (b.mvalT σ) (b.lower.eval σ)
  | _, .var i _ => by
    show TRes.AgreesO _
      (match (TEnv.get i σ.env : Option (HRef σ.H _)) with
        | some r => .ok r
        | none => .error .revert)
      ((TEnv.get i σ.env : Option (HRef σ.H _)).map (·.id))
    cases (TEnv.get i σ.env : Option (HRef σ.H _)) <;> rfl
  | _, .loc l => by
    show TRes.AgreesO _ (do TRes.ofOpt (σ.heap.readAddr (← l.addrT σ)))
      ((Tm.app2 .iread (.app0 .memory) l.lower).eval σ)
    rw [Tm.eval_app2, Op2.eval_eq_evalM]
    show TRes.AgreesO _ _ ((l.lower.eval σ).bind fun a =>
      ((σ.glob.memT.readT a).bind fun r => some (HRef.id r)))
    refine TRes.AgreesO.bind (MLoc.lower_addrT l) fun a => ?_
    simp only [Grown.readT, State.memT, MAddr.resolve_toT, Option.bind_eq_bind, Option.bind_some]
    show TRes.AgreesO _ (TRes.ofOpt (σ.heap.readAddr a)) ((σ.heap.readAddr a).bind fun r => some r.id)
    cases σ.heap.readAddr a <;> rfl

theorem MLoc.lower_addrT : {T : Ty} → (l : MLoc C Γ T) →
    TRes.AgreesO MAddr.toT (l.addrT σ) (l.lower.eval σ)
  | _, .field b _ h => by
    show TRes.AgreesO _ (do let r ← b.mvalT σ; pure (MAddr.field r h))
      ((b.lower.eval σ).map fun id => MAddrT.field id h)
    exact TRes.AgreesO.map (MPath.lower_mvalT b) fun _ => rfl
  | _, .index a b i => by
    show TRes.AgreesO _ (do let r ← b.mvalT σ; let k ← i.evalT σ; pure (MAddr.index r a k))
      ((b.lower.eval σ).bind fun x => (i.lower.eval σ).bind fun y => some (MAddrT.index x a y))
    refine TRes.AgreesO.bind (MPath.lower_mvalT b) fun _ => ?_
    exact TRes.AgreesO.bind (Val.lower_evalT i) fun _ => rfl

theorem Val.lower_evalT : {p : PrimTy} → (v : Val C Γ p) →
    TRes.AgreesO id (v.evalT σ) (v.lower.eval σ)
  | _, .simple s => TRes.AgreesO.of_eq (Simple.lower_evalT σ s)
  | _, .read l => by
    show TRes.AgreesO _ (do
        let r ← l.resolveT σ
        let v ← TRes.ofOpt (σ.storage.find r)
        pure v.view)
      ((l.lower.eval σ).bind fun r => (σ.storage.find r).bind fun v => some v.view)
    refine TRes.AgreesO.bind (Loc.lower_resolveT l) fun r => ?_
    exact TRes.AgreesO.bind (TRes.AgreesO.ofOpt_id _) fun _ => TRes.AgreesO.pure _
  | _, .binop op h hq a b => by
    subst hq
    show TRes.AgreesO _ _ ((a.lower.eval σ).bind fun x => binopT op h x (b.lower.eval σ))
    refine TRes.AgreesO.bind (Val.lower_evalT a) fun x => ?_
    show TRes.AgreesO _ (match op.shortT x with
      | some y => .ok y
      | none => do
        let y ← b.evalT σ
        TRes.ofOpt (op.evalT h x y)) (binopT op h x (b.lower.eval σ))
    unfold binopT
    cases op.shortT x with
    | some y => rfl
    | none =>
      refine TRes.AgreesO.bind (Val.lower_evalT b) fun y => ?_
      exact TRes.AgreesO.ofOpt_id _
  | _, .unop op h hq a => by
    subst hq
    show TRes.AgreesO _ _ ((a.lower.eval σ).bind (op.evalT h))
    refine TRes.AgreesO.bind (Val.lower_evalT a) fun x => ?_
    show TRes.AgreesO _ (TRes.ofOpt (op.evalT h x)) _
    exact TRes.AgreesO.ofOpt_id _
  | _, .ternary c a b => by
    show TRes.AgreesO _ _ ((c.lower.eval σ).bind fun x => cond x (a.lower.eval σ) (b.lower.eval σ))
    refine TRes.AgreesO.bind (Val.lower_evalT c) fun x => ?_
    cases x
    · exact Val.lower_evalT b
    · exact Val.lower_evalT a
  | _, .readMem l => by
    show TRes.AgreesO _ (do TRes.ofOpt (σ.heap.readAddr (← l.addrT σ)))
      ((l.lower.eval σ).bind fun a => σ.glob.memT.readT a)
    refine TRes.AgreesO.bind (MLoc.lower_addrT l) fun a => ?_
    simp only [Grown.readT, State.memT, MAddr.resolve_toT, Option.bind_eq_bind, Option.bind_some]
    exact TRes.AgreesO.ofOpt_id _
  | _, .len b hp => by
    subst hp
    show TRes.AgreesO _ (do
        let r ← b.resolveT σ
        let n ← TRes.ofOpt (σ.storage.len r)
        pure n)
      ((b.lower.eval σ).bind fun r => σ.storage.len r)
    refine TRes.AgreesO.bind (SPath.lower_resolveT b) fun r => ?_
    show TRes.AgreesO id (TRes.ofOpt (σ.storage.len r) >>= fun n => pure n) (σ.storage.len r)
    cases σ.storage.len r <;> rfl
  | _, .mlen b hp => by
    subst hp
    show TRes.AgreesO _ (do let r ← b.mvalT σ; pure (σ.heap.lenU r))
      ((b.lower.eval σ).bind fun id =>
        (HRef.ofId? σ.H (.array _) id).bind fun r => some (σ.heap.lenU r))
    refine TRes.AgreesO.bind (MPath.lower_mvalT b) fun r => ?_
    simp only [HRef.ofId?_id, Option.bind_some]
    rfl
  | _, .keccak b hp => by
    subst hp
    show TRes.AgreesO _ (do let r ← b.mvalT σ; pure (σ.heap.keccak r))
      ((b.lower.eval σ).bind fun id =>
        some (((HRef.ofId? σ.H _ id).map σ.heap.keccak).getD (PrimTy.dflt .uint)))
    refine TRes.AgreesO.bind (MPath.lower_mvalT b) fun r => ?_
    simp only [HRef.ofId?_id, Option.map_some, Option.getD_some]
    rfl

  | _, .modular op a b k => by
    show TRes.AgreesO id (do
      let x ← a.evalT σ
      let y ← b.evalT σ
      let m ← k.evalT σ
      TRes.ofOpt (op.evalT x y m)) (do
      let x ← a.lower.eval σ
      let y ← b.lower.eval σ
      let m ← k.lower.eval σ
      op.evalT x y m)
    exact TRes.AgreesO.bind (Val.lower_evalT a) fun _ =>
      TRes.AgreesO.bind (Val.lower_evalT b) fun _ =>
        TRes.AgreesO.bind (Val.lower_evalT k) fun _ => TRes.AgreesO.ofOpt_id _

end

/-- A storage write's source. -/
theorem Src.lower_valueT {T : Ty} (r : Src C Γ T) :
    TRes.AgreesO id (r.valueT σ) (r.lower.eval σ) := by
  cases r with
  | val v =>
    show TRes.AgreesO _ (do pure (SVal.prim (← v.evalT σ))) ((v.lower.eval σ).map SVal.prim)
    exact TRes.AgreesO.map (Val.lower_evalT σ v) (k' := SVal.prim) fun _ => rfl
  | copy p _ =>
    show TRes.AgreesO _ (do let r ← p.resolveT σ; TRes.ofOpt (σ.storage.find r))
      ((p.lower.eval σ).bind fun r => σ.storage.find r)
    exact TRes.AgreesO.bind (SPath.lower_resolveT σ p) fun r => TRes.AgreesO.ofOpt_id _
  | copyMem p =>
    show TRes.AgreesO _ (do pure (MVal.copyMToSt σ.heap (← p.mvalT σ)))
      ((Tm.app2 .copyMem (.app0 .memory) p.lower).eval σ)
    rw [Tm.eval_app2, Op2.eval_eq_evalM]
    simp only [Tm.eval_app0, Op0.eval, State.memT, Option.bind_some]
    refine TRes.AgreesO.bind (MPath.lower_mvalT σ p) fun mv => ?_
    simp only [HRef.ofId?_id]
    rfl
  | fixedCopy p shape _ =>
    show TRes.AgreesO id (do let r ← p.resolveT σ; let v ← TRes.ofOpt (σ.storage.find r); pure (shape.apply v))
      (((p.lower.eval σ).bind fun r => σ.storage.find r).map shape.apply)
    rw [Option.map_bind]
    refine TRes.AgreesO.bind (SPath.lower_resolveT σ p) fun r => ?_
    exact TRes.AgreesO.map (TRes.AgreesO.ofOpt_id (σ.storage.find r))
      (g := id) (k := shape.apply) (k' := shape.apply) fun _ => rfl

/-- A memory slot as a memory write writes it: a word, or an identity. -/
def MVal.toT {H : HTy} : (T : Ty) → MVal H T → MvT T
  | .prim _, v => v
  | .ref _, r => (r : HRef H _).id

/-- A memory write's source. -/
theorem MSrc.lower_mvalT {T : Ty} (r : MSrc C Γ T) :
    TRes.AgreesO (MVal.toT T) (r.mvalT σ) (r.lower.eval σ) := by
  cases r with
  | val v => exact Val.lower_evalT σ v
  | ref p => exact MPath.lower_mvalT σ p

end Solidity
