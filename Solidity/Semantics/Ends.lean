import Solidity.Semantics.Run

/-!
# Typed results that end

A typed result that does not diverge (`TRes.NoDiv`), and one that neither
diverges nor is exhausted (`TRes.Ends`): it ends, reverts or panics.  Every
evaluator, and every write but a push, ends (`Val.evalT_ends` and its kin):
a failed read, a bad index, an overflow revert (`TRes.ofOpt`).  A push onto
`2^256 - 1` elements is exhausted (`TRun.push`, `Storage.full`, decision
15), and a loop with no last iteration diverges.  The update rules'
soundness asks the first (`Calculus/SoundArms.lean`: an update does
not diverge under the diamond), the storage builder the second
(`Typing/Constructibility.lean`: the builder's typed run ends).
-/

namespace Solidity

variable {C : Contract}

/-! ## Results that do not diverge -/

/-- A typed result that does not diverge. -/
def TRes.NoDiv {α : Type} (t : TRes α) : Prop := t ≠ .error .diverge

theorem TRes.NoDiv.bind {α γ : Type} {t : TRes α} (h : t.NoDiv) {k : α → TRes γ}
    (hk : ∀ a, (k a).NoDiv) : (t >>= k).NoDiv := by
  match t with
  | .ok a => exact hk a
  | .error e => exact fun h' => h (by cases h'; rfl)

theorem TRes.NoDiv.map {α γ : Type} {t : TRes α} (h : t.NoDiv) (k : α → γ) :
    TRes.NoDiv (t.map k) := by
  match t with
  | .ok _ => exact fun h' => nomatch h'
  | .error e => exact fun h' => h (by cases (h' : Except.error e = .error .diverge); rfl)

theorem TRes.NoDiv.ofOpt {α : Type} (x : Option α) : (TRes.ofOpt x).NoDiv := by
  cases x <;> exact fun h => nomatch h

theorem TRes.NoDiv.ok {α : Type} (a : α) : TRes.NoDiv (Except.ok a : TRes α) :=
  fun h => nomatch h

/-- A typed result that neither diverges nor is exhausted: it ends, reverts
or panics. -/
def TRes.Ends {α : Type} (t : TRes α) : Prop := t ≠ .error .diverge ∧ t ≠ .error .exhausted

theorem TRes.Ends.bind {α γ : Type} {t : TRes α} (h : t.Ends) {k : α → TRes γ}
    (hk : ∀ a, (k a).Ends) : (t >>= k).Ends := by
  match t with
  | .ok a => exact hk a
  | .error e => exact ⟨fun h' => h.1 (by cases h'; rfl), fun h' => h.2 (by cases h'; rfl)⟩

theorem TRes.Ends.map {α γ : Type} {t : TRes α} (h : t.Ends) (k : α → γ) :
    TRes.Ends (t.map k) := by
  match t with
  | .ok _ => exact ⟨nofun, nofun⟩
  | .error e =>
    exact ⟨fun h' => h.1 (by cases (h' : Except.error e = .error .diverge); rfl),
      fun h' => h.2 (by cases (h' : Except.error e = .error .exhausted); rfl)⟩

theorem TRes.Ends.ofOpt {α : Type} (x : Option α) : (TRes.ofOpt x).Ends := by
  cases x <;> exact ⟨nofun, nofun⟩

theorem TRes.Ends.ok {α : Type} (a : α) : TRes.Ends (Except.ok a : TRes α) :=
  ⟨nofun, nofun⟩

/-! ## Evaluators end

Every evaluator, and every write but a push, neither diverges nor is
exhausted (`TRes.Ends`): a failed read, a bad index, an overflow revert
(`TRes.ofOpt`). -/

section Ends

variable {Γ : Ctx} (σ : State C Γ)

mutual

theorem SPath.resolveT_ends : {T : Ty} → (b : SPath C Γ T) → (b.resolveT σ).Ends
  | _, .alias i => by
    show (match (TEnv.get i σ.env : Option (SRef C _)) with
      | some r => .ok r
      | none => .error .revert : TRes _).Ends
    cases (TEnv.get i σ.env : Option (SRef C _)) <;> exact ⟨nofun, nofun⟩
  | _, .loc l => Loc.resolveT_ends l

theorem Loc.resolveT_ends : {T : Ty} → (l : Loc C Γ T) → (l.resolveT σ).Ends
  | _, .root .. => TRes.Ends.ok _
  | _, .field b _ _ => (SPath.resolveT_ends b).bind fun _ => TRes.Ends.ok _
  | _, .index _ b i => (SPath.resolveT_ends b).bind fun _ => (Val.evalT_ends i).bind fun _ =>
      (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _

theorem MPath.mvalT_ends : {T : Ty} → (b : MPath C Γ T) → (b.mvalT σ).Ends
  | _, .var i _ => by
    show (match (TEnv.get i σ.env : Option (HRef σ.H _)) with
      | some r => .ok r
      | none => .error .revert : TRes _).Ends
    cases (TEnv.get i σ.env : Option (HRef σ.H _)) <;> exact ⟨nofun, nofun⟩
  | _, .loc l => (MLoc.addrT_ends l).bind fun _ => TRes.Ends.ofOpt _

theorem MLoc.addrT_ends : {T : Ty} → (l : MLoc C Γ T) → (l.addrT σ).Ends
  | _, .field b _ _ => (MPath.mvalT_ends b).bind fun _ => TRes.Ends.ok _
  | _, .index _ b i => (MPath.mvalT_ends b).bind fun _ => (Val.evalT_ends i).bind fun _ =>
      TRes.Ends.ok _

theorem Val.evalT_ends : {p : PrimTy} → (v : Val C Γ p) → (v.evalT σ).Ends
  | _, .simple _ => TRes.Ends.ok _
  | _, .read l => (Loc.resolveT_ends l).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ =>
      TRes.Ends.ok _
  | _, .binop op _ hq a b => by
    subst hq
    refine (Val.evalT_ends a).bind fun x => ?_
    show (match op.shortT x with
      | some y => pure y
      | none => do
        let y ← b.evalT σ
        TRes.ofOpt (op.evalT x y) : TRes _).Ends
    cases op.shortT x with
    | some _ => exact TRes.Ends.ok _
    | none => exact (Val.evalT_ends b).bind fun _ => TRes.Ends.ofOpt _
  | _, .unop op _ hq a => by
    subst hq
    exact (Val.evalT_ends a).bind fun _ => TRes.Ends.ofOpt _
  | _, .ternary c a b => (Val.evalT_ends c).bind fun x => by
    cases x
    · exact Val.evalT_ends b
    · exact Val.evalT_ends a
  | _, .readMem l => (MLoc.addrT_ends l).bind fun _ => TRes.Ends.ofOpt _
  | _, .len b hp => by
    subst hp
    exact (SPath.resolveT_ends b).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _
  | _, .mlen b hp => by
    subst hp
    exact (MPath.mvalT_ends b).bind fun _ => TRes.Ends.ok _

end

theorem Src.valueT_ends {T : Ty} : (r : Src C Γ T) → (r.valueT σ).Ends
  | .val v => (Val.evalT_ends σ v).bind fun _ => TRes.Ends.ok _
  | .copy p _ => (SPath.resolveT_ends σ p).bind fun _ => TRes.Ends.ofOpt _

theorem MSrc.mvalT_ends {T : Ty} : (r : MSrc C Γ T) → (r.mvalT σ).Ends
  | .val v => Val.evalT_ends σ v
  | .ref p => MPath.mvalT_ends σ p

theorem MRhs.evalT_ends {R : RefTy} : (r : MRhs C Γ R) → (r.evalT σ).Ends
  | .alias p => (MPath.mvalT_ends σ p).bind fun _ => TRes.Ends.ok _
  | .copy p _ => (SPath.resolveT_ends σ p).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ =>
      TRes.Ends.ok _
  | .newArr .. => TRes.Ends.ok _

theorem opStoreT_ends (op : BinOp) {p : PrimTy} (r : SRef C (.prim p)) (v : p.Denote) :
    (opStoreT σ op r v).Ends :=
  (TRes.Ends.ofOpt _).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ =>
    (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _

theorem opMemT_ends (op : BinOp) {p : PrimTy} (a : MAddr σ.H (.prim p)) (v : p.Denote) :
    (opMemT σ op a v).Ends :=
  (TRes.Ends.ofOpt _).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ =>
    (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _

theorem OpLoc.storeT_ends (op : BinOp) {p : PrimTy} : (l : OpLoc C Γ p) → (v : p.Denote) →
    (l.storeT σ op v).Ends
  | .local _, _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _
  | .root .., _ => opStoreT_ends σ op _ _
  | .field .., _ => (Loc.resolveT_ends σ _).bind fun _ => opStoreT_ends σ op _ _
  | .index .., _ => (Loc.resolveT_ends σ _).bind fun _ => opStoreT_ends σ op _ _
  | .mfield .., _ => (MLoc.addrT_ends σ _).bind fun _ => opMemT_ends σ op _ _
  | .mindex .., _ => (MLoc.addrT_ends σ _).bind fun _ => opMemT_ends σ op _ _

theorem bumpStoreT_ends (op : IncDec) {p : PrimTy} (r : SRef C (.prim p)) :
    (bumpStoreT σ op r).Ends :=
  (TRes.Ends.ofOpt _).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ =>
    (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _

theorem bumpMemT_ends (op : IncDec) {p : PrimTy} (a : MAddr σ.H (.prim p)) :
    (bumpMemT σ op a).Ends :=
  (TRes.Ends.ofOpt _).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ =>
    (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _

theorem OpLoc.bumpT_ends (op : IncDec) {p : PrimTy} : (l : OpLoc C Γ p) → (l.bumpT σ op).Ends
  | .local _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _
  | .root .. => bumpStoreT_ends σ op _
  | .field .. => (Loc.resolveT_ends σ _).bind fun _ => bumpStoreT_ends σ op _
  | .index .. => (Loc.resolveT_ends σ _).bind fun _ => bumpStoreT_ends σ op _
  | .mfield .. => (MLoc.addrT_ends σ _).bind fun _ => bumpMemT_ends σ op _
  | .mindex .. => (MLoc.addrT_ends σ _).bind fun _ => bumpMemT_ends σ op _

end Ends

end Solidity
