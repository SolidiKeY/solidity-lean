import Solidity.Semantics.Run

/-!
# Typed results that end

A typed result that does not diverge (`TRes.NoDiv`), and one that neither
diverges nor is exhausted (`TRes.Ends`): it ends, reverts or panics.  Every
evaluator, and every write but a push, can only halt by a revert
(`TRes.RevertOnly`: a failed read, a bad index, an overflow revert,
`TRes.ofOpt`), so it ends (`Val.evalT_ends` and its kin).  A push onto
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

/-- A typed result that can only halt by a revert: it returns or reverts.
Every evaluator is one, so each of `TRes.Ends` and `TRes.NoPanic`
(`Semantics/NoPanic.lean`) is proved of it once, here. -/
def TRes.RevertOnly {α : Type} (t : TRes α) : Prop := ∀ e, t = .error e → e = .revert

theorem TRes.RevertOnly.ok {α : Type} (a : α) : TRes.RevertOnly (Except.ok a : TRes α) :=
  fun _ h => nomatch h

theorem TRes.RevertOnly.ofOpt {α : Type} (x : Option α) : (TRes.ofOpt x).RevertOnly := by
  cases x <;> exact fun _ h => by cases h <;> rfl

theorem TRes.RevertOnly.bind {α β : Type} {t : TRes α} {k : α → TRes β}
    (h : t.RevertOnly) (hk : ∀ a, (k a).RevertOnly) : (t >>= k).RevertOnly := by
  match t with
  | .ok a => exact hk a
  | .error e => exact fun _ h' => by cases h'; exact h e rfl

theorem TRes.RevertOnly.error {α : Type} {t : TRes α} (h : t.RevertOnly)
    {e : THalt} (he : t = .error e) : e = .revert := h e he

theorem TRes.RevertOnly.ends {α : Type} {t : TRes α} (h : t.RevertOnly) : t.Ends :=
  ⟨(fun h' => nomatch h _ h'), (fun h' => nomatch h _ h')⟩

/-! ## Evaluators only revert

Every evaluator, and every write but a push, returns or reverts
(`TRes.RevertOnly`): a failed read, a bad index, an overflow revert
(`TRes.ofOpt`).  So each ends (`Val.evalT_ends` and its kin) and does not
panic (`Val.evalT_noPanic`, `Semantics/NoPanic.lean`). -/

section Ends

variable {Γ : Ctx} (σ : State C Γ)

mutual

theorem SPath.resolveT_revertOnly : {T : Ty} → (b : SPath C Γ T) → (b.resolveT σ).RevertOnly
  | _, .alias i => by
    show (match (TEnv.get i σ.env : Option (SRef C _)) with
      | some r => .ok r
      | none => .error .revert : TRes _).RevertOnly
    cases (TEnv.get i σ.env : Option (SRef C _)) <;> exact fun _ h => by cases h <;> rfl
  | _, .loc l => Loc.resolveT_revertOnly l

theorem Loc.resolveT_revertOnly : {T : Ty} → (l : Loc C Γ T) → (l.resolveT σ).RevertOnly
  | _, .root .. => TRes.RevertOnly.ok _
  | _, .field b _ _ => (SPath.resolveT_revertOnly b).bind fun _ => TRes.RevertOnly.ok _
  | _, .index _ b i => (SPath.resolveT_revertOnly b).bind fun _ => (Val.evalT_revertOnly i).bind fun _ =>
      (TRes.RevertOnly.ofOpt _).bind fun _ => TRes.RevertOnly.ok _

theorem MPath.mvalT_revertOnly : {T : Ty} → (b : MPath C Γ T) → (b.mvalT σ).RevertOnly
  | _, .var i _ => by
    show (match (TEnv.get i σ.env : Option (HRef σ.H _)) with
      | some r => .ok r
      | none => .error .revert : TRes _).RevertOnly
    cases (TEnv.get i σ.env : Option (HRef σ.H _)) <;> exact fun _ h => by cases h <;> rfl
  | _, .loc l => (MLoc.addrT_revertOnly l).bind fun _ => TRes.RevertOnly.ofOpt _

theorem MLoc.addrT_revertOnly : {T : Ty} → (l : MLoc C Γ T) → (l.addrT σ).RevertOnly
  | _, .field b _ _ => (MPath.mvalT_revertOnly b).bind fun _ => TRes.RevertOnly.ok _
  | _, .index _ b i => (MPath.mvalT_revertOnly b).bind fun _ => (Val.evalT_revertOnly i).bind fun _ =>
      TRes.RevertOnly.ok _

theorem Val.evalT_revertOnly : {p : PrimTy} → (v : Val C Γ p) → (v.evalT σ).RevertOnly
  | _, .simple _ => TRes.RevertOnly.ok _
  | _, .read l => (Loc.resolveT_revertOnly l).bind fun _ => (TRes.RevertOnly.ofOpt _).bind fun _ =>
      TRes.RevertOnly.ok _
  | _, .binop op _ hq a b => by
    subst hq
    refine (Val.evalT_revertOnly a).bind fun x => ?_
    show (match op.shortT x with
      | some y => pure y
      | none => do
        let y ← b.evalT σ
        TRes.ofOpt (op.evalT _ x y) : TRes _).RevertOnly
    cases op.shortT x with
    | some _ => exact TRes.RevertOnly.ok _
    | none => exact (Val.evalT_revertOnly b).bind fun _ => TRes.RevertOnly.ofOpt _
  | _, .unop op _ hq a => by
    subst hq
    exact (Val.evalT_revertOnly a).bind fun _ => TRes.RevertOnly.ofOpt _
  | _, .ternary c a b => (Val.evalT_revertOnly c).bind fun x => by
    cases x
    · exact Val.evalT_revertOnly b
    · exact Val.evalT_revertOnly a
  | _, .readMem l => (MLoc.addrT_revertOnly l).bind fun _ => TRes.RevertOnly.ofOpt _
  | _, .len b hp => by
    subst hp
    exact (SPath.resolveT_revertOnly b).bind fun _ => (TRes.RevertOnly.ofOpt _).bind fun _ => TRes.RevertOnly.ok _
  | _, .mlen b hp => by
    subst hp
    exact (MPath.mvalT_revertOnly b).bind fun _ => TRes.RevertOnly.ok _
  | _, .modular _ a b k => (Val.evalT_revertOnly a).bind fun _ =>
      (Val.evalT_revertOnly b).bind fun _ => (Val.evalT_revertOnly k).bind fun _ => TRes.RevertOnly.ofOpt _
  | _, .hash _ b hp => by
    subst hp
    exact (MPath.mvalT_revertOnly b).bind fun _ => TRes.RevertOnly.ok _

end

theorem Src.valueT_revertOnly {T : Ty} : (r : Src C Γ T) → (r.valueT σ).RevertOnly
  | .val v => (Val.evalT_revertOnly σ v).bind fun _ => TRes.RevertOnly.ok _
  | .copy p _ => (SPath.resolveT_revertOnly σ p).bind fun _ => TRes.RevertOnly.ofOpt _
  | .fixedCopy p _ _ => (SPath.resolveT_revertOnly σ p).bind fun _ =>
      (TRes.RevertOnly.ofOpt _).bind fun _ => TRes.RevertOnly.ok _
  | .copyMem p => (MPath.mvalT_revertOnly σ p).bind fun _ => TRes.RevertOnly.ok _

theorem MSrc.mvalT_revertOnly {T : Ty} : (r : MSrc C Γ T) → (r.mvalT σ).RevertOnly
  | .val v => Val.evalT_revertOnly σ v
  | .ref p => MPath.mvalT_revertOnly σ p

theorem MRhs.evalT_revertOnly {R : RefTy} : (r : MRhs C Γ R) → (r.evalT σ).RevertOnly
  | .alias p => (MPath.mvalT_revertOnly σ p).bind fun _ => TRes.RevertOnly.ok _
  | .copy p _ => (SPath.resolveT_revertOnly σ p).bind fun _ => (TRes.RevertOnly.ofOpt _).bind fun _ =>
      TRes.RevertOnly.ok _
  | .newArr .. => TRes.RevertOnly.ok _

theorem opStoreT_revertOnly (op : BinOp) {p : PrimTy} (r : SRef C (.prim p)) (v : p.Denote) :
    (opStoreT σ op r v).RevertOnly :=
  (TRes.RevertOnly.ofOpt _).bind fun _ => (TRes.RevertOnly.ofOpt _).bind fun _ =>
    (TRes.RevertOnly.ofOpt _).bind fun _ => TRes.RevertOnly.ok _

theorem opMemT_revertOnly (op : BinOp) {p : PrimTy} (a : MAddr σ.H (.prim p)) (v : p.Denote) :
    (opMemT σ op a v).RevertOnly :=
  (TRes.RevertOnly.ofOpt _).bind fun _ => (TRes.RevertOnly.ofOpt _).bind fun _ =>
    (TRes.RevertOnly.ofOpt _).bind fun _ => TRes.RevertOnly.ok _

theorem OpLoc.storeT_revertOnly (op : BinOp) {p : PrimTy} : (l : OpLoc C Γ p) → (v : p.Denote) →
    (l.storeT σ op v).RevertOnly
  | .local _, _ => (TRes.RevertOnly.ofOpt _).bind fun _ => TRes.RevertOnly.ok _
  | .root .., _ => opStoreT_revertOnly σ op _ _
  | .field .., _ => (Loc.resolveT_revertOnly σ _).bind fun _ => opStoreT_revertOnly σ op _ _
  | .index .., _ => (Loc.resolveT_revertOnly σ _).bind fun _ => opStoreT_revertOnly σ op _ _
  | .mfield .., _ => (MLoc.addrT_revertOnly σ _).bind fun _ => opMemT_revertOnly σ op _ _
  | .mindex .., _ => (MLoc.addrT_revertOnly σ _).bind fun _ => opMemT_revertOnly σ op _ _

theorem bumpStoreT_revertOnly (op : IncDec) {p : PrimTy} (r : SRef C (.prim p)) :
    (bumpStoreT σ op r).RevertOnly :=
  (TRes.RevertOnly.ofOpt _).bind fun _ => (TRes.RevertOnly.ofOpt _).bind fun _ =>
    (TRes.RevertOnly.ofOpt _).bind fun _ => TRes.RevertOnly.ok _

theorem bumpMemT_revertOnly (op : IncDec) {p : PrimTy} (a : MAddr σ.H (.prim p)) :
    (bumpMemT σ op a).RevertOnly :=
  (TRes.RevertOnly.ofOpt _).bind fun _ => (TRes.RevertOnly.ofOpt _).bind fun _ =>
    (TRes.RevertOnly.ofOpt _).bind fun _ => TRes.RevertOnly.ok _

theorem OpLoc.bumpT_revertOnly (op : IncDec) {p : PrimTy} : (l : OpLoc C Γ p) → (l.bumpT σ op).RevertOnly
  | .local _ => (TRes.RevertOnly.ofOpt _).bind fun _ => TRes.RevertOnly.ok _
  | .root .. => bumpStoreT_revertOnly σ op _
  | .field .. => (Loc.resolveT_revertOnly σ _).bind fun _ => bumpStoreT_revertOnly σ op _
  | .index .. => (Loc.resolveT_revertOnly σ _).bind fun _ => bumpStoreT_revertOnly σ op _
  | .mfield .. => (MLoc.addrT_revertOnly σ _).bind fun _ => bumpMemT_revertOnly σ op _
  | .mindex .. => (MLoc.addrT_revertOnly σ _).bind fun _ => bumpMemT_revertOnly σ op _

theorem Args.evalT_revertOnly : {ps : Ctx} → (args : Args C Γ ps) → (args.evalT σ).RevertOnly
  | _, .nil => TRes.RevertOnly.ok _
  | _, .snoc as _ _ e => (Args.evalT_revertOnly as).bind fun _ =>
      (Val.evalT_revertOnly σ e).bind fun _ => TRes.RevertOnly.ok _
  | _, .snocStorage as _ _ e => (Args.evalT_revertOnly as).bind fun _ =>
      (SPath.resolveT_revertOnly σ e).bind fun _ => TRes.RevertOnly.ok _
  | _, .snocMemory as _ _ e => (Args.evalT_revertOnly as).bind fun _ =>
      (MPath.mvalT_revertOnly σ e).bind fun _ => TRes.RevertOnly.ok _

theorem SPath.resolveT_ends {T : Ty} (b : SPath C Γ T) : (b.resolveT σ).Ends :=
  (SPath.resolveT_revertOnly σ b).ends
theorem Loc.resolveT_ends {T : Ty} (l : Loc C Γ T) : (l.resolveT σ).Ends :=
  (Loc.resolveT_revertOnly σ l).ends
theorem MPath.mvalT_ends {T : Ty} (b : MPath C Γ T) : (b.mvalT σ).Ends :=
  (MPath.mvalT_revertOnly σ b).ends
theorem MLoc.addrT_ends {T : Ty} (l : MLoc C Γ T) : (l.addrT σ).Ends :=
  (MLoc.addrT_revertOnly σ l).ends
theorem Val.evalT_ends {p : PrimTy} (v : Val C Γ p) : (v.evalT σ).Ends :=
  (Val.evalT_revertOnly σ v).ends
theorem Src.valueT_ends {T : Ty} (r : Src C Γ T) : (r.valueT σ).Ends :=
  (Src.valueT_revertOnly σ r).ends
theorem MSrc.mvalT_ends {T : Ty} (r : MSrc C Γ T) : (r.mvalT σ).Ends :=
  (MSrc.mvalT_revertOnly σ r).ends
theorem MRhs.evalT_ends {R : RefTy} (r : MRhs C Γ R) : (r.evalT σ).Ends :=
  (MRhs.evalT_revertOnly σ r).ends
theorem opStoreT_ends (op : BinOp) {p : PrimTy} (r : SRef C (.prim p)) (v : p.Denote) :
    (opStoreT σ op r v).Ends := (opStoreT_revertOnly σ op r v).ends
theorem opMemT_ends (op : BinOp) {p : PrimTy} (a : MAddr σ.H (.prim p)) (v : p.Denote) :
    (opMemT σ op a v).Ends := (opMemT_revertOnly σ op a v).ends
theorem OpLoc.storeT_ends (op : BinOp) {p : PrimTy} (l : OpLoc C Γ p) (v : p.Denote) :
    (l.storeT σ op v).Ends := (OpLoc.storeT_revertOnly σ op l v).ends
theorem bumpStoreT_ends (op : IncDec) {p : PrimTy} (r : SRef C (.prim p)) :
    (bumpStoreT σ op r).Ends := (bumpStoreT_revertOnly σ op r).ends
theorem bumpMemT_ends (op : IncDec) {p : PrimTy} (a : MAddr σ.H (.prim p)) :
    (bumpMemT σ op a).Ends := (bumpMemT_revertOnly σ op a).ends
theorem OpLoc.bumpT_ends (op : IncDec) {p : PrimTy} (l : OpLoc C Γ p) : (l.bumpT σ op).Ends :=
  (OpLoc.bumpT_revertOnly σ op l).ends

end Ends

end Solidity
