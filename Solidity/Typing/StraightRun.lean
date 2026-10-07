import Solidity.Semantics.Core.TypedRunErase

/-!
# Straight programs: the typed run ends where the scoped one does

`Prog.trun_erase` reads one way: a typed run that ends, ends the scoped run
in its erasure.  The other way fails in general, since the typed run diverges
on a length past `uint` (`lenT`) and on a loop with no last iteration, where
the scoped run may end.  A *straight* program (`Prog.straight`) has neither:
it assigns simple values, binds aliases to paths, pushes defaults, pops,
deletes and opens blocks, at paths whose indices are simple and whose mapping
keys are not `bool`.  Its typed run never diverges (`Prog.trun_noDiv`) and is
on the bridge (`Prog.bridgeOk_of_straight`), so it ends exactly where the
scoped run does (`Prog.trun_of_run`).  The storage builder
(`Core.Build.rootsProg`, `Typing/Constructibility.lean`) is straight, which
is how a storage the builder reaches is reached by the typed run.
-/

namespace Solidity.Core

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

/-! ## Straight programs -/

section Straight

variable {Γ : Ctx}

mutual

/-- A path whose indices are simple values and whose mapping keys are not
`bool`. -/
def SPath.straight : {T : Ty} → SPath C Γ T → Bool
  | _, .alias _ => true
  | _, .loc l => l.straight

def Loc.straight : {T : Ty} → Loc C Γ T → Bool
  | _, .root .. => true
  | _, .field b _ _ => b.straight
  | _, .index (k := k) _ b i => k != .bool && b.straight && i.isSimple

end

/-- A source that is a simple value. -/
def Src.straight {T : Ty} : Src C Γ T → Bool
  | .val v => v.isSimple
  | .copy .. => false

/-- An alias bound to a straight path. -/
def ARhs.straight {R : RefTy} : ARhs C Γ R → Bool
  | .path p => p.straight
  | .push .. => false

end Straight

mutual

/-- A straight statement: a simple value assigned, an alias bound to a path,
a default pushed, a `pop`, a `delete`, or a block of straight statements, at
straight paths.  No loop, no length, no call. -/
def Stmt.straight : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Bool
  | _, _, .assign l r => l.straight && r.straight
  | _, _, .declStorage _ _ init => init.all ARhs.straight
  | _, _, .push b v _ => b.straight && v.isNone
  | _, _, .pop b => b.straight
  | _, _, .delete l => l.straight
  | _, _, .block body => Prog.straight body
  | _, _, .rebind .. | _, _, .assignLocal .. | _, _, .declLocal .. | _, _, .opAssign ..
  | _, _, .incDec .. | _, _, .assignIncDec .. | _, _, .transfer .. | _, _, .send ..
  | _, _, .declMem .. | _, _, .rebindMem .. | _, _, .assignFromMem .. | _, _, .assignMem ..
  | _, _, .deleteMem .. | _, _, .assignNew .. | _, _, .ite .. | _, _, .require ..
  | _, _, .assert .. | _, _, .revert | _, _, .call .. | _, _, .tryCall ..
  | _, _, .loop .. => false

def Prog.straight : {Γ Γ' : Ctx} → Prog C Γ Γ' → Bool
  | _, _, .nil => true
  | _, _, .cons s P => s.straight && Prog.straight P

end

/-! ## Straight programs are on the bridge -/

section Bridge

variable {Γ : Ctx}

theorem Val.bridgeOk_of_isSimple {p : PrimTy} : {v : Val C Γ p} → v.isSimple = true →
    v.bridgeOk = true
  | .simple _, _ => rfl

theorem Val.eq_simple_of_isSimple {p : PrimTy} : {v : Val C Γ p} → v.isSimple = true →
    ∃ s, v = .simple s
  | .simple s, _ => ⟨s, rfl⟩

mutual

theorem SPath.bridgeOk_of_straight : {T : Ty} → (q : SPath C Γ T) → q.straight = true →
    q.bridgeOk = true
  | _, .alias _, _ => rfl
  | _, .loc l, h => Loc.bridgeOk_of_straight l h

theorem Loc.bridgeOk_of_straight : {T : Ty} → (l : Loc C Γ T) → l.straight = true →
    l.bridgeOk = true
  | _, .root .., _ => rfl
  | _, .field b _ _, h => SPath.bridgeOk_of_straight b h
  | _, .index _ b i, h => by
    simp only [Loc.straight, Bool.and_eq_true] at h
    obtain ⟨⟨hk, hb⟩, hi⟩ := h
    simp only [Loc.bridgeOk, hk, SPath.bridgeOk_of_straight b hb, Val.bridgeOk_of_isSimple hi,
      Bool.and_self]

end

theorem Src.bridgeOk_of_straight {T : Ty} : {r : Src C Γ T} → r.straight = true →
    r.bridgeOk = true
  | .val _, h => Val.bridgeOk_of_isSimple h

theorem ARhs.bridgeOk_of_straight {R : RefTy} : {r : ARhs C Γ R} → r.straight = true →
    r.bridgeOk = true
  | .path p, h => SPath.bridgeOk_of_straight p h

end Bridge

mutual

theorem Stmt.bridgeOk_of_straight : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → s.straight = true →
    s.bridgeOk = true
  | _, _, .assign l r, h => by
    simp only [Stmt.straight, Bool.and_eq_true] at h
    simp only [Stmt.bridgeOk, Loc.bridgeOk_of_straight l h.1, Src.bridgeOk_of_straight h.2,
      Bool.and_self]
  | _, _, .declStorage _ _ init, h => by
    cases init with
    | none => rfl
    | some r =>
      simp only [Stmt.straight, Option.all_some] at h
      simp only [Stmt.bridgeOk, Option.all_some, ARhs.bridgeOk_of_straight h]
  | _, _, .push b v _, h => by
    simp only [Stmt.straight, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨hb, rfl⟩ := h
    simp only [Stmt.bridgeOk, SPath.bridgeOk_of_straight b hb, Option.all_none, Bool.and_self]
  | _, _, .pop b, h => SPath.bridgeOk_of_straight b h
  | _, _, .delete l, h => Loc.bridgeOk_of_straight l h
  | _, _, .block body, h => Prog.bridgeOk_of_straight body h
  | _, _, .rebind .., h | _, _, .assignLocal .., h | _, _, .declLocal .., h
  | _, _, .opAssign .., h | _, _, .incDec .., h | _, _, .assignIncDec .., h
  | _, _, .transfer .., h | _, _, .send .., h | _, _, .declMem .., h | _, _, .rebindMem .., h
  | _, _, .assignFromMem .., h | _, _, .assignMem .., h | _, _, .deleteMem .., h
  | _, _, .assignNew .., h | _, _, .ite .., h | _, _, .require .., h | _, _, .assert .., h
  | _, _, .revert, h | _, _, .call .., h | _, _, .tryCall .., h | _, _, .loop .., h =>
    absurd h Bool.false_ne_true

theorem Prog.bridgeOk_of_straight : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → P.straight = true →
    P.bridgeOk = true
  | _, _, .nil, _ => rfl
  | _, _, .cons s P, h => by
    simp only [Prog.straight, Bool.and_eq_true] at h
    simp only [Prog.bridgeOk, Stmt.bridgeOk_of_straight s h.1, Prog.bridgeOk_of_straight P h.2,
      Bool.and_self]

end

/-! ## Straight programs do not diverge -/

section NoDiv

variable {Γ : Ctx}

theorem Val.evalT_noDiv_of_isSimple (σ : TState C Γ) {p : PrimTy} {v : Val C Γ p}
    (h : v.isSimple = true) : (v.evalT σ).NoDiv := by
  obtain ⟨s, rfl⟩ := Val.eq_simple_of_isSimple h
  exact TRes.NoDiv.ok _

mutual

theorem SPath.resolveT_noDiv (σ : TState C Γ) : {T : Ty} → (b : SPath C Γ T) → b.straight = true →
    (b.resolveT σ).NoDiv
  | _, .alias i, _ => by
    show (match (TEnv.get i σ.env : Option (SRef C _)) with
      | some r => .ok r
      | none => .error .revert : TRes _).NoDiv
    cases (TEnv.get i σ.env : Option (SRef C _)) <;> exact fun h => nomatch h
  | _, .loc l, h => Loc.resolveT_noDiv σ l h

theorem Loc.resolveT_noDiv (σ : TState C Γ) : {T : Ty} → (l : Loc C Γ T) → l.straight = true →
    (l.resolveT σ).NoDiv
  | _, .root .., _ => TRes.NoDiv.ok _
  | _, .field b _ _, h => (SPath.resolveT_noDiv σ b h).bind fun _ => TRes.NoDiv.ok _
  | _, .index _ b i, h => by
    simp only [Loc.straight, Bool.and_eq_true] at h
    exact (SPath.resolveT_noDiv σ b h.1.2).bind fun _ =>
      (Val.evalT_noDiv_of_isSimple σ h.2).bind fun _ =>
        (TRes.NoDiv.ofOpt _).bind fun _ => TRes.NoDiv.ok _

end

theorem Src.valueT_noDiv (σ : TState C Γ) {T : Ty} : {r : Src C Γ T} → r.straight = true →
    (r.valueT σ).NoDiv
  | .val _, h => (Val.evalT_noDiv_of_isSimple σ h).bind fun _ => TRes.NoDiv.ok _

theorem ARhs.evalT_noDiv (σ : TState C Γ) {R : RefTy} : {r : ARhs C Γ R} → r.straight = true →
    (r.evalT σ).NoDiv
  | .path p, h => (SPath.resolveT_noDiv σ p h).bind fun _ => TRes.NoDiv.ok _

end NoDiv

mutual

/-- **A straight statement's typed run does not diverge.** -/
theorem Stmt.trun_noDiv : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → s.straight = true →
    ∀ σ : TState C Γ, (s.trun σ).NoDiv
  | _, _, .assign l r, h, σ => by
    simp only [Stmt.straight, Bool.and_eq_true] at h
    exact (Src.valueT_noDiv σ h.2).bind fun _ => (Loc.resolveT_noDiv σ l h.1).bind fun _ =>
      (TRes.NoDiv.ofOpt _).bind fun _ => TRes.NoDiv.ok _
  | _, _, .declStorage _ _ init, h, σ => by
    cases init with
    | none => exact TRes.NoDiv.ok _
    | some r =>
      simp only [Stmt.straight, Option.all_some] at h
      exact (ARhs.evalT_noDiv σ h).bind fun _ => TRes.NoDiv.ok _
  | _, _, .push b v _, h, σ => by
    simp only [Stmt.straight, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨hb, rfl⟩ := h
    exact (SPath.resolveT_noDiv σ b hb).bind fun _ => (TRes.NoDiv.ok _).bind fun _ =>
      (TRes.NoDiv.ofOpt _).bind fun _ => TRes.NoDiv.ok _
  | _, _, .pop b, h, σ => (SPath.resolveT_noDiv σ b h).bind fun _ =>
      (TRes.NoDiv.ofOpt _).bind fun _ => TRes.NoDiv.ok _
  | _, _, .delete l, h, σ => (Loc.resolveT_noDiv σ l h).bind fun _ =>
      (TRes.NoDiv.ofOpt _).bind fun _ => TRes.NoDiv.ok _
  | _, _, .block body, h, σ => (Prog.trun_noDiv body h σ).map _
  | _, _, .rebind .., h, _ | _, _, .assignLocal .., h, _ | _, _, .declLocal .., h, _
  | _, _, .opAssign .., h, _ | _, _, .incDec .., h, _ | _, _, .assignIncDec .., h, _
  | _, _, .transfer .., h, _ | _, _, .send .., h, _ | _, _, .declMem .., h, _
  | _, _, .rebindMem .., h, _ | _, _, .assignFromMem .., h, _ | _, _, .assignMem .., h, _
  | _, _, .deleteMem .., h, _ | _, _, .assignNew .., h, _ | _, _, .ite .., h, _
  | _, _, .require .., h, _ | _, _, .assert .., h, _ | _, _, .revert, h, _
  | _, _, .call .., h, _ | _, _, .tryCall .., h, _ | _, _, .loop .., h, _ =>
    absurd h Bool.false_ne_true

/-- **A straight program's typed run does not diverge.** -/
theorem Prog.trun_noDiv : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → P.straight = true →
    ∀ σ : TState C Γ, (P.trun σ).NoDiv
  | _, _, .nil, _, _ => TRes.NoDiv.ok _
  | _, _, .cons s P, h, σ => by
    simp only [Prog.straight, Bool.and_eq_true] at h
    show (TRun.seq s.trunR P.trunR σ).NoDiv
    unfold TRun.seq
    cases hs : s.trunR σ with
    | ok o => exact (Prog.trun_noDiv P h.2 o.st).map _
    | error e =>
      have := Stmt.trun_noDiv s h.1 σ
      simp only [Stmt.trun, hs] at this
      exact fun h' => this (by cases (h' : Except.error e = .error .diverge); rfl)

end

/-- **A straight program's typed run ends where its scoped run does**: in
the state the scoped run ends in, erased. -/
theorem Prog.trun_of_run {Γ Γ' : Ctx} {P : Prog C Γ Γ'} (h : P.straight = true)
    (σ : TState C Γ) {τ : State C Γ'} (hr : P.run σ.erase = .ok τ) :
    ∃ o : Out C σ.H Γ', P.trun σ = .ok o ∧ o.st.erase = τ := by
  have ha := Prog.trun_erase σ P (Prog.bridgeOk_of_straight P h)
  have hn := Prog.trun_noDiv P h σ
  cases hq : P.trun σ with
  | ok o =>
    rw [hq] at ha
    have he : P.run σ.erase = .ok o.st.erase := ha
    rw [hr] at he
    exact ⟨o, rfl, (Except.ok.inj he).symm⟩
  | error e =>
    rw [hq] at ha hn
    cases e with
    | revert =>
      have he : P.run σ.erase = .error .revert := ha
      rw [hr] at he; exact nomatch he
    | panic =>
      have he : P.run σ.erase = .error .panic := ha
      rw [hr] at he; exact nomatch he
    | diverge => exact absurd rfl hn

end Solidity.Core
