import Solidity.Semantics.Core.TypedRunErase

/-!
# Straight programs: the typed run ends where the scoped one does

`Prog.trun_erase` reads one way: a typed run that ends, ends the scoped run
in its erasure.  The other way fails in general, since the typed run diverges
on a loop with no last iteration and is exhausted on a push onto
`2^256 - 1` elements (`Storage.full`), where the scoped run may end.  A
*straight* program (`Prog.straight`) has no loop: it assigns simple values,
binds aliases to paths, pushes defaults, pops, deletes and opens blocks, at
paths whose indices are simple.  Its typed run neither diverges nor is
exhausted when every push of its scoped run lands below the bound
(`Prog.pushesShort`, `Prog.trun_ends`), so it ends exactly where the scoped
run does (`Prog.trun_of_run`).  The storage builder
(`Core.Build.rootsProg`, `Typing/Constructibility.lean`) is straight and its
pushes are short, which is how a storage the builder reaches is reached by
the typed run.
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

/-- A typed result that neither diverges nor is exhausted: it ends, reverts
or panics, as the scoped run does. -/
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

/-! ## Straight programs -/

section Straight

variable {Γ : Ctx}

mutual

/-- A path whose indices are simple values. -/
def SPath.straight : {T : Ty} → SPath C Γ T → Bool
  | _, .alias _ => true
  | _, .loc l => l.straight

def Loc.straight : {T : Ty} → Loc C Γ T → Bool
  | _, .root .. => true
  | _, .field b _ _ => b.straight
  | _, .index _ b i => b.straight && i.isSimple

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

section Simple

variable {Γ : Ctx}

theorem Val.eq_simple_of_isSimple {p : PrimTy} : {v : Val C Γ p} → v.isSimple = true →
    ∃ s, v = .simple s
  | .simple s, _ => ⟨s, rfl⟩

end Simple

/-! ## Pushes below the bound

A push onto `2^256 - 1` elements is out of gas in the typed run (`TRun.push`,
`Storage.full`), and the scoped run, which has no bound, goes on: a straight
program's typed run ends where its scoped one does if every push of the
scoped run lands below the bound. -/

mutual

/-- Every `push` of the statement, run from `σ` by the scoped interpreter,
lands on an array of fewer than `2^256 - 1` elements. -/
def Stmt.pushesShort : {Γ Γ' : Ctx} → Stmt C Γ Γ' → State C Γ → Prop
  | _, _, .push b _ _, σ => ∀ r segs elems sh fx, b.resolve σ = .ok (r, segs) →
      σ.glob.findStorage r segs = .ok (.array elems sh fx) → elems.length + 1 < 2 ^ 256
  | _, _, .block body, σ => Prog.pushesShort body σ
  | _, _, _, _ => True

/-- Every `push` of the program, along its scoped run from `σ`. -/
def Prog.pushesShort : {Γ Γ' : Ctx} → Prog C Γ Γ' → State C Γ → Prop
  | _, _, .nil, _ => True
  | _, _, .cons s P, σ => Stmt.pushesShort s σ ∧ ∀ τ, s.run σ = .ok τ → Prog.pushesShort P τ

end

/-! ## Evaluators end

Every evaluator, and every write but a push, neither diverges nor is
exhausted (`TRes.Ends`): a failed read, a bad index, an overflow revert
(`TRes.ofOpt`). -/

section Ends

variable {Γ : Ctx} (σ : TState C Γ)

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
  | _, .var .. => TRes.Ends.ok _
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

/-! ## Straight programs end -/

mutual

/-- **A straight statement's typed run neither diverges nor is exhausted**,
its pushes below the bound. -/
theorem Stmt.trun_ends : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → s.straight = true →
    ∀ σ : TState C Γ, s.pushesShort σ.erase → (s.trun σ).Ends
  | _, _, .assign l r, _, σ, _ =>
    (Src.valueT_ends σ r).bind fun _ => (Loc.resolveT_ends σ l).bind fun _ =>
      (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _
  | _, _, .declStorage _ _ init, h, σ, _ => by
    cases init with
    | none => exact TRes.Ends.ok _
    | some r =>
      simp only [Stmt.straight, Option.all_some] at h
      cases r with
      | path p =>
        exact ((SPath.resolveT_ends σ p).bind fun _ => TRes.Ends.ok _).bind fun _ => TRes.Ends.ok _
      | push _ _ => exact absurd h Bool.false_ne_true
  | _, _, .push b v _, h, σ, hp => by
    simp only [Stmt.straight, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨_, rfl⟩ := h
    show (TRun.push b none σ).Ends
    unfold TRun.push
    have hres := b.resolveT_erase σ
    have hnd := SPath.resolveT_ends σ b
    cases hr : b.resolveT σ with
    | error e =>
      rw [hr] at hnd
      simp only [bind, Except.bind]
      exact ⟨fun h' => hnd.1 (by cases h'; rfl), fun h' => hnd.2 (by cases h'; rfl)⟩
    | ok ref =>
      rw [hr] at hres
      have hfull : σ.storage.full ref = false :=
        Storage.full_eq_false rfl ref fun elems sh fx hf => hp _ _ elems sh fx hres hf
      simp only [bind, Except.bind, pure, Except.pure, hfull, Bool.false_eq_true, ↓reduceIte]
      exact (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _
  | _, _, .pop b, _, σ, _ => (SPath.resolveT_ends σ b).bind fun _ =>
      (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _
  | _, _, .delete l, _, σ, _ => (Loc.resolveT_ends σ l).bind fun _ =>
      (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _
  | _, _, .block body, h, σ, hp => (Prog.trun_ends body h σ hp).map _
  | _, _, .rebind .., h, _, _ | _, _, .assignLocal .., h, _, _ | _, _, .declLocal .., h, _, _
  | _, _, .opAssign .., h, _, _ | _, _, .incDec .., h, _, _ | _, _, .assignIncDec .., h, _, _
  | _, _, .transfer .., h, _, _ | _, _, .send .., h, _, _ | _, _, .declMem .., h, _, _
  | _, _, .rebindMem .., h, _, _ | _, _, .assignFromMem .., h, _, _
  | _, _, .assignMem .., h, _, _ | _, _, .deleteMem .., h, _, _ | _, _, .assignNew .., h, _, _
  | _, _, .ite .., h, _, _ | _, _, .require .., h, _, _ | _, _, .assert .., h, _, _
  | _, _, .revert, h, _, _ | _, _, .call .., h, _, _ | _, _, .tryCall .., h, _, _
  | _, _, .loop .., h, _, _ =>
    absurd h Bool.false_ne_true

/-- **A straight program's typed run neither diverges nor is exhausted**,
its pushes below the bound. -/
theorem Prog.trun_ends : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → P.straight = true →
    ∀ σ : TState C Γ, P.pushesShort σ.erase → (P.trun σ).Ends
  | _, _, .nil, _, _, _ => TRes.Ends.ok _
  | _, _, .cons s P, h, σ, hp => by
    simp only [Prog.straight, Bool.and_eq_true] at h
    show (TRun.seq s.trunR P.trunR σ).Ends
    unfold TRun.seq
    cases hs : s.trunR σ with
    | ok o =>
      have hr : s.run σ.erase = .ok o.st.erase := by
        have := Stmt.trun_erase σ s
        simp only [Stmt.trun, hs] at this
        exact this
      exact (Prog.trun_ends P h.2 o.st (hp.2 _ hr)).map _
    | error e =>
      have := Stmt.trun_ends s h.1 σ hp.1
      simp only [Stmt.trun, hs] at this
      exact ⟨fun h' => this.1 (by cases h'; rfl), fun h' => this.2 (by cases h'; rfl)⟩

end

/-- **A straight program's typed run ends where its scoped run does**: in
the state the scoped run ends in, erased. -/
theorem Prog.trun_of_run {Γ Γ' : Ctx} {P : Prog C Γ Γ'} (h : P.straight = true)
    (σ : TState C Γ) {τ : State C Γ'} (hr : P.run σ.erase = .ok τ)
    (hp : P.pushesShort σ.erase) :
    ∃ o : Out C σ.H Γ', P.trun σ = .ok o ∧ o.st.erase = τ := by
  have ha := Prog.trun_erase σ P
  have hn := Prog.trun_ends P h σ hp
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
    | diverge => exact absurd rfl hn.1
    | exhausted => exact absurd rfl hn.2

end Solidity.Core
