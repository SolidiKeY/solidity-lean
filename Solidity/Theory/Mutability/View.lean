import Solidity.Semantics.Transient
import Solidity.Semantics.CallbackFrame


namespace Solidity.Theory.Mutability

open Solidity

variable {C : Contract}

structure Globals (C : Contract) where
  storage : Storage C
  net : Ledger
  selfBalance : PrimTy.uint.Denote

def globals {Γ : Ctx} (σ : State C Γ) : Globals C := ⟨σ.storage, σ.net, σ.selfBalance⟩

def committed {Γ Γ' : Ctx} (σ : State C Γ) : TRes (Out C σ.H Γ') → Globals C
  | .ok o => globals o.st
  | .error _ => globals σ

theorem view_ne_nonpayable : (Mutability.view) ≠ .nonpayable := by decide
theorem pure_ne_nonpayable : (Mutability.pure) ≠ .nonpayable := by decide

theorem frame_globals {μ : Mutability} {Γ Δ : Ctx} {σ : State C Γ} {τ : State C Δ}
    (h : TGFrame μ σ τ) (hμ : μ ≠ .nonpayable) : globals τ = globals σ := by
  have hk := h.keeps hμ
  have hb := h.selfBalance hμ
  simp only [globals, hk.1, hk.2, hb]

theorem Prog.committed_readOnly {μ : Mutability} {Γ Γ' : Ctx} (P : Prog C Γ Γ')
    (hw : Prog.within μ P = true) (hμ : μ ≠ .nonpayable) (σ : State C Γ) :
    committed σ (Prog.run σ P) = globals σ := by
  cases h : Prog.run σ P with
  | error e => rfl
  | ok o => exact frame_globals (Prog.run_frame P hw 0 h).1 hμ

theorem Prog.committed_view {Γ Γ' : Ctx} (P : Prog C Γ Γ') (hw : Prog.within .view P = true)
    (σ : State C Γ) : committed σ (Prog.run σ P) = globals σ :=
  Prog.committed_readOnly P hw view_ne_nonpayable σ

theorem Prog.run_readOnly {μ : Mutability} {Γ Γ' : Ctx} {P : Prog C Γ Γ'}
    (hw : Prog.within μ P = true) (hμ : μ ≠ .nonpayable) {σ : State C Γ} {o : Out C σ.H Γ'}
    (h : Prog.run σ P = .ok o) :
    o.st.storage = σ.storage ∧ o.st.net = σ.net ∧ o.st.selfBalance = σ.selfBalance := by
  have hg := (Prog.run_frame P hw 0 h).1
  exact ⟨(hg.keeps hμ).1, (hg.keeps hμ).2, hg.selfBalance hμ⟩

def committedC {Γ Γ' : Ctx} (σ : State C Γ) : COut C σ.H Γ' → Globals C
  | .ok o => globals o.st
  | .halt _ | .violated => globals σ

theorem ExecP.committed_readOnly {J : StateInv C} {μ : Mutability} {Γ Γ' : Ctx}
    {σ : State C Γ} {P : Prog C Γ Γ'} {o : COut C σ.H Γ'} (h : ExecP J σ P o)
    (hw : Prog.within μ P = true) (hμ : μ ≠ .nonpayable) : committedC σ o = globals σ := by
  cases o with
  | ok o' => exact frame_globals (ExecP.frame h hw 0 o' rfl).1 hμ
  | halt e => rfl
  | violated => rfl


namespace Transient

open Solidity.Transient

theorem permits_readOnly {m μ : Mutability} (h : Program.permits m μ = true)
    (hm : m ≠ .nonpayable) : μ ≠ .nonpayable := by
  cases m <;> cases μ <;> simp only [Program.permits] at h <;> first
    | exact absurd rfl hm | decide | exact absurd h (by decide)

def ReadOnlyCtx (ctx : Context) : Prop := ctx.static = true ∨ ctx.mutability ≠ .nonpayable

theorem calleeContext_static {ctx : Context} (hro : ReadOnlyCtx ctx) (μ : Mutability)
    (forced : Bool) : (Program.calleeContext ctx μ forced).static = true := by
  change (ctx.static || forced || (ctx.mutability != .nonpayable) || (μ != .nonpayable)) = true
  rcases hro with hs | hμ
  · simp only [hs, Bool.true_or]
  · have hne : (ctx.mutability != .nonpayable) = true := by
      simpa only [bne_iff_ne, ne_eq] using hμ
    simp only [hne, Bool.or_true, Bool.true_or]

theorem Program.static_preserves_all {L : Layout} {α : Type} (body : Program C L α)
    {ctx : Context} {s t : FrameState C L} {v : α} (hμ : ReadOnlyCtx ctx)
    (success : Program.run body ctx s = .ok (v, t)) :
    t.cells = s.cells ∧ globals t.base = globals s.base := by
  induction body generalizing ctx s t with
  | pure x =>
    change Except.ok (x, s) = Except.ok (v, t) at success
    cases success
    exact ⟨rfl, rfl⟩
  | bind body next ih ihNext =>
    change (do let (x, u) ← Program.run body ctx s; Program.run (next x) ctx u) = .ok (v, t)
      at success
    cases first : Program.run body ctx s with
    | error e => rw [first] at success; cases success
    | ok result =>
      obtain ⟨x, u⟩ := result
      rw [first] at success
      obtain ⟨h₁, h₂⟩ := ih hμ first
      obtain ⟨h₃, h₄⟩ := ihNext x hμ success
      exact ⟨h₃.trans h₁, h₄.trans h₂⟩
  | halt e =>
    change Except.error e = Except.ok (v, t) at success
    cases success
  | read i =>
    change (if ctx.mutability == .pure then Except.error THalt.revert
      else Except.ok (Store.get i s.cells, s)) = .ok (v, t) at success
    split at success
    · cases success
    · cases success; exact ⟨rfl, rfl⟩
  | write i value =>
    change (if ctx.mutability != .nonpayable || ctx.static then Except.error THalt.revert
      else Except.ok ((), { s with cells := Store.set i value s.cells })) = .ok (v, t) at success
    have hne : (ctx.mutability != .nonpayable || ctx.static) = true := by
      rcases hμ with hs | hm
      · simp only [hs, Bool.or_true]
      · have h' : (ctx.mutability != .nonpayable) = true := by
          simpa only [bne_iff_ne, ne_eq] using hm
        simp only [h', Bool.true_or]
    simp only [hne, if_true] at success
    cases success
  | ordinary μ P within =>
    change (if Program.ordinaryAllowed ctx μ P then
      (do let o ← P.run s.base; Except.ok ((), { s with base := o.st }))
      else Except.error THalt.revert) = .ok (v, t) at success
    split at success
    · rename_i allowed
      simp only [Program.ordinaryAllowed, Bool.and_eq_true] at allowed
      cases ran : P.run s.base with
      | error e => rw [ran] at success; cases success
      | ok o =>
        rw [ran] at success
        cases success
        refine ⟨rfl, ?_⟩
        rcases hμ with hs | hm
        · have hv : Prog.within .view P = true := by
            have h2 := allowed.2
            simp only [hs, Bool.not_true, Bool.false_or] at h2
            exact h2
          exact frame_globals (Prog.run_frame P hv 0 ran).1 view_ne_nonpayable
        · exact frame_globals (Prog.run_frame P within 0 ran).1 (permits_readOnly allowed.1 hm)
    · cases success
  | selfCall μ forced body ih =>
    change (if Program.permits ctx.mutability μ then
      (do let (x, child) ← Program.run body (Program.calleeContext ctx μ forced) s.enterSelf
          Except.ok (x, s.resume child)) else Except.error THalt.revert) = .ok (v, t) at success
    split at success
    · rename_i hp
      cases ran : Program.run body (Program.calleeContext ctx μ forced) s.enterSelf with
      | error e => rw [ran] at success; cases success
      | ok result =>
        obtain ⟨x, child⟩ := result
        rw [ran] at success
        cases success
        obtain ⟨h₁, h₂⟩ := ih (ctx := Program.calleeContext ctx μ forced) (s := s.enterSelf)
          (t := child) (v := v) (Or.inl (calleeContext_static hμ μ forced)) ran
        refine ⟨h₁, ?_⟩
        have e : globals (s.resume child).base = globals child.base := rfl
        rw [e, h₂]
        rfl
    · cases success
  | attempt body ih =>
    change (match Program.run body ctx s with
      | .ok (x, u) => Except.ok (Except.ok x, u)
      | .error e => if Program.catchable e then Except.ok (Except.error e, s)
        else Except.error e) = .ok (v, t) at success
    cases ran : Program.run body ctx s with
    | error e =>
      simp only [ran] at success
      split at success
      · cases success; exact ⟨rfl, rfl⟩
      · cases success
    | ok result =>
      obtain ⟨x, u⟩ := result
      rw [ran] at success
      cases success
      exact ih hμ ran

theorem Program.readOnly_preserves {L : Layout} {α : Type} (body : Program C L α)
    {ctx : Context} {s t : FrameState C L} {v : α} (hμ : ctx.mutability ≠ .nonpayable)
    (success : Program.run body ctx s = .ok (v, t)) :
    t.cells = s.cells ∧ globals t.base = globals s.base :=
  Program.static_preserves_all body (Or.inr hμ) success

theorem Program.write_readOnly {L : Layout} {p : PrimTy} (i : Slot L p) (value : p.Denote)
    {ctx : Context} (hμ : ctx.mutability ≠ .nonpayable) (s : FrameState C L) :
    Program.run (Program.write i value) ctx s = .error .revert := by
  change (if ctx.mutability != .nonpayable || ctx.static then Except.error THalt.revert
    else Except.ok ((), { s with cells := Store.set i value s.cells })) = _
  have hne : (ctx.mutability != .nonpayable) = true := by
    simpa only [bne_iff_ne, ne_eq] using hμ
  simp only [hne, Bool.true_or, if_true]

theorem Program.ordinary_static {L : Layout} (μ : Mutability) (P : Prog C [] [])
    (within : Prog.within μ P = true) (hv : Prog.within .view P = false) {ctx : Context}
    (hs : ctx.static = true) (s : FrameState C L) :
    Program.run (Program.ordinary μ P within) ctx s = .error .revert := by
  change (if Program.ordinaryAllowed ctx μ P then
    (do let o ← P.run s.base; Except.ok ((), { s with base := o.st }))
    else Except.error THalt.revert) = _
  have h : Program.ordinaryAllowed ctx μ P = false := by
    simp only [Program.ordinaryAllowed, hs, hv, Bool.not_true, Bool.or_self, Bool.and_false]
  rw [h]
  rfl

theorem Program.write_static {L : Layout} {p : PrimTy} (i : Slot L p) (value : p.Denote)
    {ctx : Context} (hs : ctx.static = true) (s : FrameState C L) :
    Program.run (Program.write i value) ctx s = .error .revert := by
  change (if ctx.mutability != .nonpayable || ctx.static then Except.error THalt.revert
    else Except.ok ((), { s with cells := Store.set i value s.cells })) = _
  simp only [hs, Bool.or_true, if_true]

theorem Program.read_pure {L : Layout} {p : PrimTy} (i : Slot L p) {ctx : Context}
    (hμ : ctx.mutability = .pure) (s : FrameState C L) :
    Program.run (Program.read i) ctx s = .error .revert := by
  change (if ctx.mutability == .pure then Except.error THalt.revert
    else Except.ok (Store.get i s.cells, s)) = _
  simp only [hμ, BEq.rfl, if_true]

theorem Program.selfCall_nonpayable_readOnly {L : Layout} {α : Type} (body : Program C L α)
    (forced : Bool) {ctx : Context} (hμ : ctx.mutability ≠ .nonpayable) (s : FrameState C L) :
    Program.run (Program.selfCall .nonpayable forced body) ctx s = .error .revert := by
  change (if Program.permits ctx.mutability .nonpayable then
    (do let (x, child) ← Program.run body (Program.calleeContext ctx .nonpayable forced)
          s.enterSelf
        Except.ok (x, s.resume child)) else Except.error THalt.revert) = _
  have hp : Program.permits ctx.mutability .nonpayable = false := by
    cases h : ctx.mutability with
    | nonpayable => exact absurd h hμ
    | pure => rfl
    | view => rfl
  rw [hp]
  rfl

end Transient

end Solidity.Theory.Mutability
