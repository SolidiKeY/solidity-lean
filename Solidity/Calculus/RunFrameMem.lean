import Solidity.Semantics.RunFrame
import Solidity.Theory.Typed.Mem

/-!
# A body that allocates runs within a grown frame

`Semantics/RunFrame.lean`'s frame is for a body within a mutability
(`Stmt.within`), which allocates nothing: the heap and its typing are kept
(`TGFrame`).  A memory return's callee allocates (`docs/kernel-port.md`,
"Recursion", "What is left"), so its frame is over a grown heap
(`TGFrameM`): the heap typing extended, every object the caller had kept as
it was (`Heap.Keeps`), the locals of the context below written only where
`writesAt` lists them, each other one weakened along the extension
(`TLocAgreeM`).

`Stmt.withinM` is `Stmt.within` and the statements that allocate or bind a
memory local without writing an object: a memory declaration and a rebind
(`declMem`, `rebindMem`: a fresh object, a copy of storage, a new array, or
an alias of a memory value), a call of any return, with its callee's body
within `withinM` (a memory return's entry object is fresh), `if` and a
block over them.  A write into an object (`assignMem`, `deleteMem`, a
memory push, an `opAssign` at a memory location) is outside it: such a
write keeps the caller's objects only where it reaches none of them, the
run invariant `docs/kernel-port.md` calls step (1), which is not here.
-/

namespace Solidity

open Solidity (Mutability)

variable {C : Contract}

/-! ## Which bodies -/

/-- A memory right-hand side a callee of mutability `μ` may bind: an alias
or a new array (no state read), a copy of storage (not `pure`). -/
def MRhs.allocIn {Γ : Ctx} {R : RefTy} (μ : Mutability) : MRhs C Γ R → Bool
  | .alias _ => true
  | .copy .. => μ != .pure
  | .newArr .. => true

mutual

/-- **A statement a callee of mutability `μ` that allocates may run**: one
within `μ` (`Stmt.within`), a memory declaration or rebind, or `if`, a block
or a call over such statements. -/
def Stmt.withinM (μ : Mutability) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Bool
  | _, _, s => Stmt.within μ s || Stmt.casesOn (motive_1 := fun _ _ _ => Bool) s
    (assign := fun _ _ => false) (rebind := fun _ _ => false)
    (assignLocal := fun _ _ => false) (declLocal := fun _ _ _ => false)
    (declStorage := fun _ _ _ => false) (opAssign := fun _ _ _ _ _ => false)
    (incDec := fun _ _ _ => false) (assignIncDec := fun _ _ _ _ _ => false)
    (assignLocalPush := fun _ _ => false)
    (pushOpAssign := fun _ _ _ _ _ => false) (pushIncDec := fun _ _ _ => false)
    (push := fun _ _ _ => false) (pop := fun _ => false)
    (transfer := fun _ _ => false) (send := fun _ _ _ _ => false)
    (declMem := fun _ _ init _ _ => match init with
      | none => true
      | some r => r.allocIn μ)
    (rebindMem := fun _ r => r.allocIn μ)
    (assignFromMem := fun _ _ => false) (assignMem := fun _ _ => false)
    (delete := fun _ => false) (deleteMem := fun _ _ => false)
    (assignNew := fun _ _ _ => false)
    (ite := fun c thn els => c.readsIn μ && Prog.withinM μ thn && Prog.withinM μ els)
    (require := fun _ => false) (assert := fun _ => false) (revert := false)
    (assumeFalse := false)
    (call := fun _ args _ body => args.readsIn μ && Prog.withinM μ body)
    (tryCall := fun _ _ _ _ _ _ _ _ _ _ => false)
    (loop := fun _ _ _ => false)
    (block := fun body => Prog.withinM μ body)
    (callReceiver := fun _ _ _ _ _ => false)
    (callReceiverPush := fun _ _ _ _ _ _ => false)
    (callRec := fun _ _ args _ body => args.readsIn μ && Prog.withinM μ (body ()))
    (revertData := fun _ => false)
    (catchData := fun _ _ _ _ _ _ _ _ => false)
  termination_by structural _ _ s => s

/-- `Stmt.withinM` of every statement. -/
def Prog.withinM (μ : Mutability) : {Γ Γ' : Ctx} → Prog C Γ Γ' → Bool
  | _, _, P => Prog.casesOn (motive_2 := fun _ _ _ => Bool) P true
      (fun s P => Stmt.withinM μ s && Prog.withinM μ P)
  termination_by structural _ _ P => P

end

theorem Prog.withinM_nil {μ : Mutability} {Γ : Ctx} : Prog.withinM μ (.nil : Prog C Γ Γ) = true :=
  rfl

theorem Prog.withinM_cons {μ : Mutability} {Γ Γ₁ Γ₂ : Ctx} (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ₂) :
    Prog.withinM μ (.cons s P) = (Stmt.withinM μ s && Prog.withinM μ P) :=
  rfl

/-- Every frame of an unrolling is within `μ` where each frame is from the
one below. -/
theorem Prog.withinM_recUnroll {μ : Mutability} {F : Ctx}
    {step : Nat → (Unit → Prog C F F) → Prog C F F}
    (hs : ∀ n (t : Unit → Prog C F F), Prog.withinM μ (t ()) = true →
      Prog.withinM μ (step n t) = true) (d : Nat) :
    Prog.withinM μ (recUnroll Prog.recBase step d) = true :=
  recUnroll_induct (fun b => Prog.withinM μ b = true) rfl hs d

/-! ## The frame -/

namespace LTy

theorem TDenote.wk_wk {H H₁ H₂ : HTy} (e₁ : H <+: H₁) (e₂ : H₁ <+: H₂) :
    (t : LTy) → (v : t.TDenote C H) →
      TDenote.wk e₂ t (TDenote.wk e₁ t v) = TDenote.wk (e₁.trans e₂) t v
  | .val _, _ | .alias _, _ | .old, _ | .oldNet, _ | .kint, _ => rfl
  | .mem _, v => by cases v <;> rfl

theorem TDenote.wk_refl {H : HTy} (e : H <+: H) : (t : LTy) → (v : t.TDenote C H) →
    TDenote.wk e t v = v
  | .val _, _ | .alias _, _ | .old, _ | .oldNet, _ | .kint, _ => rfl
  | .mem _, v => by cases v <;> rfl

end LTy

/-- The locals at least `d` deep read in `e'` what they read in `e`,
weakened along `e₀`, but where `W` lists them. -/
def TLocAgreeM {Γ : Ctx} {H H' : HTy} (e₀ : H <+: H') (d : Nat) (W : List (LTy × Nat))
    (e : TEnv C H Γ) (e' : TEnv C H' Γ) : Prop :=
  ∀ (t : LTy) (i : Idx Γ t), d ≤ i.toNat → (t, i.toNat - d) ∉ W →
    TEnv.get i e' = LTy.TDenote.wk e₀ t (TEnv.get i e)

namespace TLocAgreeM

variable {Γ : Ctx} {d : Nat} {W W' : List (LTy × Nat)} {H₁ H₂ H₃ : HTy}

theorem trans {e₁₂ : H₁ <+: H₂} {e₂₃ : H₂ <+: H₃} {e₁₃ : H₁ <+: H₃} {e₁ : TEnv C H₁ Γ}
    {e₂ : TEnv C H₂ Γ} {e₃ : TEnv C H₃ Γ}
    (h₁ : TLocAgreeM e₁₂ d W e₁ e₂) (h₂ : TLocAgreeM e₂₃ d W e₂ e₃) :
    TLocAgreeM e₁₃ d W e₁ e₃ := fun t i hd hw => by
  rw [h₂ t i hd hw, h₁ t i hd hw, LTy.TDenote.wk_wk]

theorem mono (hW : ∀ x ∈ W, x ∈ W') {e₀ : H₁ <+: H₂} {e : TEnv C H₁ Γ} {e' : TEnv C H₂ Γ}
    (h : TLocAgreeM e₀ d W e e') : TLocAgreeM e₀ d W' e e' :=
  fun t i hd hw => h t i hd fun hx => hw (hW _ hx)

theorem left {e₀ : H₁ <+: H₂} {e : TEnv C H₁ Γ} {e' : TEnv C H₂ Γ}
    (h : TLocAgreeM e₀ d W e e') : TLocAgreeM e₀ d (W ++ W') e e' :=
  mono (fun _ hx => List.mem_append_left _ hx) h

theorem right {e₀ : H₁ <+: H₂} {e : TEnv C H₁ Γ} {e' : TEnv C H₂ Γ}
    (h : TLocAgreeM e₀ d W' e e') : TLocAgreeM e₀ d (W ++ W') e e' :=
  mono (fun _ hx => List.mem_append_right _ hx) h

/-- Locals that agree over one heap typing. -/
theorem ofAgree {e₀ : H₁ <+: H₂} (hH : H₂ = H₁) {e : TEnv C H₁ Γ} {e' : TEnv C H₂ Γ}
    (h : TLocAgree d W e e') : TLocAgreeM e₀ d W e e' := by
  subst hH
  intro t i hd hw
  rw [LTy.TDenote.wk_refl]
  exact eq_of_heq (h t i hd hw)

/-- The locals weakened along a grown heap. -/
theorem wk (e₀ : H₁ <+: H₂) (e : TEnv C H₁ Γ) : TLocAgreeM e₀ d W e (TEnv.wk e₀ Γ e) :=
  fun _ i _ _ => TEnv.get_wk e₀ i e

/-- A local set: the one `Idx.outer` lists. -/
theorem set {t : LTy} (i : Idx Γ t) (v : t.TDenote C H₁) (e : TEnv C H₁ Γ) (e₀ : H₁ <+: H₁) :
    TLocAgreeM e₀ d (i.outer d) e (TEnv.set i v e) :=
  ofAgree rfl (TLocAgree.set i v e)

/-- Popped locals: the positions move down by as many. -/
theorem drop {Δ : Ctx} (h : Ext Γ Δ) {e₀ : H₁ <+: H₂} {e : TEnv C H₁ Δ} {e' : TEnv C H₂ Δ}
    (ha : TLocAgreeM e₀ (d + h.depth) W e e') :
    TLocAgreeM e₀ d W (TEnv.drop h e) (TEnv.drop h e') := by
  intro t i hd hw
  have := ha t (i.ext h) (by rw [Ext.toNat_idx]; omega)
    (by rw [Ext.toNat_idx, show i.toNat + h.depth - (d + h.depth) = i.toNat - d by omega]; exact hw)
  rwa [TEnv.get_ext_drop, TEnv.get_ext_drop] at this

end TLocAgreeM

/-- **What a run that allocates within `μ` leaves of the global part**: the
heap grown along `e`, every older object kept, the funds and the
transaction, and, unless `μ` is `nonpayable`, the storage and the ledger. -/
structure TGFrameM (μ : Mutability) {Γ Δ : Ctx} (σ : State C Γ) (τ : State C Δ)
    (e : σ.H <+: τ.H) : Prop where
  keeps : Heap.Keeps e σ.heap τ.heap
  selfBalance : τ.selfBalance = σ.selfBalance
  tx : τ.tx = σ.tx
  keepsSt : μ ≠ .nonpayable → τ.storage = σ.storage ∧ τ.net = σ.net

namespace TGFrameM

variable {μ : Mutability} {Γ Δ Ε : Ctx}

theorem trans {σ : State C Γ} {τ : State C Δ} {υ : State C Ε} {e₁ : σ.H <+: τ.H}
    {e₂ : τ.H <+: υ.H} (h₁ : TGFrameM μ σ τ e₁) (h₂ : TGFrameM μ τ υ e₂) (e : σ.H <+: υ.H) :
    TGFrameM μ σ υ e :=
  ⟨Heap.Keeps.trans h₁.keeps h₂.keeps, h₂.selfBalance.trans h₁.selfBalance, h₂.tx.trans h₁.tx,
    fun hμ => ⟨(h₂.keepsSt hμ).1.trans (h₁.keepsSt hμ).1,
      (h₂.keepsSt hμ).2.trans (h₁.keepsSt hμ).2⟩⟩

/-- A frame at one heap typing is a grown one. -/
theorem ofFrame {σ : State C Γ} {τ : State C Δ} (h : TGFrame μ σ τ) (e : σ.H <+: τ.H) :
    TGFrameM μ σ τ e := by
  refine ⟨?_, h.selfBalance, h.tx, h.keeps⟩
  obtain ⟨st, H, hp, env, nt, sb, tx⟩ := τ
  have hH : H = σ.H := h.H
  have hh : HEq hp σ.heap := h.heap
  subst hH
  cases hh
  intro R r
  exact (MObj.wk_refl R _).symm

theorem withEnv {σ : State C Γ} {τ : State C Δ} {e : σ.H <+: τ.H} (h : TGFrameM μ σ τ e)
    (env : TEnv C τ.H Ε) : TGFrameM μ σ (τ.withEnv env) e :=
  ⟨h.keeps, h.selfBalance, h.tx, h.keepsSt⟩

theorem env (σ : State C Γ) (env : TEnv C σ.H Δ) (e : σ.H <+: σ.H) :
    TGFrameM μ σ (σ.withEnv env) e :=
  ofFrame ((TGFrame.refl σ).withEnv env) e

/-- A grown heap that keeps every object, adopted. -/
theorem adopt {α : HTy → Type} (σ : State C Γ) (g : Grown σ.H α)
    (hk : Heap.Keeps g.ext σ.heap g.heap) : TGFrameM μ σ (σ.adopt g).1 g.ext :=
  ⟨hk, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

end TGFrameM

/-! ## Each allocation keeps the older objects -/

section Alloc

variable {Γ : Ctx}

theorem State.keeps_copyStToMG {T : Ty} (σ : State C Γ) (v : SVal T) (h : T.mapFree = true) :
    Heap.Keeps (σ.copyStToMG v h).ext σ.heap (σ.copyStToMG v h).st.heap :=
  SVal.keeps_copyStToM v h σ.heap

theorem State.keeps_allocDefaultG (σ : State C Γ) (R : RefTy) (h : (Ty.ref R).mapFree = true) :
    Heap.Keeps (σ.allocDefaultG R h).ext σ.heap (σ.allocDefaultG R h).st.heap :=
  SVal.keeps_copyStToM _ h σ.heap

/-- **A memory right-hand side keeps the older objects**: an alias reads,
a copy and a new array allocate. -/
theorem MRhs.evalT_frame {R : RefTy} (μ : Mutability) (d : Nat) (r : MRhs C Γ R)
    {σ : State C Γ} {g : Grew C Γ σ.H (HRef · R)} (h : r.evalT σ = .ok g) :
    TGFrameM μ σ g.st g.ext ∧ TLocAgreeM g.ext d [] σ.env g.st.env := by
  cases r with
  | alias p =>
    simp only [MRhs.evalT] at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨TGFrameM.ofFrame (TGFrame.refl σ) _, TLocAgreeM.ofAgree rfl (TLocAgree.refl _)⟩
  | copy p hm =>
    simp only [MRhs.evalT] at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨sv, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨TGFrameM.adopt σ _ (SVal.keeps_copyStToM _ _ σ.heap), TLocAgreeM.wk _ _⟩
  | newArr n hn =>
    simp only [MRhs.evalT] at h
    cases h
    exact ⟨TGFrameM.adopt σ _ (SVal.keeps_copyStToM _ _ σ.heap), TLocAgreeM.wk _ _⟩

/-- A call's frame entered: a memory return's object fresh. -/
theorem CallRet.enterT_frameM {μ : Mutability} {Γ' rs ps : Ctx} (ret : CallRet Γ rs Γ')
    (σ : State C ps) : TGFrameM μ σ (ret.enterT σ).st (ret.enterT σ).ext := by
  cases ret with
  | none | val | rets | storage => exact TGFrameM.ofFrame (CallRet.enterT_frame _ rfl σ) _
  | mem R r hd hm =>
    exact ⟨State.keeps_allocDefaultG σ R hm, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- What a call leaves its caller's locals: the result where it lands, the
rest as they were, weakened along the heap the call grew. -/
theorem CallRet.leaveT_frameM {Γ' rs : Ctx} (ret : CallRet Γ rs Γ') {H H' : HTy}
    (e₀ : H <+: H') (e : TEnv C H Γ) (x : TEnv C H' rs) (d : Nat) :
    TLocAgreeM e₀ d (ret.writesAt d) e (TEnv.drop ret.ext (ret.leaveT (TEnv.wk e₀ Γ e) x)) := by
  cases ret with
  | none => exact TLocAgreeM.wk e₀ e
  | val p r res =>
    cases res with
    | none => exact TLocAgreeM.wk e₀ e
    | some j =>
      intro t i hd hw
      show TEnv.get i (TEnv.set j _ (TEnv.wk e₀ Γ e)) = _
      rw [← TEnv.get_wk e₀ i e]
      exact eq_of_heq (TLocAgree.set (d := d) j x.1 (TEnv.wk e₀ Γ e) t i hd hw)
  | rets bs =>
    show TLocAgreeM e₀ d [] e (TEnv.drop (Ext.append _ _) (TEnv.append _ x (TEnv.wk e₀ Γ e)))
    rw [TEnv.drop_append]
    exact TLocAgreeM.wk e₀ e
  | mem => exact TLocAgreeM.wk e₀ e
  | storage => exact TLocAgreeM.wk e₀ e

end Alloc

/-! ## A program that allocates within its grown frame -/

section Progs

variable {μ : Mutability}

/-- A statement within `μ`, by `Stmt.run_frame`. -/
theorem Stmt.run_frameM_of_within {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (hw : s.within μ = true)
    (d : Nat) {σ : State C Γ} {o : Out C σ.H Γ'} (h : s.run σ = .ok o) :
    TGFrameM μ σ o.st o.ext ∧ TLocAgreeM o.ext d (s.writesAt d) σ.env (TEnv.drop s.ext o.st.env) :=
  let ⟨hg, ha⟩ := Stmt.run_frame s hw d h
  ⟨TGFrameM.ofFrame hg _, TLocAgreeM.ofAgree hg.H ha⟩

mutual

/-- **A statement that allocates within `μ` runs within `μ`'s grown
frame**, writing of the context `d` below its own at most `s.writesAt d`,
the other locals weakened along the heap it grew. -/
theorem Stmt.run_frameM : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → s.withinM μ = true → (d : Nat) →
    {σ : State C Γ} → {o : Out C σ.H Γ'} → s.run σ = .ok o →
      TGFrameM μ σ o.st o.ext ∧
        TLocAgreeM o.ext d (s.writesAt d) σ.env (TEnv.drop s.ext o.st.env)
  | _, _, .declMem R _ init _ hm, hw, d, σ, o, h => by
    change TRun.declMem R init hm σ = .ok o at h
    cases init with
    | none =>
      cases h
      exact ⟨(TGFrameM.adopt (μ := μ) σ _ (State.keeps_allocDefaultG σ R hm)).withEnv _,
        TLocAgreeM.wk _ _⟩
    | some r =>
      simp only [TRun.declMem] at h
      obtain ⟨g, hg, h⟩ := tbind_ok_inv h
      cases h
      obtain ⟨hf, ha⟩ := MRhs.evalT_frame μ d r hg
      exact ⟨hf.withEnv _, ha⟩
  | _, _, .rebindMem i r, hw, d, σ, o, h => by
    change TRun.rebindMem i r σ = .ok o at h
    simp only [TRun.rebindMem] at h
    obtain ⟨g, hg, h⟩ := tbind_ok_inv h
    cases h
    obtain ⟨hf, ha⟩ := MRhs.evalT_frame μ d r hg
    exact ⟨hf.withEnv _, (ha.mono fun _ hx => absurd hx List.not_mem_nil).trans
      (TLocAgreeM.set i _ _ (List.prefix_refl _))⟩
  | _, _, .ite c thn els, hw, d, σ, o, h => by
    cases hwi : Stmt.within μ (Stmt.ite c thn els)
    case true => exact Stmt.run_frameM_of_within _ hwi d h
    have hw' : (c.readsIn μ && Prog.withinM μ thn && Prog.withinM μ els) = true := by
      simpa only [Stmt.withinM, hwi, Bool.false_or] using hw
    simp only [Bool.and_eq_true] at hw'
    change TRun.ite c thn.ext thn.runR els.ext els.runR σ = .ok o at h
    simp only [TRun.ite] at h
    obtain ⟨v, _, h⟩ := tbind_ok_inv h
    split at h
    · obtain ⟨o', h', rfl⟩ := tmap_ok_inv h
      obtain ⟨hg, ha⟩ := Prog.run_frameM thn hw'.1.2 d h'
      exact ⟨hg.withEnv _, ha.left⟩
    · obtain ⟨o', h', rfl⟩ := tmap_ok_inv h
      obtain ⟨hg, ha⟩ := Prog.run_frameM els hw'.2 d h'
      exact ⟨hg.withEnv _, ha.right⟩
  | _, _, .block body, hw, d, σ, o, h => by
    cases hwi : Stmt.within μ (Stmt.block body)
    case true => exact Stmt.run_frameM_of_within _ hwi d h
    have hw' : Prog.withinM μ body = true := by simpa only [Stmt.withinM, hwi, Bool.false_or] using hw
    change (body.runR σ).map (fun o => ⟨o.st.drop body.ext, o.ext⟩) = .ok o at h
    obtain ⟨o', h', rfl⟩ := tmap_ok_inv h
    obtain ⟨hg, ha⟩ := Prog.run_frameM body hw' d h'
    exact ⟨hg.withEnv _, ha⟩
  | Γ, _, .call _ args ret body, hw, d, σ, o, h => by
    cases hwi : Stmt.within μ (Stmt.call _ args ret body)
    case true => exact Stmt.run_frameM_of_within _ hwi d h
    have hw' : (args.readsIn μ && Prog.withinM μ body) = true := by
      simpa only [Stmt.withinM, hwi, Bool.false_or] using hw
    simp only [Bool.and_eq_true] at hw'
    change TRun.call args ret body.ext body.runR σ = .ok o at h
    rw [TRun.call_eq] at h
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    unfold TRun.callFrom at h
    obtain ⟨o', hb, h⟩ := tbind_ok_inv h
    cases h
    have he := CallRet.enterT_frameM (μ := μ) ret (σ.withEnv a)
    obtain ⟨hg, -⟩ := Prog.run_frameM body hw'.2 0 hb
    exact ⟨(((TGFrameM.env σ a (List.prefix_refl _)).trans he
      (ret.enterT (σ.withEnv a)).ext).trans hg _).withEnv _,
      CallRet.leaveT_frameM ret _ σ.env _ d⟩
  | Γ, _, .callRec _ _ args ret body, hw, d, σ, o, h => by
    cases hwi : Stmt.within μ (Stmt.callRec _ _ args ret body)
    case true => exact Stmt.run_frameM_of_within _ hwi d h
    have hw' : (args.readsIn μ && Prog.withinM μ (body ())) = true := by
      simpa only [Stmt.withinM, hwi, Bool.false_or] using hw
    simp only [Bool.and_eq_true] at hw'
    change TRun.call args ret (body ()).ext (body ()).runR σ = .ok o at h
    rw [TRun.call_eq] at h
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    unfold TRun.callFrom at h
    obtain ⟨o', hb, h⟩ := tbind_ok_inv h
    cases h
    have he := CallRet.enterT_frameM (μ := μ) ret (σ.withEnv a)
    obtain ⟨hg, -⟩ := Prog.run_frameM (body ()) hw'.2 0 hb
    exact ⟨(((TGFrameM.env σ a (List.prefix_refl _)).trans he
      (ret.enterT (σ.withEnv a)).ext).trans hg _).withEnv _,
      CallRet.leaveT_frameM ret _ σ.env _ d⟩
  | _, _, .assign .., hw, d, _, _, h
  | _, _, .rebind .., hw, d, _, _, h
  | _, _, .assignLocal .., hw, d, _, _, h
  | _, _, .declLocal .., hw, d, _, _, h
  | _, _, .declStorage .., hw, d, _, _, h
  | _, _, .opAssign .., hw, d, _, _, h
  | _, _, .incDec .., hw, d, _, _, h
  | _, _, .assignIncDec .., hw, d, _, _, h
  | _, _, .assignLocalPush .., hw, d, _, _, h
  | _, _, .push .., hw, d, _, _, h
  | _, _, .pop .., hw, d, _, _, h
  | _, _, .transfer .., hw, d, _, _, h
  | _, _, .send .., hw, d, _, _, h
  | _, _, .assignFromMem .., hw, d, _, _, h
  | _, _, .assignMem .., hw, d, _, _, h
  | _, _, .delete .., hw, d, _, _, h
  | _, _, .deleteMem .., hw, d, _, _, h
  | _, _, .assignNew .., hw, d, _, _, h
  | _, _, .require .., hw, d, _, _, h
  | _, _, .assert .., hw, d, _, _, h
  | _, _, .revert, hw, d, _, _, h
  | _, _, .assumeFalse, hw, d, _, _, h
  | _, _, .tryCall .., hw, d, _, _, h
  | _, _, .loop .., hw, d, _, _, h
  | _, _, .pushOpAssign .., hw, d, _, _, h
  | _, _, .pushIncDec .., hw, d, _, _, h
  | _, _, .callReceiver .., hw, d, _, _, h
  | _, _, .callReceiverPush .., hw, d, _, _, h
  | _, _, .revertData .., hw, d, _, _, h
  | _, _, .catchData .., hw, d, _, _, h =>
    Stmt.run_frameM_of_within _ (by simpa only [Stmt.withinM, Bool.or_false] using hw) d h

/-- **A program that allocates within `μ` runs within `μ`'s grown frame.** -/
theorem Prog.run_frameM : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.withinM μ P = true →
    (d : Nat) → {σ : State C Γ} → {o : Out C σ.H Γ'} → Prog.run σ P = .ok o →
      TGFrameM μ σ o.st o.ext ∧
        TLocAgreeM o.ext d (Prog.writesAt d P) σ.env (TEnv.drop P.ext o.st.env)
  | _, _, .nil, _, _, σ, _, h => by
    cases h
    exact ⟨TGFrameM.ofFrame (TGFrame.refl σ) _, TLocAgreeM.ofAgree rfl (TLocAgree.refl _)⟩
  | _, _, .cons s P, hw, d, σ, o, h => by
    rw [Prog.withinM_cons, Bool.and_eq_true] at hw
    change TRun.seq s.runR P.runR σ = .ok o at h
    unfold TRun.seq at h
    split at h
    · rename_i o₁ hs
      obtain ⟨o₂, h₂, rfl⟩ := tmap_ok_inv h
      obtain ⟨hg₁, ha₁⟩ := Stmt.run_frameM s hw.1 d hs
      obtain ⟨hg₂, ha₂⟩ := Prog.run_frameM P hw.2 (d + s.ext.depth) h₂
      refine ⟨hg₁.trans hg₂ _, ?_⟩
      show TLocAgreeM _ d (Stmt.writesAt d s ++ Prog.writesAt (d + s.ext.depth) P) σ.env
        (TEnv.drop (s.ext.trans P.ext) o₂.st.env)
      rw [TEnv.drop_trans]
      exact ha₁.left.trans (TLocAgreeM.drop s.ext ha₂).right
    · cases h

end

end Progs

end Solidity
