import Solidity.Semantics.Core.TypedRunWk
import Solidity.Calculus.Core.RunFrame

/-!
# A loop body runs within its frame, typed

`Calculus/Core/RunFrame.lean`'s `Prog.run_frame` for the typed run
(`docs/intrinsic.md`, W1 lane `runlemmas`): a program within the mutability
`μ` (`Stmt.within`, `Calculus/Core/Blocks.lean`) keeps the heap and its
typing, the funds and the transaction, and the storage and the ledger too
unless `μ` is `nonpayable` (`TGFrame`); of the locals of the context `d`
below its own, it writes only the ones `writesAt d` lists (`TLocAgree`).

A program within a mutability allocates nothing (no memory statement, no
memory return), so its heap typing is the one it started with; the two
states' heaps and locals are compared heterogeneously (`HEq`), which an
equation of the heap typings (`TGFrame.H`) turns into equality.

A state in a loop body's frame is one `{anon(xs)}` (and `{havoc}` when the
body may write the storage) makes of the loop's first state:
`TState.eq_anonHavoc`, what the loop invariant rules read.
-/

namespace Solidity.Core

open Solidity (Mutability)

variable {C : Contract}

theorem tbind_ok_inv {α β : Type} {x : TRes α} {f : α → TRes β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

theorem tmap_ok_inv {α β : Type} {f : α → β} {x : TRes α} {b : β} (h : x.map f = .ok b) :
    ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

/-! ## Positions -/

namespace TEnv

variable {H : HTy}

theorem get_set_ne {Γ : Ctx} {t u : LTy} : (i : Idx Γ t) → (j : Idx Γ u) → (v : t.TDenote C H) →
    (e : TEnv C H Γ) → i.toNat ≠ j.toNat → TEnv.get j (TEnv.set i v e) = TEnv.get j e
  | .here, .here, _, _, h => absurd rfl h
  | .here, .there _, _, _, _ => rfl
  | .there _, .here, _, _, _ => rfl
  | .there i, .there j, v, e, h => get_set_ne i j v e.2 fun h' => h (congrArg (· + 1) h')

theorem get_set {Γ : Ctx} {t : LTy} : (i : Idx Γ t) → (v : t.TDenote C H) → (e : TEnv C H Γ) →
    TEnv.get i (TEnv.set i v e) = v
  | .here, _, _ => rfl
  | .there i, v, e => get_set i v e.2

theorem get_ext_drop {Γ : Ctx} {t : LTy} (i : Idx Γ t) : {Δ : Ctx} → (h : Ext Γ Δ) →
    (e : TEnv C H Δ) → TEnv.get (i.ext h) e = TEnv.get i (TEnv.drop h e)
  | _, .refl, _ => rfl
  | _, .push h, e => get_ext_drop i h e.2

theorem drop_trans {Γ Δ : Ctx} (a : Ext Γ Δ) : {Ε : Ctx} → (b : Ext Δ Ε) → (e : TEnv C H Ε) →
    TEnv.drop (a.trans b) e = TEnv.drop a (TEnv.drop b e)
  | _, .refl, _ => rfl
  | _, .push b, e => drop_trans a b e.2

/-- Two environments that read alike at every position are equal. -/
theorem ext : {Γ : Ctx} → {e e' : TEnv C H Γ} → (∀ t (i : Idx Γ t), TEnv.get i e = TEnv.get i e') →
    e = e'
  | [], _, _, _ => rfl
  | _ :: _, e, e', h => by
    have h1 : e.1 = e'.1 := h _ .here
    have h2 : e.2 = e'.2 := ext fun t i => h t (.there i)
    show (e.1, e.2) = (e'.1, e'.2)
    rw [h1, h2]

end TEnv

/-- The locals at least `d` deep read alike in `e` and `e'` (over heap
typings that may differ by a proof), but where `W` lists them, by type and
position below `d`. -/
def TLocAgree {Γ : Ctx} {H H' : HTy} (d : Nat) (W : List (LTy × Nat)) (e : TEnv C H Γ)
    (e' : TEnv C H' Γ) : Prop :=
  ∀ (t : LTy) (i : Idx Γ t), d ≤ i.toNat → (t, i.toNat - d) ∉ W →
    HEq (TEnv.get i e') (TEnv.get i e)

namespace TLocAgree

variable {Γ : Ctx} {d : Nat} {W W' : List (LTy × Nat)} {H₁ H₂ H₃ : HTy}

theorem refl (e : TEnv C H₁ Γ) : TLocAgree d W e e := fun _ _ _ _ => HEq.rfl

theorem trans {e₁ : TEnv C H₁ Γ} {e₂ : TEnv C H₂ Γ} {e₃ : TEnv C H₃ Γ}
    (h₁ : TLocAgree d W e₁ e₂) (h₂ : TLocAgree d W e₂ e₃) : TLocAgree d W e₁ e₃ :=
  fun t i hd hw => (h₂ t i hd hw).trans (h₁ t i hd hw)

theorem mono (hW : ∀ x ∈ W, x ∈ W') {e : TEnv C H₁ Γ} {e' : TEnv C H₂ Γ}
    (h : TLocAgree d W e e') : TLocAgree d W' e e' :=
  fun t i hd hw => h t i hd fun hx => hw (hW _ hx)

theorem left {e : TEnv C H₁ Γ} {e' : TEnv C H₂ Γ} (h : TLocAgree d W e e') :
    TLocAgree d (W ++ W') e e' :=
  mono (fun _ hx => List.mem_append_left _ hx) h

theorem right {e : TEnv C H₁ Γ} {e' : TEnv C H₂ Γ} (h : TLocAgree d W' e e') :
    TLocAgree d (W ++ W') e e' :=
  mono (fun _ hx => List.mem_append_right _ hx) h

/-- A local set: the one `Idx.outer` lists. -/
theorem set {t : LTy} (i : Idx Γ t) (v : t.TDenote C H₁) (e : TEnv C H₁ Γ) :
    TLocAgree d (i.outer d) e (TEnv.set i v e) := by
  intro u j hd hw
  refine heq_of_eq (TEnv.get_set_ne i j v e fun hij => hw ?_)
  have hl : d ≤ i.toNat := hij ▸ hd
  have htu : t = u := by
    have h1 := Idx.getElem?_toNat i
    have h2 := Idx.getElem?_toNat j
    rw [hij] at h1
    rw [h1] at h2
    exact Option.some.inj h2
  subst htu
  simp only [Idx.outer, hij, hd, if_true, List.mem_singleton]

/-- The locals over a heap grown by nothing: what they were. -/
theorem wk (e₀ : H₁ <+: H₂) (hH : H₂ = H₁) (e : TEnv C H₁ Γ) :
    TLocAgree d W e (TEnv.wk e₀ Γ e) := by
  intro t i _ _
  rw [TEnv.get_wk]
  exact LTy.TDenote.wk_heq e₀ hH t _

/-- Popped locals: the positions move down by as many. -/
theorem drop {Δ : Ctx} (h : Ext Γ Δ) {e : TEnv C H₁ Δ} {e' : TEnv C H₂ Δ}
    (ha : TLocAgree (d + h.depth) W e e') : TLocAgree d W (TEnv.drop h e) (TEnv.drop h e') := by
  intro t i hd hw
  have := ha t (i.ext h) (by rw [Ext.toNat_idx]; omega)
    (by rw [Ext.toNat_idx, show i.toNat + h.depth - (d + h.depth) = i.toNat - d by omega]; exact hw)
  rwa [TEnv.get_ext_drop, TEnv.get_ext_drop] at this

end TLocAgree

/-! ## The global part -/

/-- **What a run within `μ` leaves of the global part**: the heap and its
typing, the funds and the transaction, and, unless `μ` is `nonpayable`, the
storage and the ledger. -/
structure TGFrame (μ : Mutability) {Γ Δ : Ctx} (σ : TState C Γ) (τ : TState C Δ) : Prop where
  H : τ.H = σ.H
  heap : HEq τ.heap σ.heap
  selfBalance : τ.selfBalance = σ.selfBalance
  tx : τ.tx = σ.tx
  keeps : μ ≠ .nonpayable → τ.storage = σ.storage ∧ τ.net = σ.net

namespace TGFrame

variable {μ : Mutability} {Γ Δ Ε : Ctx}

theorem refl (σ : TState C Γ) : TGFrame μ σ σ := ⟨rfl, HEq.rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem trans {σ : TState C Γ} {τ : TState C Δ} {υ : TState C Ε} (h₁ : TGFrame μ σ τ)
    (h₂ : TGFrame μ τ υ) : TGFrame μ σ υ :=
  ⟨h₂.H.trans h₁.H, h₂.heap.trans h₁.heap, h₂.selfBalance.trans h₁.selfBalance,
    h₂.tx.trans h₁.tx, fun hμ => ⟨(h₂.keeps hμ).1.trans (h₁.keeps hμ).1,
      (h₂.keeps hμ).2.trans (h₁.keeps hμ).2⟩⟩

theorem withEnv {σ : TState C Γ} {τ : TState C Δ} (h : TGFrame μ σ τ) (e : TEnv C τ.H Ε) :
    TGFrame μ σ (τ.withEnv e) := ⟨h.H, h.heap, h.selfBalance, h.tx, h.keeps⟩

theorem env (σ : TState C Γ) (e : TEnv C σ.H Δ) : TGFrame μ σ (σ.withEnv e) :=
  (refl σ).withEnv e

theorem setLocal (σ : TState C Γ) {t : LTy} (i : Idx Γ t) (v : t.TDenote C σ.H) :
    TGFrame μ σ (σ.setLocal i v) := ⟨rfl, HEq.rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem push (σ : TState C Γ) {t : LTy} (v : t.TDenote C σ.H) : TGFrame μ σ (σ.push v) :=
  ⟨rfl, HEq.rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem withStorage (σ : TState C Γ) (st : Storage C) :
    TGFrame .nonpayable σ (σ.withStorage st) :=
  ⟨rfl, HEq.rfl, rfl, rfl, fun h => absurd rfl h⟩

theorem pay (σ : TState C Γ) (a m : Int) : TGFrame .nonpayable σ (σ.pay a m) :=
  ⟨rfl, HEq.rfl, rfl, rfl, fun h => absurd rfl h⟩

end TGFrame

/-! ## Each operation within its frame -/

section Ops

variable {Γ : Ctx} {μ : Mutability}

theorem nonpayable_of_within' {μ : Mutability} (h : (μ == .nonpayable) = true) :
    μ = .nonpayable := by
  simpa only [beq_iff_eq] using h

theorem opStoreT_frame {σ : TState C Γ} (op : BinOp) {p : PrimTy} {r : SRef C (.prim p)}
    {v : p.Denote} {o : Out C σ.H Γ} (h : opStoreT σ op r v = .ok o) :
    TGFrame .nonpayable σ o.st ∧ TLocAgree 0 [] σ.env o.st.env := by
  unfold opStoreT at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨st, _, h⟩ := tbind_ok_inv h
  cases h
  exact ⟨TGFrame.withStorage σ st, TLocAgree.refl _⟩

theorem bumpStoreT_frame {σ : TState C Γ} (op : IncDec) {p : PrimTy} {r : SRef C (.prim p)}
    {o : Out C σ.H Γ} {w : p.Denote} (h : bumpStoreT σ op r = .ok (o, w)) :
    TGFrame .nonpayable σ o.st ∧ TLocAgree 0 [] σ.env o.st.env := by
  unfold bumpStoreT at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨st, _, h⟩ := tbind_ok_inv h
  cases h
  exact ⟨TGFrame.withStorage σ st, TLocAgree.refl _⟩

/-- Of the global part a frame keeps, only what holds for any depth. -/
theorem TLocAgree.nil_any {Γ : Ctx} {H H' : HTy} {d : Nat} {W : List (LTy × Nat)}
    {e : TEnv C H Γ} {e' : TEnv C H' Γ} (h : TLocAgree 0 [] e e') : TLocAgree d W e e' :=
  fun t i _ _ => h t i (Nat.zero_le _) List.not_mem_nil

theorem OpLoc.storeT_frame {p : PrimTy} (op : BinOp) (l : OpLoc C Γ p) (d : Nat) {σ : TState C Γ}
    {v : p.Denote} {o : Out C σ.H Γ} (hl : l.writableIn μ = true) (h : l.storeT σ op v = .ok o) :
    TGFrame μ σ o.st ∧ TLocAgree d (l.writesAt d) σ.env o.st.env := by
  cases l with
  | «local» i =>
    simp only [OpLoc.storeT] at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨TGFrame.setLocal σ i _, TLocAgree.set i _ _⟩
  | root r _ =>
    have hμ : μ = .nonpayable := by
      simpa only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true,
        beq_iff_eq] using hl
    subst hμ
    obtain ⟨hg, ha⟩ := opStoreT_frame op h
    exact ⟨hg, ha.nil_any⟩
  | field b f hf =>
    have hμ : μ = .nonpayable := by
      simpa only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true,
        beq_iff_eq] using hl
    subst hμ
    simp only [OpLoc.storeT] at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨hg, ha⟩ := opStoreT_frame op h
    exact ⟨hg, ha.nil_any⟩
  | index it b i =>
    have hμ : μ = .nonpayable := by
      simpa only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true,
        beq_iff_eq] using hl
    subst hμ
    simp only [OpLoc.storeT] at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨hg, ha⟩ := opStoreT_frame op h
    exact ⟨hg, ha.nil_any⟩
  | mfield =>
    simp only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.and_false, Bool.or_self,
      Bool.false_eq_true] at hl
  | mindex =>
    simp only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.and_false, Bool.or_self,
      Bool.false_eq_true] at hl

theorem OpLoc.bumpT_frame {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) (d : Nat) {σ : TState C Γ}
    {o : Out C σ.H Γ} {w : p.Denote} (hl : l.writableIn μ = true) (h : l.bumpT σ op = .ok (o, w)) :
    TGFrame μ σ o.st ∧ TLocAgree d (l.writesAt d) σ.env o.st.env := by
  cases l with
  | «local» i =>
    simp only [OpLoc.bumpT] at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨TGFrame.setLocal σ i _, TLocAgree.set i _ _⟩
  | root r _ =>
    have hμ : μ = .nonpayable := by
      simpa only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true,
        beq_iff_eq] using hl
    subst hμ
    obtain ⟨hg, ha⟩ := bumpStoreT_frame op h
    exact ⟨hg, ha.nil_any⟩
  | field b f hf =>
    have hμ : μ = .nonpayable := by
      simpa only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true,
        beq_iff_eq] using hl
    subst hμ
    simp only [OpLoc.bumpT] at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨hg, ha⟩ := bumpStoreT_frame op h
    exact ⟨hg, ha.nil_any⟩
  | index it b i =>
    have hμ : μ = .nonpayable := by
      simpa only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true,
        beq_iff_eq] using hl
    subst hμ
    simp only [OpLoc.bumpT] at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨hg, ha⟩ := bumpStoreT_frame op h
    exact ⟨hg, ha.nil_any⟩
  | mfield =>
    simp only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.and_false, Bool.or_self,
      Bool.false_eq_true] at hl
  | mindex =>
    simp only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.and_false, Bool.or_self,
      Bool.false_eq_true] at hl

/-- A call's frame entered, with no memory return: the caller's global part,
nothing allocated. -/
theorem CallRet.enterT_frame {Γ' rs ps : Ctx} (ret : CallRet Γ rs Γ') (hm : ret.noMem = true)
    (σ : TState C ps) : TGFrame μ σ (ret.enterT σ).st := by
  cases ret with
  | none | val | rets => exact ⟨rfl, HEq.rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
  | mem => exact absurd hm Bool.false_ne_true

/-- What a call with no memory return leaves its caller's locals: the result
where it lands, the rest as they were (over a heap typing the call did not
grow). -/
theorem CallRet.leaveT_frame {Γ' rs : Ctx} (ret : CallRet Γ rs Γ') (hm : ret.noMem = true)
    {H H' : HTy} (e₀ : H <+: H') (hH : H' = H) (e : TEnv C H Γ) (x : TEnv C H' rs) (d : Nat) :
    TLocAgree d (ret.writesAt d) e (TEnv.drop ret.ext (ret.leaveT (TEnv.wk e₀ Γ e) x)) := by
  cases ret with
  | none => exact TLocAgree.wk e₀ hH e
  | val p r res =>
    cases res with
    | none => exact TLocAgree.wk e₀ hH e
    | some j => exact (TLocAgree.wk e₀ hH e).trans (TLocAgree.set j _ _)
  | rets bs =>
    show TLocAgree d [] e (TEnv.drop (Ext.append _ _) (TEnv.append _ x (TEnv.wk e₀ Γ e)))
    rw [TEnv.drop_append]
    exact TLocAgree.wk e₀ hH e
  | mem => exact absurd hm Bool.false_ne_true

end Ops

/-! ## A program within its frame -/

section Progs

variable {μ : Mutability}

mutual

/-- **A statement within `μ` runs within `μ`'s frame**, writing of the
context `d` below its own at most `s.writesAt d`. -/
theorem Stmt.trun_frame : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → s.within μ = true → (d : Nat) →
    {σ : TState C Γ} → {o : Out C σ.H Γ'} → s.trun σ = .ok o →
      TGFrame μ σ o.st ∧ TLocAgree d (s.writesAt d) σ.env (TEnv.drop s.ext o.st.env)
  | _, _, .assign l r, hw, d, σ, o, h => by
    have hμ := nonpayable_of_within' hw
    subst hμ
    change TRun.assign l r σ = .ok o at h
    simp only [TRun.assign] at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨st, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨TGFrame.withStorage σ st, TLocAgree.refl _⟩
  | _, _, .assignLocal i r, _, d, σ, o, h => by
    change TRun.assignLocal i r σ = .ok o at h
    simp only [TRun.assignLocal] at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨TGFrame.setLocal σ i _, TLocAgree.set i _ _⟩
  | _, _, .declLocal p _ init, _, d, σ, o, h => by
    change TRun.declLocal p init σ = .ok o at h
    cases init with
    | none =>
      cases h
      exact ⟨TGFrame.push (t := .val p) σ _, TLocAgree.refl _⟩
    | some e =>
      simp only [TRun.declLocal] at h
      obtain ⟨_, _, h⟩ := tbind_ok_inv h
      cases h
      exact ⟨TGFrame.push (t := .val p) σ _, TLocAgree.refl _⟩
  | _, _, .opAssign op _ _ l r, hw, d, σ, o, h => by
    have hw' : (r.readsIn μ && l.writableIn μ) = true := hw
    rw [Bool.and_eq_true] at hw'
    change TRun.opAssign op l r σ = .ok o at h
    simp only [TRun.opAssign] at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    exact OpLoc.storeT_frame op l d hw'.2 h
  | _, _, .incDec op _ l, hw, d, σ, o, h => by
    change TRun.incDec op l σ = .ok o at h
    simp only [TRun.incDec] at h
    obtain ⟨⟨o', w⟩, hb, h⟩ := tbind_ok_inv h
    cases h
    exact OpLoc.bumpT_frame op l d hw hb
  | _, _, .assignIncDec i op _ l _, hw, d, σ, o, h => by
    change TRun.assignIncDec i op l σ = .ok o at h
    simp only [TRun.assignIncDec] at h
    obtain ⟨⟨o', w⟩, hb, h⟩ := tbind_ok_inv h
    cases h
    obtain ⟨hg, ha⟩ := OpLoc.bumpT_frame op l d hw hb
    exact ⟨hg.trans (TGFrame.setLocal _ i w), ha.right.trans (TLocAgree.set i w o'.st.env).left⟩
  | _, _, .transfer r a, hw, d, σ, o, h => by
    have hμ := nonpayable_of_within' hw
    subst hμ
    change TRun.transfer r a σ = .ok o at h
    simp only [TRun.transfer] at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨TGFrame.pay σ _ _, TLocAgree.refl _⟩
  | _, _, .send pv r a, hw, d, σ, o, h => by
    have hμ := nonpayable_of_within' hw
    subst hμ
    change TRun.send pv r a σ = .ok o at h
    simp only [TRun.send] at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    unfold sendT
    rcases Semantics.lookupBy (sendKey _ _) σ.tx.ext with _ | (_ | _ | _ | _) <;>
      first
      | exact ⟨(TGFrame.pay σ _ _).trans (TGFrame.setLocal _ pv _), TLocAgree.set pv _ _⟩
      | exact ⟨TGFrame.setLocal σ pv _, TLocAgree.set pv _ _⟩
  | _, _, .delete l, hw, d, σ, o, h => by
    have hμ := nonpayable_of_within' hw
    subst hμ
    change TRun.delete l σ = .ok o at h
    simp only [TRun.delete] at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨st, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨TGFrame.withStorage σ st, TLocAgree.refl _⟩
  | _, _, .ite c thn els, hw, d, σ, o, h => by
    have hw' : (c.readsIn μ && Prog.within μ thn && Prog.within μ els) = true := hw
    simp only [Bool.and_eq_true] at hw'
    change TRun.ite c thn.ext thn.trunR els.ext els.trunR σ = .ok o at h
    simp only [TRun.ite] at h
    obtain ⟨v, _, h⟩ := tbind_ok_inv h
    split at h
    · obtain ⟨o', h', rfl⟩ := tmap_ok_inv h
      obtain ⟨hg, ha⟩ := Prog.trun_frame thn hw'.1.2 d h'
      exact ⟨hg.withEnv _, ha.left⟩
    · obtain ⟨o', h', rfl⟩ := tmap_ok_inv h
      obtain ⟨hg, ha⟩ := Prog.trun_frame els hw'.2 d h'
      exact ⟨hg.withEnv _, ha.right⟩
  | _, _, .require c, _, d, σ, o, h => by
    change TRun.require c σ = .ok o at h
    simp only [TRun.require] at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    split at h
    · cases h
      exact ⟨TGFrame.refl σ, TLocAgree.refl _⟩
    · cases h
  | _, _, .assert c, _, d, σ, o, h => by
    change TRun.assert c σ = .ok o at h
    simp only [TRun.assert] at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    split at h
    · cases h
      exact ⟨TGFrame.refl σ, TLocAgree.refl _⟩
    · cases h
  | _, _, .revert, _, _, _, _, h => by cases h
  | _, _, .call _ args ret body, hw, d, σ, o, h => by
    have hw' : (args.readsIn μ && ret.noMem && Prog.within μ body) = true := hw
    simp only [Bool.and_eq_true] at hw'
    change TRun.call args ret body.ext body.trunR σ = .ok o at h
    rw [TRun.call_eq] at h
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    unfold TRun.callFrom at h
    obtain ⟨o', hb, h⟩ := tbind_ok_inv h
    cases h
    have he := CallRet.enterT_frame (μ := μ) ret hw'.1.2 (σ.withEnv a)
    obtain ⟨hg, -⟩ := Prog.trun_frame body hw'.2 0 hb
    have hg' := ((TGFrame.env σ a).trans he).trans hg
    exact ⟨hg'.withEnv _, CallRet.leaveT_frame ret hw'.1.2 _ hg'.H σ.env _ d⟩
  | _, _, .loop _ c body, hw, d, σ, o, h => by
    have hw' : (c.readsIn μ && Prog.within μ body) = true := hw
    rw [Bool.and_eq_true] at hw'
    change TLoop.run (fun o : Out C σ.H _ => (body.trunR o.st).map
        fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩) (fun o => c.evalT o.st)
        ⟨σ, List.prefix_refl _⟩ = .ok o at h
    refine TLoop.run_induct
      (P := fun a : Out C σ.H _ =>
        TGFrame μ σ a.st ∧ TLocAgree d (Prog.writesAt d body) σ.env a.st.env)
      (Q := fun r => ∀ o, r = .ok o →
        TGFrame μ σ o.st ∧ TLocAgree d (Prog.writesAt d body) σ.env o.st.env)
      ⟨TGFrame.refl σ, TLocAgree.refl _⟩ (fun a ha => ?_) (fun _ h => by cases h) o h
    unfold TLoop.step
    dsimp only
    cases c.evalT a.st with
    | error => dsimp only; intro _ h; cases h
    | ok v =>
      cases v with
      | false => dsimp only; intro _ h; cases h; exact ha
      | true =>
        dsimp only
        cases hb : (body.trunR a.st).map
            (fun o' => (⟨o'.st.drop body.ext, a.ext.trans o'.ext⟩ : Out C σ.H _)) with
        | error => dsimp only; intro _ h; cases h
        | ok a' =>
          dsimp only
          obtain ⟨o', hb', rfl⟩ := tmap_ok_inv hb
          obtain ⟨hg, ha'⟩ := Prog.trun_frame body hw'.2 d hb'
          exact ⟨ha.1.trans (hg.withEnv _), ha.2.trans ha'⟩
  | _, _, .block body, hw, d, σ, o, h => by
    change (body.trunR σ).map (fun o => ⟨o.st.drop body.ext, o.ext⟩) = .ok o at h
    obtain ⟨o', h', rfl⟩ := tmap_ok_inv h
    obtain ⟨hg, ha⟩ := Prog.trun_frame body hw d h'
    exact ⟨hg.withEnv _, ha⟩
  | _, _, .rebind .., hw, _, _, _, _ | _, _, .declStorage .., hw, _, _, _, _
  | _, _, .push .., hw, _, _, _, _ | _, _, .pop _, hw, _, _, _, _
  | _, _, .declMem .., hw, _, _, _, _ | _, _, .rebindMem .., hw, _, _, _, _
  | _, _, .assignFromMem .., hw, _, _, _, _ | _, _, .assignMem .., hw, _, _, _, _
  | _, _, .deleteMem .., hw, _, _, _, _ | _, _, .assignNew .., hw, _, _, _, _
  | _, _, .tryCall .., hw, _, _, _, _ => by cases hw

/-- **A program within `μ` runs within `μ`'s frame.** -/
theorem Prog.trun_frame : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.within μ P = true → (d : Nat) →
    {σ : TState C Γ} → {o : Out C σ.H Γ'} → Prog.trun σ P = .ok o →
      TGFrame μ σ o.st ∧ TLocAgree d (Prog.writesAt d P) σ.env (TEnv.drop P.ext o.st.env)
  | _, _, .nil, _, _, σ, _, h => by cases h; exact ⟨TGFrame.refl σ, TLocAgree.refl _⟩
  | _, _, .cons s P, hw, d, σ, o, h => by
    have hw' : (Stmt.within μ s && Prog.within μ P) = true := hw
    rw [Bool.and_eq_true] at hw'
    change TRun.seq s.trunR P.trunR σ = .ok o at h
    unfold TRun.seq at h
    split at h
    · rename_i o₁ hs
      obtain ⟨o₂, h₂, rfl⟩ := tmap_ok_inv h
      obtain ⟨hg₁, ha₁⟩ := Stmt.trun_frame s hw'.1 d hs
      obtain ⟨hg₂, ha₂⟩ := Prog.trun_frame P hw'.2 (d + s.ext.depth) h₂
      refine ⟨hg₁.trans hg₂, ?_⟩
      show TLocAgree d (Stmt.writesAt d s ++ Prog.writesAt (d + s.ext.depth) P) σ.env
        (TEnv.drop (s.ext.trans P.ext) o₂.st.env)
      rw [TEnv.drop_trans]
      exact ha₁.left.trans (TLocAgree.drop s.ext ha₂).right
    · cases h

end

end Progs

/-! ## The loop frame, anonymised -/

section Anon

variable {Γ : Ctx}

/-- The locals `xs` set as `b` says: a loop body's frame anonymised. -/
def TState.anon (σ : TState C Γ) (xs : List ((t : LTy) × Idx Γ t))
    (b : (x : (t : LTy) × Idx Γ t) → x.1.TDenote C σ.H) : TState C Γ :=
  σ.withEnv (xs.foldl (fun e x => TEnv.set x.2 (b x) e) σ.env)

/-- The state after a callback: storage and ledger replaced by what the
callee left, the locals, memory and funds kept (`Semantics.State.havoc`). -/
def TState.havoc (σ : TState C Γ) (st : Storage C) (nt : List (Int × Int)) : TState C Γ :=
  { σ with storage := st, net := nt }

theorem TState.havoc_self (σ : TState C Γ) : σ.havoc σ.storage σ.net = σ := rfl

/-- What the anonymised locals read at a position: the value `b` gives where
`xs` lists it, the old one elsewhere. -/
theorem TEnv.foldl_set_get {H : HTy} (xs : List ((t : LTy) × Idx Γ t))
    (b : (x : (t : LTy) × Idx Γ t) → x.1.TDenote C H) {t : LTy} (i : Idx Γ t) :
    (e : TEnv C H Γ) →
      ((⟨t, i⟩ : (t : LTy) × Idx Γ t) ∈ xs →
        TEnv.get i (xs.foldl (fun e x => TEnv.set x.2 (b x) e) e) = b ⟨t, i⟩) ∧
      ((⟨t, i⟩ : (t : LTy) × Idx Γ t) ∉ xs →
        TEnv.get i (xs.foldl (fun e x => TEnv.set x.2 (b x) e) e) = TEnv.get i e) := by
  induction xs with
  | nil => intro e; exact ⟨fun h => (by cases h), fun _ => rfl⟩
  | cons x xs ih =>
    intro e
    rw [List.foldl_cons]
    have hne : x ≠ ⟨t, i⟩ → x.2.toNat ≠ i.toNat := by
      obtain ⟨u, j⟩ := x
      intro hx hji
      have hut : u = t := by
        have h1 := Idx.getElem?_toNat j
        have h2 := Idx.getElem?_toNat i
        rw [hji] at h1
        rw [h1] at h2
        exact Option.some.inj h2
      subst hut
      exact hx (by rw [Idx.toNat_inj j i hji])
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · by_cases hx : (⟨t, i⟩ : (t : LTy) × Idx Γ t) ∈ xs
      · exact (ih _).1 hx
      · have hxe : x = ⟨t, i⟩ := by
          rcases List.mem_cons.1 hm with h | h
          · exact h.symm
          · exact absurd h hx
        rw [(ih _).2 hx]
        subst hxe
        exact TEnv.get_set i _ e
    · have hx : (⟨t, i⟩ : (t : LTy) × Idx Γ t) ∉ xs := fun h => hm (List.mem_cons_of_mem _ h)
      rw [(ih _).2 hx]
      exact TEnv.get_set_ne x.2 i _ e (hne fun h => hm (h ▸ List.mem_cons_self ..))

/-- **A state in a loop body's frame is one its anonymised premise covers**:
`{anon(xs)}` of the loop's first state, then the storage and the ledger
replaced (`{havoc}`), reaches every state that agrees with it but where the
body may write; when the frame is `view` the storage and the ledger are
kept, so the `{havoc}` changes nothing (`TGFrame.keeps`). -/
theorem TState.eq_anonHavoc {σ τ : TState C Γ} {xs : List ((t : LTy) × Idx Γ t)} {μ : Mutability}
    {W : List (LTy × Nat)}
    (hxs : ∀ t (i : Idx Γ t), (t, i.toNat) ∈ W → (⟨t, i⟩ : (t : LTy) × Idx Γ t) ∈ xs)
    (hg : TGFrame μ σ τ) (ha : TLocAgree 0 W σ.env τ.env) :
    ∃ b, τ = (σ.anon xs b).havoc τ.storage τ.net := by
  obtain ⟨st, H, hp, env, net, sb, tx⟩ := τ
  obtain ⟨hH, hhp, hsb, htx, -⟩ := hg
  dsimp only at hH hhp hsb htx
  subst hH hsb htx
  cases hhp
  let b : (x : (t : LTy) × Idx Γ t) → x.1.TDenote C σ.H := fun x => TEnv.get x.2 env
  refine ⟨b, ?_⟩
  have henv : xs.foldl (fun e x => TEnv.set x.2 (b x) e) σ.env = env := TEnv.ext fun t i => by
    by_cases hm : (⟨t, i⟩ : (t : LTy) × Idx Γ t) ∈ xs
    · exact (TEnv.foldl_set_get xs b i σ.env).1 hm
    · rw [(TEnv.foldl_set_get xs b i σ.env).2 hm]
      exact (eq_of_heq (ha t i (Nat.zero_le _)
        fun hw => hm (hxs t i (by rwa [Nat.sub_zero] at hw)))).symm
  simp only [TState.havoc, TState.anon, TState.withEnv, henv]

/-- A loop body with a frame runs within its mutability, and its frame lists
every local of the loop's context it may write (`Prog.frame_some`), so its
outcome is one `{anon(xs)}`/`{havoc}` covers. -/
theorem Prog.trun_frame_anon {Γ₁ : Ctx} {P : Prog C Γ Γ₁} {xs : List ((t : LTy) × Idx Γ t)}
    {hv : Bool} (hf : P.frame = some (xs, hv)) {σ : TState C Γ} {o : Out C σ.H Γ₁}
    (h : Prog.trun σ P = .ok o) :
    TGFrame (frameMut hv) σ (o.st.drop P.ext) ∧
      ∃ b, o.st.drop P.ext = (σ.anon xs b).havoc (o.st.drop P.ext).storage
        (o.st.drop P.ext).net := by
  obtain ⟨hw, hxs⟩ := Prog.frame_some hf
  obtain ⟨hg, ha⟩ := Prog.trun_frame P hw 0 h
  have hg' : TGFrame (frameMut hv) σ (o.st.drop P.ext) := hg.withEnv _
  exact ⟨hg', TState.eq_anonHavoc hxs hg' ha⟩

end Anon

end Solidity.Core
