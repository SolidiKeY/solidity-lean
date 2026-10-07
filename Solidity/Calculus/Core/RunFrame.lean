import Solidity.Calculus.Core.Blocks
import Solidity.Calculus.Core.Logic
import Solidity.Semantics.Mutability
import Solidity.Typing.Soundness

/-!
# A loop body runs within its frame

`Mutability.lean`'s `Prog.frame_of_within` on the scoped syntax: a program
within the mutability `μ` (`Stmt.within`, `Calculus/Core/Blocks.lean`) leaves
the memory, the funds and the transaction as they were, and the storage and
the ledger too unless `μ` is `nonpayable` (`GFrame`); of the locals of the
context `d` below its own, it writes only the ones `writesAt d` lists, by
type and position there (`LocAgree`).  The body's own locals are popped before
the frame is read (`Env.drop s.ext`), so they need no listing.

`holds_anonHavoc` is what the loop invariant rules read: a state in a body's
frame `(xs, hv)` (`Prog.frame_some`) is one `{anon(xs)}`, with `{havoc}` when
`hv`, makes of the first (`State.anon_get`).
-/

namespace Solidity.Core

open Semantics (Value Res Halt bind_ok_inv)
open Solidity (Mutability)

variable {C : Contract}

/-! ## Positions -/

namespace Env

theorem get_set_ne {Γ : Ctx} {t u : LTy} : (i : Idx Γ t) → (j : Idx Γ u) → (v : t.Denote C) →
    (e : Env C Γ) → i.toNat ≠ j.toNat → Env.get j (Env.set i v e) = Env.get j e
  | .here, .here, _, _, h => absurd rfl h
  | .here, .there _, _, _, _ => rfl
  | .there _, .here, _, _, _ => rfl
  | .there i, .there j, v, e, h => get_set_ne i j v e.2 fun h' => h (congrArg (· + 1) h')

theorem get_ext_drop {Γ : Ctx} {t : LTy} (i : Idx Γ t) : {Δ : Ctx} → (h : Ext Γ Δ) →
    (e : Env C Δ) → Env.get (i.ext h) e = Env.get i (Env.drop h e)
  | _, .refl, _ => rfl
  | _, .push h, e => get_ext_drop i h e.2

theorem drop_trans {Γ Δ : Ctx} (a : Ext Γ Δ) : {Ε : Ctx} → (b : Ext Δ Ε) → (e : Env C Ε) →
    Env.drop (a.trans b) e = Env.drop a (Env.drop b e)
  | _, .refl, _ => rfl
  | _, .push b, e => drop_trans a b e.2

/-- Two environments that read alike at every position are equal. -/
theorem ext : {Γ : Ctx} → {e e' : Env C Γ} → (∀ t (i : Idx Γ t), Env.get i e = Env.get i e') →
    e = e'
  | [], _, _, _ => rfl
  | _ :: _, e, e', h => by
    have h1 : e.1 = e'.1 := h _ .here
    have h2 : e.2 = e'.2 := ext fun t i => h t (.there i)
    show (e.1, e.2) = (e'.1, e'.2)
    rw [h1, h2]

end Env

/-- The locals at least `d` deep read alike in `e` and `e'`, but where `W`
lists them, by type and position below `d`. -/
def LocAgree {Γ : Ctx} (d : Nat) (W : List (LTy × Nat)) (e e' : Env C Γ) : Prop :=
  ∀ (t : LTy) (i : Idx Γ t), d ≤ i.toNat → (t, i.toNat - d) ∉ W → Env.get i e' = Env.get i e

namespace LocAgree

variable {Γ : Ctx} {d : Nat} {W W' : List (LTy × Nat)}

theorem refl (e : Env C Γ) : LocAgree d W e e := fun _ _ _ _ => rfl

theorem trans {e₁ e₂ e₃ : Env C Γ} (h₁ : LocAgree d W e₁ e₂) (h₂ : LocAgree d W e₂ e₃) :
    LocAgree d W e₁ e₃ :=
  fun t i hd hw => (h₂ t i hd hw).trans (h₁ t i hd hw)

theorem mono (hW : ∀ x ∈ W, x ∈ W') {e e' : Env C Γ} (h : LocAgree d W e e') : LocAgree d W' e e' :=
  fun t i hd hw => h t i hd fun hx => hw (hW _ hx)

theorem left {e e' : Env C Γ} (h : LocAgree d W e e') : LocAgree d (W ++ W') e e' :=
  mono (fun _ hx => List.mem_append_left _ hx) h

theorem right {e e' : Env C Γ} (h : LocAgree d W' e e') : LocAgree d (W ++ W') e e' :=
  mono (fun _ hx => List.mem_append_right _ hx) h

/-- A local set: the one `Idx.outer` lists. -/
theorem set {t : LTy} (i : Idx Γ t) (v : t.Denote C) (e : Env C Γ) :
    LocAgree d (i.outer d) e (Env.set i v e) := by
  intro u j hd hw
  refine Env.get_set_ne i j v e fun hij => hw ?_
  have hl : d ≤ i.toNat := hij ▸ hd
  have htu : t = u := by
    have h1 := Idx.getElem?_toNat i
    have h2 := Idx.getElem?_toNat j
    rw [hij] at h1
    rw [h1] at h2
    exact Option.some.inj h2
  subst htu
  simp only [Idx.outer, hij, hd, if_true, List.mem_singleton]

/-- Popped locals: the positions move down by as many. -/
theorem drop {Δ : Ctx} (h : Ext Γ Δ) {e e' : Env C Δ} (ha : LocAgree (d + h.depth) W e e') :
    LocAgree d W (Env.drop h e) (Env.drop h e') := by
  intro t i hd hw
  have := ha t (i.ext h) (by rw [Ext.toNat_idx]; omega)
    (by rw [Ext.toNat_idx, show i.toNat + h.depth - (d + h.depth) = i.toNat - d by omega]; exact hw)
  rwa [Env.get_ext_drop, Env.get_ext_drop] at this

end LocAgree

/-! ## The global part -/

/-- **What a run within `μ` leaves of the global part**: the memory, the
funds and the transaction, and, unless `μ` is `nonpayable`, the storage and
the ledger (`Mutability.Frame`). -/
structure GFrame (μ : Mutability) {Γ Δ : Ctx} (σ : State C Γ) (τ : State C Δ) : Prop where
  heap : τ.heap = σ.heap
  nextId : τ.nextId = σ.nextId
  selfBalance : τ.selfBalance = σ.selfBalance
  tx : τ.tx = σ.tx
  keeps : μ ≠ .nonpayable → τ.storage = σ.storage ∧ τ.net = σ.net

namespace GFrame

variable {μ : Mutability} {Γ Δ Ε : Ctx}

theorem refl (σ : State C Γ) : GFrame μ σ σ := ⟨rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem trans {σ : State C Γ} {τ : State C Δ} {υ : State C Ε} (h₁ : GFrame μ σ τ)
    (h₂ : GFrame μ τ υ) : GFrame μ σ υ :=
  ⟨h₂.heap.trans h₁.heap, h₂.nextId.trans h₁.nextId, h₂.selfBalance.trans h₁.selfBalance,
    h₂.tx.trans h₁.tx, fun hμ => ⟨(h₂.keeps hμ).1.trans (h₁.keeps hμ).1,
      (h₂.keeps hμ).2.trans (h₁.keeps hμ).2⟩⟩

theorem withEnv {σ : State C Γ} {τ : State C Δ} (h : GFrame μ σ τ) (e : Env C Ε) :
    GFrame μ σ (τ.withEnv e) := ⟨h.heap, h.nextId, h.selfBalance, h.tx, h.keeps⟩

theorem withEnvL {σ : State C Γ} {τ : State C Δ} (e : Env C Ε) (h : GFrame μ σ τ) :
    GFrame μ (σ.withEnv e) τ := ⟨h.heap, h.nextId, h.selfBalance, h.tx, h.keeps⟩

theorem env (σ : State C Γ) (e : Env C Δ) : GFrame μ σ (σ.withEnv e) := (refl σ).withEnv e

/-- A step of the global part within `Mutability.lean`'s frame. -/
theorem ofFrame {W : List Var} {σ : State C Γ} {g : Semantics.State} (h : μ.Frame W σ.glob g) :
    GFrame μ σ (σ.withGlob g) := by
  cases μ with
  | nonpayable => exact ⟨h.heap.symm, h.nextId.symm, h.selfBalance.symm, h.tx.symm, fun h' => absurd rfl h'⟩
  | pure =>
    have h' : Semantics.EnvAgreeExcept W σ.glob g := h
    exact ⟨h'.heap.symm, h'.nextId.symm, h'.selfBalance.symm, h'.tx.symm,
      fun _ => ⟨h'.storage.symm, h'.net.symm⟩⟩
  | view =>
    have h' : Semantics.EnvAgreeExcept W σ.glob g := h
    exact ⟨h'.heap.symm, h'.nextId.symm, h'.selfBalance.symm, h'.tx.symm,
      fun _ => ⟨h'.storage.symm, h'.net.symm⟩⟩

end GFrame

/-! ## Each statement within its frame -/

section Stmts

variable {Γ : Ctx} {μ : Mutability}

theorem guardOk_eq' {α : Type} {v : Value} {a b : α} (h : guardOk v a = .ok b) : a = b := by
  unfold guardOk at h
  split at h <;> first | (cases h; rfl) | cases h

theorem assertOk_eq' {α : Type} {v : Value} {a b : α} (h : assertOk v a = .ok b) : a = b := by
  unfold assertOk at h
  split at h <;> first | (cases h; rfl) | cases h

theorem OpLoc.store_frame {p : PrimTy} (op : BinOp) (l : OpLoc C Γ p) (d : Nat) {σ υ : State C Γ}
    {v : Value} (hl : l.writableIn μ = true) (h : l.store σ op v = .ok υ) :
    GFrame μ σ υ ∧ LocAgree d (l.writesAt d) σ.env υ.env := by
  cases l with
  | «local» i =>
    change opLocal σ op p i v = .ok υ at h
    unfold opLocal at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    cases h
    exact ⟨GFrame.env σ _, LocAgree.set i _ _⟩
  | root r _ =>
    have hμ : μ = .nonpayable := by
      simpa only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true,
        beq_iff_eq] using hl
    subst hμ
    obtain ⟨g, hg, rfl⟩ := map_ok_inv h
    exact ⟨GFrame.ofFrame (Mutability.opStore_frame (W := []) hg), LocAgree.refl _⟩
  | field b f hf =>
    have hμ : μ = .nonpayable := by
      simpa only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true,
        beq_iff_eq] using hl
    subst hμ
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨g, hg, rfl⟩ := map_ok_inv h
    exact ⟨GFrame.ofFrame (Mutability.opStore_frame (W := []) hg), LocAgree.refl _⟩
  | index it b i =>
    have hμ : μ = .nonpayable := by
      simpa only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true,
        beq_iff_eq] using hl
    subst hμ
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨g, hg, rfl⟩ := map_ok_inv h
    exact ⟨GFrame.ofFrame (Mutability.opStore_frame (W := []) hg), LocAgree.refl _⟩
  | mfield =>
    simp only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.and_false, Bool.or_self,
      Bool.false_eq_true] at hl
  | mindex =>
    simp only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.and_false, Bool.or_self,
      Bool.false_eq_true] at hl

theorem OpLoc.bump_frame {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) (d : Nat) {σ υ : State C Γ}
    {w : Value} (hl : l.writableIn μ = true) (h : l.bump σ op = .ok (υ, w)) :
    GFrame μ σ υ ∧ LocAgree d (l.writesAt d) σ.env υ.env := by
  cases l with
  | «local» i =>
    change bumpLocal σ op p i = .ok (υ, w) at h
    unfold bumpLocal at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    cases h
    exact ⟨GFrame.env σ _, LocAgree.set i _ _⟩
  | root r _ =>
    have hμ : μ = .nonpayable := by
      simpa only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true,
        beq_iff_eq] using hl
    subst hμ
    obtain ⟨⟨g, v⟩, hg, he⟩ := map_ok_inv h
    cases he
    exact ⟨GFrame.ofFrame (Mutability.bumpStore_frame (W := []) hg), LocAgree.refl _⟩
  | field b f hf =>
    have hμ : μ = .nonpayable := by
      simpa only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true,
        beq_iff_eq] using hl
    subst hμ
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨⟨g, v⟩, hg, he⟩ := map_ok_inv h
    cases he
    exact ⟨GFrame.ofFrame (Mutability.bumpStore_frame (W := []) hg), LocAgree.refl _⟩
  | index it b i =>
    have hμ : μ = .nonpayable := by
      simpa only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true,
        beq_iff_eq] using hl
    subst hμ
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨⟨g, v⟩, hg, he⟩ := map_ok_inv h
    cases he
    exact ⟨GFrame.ofFrame (Mutability.bumpStore_frame (W := []) hg), LocAgree.refl _⟩
  | mfield =>
    simp only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.and_false, Bool.or_self,
      Bool.false_eq_true] at hl
  | mindex =>
    simp only [OpLoc.writableIn, OpLoc.isLocal, OpLoc.isStorage, Bool.and_false, Bool.or_self,
      Bool.false_eq_true] at hl

end Stmts

/-! ## A program within its frame -/

section Progs

variable {μ : Mutability}

theorem map_ok_inv' {Γ Δ : Ctx} {f : State C Γ → State C Δ} {x : Res (State C Γ)} {b : State C Δ}
    (h : x.map f = .ok b) : ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

theorem nonpayable_of_within {μ : Mutability} (h : (μ == .nonpayable) = true) :
    μ = .nonpayable := by
  simpa only [beq_iff_eq] using h

mutual

/-- **A statement within `μ` runs within `μ`'s frame**, writing of the
context `d` below its own at most `s.writesAt d`. -/
theorem Stmt.run_frame : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → s.within μ = true → (d : Nat) →
    {σ : State C Γ} → {υ : State C Γ'} → s.run σ = .ok υ →
      GFrame μ σ υ ∧ LocAgree d (s.writesAt d) σ.env (Env.drop s.ext υ.env)
  | _, _, .assign l r, hw, d, σ, υ, h => by
    have hμ := nonpayable_of_within hw
    subst hμ
    change Run.assign l r σ = .ok υ at h
    unfold Run.assign at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok_inv h
    obtain ⟨g, hg, rfl⟩ := map_ok_inv h
    exact ⟨GFrame.ofFrame (Mutability.writeStorage_frame (W := []) hg), LocAgree.refl _⟩
  | _, _, .assignLocal i r, _, d, σ, υ, h => by
    change Run.assignLocal i r σ = .ok υ at h
    unfold Run.assignLocal at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    cases h
    exact ⟨GFrame.env σ _, LocAgree.set i _ _⟩
  | _, _, .declLocal p _ init, _, d, σ, υ, h => by
    change Run.declLocal p init σ = .ok υ at h
    unfold Run.declLocal at h
    cases init with
    | none =>
      cases h
      exact ⟨GFrame.env σ _, LocAgree.refl _⟩
    | some e =>
      obtain ⟨_, _, h⟩ := bind_ok_inv h
      cases h
      exact ⟨GFrame.env σ _, LocAgree.refl _⟩
  | _, _, .opAssign op _ _ l r, hw, d, σ, υ, h => by
    have hw' : (r.readsIn μ && l.writableIn μ) = true := hw
    rw [Bool.and_eq_true] at hw'
    change Run.opAssign op l r σ = .ok υ at h
    unfold Run.opAssign at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    exact OpLoc.store_frame op l d hw'.2 h
  | _, _, .incDec op _ l, hw, d, σ, υ, h => by
    change Run.incDec op l σ = .ok υ at h
    unfold Run.incDec at h
    obtain ⟨⟨υ', w⟩, hb, h⟩ := bind_ok_inv h
    cases h
    exact OpLoc.bump_frame op l d hw hb
  | _, _, .assignIncDec i op _ l _, hw, d, σ, υ, h => by
    change Run.assignIncDec i op l σ = .ok υ at h
    unfold Run.assignIncDec at h
    obtain ⟨⟨υ', w⟩, hb, h⟩ := bind_ok_inv h
    cases h
    obtain ⟨hg, ha⟩ := OpLoc.bump_frame op l d hw hb
    exact ⟨hg.withEnv _, ha.right.trans (LocAgree.set i w υ'.env).left⟩
  | _, _, .transfer r a, hw, d, σ, υ, h => by
    have hμ := nonpayable_of_within hw
    subst hμ
    change Run.transfer r a σ = .ok υ at h
    unfold Run.transfer at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨g, hg, rfl⟩ := map_ok_inv h
    unfold Solidity.transferAt at hg
    split at hg
    · cases hg
    · cases hg
      exact ⟨GFrame.ofFrame (Mutability.Frame.net [] σ.glob _), LocAgree.refl _⟩
  | _, _, .send pv r a, hw, d, σ, υ, h => by
    have hμ := nonpayable_of_within hw
    subst hμ
    change Run.send pv r a σ = .ok υ at h
    unfold Run.send at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    unfold sendAt at h
    split at h
    · cases h
    · split at h <;> cases h <;>
        first
        | exact ⟨(GFrame.ofFrame (Mutability.Frame.net [] σ.glob _)).withEnv _, LocAgree.set pv _ _⟩
        | exact ⟨GFrame.env σ _, LocAgree.set pv _ _⟩
  | _, _, .delete l, hw, d, σ, υ, h => by
    have hμ := nonpayable_of_within hw
    subst hμ
    change Run.delete l σ = .ok υ at h
    unfold Run.delete at h
    obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨g, hg, rfl⟩ := map_ok_inv h
    exact ⟨GFrame.ofFrame (Mutability.saveStorage_frame (W := []) hg), LocAgree.refl _⟩
  | _, _, .ite c thn els, hw, d, σ, υ, h => by
    have hw' : (c.readsIn μ && Prog.within μ thn && Prog.within μ els) = true := hw
    simp only [Bool.and_eq_true] at hw'
    change Run.ite c thn.ext thn.runR els.ext els.runR σ = .ok υ at h
    unfold Run.ite at h
    obtain ⟨v, _, h⟩ := bind_ok_inv h
    rcases v with _ | (_ | _)
    · cases h
    · obtain ⟨υ', h', rfl⟩ := map_ok_inv' h
      obtain ⟨hg, ha⟩ := Prog.run_frame els hw'.2 d h'
      exact ⟨hg.withEnv _, ha.right⟩
    · obtain ⟨υ', h', rfl⟩ := map_ok_inv' h
      obtain ⟨hg, ha⟩ := Prog.run_frame thn hw'.1.2 d h'
      exact ⟨hg.withEnv _, ha.left⟩
  | _, _, .require c, _, d, σ, υ, h => by
    change (c.eval σ >>= fun v => guardOk v σ) = .ok υ at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    cases guardOk_eq' h
    exact ⟨GFrame.refl σ, LocAgree.refl _⟩
  | _, _, .assert c, _, d, σ, υ, h => by
    change (c.eval σ >>= fun v => assertOk v σ) = .ok υ at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    cases assertOk_eq' h
    exact ⟨GFrame.refl σ, LocAgree.refl _⟩
  | _, _, .revert, _, _, _, _, h => by cases h
  | _, _, .call _ args ret body, hw, d, σ, υ, h => by
    have hw' : (args.readsIn μ && ret.noMem && Prog.within μ body) = true := hw
    simp only [Bool.and_eq_true] at hw'
    change Run.call args ret body.ext body.runR σ = .ok υ at h
    unfold Run.call at h
    obtain ⟨a, _, h⟩ := bind_ok_inv h
    obtain ⟨⟨g, r⟩, he, h⟩ := bind_ok_inv h
    obtain ⟨υ', hb, h⟩ := bind_ok_inv h
    cases h
    obtain ⟨hg, -⟩ := Prog.run_frame body hw'.2 0 hb
    cases ret with
    | none =>
      cases he
      exact ⟨((GFrame.env σ _).trans hg).withEnv _, LocAgree.refl _⟩
    | val p x res =>
      cases he
      refine ⟨((GFrame.env σ _).trans hg).withEnv _, ?_⟩
      cases res with
      | none => exact LocAgree.refl _
      | some j => exact LocAgree.set j _ _
    | rets bs =>
      cases he
      refine ⟨((GFrame.env σ _).trans hg).withEnv _, ?_⟩
      show LocAgree d [] σ.env (Env.drop (Ext.append _ _) (Env.append _ _ σ.env))
      rw [Env.drop_append]
      exact LocAgree.refl _
    | mem => exact absurd (hw'.1.2 : false = true) Bool.false_ne_true
  | _, _, .loop _ c body, hw, d, σ, υ, h => by
    have hw' : (c.readsIn μ && Prog.within μ body) = true := hw
    rw [Bool.and_eq_true] at hw'
    change Loop.run (fun τ => (Prog.run τ body).map (State.drop body.ext)) (fun τ => c.eval τ) σ =
      .ok υ at h
    refine Loop.run_induct
      (P := fun τ => GFrame μ σ τ ∧ LocAgree d (Prog.writesAt d body) σ.env τ.env)
      (Q := fun r => ∀ υ, r = .ok υ → GFrame μ σ υ ∧ LocAgree d (Prog.writesAt d body) σ.env υ.env)
      ⟨GFrame.refl σ, LocAgree.refl _⟩ (fun τ hτ => ?_) (fun _ h => by cases h) υ h
    unfold Loop.step
    dsimp only
    cases c.eval τ with
    | error => dsimp only; intro _ h; cases h
    | ok v =>
      rcases v with _ | (_ | _)
      · dsimp only; intro _ h; cases h
      · dsimp only; intro _ h; cases h; exact hτ
      · dsimp only
        cases hb : (Prog.run τ body).map (State.drop body.ext) with
        | error => dsimp only; intro _ h; cases h
        | ok τ' =>
          dsimp only
          obtain ⟨τ₀, hb', rfl⟩ := map_ok_inv' hb
          obtain ⟨hg, ha⟩ := Prog.run_frame body hw'.2 d hb'
          exact ⟨hτ.1.trans (hg.withEnv _), hτ.2.trans ha⟩
  | _, _, .block body, hw, d, σ, υ, h => by
    change (Prog.run σ body).map (State.drop body.ext) = .ok υ at h
    obtain ⟨υ', h', rfl⟩ := map_ok_inv' h
    obtain ⟨hg, ha⟩ := Prog.run_frame body hw d h'
    exact ⟨hg.withEnv _, ha⟩
  | _, _, .rebind .., hw, _, _, _, _ | _, _, .declStorage .., hw, _, _, _, _
  | _, _, .push .., hw, _, _, _, _ | _, _, .pop _, hw, _, _, _, _
  | _, _, .declMem .., hw, _, _, _, _ | _, _, .rebindMem .., hw, _, _, _, _
  | _, _, .assignFromMem .., hw, _, _, _, _ | _, _, .assignMem .., hw, _, _, _, _
  | _, _, .deleteMem .., hw, _, _, _, _ | _, _, .assignNew .., hw, _, _, _, _
  | _, _, .tryCall .., hw, _, _, _, _ => by cases hw

/-- **A program within `μ` runs within `μ`'s frame.** -/
theorem Prog.run_frame : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.within μ P = true → (d : Nat) →
    {σ : State C Γ} → {υ : State C Γ'} → Prog.run σ P = .ok υ →
      GFrame μ σ υ ∧ LocAgree d (Prog.writesAt d P) σ.env (Env.drop P.ext υ.env)
  | _, _, .nil, _, _, σ, _, h => by cases h; exact ⟨GFrame.refl σ, LocAgree.refl _⟩
  | _, _, .cons s P, hw, d, σ, υ, h => by
    have hw' : (Stmt.within μ s && Prog.within μ P) = true := hw
    rw [Bool.and_eq_true] at hw'
    rw [Prog.run_cons] at h
    cases hs : s.run σ with
    | error => rw [hs] at h; cases h
    | ok τ =>
      rw [hs] at h
      obtain ⟨hg₁, ha₁⟩ := Stmt.run_frame s hw'.1 d hs
      obtain ⟨hg₂, ha₂⟩ := Prog.run_frame P hw'.2 (d + s.ext.depth) h
      refine ⟨hg₁.trans hg₂, ?_⟩
      show LocAgree d (Stmt.writesAt d s ++ Prog.writesAt (d + s.ext.depth) P) σ.env
        (Env.drop (s.ext.trans P.ext) υ.env)
      rw [Env.drop_trans]
      exact ha₁.left.trans (LocAgree.drop s.ext ha₂).right

end

end Progs

/-! ## The loop frame, anonymised -/

section Anon

variable {Γ : Ctx}

/-- `State.anon` sets locals only. -/
theorem State.anon_eq (xs : List ((t : LTy) × Idx Γ t)) (b : (x : (t : LTy) × Idx Γ t) → x.1.Denote C) :
    (σ : State C Γ) → σ.anon xs b = σ.withEnv (σ.anon xs b).env := by
  induction xs with
  | nil => intro σ; cases σ; rfl
  | cons x xs ih => intro σ; exact ih (σ.setLocal x.2 (b x))

/-- What `State.anon` reads at a position: the value `b` gives where `xs`
lists it, the state's elsewhere. -/
theorem State.anon_get (xs : List ((t : LTy) × Idx Γ t))
    (b : (x : (t : LTy) × Idx Γ t) → x.1.Denote C) {t : LTy} (i : Idx Γ t) :
    (σ : State C Γ) → ((⟨t, i⟩ : (t : LTy) × Idx Γ t) ∈ xs →
        Env.get i (σ.anon xs b).env = b ⟨t, i⟩) ∧
      ((⟨t, i⟩ : (t : LTy) × Idx Γ t) ∉ xs → Env.get i (σ.anon xs b).env = Env.get i σ.env) := by
  induction xs with
  | nil => intro σ; exact ⟨fun h => (by cases h), fun _ => rfl⟩
  | cons x xs ih =>
    intro σ
    have hs : σ.anon (x :: xs) b = (σ.setLocal x.2 (b x)).anon xs b := rfl
    rw [hs]
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
        exact Env.get_set i _ σ.env
    · have hx : (⟨t, i⟩ : (t : LTy) × Idx Γ t) ∉ xs := fun h => hm (List.mem_cons_of_mem _ h)
      rw [(ih _).2 hx]
      exact Env.get_set_ne x.2 i _ σ.env (hne fun h => hm (h ▸ List.mem_cons_self ..))

/-- The mutability a loop frame's flag stands for. -/
def frameMut (hv : Bool) : Mutability := if hv then .nonpayable else .view

/-- **A body with a frame** is within its mutability, and its frame lists
every local of the loop's context it may write. -/
theorem Prog.frame_some {Γ₁ : Ctx} {P : Prog C Γ Γ₁} {xs : List ((t : LTy) × Idx Γ t)}
    {hv : Bool} (h : P.frame = some (xs, hv)) :
    Prog.within (frameMut hv) P = true ∧
      ∀ t (i : Idx Γ t), (t, i.toNat) ∈ Prog.writesAt 0 P → (⟨t, i⟩ : (t : LTy) × Idx Γ t) ∈ xs := by
  unfold Prog.frame at h
  have hxs : ∀ ys : List ((t : LTy) × Idx Γ t),
      ys = (Prog.writesAt 0 P).filterMap (fun (tn : LTy × Nat) => (Γ.idx? tn.2 tn.1).map (⟨tn.1, ·⟩)) →
      ∀ t (i : Idx Γ t), (t, i.toNat) ∈ Prog.writesAt 0 P → (⟨t, i⟩ : (t : LTy) × Idx Γ t) ∈ ys := by
    intro ys hys t i hm
    rw [hys, List.mem_filterMap]
    exact ⟨(t, i.toNat), hm, by simp only [Ctx.idx?_toNat, Option.map_some]⟩
  split at h
  · cases h
    exact ⟨by assumption, hxs _ rfl⟩
  · split at h
    · cases h
      exact ⟨by assumption, hxs _ rfl⟩
    · cases h

/-- **A state in a loop body's frame is one its anonymised premise covers**:
`{anon(xs)}` (`{havoc}` when `hv`) of the loop's first state reaches every
state that agrees with it but where the body may write. -/
theorem holds_anonHavoc {σ τ : State C Γ} {xs : List ((t : LTy) × Idx Γ t)} {hv : Bool}
    {W : List (LTy × Nat)}
    (hxs : ∀ t (i : Idx Γ t), (t, i.toNat) ∈ W → (⟨t, i⟩ : (t : LTy) × Idx Γ t) ∈ xs)
    (hg : GFrame (frameMut hv) σ τ) (ha : LocAgree 0 W σ.env τ.env) {ψ : Fml C Γ}
    (h : holds σ (Fml.anonHavoc xs hv ψ)) : holds τ ψ := by
  let b : (x : (t : LTy) × Idx Γ t) → x.1.Denote C := fun x => Env.get x.2 τ.env
  have henv : (σ.anon xs b).env = τ.env := Env.ext fun t i => by
    by_cases hm : (⟨t, i⟩ : (t : LTy) × Idx Γ t) ∈ xs
    · exact (State.anon_get xs b i σ).1 hm
    · rw [(State.anon_get xs b i σ).2 hm]
      exact (ha t i (Nat.zero_le _) fun hw => hm (hxs t i (by rwa [Nat.sub_zero] at hw))).symm
  cases hv with
  | false =>
    have hk := hg.keeps (by simp only [frameMut]; decide)
    have hτ : τ = σ.anon xs b := by
      rw [State.anon_eq xs b σ, henv]
      cases σ; cases τ
      simp only [State.withEnv] at hk hg ⊢
      obtain ⟨h1, h2, h3, h4, -⟩ := hg
      simp only at h1 h2 h3 h4 hk
      rw [h1, h2, h3, h4, hk.1, hk.2]
    rw [hτ]
    exact h b
  | true =>
    have hτ : τ = (σ.anon xs b).withGlob ((σ.anon xs b).glob.havoc τ.storage τ.net) := by
      rw [State.anon_eq xs b σ, henv]
      cases σ; cases τ
      obtain ⟨h1, h2, h3, h4, -⟩ := hg
      simp only at h1 h2 h3 h4
      simp only [State.withGlob, State.withEnv, State.ofGlob, State.glob,
        Semantics.State.havoc, h1, h2, h3, h4]
    rw [hτ]
    exact h b τ.storage τ.net

end Anon

end Solidity.Core
