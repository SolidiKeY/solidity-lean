import Solidity.Update
import Solidity.Semantics.NoPanic

/-!
# A term never panics

A term reads the state through the interpreter's operations, none of which
panics (`Semantics/NoPanic.lean`), so neither does a term nor an update
(`Upd.apply_ne_panic`).  That is what lets a formula read an update as a box
reads a revert (`Modality.after`) while it reads a program with
`Modality.afterRun`: an update taclet's premise and its statement then agree
on what the box says of a halt.
-/

namespace Solidity

open Semantics

variable {C : Contract}

@[simp] theorem readAddr_noPanic (σ : State) (a : Addr) : NoPanic (readAddr σ a) := by
  unfold readAddr; no_panic

/-- What a term of each sort reads to does not panic. -/
def Srt.NoPanic : (s : Srt) → s.Ev → Prop
  | .val, x => Solidity.NoPanic x
  | .path, x => Solidity.NoPanic x
  | .st, x => Solidity.NoPanic x
  | .sv, x => Solidity.NoPanic x
  | .ident, x => Solidity.NoPanic x
  | .addr, x => Solidity.NoPanic x
  | .mem, x => Solidity.NoPanic x
  | .mv, x => Solidity.NoPanic x

theorem Op0.eval_noPanic (σ : State) {s : Srt} (o : Op0 s) : s.NoPanic (o.eval σ) := by
  cases o <;> simp [Op0.eval, Srt.NoPanic]

theorem Op1.eval_noPanic (σ : State) {a s : Srt} (o : Op1 a s) {ra : a.Ev} (h : a.NoPanic ra) :
    s.NoPanic (o.eval σ ra) := by
  cases o <;> simp only [Op1.eval, Srt.NoPanic] at h ⊢ <;> no_panic

theorem Op2.eval_noPanic (σ : State) {a b s : Srt} (o : Op2 a b s) {ra : a.Ev} {rb : b.Ev}
    (ha : a.NoPanic ra) (hb : b.NoPanic rb) : s.NoPanic (o.eval σ ra rb) := by
  cases o <;> simp only [Op2.eval, Srt.NoPanic] at ha hb ⊢
  case binop => exact NoPanic.bind ha fun _ _ => evalBinop_noPanic _ _ _ hb
  all_goals no_panic

theorem Op3.eval_noPanic (σ : State) {a b c s : Srt} (o : Op3 a b c s) {ra : a.Ev} {rb : b.Ev}
    {rc : c.Ev} (ha : a.NoPanic ra) (hb : b.NoPanic rb) (hc : c.NoPanic rc) :
    s.NoPanic (o.eval σ ra rb rc) := by
  cases o <;> simp only [Op3.eval, Srt.NoPanic] at ha hb hc ⊢
  case ite => exact NoPanic.bind ha fun _ _ => pickBranch_noPanic _ hb hc
  case push =>
    exact NoPanic.bind ha fun _ _ => NoPanic.bind hb fun _ _ =>
      pushAt_noPanic _ _ _ _ fun _ => by simpa using hc
  all_goals no_panic

/-- **A term never panics.** -/
theorem Tm.eval_noPanic (σ : State) {s : Srt} : (t : Tm C s) → s.NoPanic (t.eval σ)
  | .pvV x => by simp only [Tm.eval, Srt.NoPanic]; no_panic
  | .pvP x => by simp only [Tm.eval, Srt.NoPanic]; no_panic
  | .pvS x => by simp only [Tm.eval, Srt.NoPanic]; no_panic
  | .pvI x => by simp only [Tm.eval, Srt.NoPanic]; no_panic
  | .app0 o => Op0.eval_noPanic σ o
  | .app1 o a => Op1.eval_noPanic σ o (Tm.eval_noPanic σ a)
  | .app2 o a b => Op2.eval_noPanic σ o (Tm.eval_noPanic σ a) (Tm.eval_noPanic σ b)
  | .app3 o a b c =>
    Op3.eval_noPanic σ o (Tm.eval_noPanic σ a) (Tm.eval_noPanic σ b) (Tm.eval_noPanic σ c)

theorem UpdElem.write_noPanic (σ₀ : State) (e : UpdElem C) (τ : State) :
    NoPanic (e.write σ₀ τ) := by
  have hv : ∀ t : Term C, NoPanic (t.eval σ₀) := fun t => Tm.eval_noPanic σ₀ t
  have hp : ∀ t : PTerm C, NoPanic (t.eval σ₀) := fun t => Tm.eval_noPanic σ₀ t
  have hi : ∀ t : ITerm C, NoPanic (t.eval σ₀) := fun t => Tm.eval_noPanic σ₀ t
  have hs : ∀ t : STerm C, NoPanic (t.eval σ₀) := fun t => Tm.eval_noPanic σ₀ t
  have hm : ∀ t : MTerm C, NoPanic (t.eval σ₀) := fun t => Tm.eval_noPanic σ₀ t
  cases e <;> simp only [UpdElem.write] <;> no_panic

/-- **An update never panics**: what it reads are terms. -/
theorem Upd.apply_ne_panic (U : Upd C) (σ : State) : U.apply σ ≠ .error .panic := by
  unfold Upd.apply
  suffices h : ∀ (V : Upd C) (τ : State),
      NoPanic (V.foldlM (fun τ e => e.write σ τ) τ) from h U σ
  intro V
  induction V with
  | nil => intro τ; simp
  | cons e V ih =>
    intro τ
    simp only [List.foldlM_cons]
    exact NoPanic.bind (UpdElem.write_noPanic σ e τ) fun τ' _ => ih τ'

end Solidity
