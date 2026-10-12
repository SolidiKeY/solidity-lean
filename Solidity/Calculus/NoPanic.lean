import Solidity.Update
import Solidity.Semantics.NoPanicOps

/-!
# A term never panics

A term reads the state through the interpreter's operations, none of which
panics (`Semantics/NoPanicOps.lean`), so neither does a symbol (`Op1.eval_noPanic`
…), a scoped term nor an update (`Tm.eval_noPanic`, `Upd.applyV_noPanic`,
`Calculus/SoundKit.lean`).  That is what lets a formula read an update as a box
reads a revert (`Modality.after`) while the typed run reads a program with
`Modality.afterRunTR`: an update taclet's premise and its statement then agree
on what the box says of a halt.
-/

namespace Solidity

open Semantics

variable {C : Contract}

@[no_panic_simp] theorem readAddr_noPanic (σ : State) (a : Addr) : NoPanic (readAddr σ a) := by
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
  cases o <;> simp only [Srt.NoPanic, Op0.eval, ne_eq, NoPanic.pure, not_false_eq_true]

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
      pushAt_noPanic _ _ _ _ fun _ => by simpa only [bind_pure_comp, ne_eq, NoPanic.map] using hc
  all_goals no_panic

end Solidity
