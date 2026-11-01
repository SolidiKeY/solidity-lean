import Solidity.Calculus.JoinSequence
import Solidity.Calculus.SoundLocal

/-! # Typed execution of joined assignment sequences -/
namespace Solidity
variable {C : Contract} {Γ : Ctx}

/-- Execute Solidity local assignments strictly from left to right. -/
def LocalWrites.runSt (writes : LocalWrites C Γ) (σ : State C Γ) : TRes (State C Γ) :=
  match writes with
  | [] => .ok σ
  | w :: rest => (w.2.2.evalT σ).bind fun v => LocalWrites.runSt rest (σ.setLocal w.2.1 v)

/-- A fresh snapshot survives every write to an original Solidity local. -/
theorem State.setLocal_push_snapshot {p : PrimTy} (σ : State C Γ) (saved : Bool)
    (i : Idx Γ (.val p)) (v : p.Denote) :
    (σ.push (t := .val .bool) saved).setLocal i.there v =
      (σ.setLocal i v).push (t := .val .bool) saved := by
  rfl

/-- The decoded Solidity assignments execute exactly as their typed program. -/
theorem LocalWrites.program_runSt (writes : LocalWrites C Γ) (σ : State C Γ) :
    Prog.runSt σ writes.program = writes.runSt σ := by
  induction writes generalizing σ with
  | nil => rfl
  | cons w rest ih =>
    simp only [LocalWrites.program] at ih
    simp only [LocalWrites.program, List.foldr_cons, Prog.runSt_cons,
      Stmt.runSt_assignLocal, LocalWrites.runSt]
    cases w.2.2.evalT σ <;> simp only [Except.map, Except.bind, ih]

/-- A snapshot guard evaluates only the selected Solidity assignment. -/
theorem LocalWrites.guard_runSt {p : PrimTy} (σ : State C Γ) (saved positive : Bool)
    (i : Idx Γ (.val p)) (r : Val C Γ p) :
    Stmt.runSt (σ.push (t := .val .bool) saved)
      (if positive then .ite (.simple (.local .here)) (.cons (.assignLocal i.there r.up) .nil) .nil
       else .ite (.simple (.local .here)) .nil (.cons (.assignLocal i.there r.up) .nil)) =
      if saved = positive then
        (r.evalT σ).map (fun v => (σ.setLocal i v).push (t := .val .bool) saved)
      else .ok (σ.push (t := .val .bool) saved) := by
  cases positive <;> cases saved <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Stmt.runSt_ite_simple, Simple.evalT, State.get_push_here, boolT, TRes.map_drop_self, Prog.runSt_single, Prog.runSt_nil, Stmt.runSt_assignLocal, Val.evalT_up, State.setLocal_push_snapshot]

/-- The selected Solidity branch executes in order under the preserved
snapshot, followed by the explicit continuation. An unselected branch
never reads any of its RHS values. -/
theorem LocalWrites.guarded_runSt (writes : LocalWrites C Γ) (σ : State C Γ)
    (saved positive : Bool) (tail : Prog C (.val .bool :: Γ) (.val .bool :: Γ)) :
    Prog.runSt (σ.push (t := .val .bool) saved) (writes.guarded positive tail) =
      if saved = positive then
        ((writes.runSt σ).map (fun τ => τ.push (t := .val .bool) saved)).bind (Prog.runSt · tail)
      else Prog.runSt (σ.push (t := .val .bool) saved) tail := by
  induction writes generalizing σ with
  | nil => cases saved <;> cases positive <;> rfl
  | cons w rest ih =>
    change Prog.runSt (σ.push (t := .val .bool) saved) (.cons _ (LocalWrites.guarded positive rest tail)) = _
    rw [Prog.runSt_cons, LocalWrites.guard_runSt]
    cases saved <;> cases positive <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, LocalWrites.runSt] at *
    all_goals try exact ih σ
    all_goals cases w.2.2.evalT σ <;> simp only [Except.bind, Except.map, ih]

/-- Snapshotting a Solidity condition once preserves the complete selected
branch result, with just the fresh head local added. -/
theorem LocalWrites.joined_runSt (σ : State C Γ) (name : Var) (c : Simple C Γ .bool)
    (thn els : LocalWrites C Γ) :
    Prog.runSt σ (LocalWrites.joined name c thn els) =
      (if boolT (c.evalT σ) then thn.runSt σ else els.runSt σ).map
        (fun τ => τ.push (t := .val .bool) (c.evalT σ)) := by
  simp only [LocalWrites.joined, Prog.runSt_cons, Stmt.runSt_declLocal, Val.evalT, Except.map, Except.bind]
  rw [LocalWrites.guarded_runSt]
  cases hc : c.evalT σ <;> simp only [boolT, Bool.false_eq_true, ↓reduceIte]
  all_goals simp only [LocalWrites.guarded_runSt, ↓reduceIte, Prog.runSt_nil, Except.bind, Except.map]
  all_goals cases ht : LocalWrites.runSt thn σ <;> cases he : LocalWrites.runSt els σ <;>
    simp only [LocalWrites.guarded_runSt, Bool.true_eq_false, ↓reduceIte, Prog.runSt_nil]

/-- Popping the snapshot preserves every successful state and every halt of
Solidity `if (c) { writes } else { writes }`. -/
theorem LocalWrites.joined_drop_runSt (σ : State C Γ) (name : Var) (c : Simple C Γ .bool)
    (thn els : LocalWrites C Γ) :
    (Prog.runSt σ (LocalWrites.joined name c thn els)).map (State.drop (.push .refl)) =
      Stmt.runSt σ (.ite (.simple c) thn.program els.program) := by
  rw [LocalWrites.joined_runSt, Stmt.runSt_ite_simple, TRes.map_drop_self, TRes.map_drop_self,
    LocalWrites.program_runSt, LocalWrites.program_runSt]
  cases hc : c.evalT σ <;> simp only [boolT, Bool.false_eq_true, ↓reduceIte]
  all_goals cases ht : LocalWrites.runSt thn σ <;> cases he : LocalWrites.runSt els σ <;> rfl

/-- The joined Solidity branch is sound under either modality, in every
intrinsically typed state, with no validity or arithmetic premise. -/
theorem LocalWrites.joined_sound {m : Modality} (σ : State C Γ) (name : Var)
    (c : Simple C Γ .bool) (thn els : LocalWrites C Γ) :
    Premise.Runs m (.ite (.simple c) thn.program els.program)
      (.unfold (LocalWrites.joined name c thn els) (.push .refl)) σ := by
  exact Premise.sound_unfold σ (LocalWrites.joined_drop_runSt σ name c thn els)

/-- The dispatcher's captured block preserves all Solidity states and halts.
The inner block pops no locals; the capture alone pops the snapshot. -/
theorem LocalWrites.captured_drop_runSt (σ : State C Γ) (name : Var)
    (c : Simple C Γ .bool) (thn els : LocalWrites C Γ) :
    (Prog.runSt σ (.cons (.declLocal .bool name (some (.simple c)))
      (.cons (.block (thn.guarded true (els.guarded false))) .nil))).map
        (State.drop (.push .refl)) =
      Stmt.runSt σ (.ite (.simple c) thn.program els.program) := by
  rw [← LocalWrites.joined_drop_runSt σ name c thn els]
  simp only [LocalWrites.joined, Prog.runSt_cons, Stmt.runSt_block,
    TRes.map_drop_self, Prog.runSt_nil]
  congr 2
  funext τ
  cases Prog.runSt τ (thn.guarded true (els.guarded false)) <;> rfl

/-- The actual captured-block join is sound for either modality, without
adding validity, arithmetic or totality premises. -/
theorem LocalWrites.captured_sound {m : Modality} (σ : State C Γ) (name : Var)
    (c : Simple C Γ .bool) (thn els : LocalWrites C Γ) :
    Premise.Runs m (.ite (.simple c) thn.program els.program)
      (.capture .bool name (.simple c)
        (.block (thn.guarded true (els.guarded false)))) σ := by
  exact Premise.sound_unfold σ (LocalWrites.captured_drop_runSt σ name c thn els)

end Solidity
