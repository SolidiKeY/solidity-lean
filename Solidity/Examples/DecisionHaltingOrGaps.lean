import Solidity.Calculus.CloseFrame
import Solidity.Calculus.Decision
import Solidity.Examples.DecisionCoefficientBoundary
/-!
# The halting-OR APF floor hazard

Boolean lowering already handles the short-circuit operand. The separately
reproduced negative mapping block remains unknown; an illustrative key collapse
is not a full reconstruction Setting or a counterexample to GuardP.floors.
-/
namespace Solidity.Examples.DecisionHaltingOrGaps
open Solidity.Decide
open Solidity.Examples.DecisionCoefficientBoundary (Bank)
set_option Elab.async false

def yes : Tm Bank [] (.val .bool) := .app0 (.lit true)
def zero : Tm Bank [] (.val .uint) := .app0 (.lit (uintOfNat 0))
def one : Tm Bank [] (.val .uint) := .app0 (.lit (uintOfNat 1))
def badDiv : Tm Bank [] (.val .uint) := .app2 (.binop .div rfl) one zero
def badBool : Tm Bank [] (.val .bool) := .app2 (.binop .eqB rfl) badDiv zero
def left : Tm Bank [] (.val .bool) := .app2 (.binop .and rfl) yes badBool
def operand : Tm Bank [] (.val .bool) := .app2 (.binop .or rfl) left yes
def goal : Fml Bank [] := .eq operand yes
/-- info: true -/
#guard_msgs in #eval goal.inTarget {}
/-- info: true -/
#guard_msgs in #eval goal.Covered
/-- info: "refuted" -/
#guard_msgs in #eval (match decideGoal goal with | .proved => "proved" | .refuted _ => "refuted" | .unknown => "unknown")

def bound : Tm Bank [.val .bool] (.val .bool) := .pvV .here
def scopedBad : Tm Bank [.val .bool] (.val .bool) := badBool.wk (.drop .refl)
def scopedYes : Tm Bank [.val .bool] (.val .bool) := yes.wk (.drop .refl)
def scopedNo : Tm Bank [.val .bool] (.val .bool) := .app0 (.lit false)
def scopedLeft : Tm Bank [.val .bool] (.val .bool) := .app2 (.binop .and rfl) bound scopedBad
def scopedOperand : Tm Bank [.val .bool] (.val .bool) := .app2 (.binop .or rfl) scopedLeft scopedYes
def quantified : Fml Bank [] := .all (.user "b") .bool (.eq scopedOperand scopedYes)
def guarded : Fml Bank [] := .all (.user "b") .bool
  (.imp (.eq bound scopedNo) (.eq scopedOperand scopedYes))
def reflexive : Fml Bank [] := .all (.user "b") .bool (.eq scopedOperand scopedOperand)
def verdict (φ : Fml Bank []) : String :=
  match decideGoal φ with | .proved => "proved" | .refuted _ => "refuted" | .unknown => "unknown"
/-- info: [(true, true, "refuted"), (true, true, "proved"), (true, true, "proved")] -/
#guard_msgs in #eval [quantified, guarded, reflexive].map (fun φ => (φ.inTarget {}, φ.Covered, verdict φ))

def FloorProbe : Contract := contract!{ mapping(uint => uint) balances; uint value; }
def scalar {Γ : Ctx} : Tm FloorProbe Γ (.val .uint) :=
  .app2 .find (.app0 .storage) (.app0 (.root "value" rfl))
def natLit {Γ : Ctx} (n : Nat) : Tm FloorProbe Γ (.val .uint) := .app0 (.lit (uintOfNat n))
def atKey {Γ : Ctx} (k : Tm FloorProbe Γ (.val .uint)) : Tm FloorProbe Γ (.val .uint) :=
  .app2 .find (.app0 .storage) (.app2 (.at .map) (.app0 (.root "balances" rfl)) k)
def keyI : Tm FloorProbe [.val .uint, .val .uint] (.val .uint) := .pvV (.there .here)
def keyJ : Tm FloorProbe [.val .uint, .val .uint] (.val .uint) := .pvV .here
def partialBound {Γ : Ctx} : Tm FloorProbe Γ (.val .uint) :=
  .app2 (.binop .sub rfl) scalar (natLit 1)
def orderGuard : Tm FloorProbe [.val .uint, .val .uint] (.val .bool) :=
  .app2 (.binop .le (p := .uint) rfl) keyI keyJ
def partialGuard : Tm FloorProbe [.val .uint, .val .uint] (.val .bool) :=
  .app2 (.binop .lt (p := .uint) rfl) keyI partialBound
def floorGuard : Tm FloorProbe [.val .uint, .val .uint] (.val .bool) :=
  .app2 (.binop .or rfl) (.app2 (.binop .and rfl) orderGuard partialGuard)
    (.app2 (.binop .le (p := .uint) rfl) keyI keyI)
def floorBlock : Fml FloorProbe [] := .all (.user "i") .uint (.all (.user "j") .uint
  (.imp (.eq floorGuard (.app0 (.lit true))) (.eq (atKey keyI) (natLit 0))))
def floorClaim (n : Nat) : Fml FloorProbe [] := .imp floorBlock (.eq (atKey (natLit n)) (natLit 0))
@[noinline] def floorObserve (φ : Fml FloorProbe []) : Bool × Bool × String :=
  (φ.inTarget {}, φ.Covered, match decideGoal φ with
    | .proved => "proved" | .refuted _ => "refuted" | .unknown => "unknown")
/-- info: [(true, false, "unknown"), (true, false, "unknown")] -/
#guard_msgs in #eval [floorClaim 1, floorClaim 0].map floorObserve

def floorBad : Fml FloorProbe [] := .imp floorBlock (.eq (atKey (natLit 1)) (natLit 1))
/-- info: (true, false, "unknown") -/
#guard_msgs in #eval floorObserve floorBad

theorem floorClaim_one_valid : Fml.Valid (floorClaim 1) := by
  intro σ h
  exact h (uintOfNat 1) (uintOfNat 0) rfl

def originalKeys : State FloorProbe [.val .uint, .val .uint] :=
  ((State.init FloorProbe).push (t := .val .uint) (uintOfNat 2)).push
    (t := .val .uint) (uintOfNat 1)
def collapsedKeys : State FloorProbe [.val .uint, .val .uint] :=
  ((State.init FloorProbe).push (t := .val .uint) (uintOfNat 1)).push
    (t := .val .uint) (uintOfNat 1)
theorem original_guard_true : floorGuard.denote originalKeys = some true := by rfl
theorem collapsed_guard_halts : floorGuard.denote collapsedKeys = none := by rfl

theorem atKey_init_eval {Γ : Ctx} (σ : State FloorProbe Γ)
    (hs : σ.storage = Storage.init FloorProbe) (k : Tm FloorProbe Γ (.val .uint))
    (u : PrimTy.uint.Denote) (hk : k.eval σ = some u) :
    (atKey k).eval σ = some (uintOfNat 0) := by
  simp only [atKey, Tm.eval_app2, Tm.eval_app0, Op0.eval_eq_evalM, Op0.evalM,
    Op2.eval_eq_evalM, Op2.evalM, hk, Option.bind_eq_bind, Option.bind_some,
    Storage.atT, CloseS.checkIndex_map_root]
  change (σ.storage.find ((SRef.ofRoot "balances" (by rfl) : SRef FloorProbe (.ref (.mapping .uint (.prim .uint)))).index .map u)).bind
    (fun v => some v.view) = some (uintOfNat 0)
  rw [hs]
  change ((Storage.init FloorProbe).find ((SRef.ofRoot "balances" (by rfl) : SRef FloorProbe (.ref (.mapping .uint (.prim .uint)))).index .map u)).bind
    (fun v => some v.view) = some (uintOfNat 0)
  rw [Storage.find_init_total _ (by simp only [CloseS.index_append, CloseS.path_append, CloseS.path_ofRoot, Path.append_nil, Path.index_map, Path.total])]
  rfl

theorem floorBad_countermodel : ¬ holds (State.init FloorProbe) floorBad := by
  intro h
  have hb : holds (State.init FloorProbe) floorBlock := by
    intro i j hg
    apply (holds_eq_of_eval (x := uintOfNat 0) (y := uintOfNat 0)
      (atKey_init_eval _ rfl _ i rfl) (by rfl)).mpr
    rfl
  have hc : holds (State.init FloorProbe) (.eq (atKey (natLit 1)) (natLit 1)) := h hb
  have he : uintOfNat 0 = uintOfNat 1 :=
    (holds_eq_of_eval (x := uintOfNat 0) (y := uintOfNat 1)
      (atKey_init_eval _ rfl _ (uintOfNat 1) rfl) (by rfl)).mp hc
  exact (by decide +kernel : uintOfNat 0 ≠ uintOfNat 1) he
theorem floorBad_notValid : ¬ Fml.Valid floorBad := by
  intro h
  exact floorBad_countermodel (h (State.init FloorProbe))

/-- An illustrative actual numeric floor collapses the distinct keys; this is not a full Setting. -/
theorem illustrative_floor_keys : floorIn 0 [0, 1] 2 = 1 ∧ floorIn 0 [0, 1] 1 = 1 := by
  decide +kernel


private def provedCheck {C : Contract} : LeafVerdict C → Bool
  | .proved => true
  | _ => false
private def refutedCheck {C : Contract} : LeafVerdict C → Bool
  | .refuted _ => true
  | _ => false

private theorem proved_of_check {C : Contract} (φ : Fml C [])
    (h : provedCheck (decideGoal φ) = true) : decideGoal φ = .proved := by
  cases hd : decideGoal φ with
  | proved => rfl
  | refuted σ => rw [hd] at h; cases h
  | unknown => rw [hd] at h; cases h

private theorem refuted_of_check {C : Contract} (φ : Fml C [])
    (h : refutedCheck (decideGoal φ) = true) :
    ∃ σ : State C [], decideGoal φ = .refuted σ ∧ ¬ Fml.holdsH σ φ := by
  cases hd : decideGoal φ with
  | proved => rw [hd] at h; cases h
  | refuted σ => exact ⟨σ, rfl, decideGoal_refutes hd⟩
  | unknown => rw [hd] at h; cases h


private def unknownCheck {C : Contract} : LeafVerdict C → Bool
  | .unknown => true
  | _ => false

private theorem unknown_of_check {C : Contract} (φ : Fml C [])
    (h : unknownCheck (decideGoal φ) = true) : decideGoal φ = .unknown := by
  cases hd : decideGoal φ with
  | proved => rw [hd] at h; cases h
  | refuted σ => rw [hd] at h; cases h
  | unknown => rfl


theorem validAPF_target : (floorClaim 1).inTarget {} = true := by decide +kernel
theorem validAPF_notCovered : (floorClaim 1).Covered = false := by decide +kernel
theorem validAPF_unknown : decideGoal (floorClaim 1) = .unknown :=
  unknown_of_check (floorClaim 1) (by decide +kernel)

theorem zeroAPF_target : (floorClaim 0).inTarget {} = true := by decide +kernel
theorem zeroAPF_notCovered : (floorClaim 0).Covered = false := by decide +kernel
theorem zeroAPF_unknown : decideGoal (floorClaim 0) = .unknown :=
  unknown_of_check (floorClaim 0) (by decide +kernel)

theorem falseAPF_target : (floorBad).inTarget {} = true := by decide +kernel
theorem falseAPF_notCovered : (floorBad).Covered = false := by decide +kernel
theorem falseAPF_unknown : decideGoal (floorBad) = .unknown :=
  unknown_of_check (floorBad) (by decide +kernel)

theorem guarded_proved : decideGoal guarded = .proved :=
  proved_of_check guarded (by decide +kernel)
theorem guarded_validH : Fml.ValidH guarded := decideGoal_sound guarded_proved
theorem reflexive_proved : decideGoal reflexive = .proved :=
  proved_of_check reflexive (by decide +kernel)
theorem quantified_refuted : ∃ σ : State Bank [],
    decideGoal quantified = .refuted σ ∧ ¬ Fml.holdsH σ quantified :=
  refuted_of_check quantified (by decide +kernel)

theorem quantified_countermodel : ¬ holds (State.init Bank) quantified := by
  intro h
  have hc : holds ((State.init Bank).push (t := .val .bool) true)
      (.eq scopedOperand scopedYes) := h true
  change (none : Option Bool) = some true at hc
  cases hc

theorem returning_false_rhs :
    (Tm.app2 (.binop .or rfl)
      (.app2 (.binop .and rfl) yes (.app0 (.lit false))) yes).denote (State.init Bank) =
      some true := by rfl

theorem outer_false_still_halts :
    (Tm.app2 (.binop .or rfl) left (.app0 (.lit false))).denote (State.init Bank) = none := by rfl

end Solidity.Examples.DecisionHaltingOrGaps
