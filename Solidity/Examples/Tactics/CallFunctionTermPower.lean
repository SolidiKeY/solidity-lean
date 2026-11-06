import Solidity.Calculus.CallFunctionTermPower

/-! # Actual source-call/expanded-term sharing certificates
The typed family bodies contain real calls of their preceding body twice.
Every summary/expansion certificate below is checked, not an assumed oracle.
-/
namespace Solidity.Examples.Tactics.CallFunctionTermPower
open Solidity.CallFunctionTermPower Solidity.CallFunctionLeaf Solidity.CallFunctionTable
private abbrev C := StandardExample
private abbrev Γ : Ctx := [.val .uint, .val .uint]
private def name : Var := .fresh "same" 0
private def affine {Δ : Ctx} (x : Val C Δ .uint) : Val C Δ .uint :=
  .binop .add rfl rfl (.binop .mul rfl rfl x (.simple (.lit 3 rfl))) (.simple (.lit 1 rfl))
private def body : Nat → Prog C Γ Γ
  | 0 => .cons (.assignLocal .here (affine (.simple (.local (.there .here))))) .nil
  | k+1 =>
    .cons (.call "previous" (.snoc .nil .uint name (.simple (.local (.there .here))))
      (.val .uint name (some .here)) (body k))
    (.cons (.call "previous" (.snoc .nil .uint name (.simple (.local .here)))
      (.val .uint name (some .here)) (body k)) .nil)
private def args : Args C Γ [.val .uint] :=
  .snoc .nil .uint name (.simple (.local (.there .here)))
private def base : Tm C (.val .uint :: Γ) (.val .uint) :=
  (affine (.simple (.local .here))).lower
private def nested (n : Nat) (v : Val C Γ .uint) : Val C Γ .uint :=
  match n with
  | 0 => v
  | n+1 => affine (nested n v)
private def oldTerm (k : Nat) : Tm C Γ (.val .uint) :=
  (nested (2^k) (.simple (.local (.there .here)))).lower
private def oldUpdate (k : Nat) : Upd C Γ Γ :=
  Upd.nil.snoc (.local .here (.val (oldTerm k)))
private def original (n : Nat) : State C Γ :=
  (({ State.init C with selfBalance := uintOfNat 5, net := [(uintOfNat 5, 19)] }).push
    (t := .val .uint) (uintOfNat n)).push (t := .val .uint) (uintOfNat 99)
private def post (n : Nat) : Fml C Γ :=
  .and (.eq (.pvV .here) (.app0 (.lit (uintOfNat n))))
    (.eq (.pvV (.there .here)) (.app0 (.lit (uintOfNat 2))))

/-- Concrete existing source-summary equations for distinct actual family levels. -/
theorem summaryOne : CallRet.summary? args (.val .uint name (some .here)) (body 1) =
    some (oldUpdate 1) := rfl
theorem summaryTwo : CallRet.summary? args (.val .uint name (some .here)) (body 2) =
    some (oldUpdate 2) := rfl
theorem summaryThree : CallRet.summary? args (.val .uint name (some .here)) (body 3) =
    some (oldUpdate 3) := rfl

/-- Concrete actual old-term expansion certificates, including the base level. -/
theorem expansions :
    expanded? base (.there .here) (2^0) = some (oldTerm 0) ∧
    expanded? base (.there .here) (2^1) = some (oldTerm 1) ∧
    expanded? base (.there .here) (2^2) = some (oldTerm 2) ∧
    expanded? base (.there .here) (2^3) = some (oldTerm 3) := ⟨rfl, rfl, rfl, rfl⟩

/-- An inhabited concrete source call is certified through the complete shared
leaf and actual summary certificate, not directly by evaluating an oracle. -/
theorem sourceTwo (m : Modality) : holds (original 2)
    (.modal m (.cons (.call "family2" args (.val .uint name (some .here)) (body 2)) .nil)
      .nil (post 202)) := by
  apply sound_call m name name name "family2" args name (body 2) base rfl rfl rfl
    2 .here (.there .here) (oldTerm 2) expansions.2.2.1 summaryTwo .nil .nil (post 202) (original 2)
  apply (holds_leaf m name name name base rfl 2 .here (.there .here) _ (original 2)).mpr
  exact ⟨rfl, rfl⟩

/-- Another actual source level uses its own checked summary certificate. -/
theorem sourceOne (m : Modality) : holds (original 2)
    (.modal m (.cons (.call "family1" args (.val .uint name (some .here)) (body 1)) .nil)
      .nil (post 22)) := by
  apply sound_call m name name name "family1" args name (body 1) base rfl rfl rfl
    1 .here (.there .here) (oldTerm 1) expansions.2.1 summaryOne .nil .nil (post 22) (original 2)
  apply (holds_leaf m name name name base rfl 1 .here (.there .here) _ (original 2)).mpr
  exact ⟨rfl, rfl⟩

/-- A third source level witnesses that the bridge is not a fixed two-call case. -/
theorem sourceThree (m : Modality) : holds (original 2)
    (.modal m (.cons (.call "family3" args (.val .uint name (some .here)) (body 3)) .nil)
      .nil (post 16402)) := by
  apply sound_call m name name name "family3" args name (body 3) base rfl rfl rfl
    3 .here (.there .here) (oldTerm 3) expansions.2.2.2 summaryThree .nil .nil (post 16402) (original 2)
  apply (holds_leaf m name name name base rfl 3 .here (.there .here) _ (original 2)).mpr
  exact ⟨rfl, rfl⟩

/-- The actual typed source run returns the same whole caller state, not only
an injected result value or an agreement assumption. -/
theorem actualRunTwo : Stmt.runSt (original 2)
    (.call "family2" args (.val .uint name (some .here)) (body 2)) =
      .ok ((original 2).setLocal .here (uintOfNat 202)) :=
  run_of_summary_eval "family2" args name (body 2) .here (oldTerm 2) summaryTwo
    (original 2) (uintOfNat 202) rfl

/-- The wrong source post is false on that same inhabited actual run. -/
theorem sourceWrongResult (m : Modality) : ¬ holds (original 2)
    (.modal m (.cons (.call "family2" args (.val .uint name (some .here)) (body 2)) .nil)
      .nil (post 203)) := by
  intro hh
  rw [holds_modal_cons_iff, actualRunTwo] at hh
  have hp : holds ((original 2).setLocal .here (uintOfNat 202)) (post 203) := hh.1.1
  have he : (some (uintOfNat 202) : Option Key) = some (uintOfNat 203) := hp.1
  have bad : (202 : Int) = 203 := congrArg Subtype.val (Option.some.inj he)
  omega

/-- Nontrivial globals and the old input are preserved on the real returned state. -/
theorem actualSourceFrame :
    (Stmt.runSt (original 2)
      (.call "family2" args (.val .uint name (some .here)) (body 2))).map
        (fun τ => (τ.selfBalance, τ.net.at (uintOfNat 5), τ.getV (.there .here))) =
          .ok (uintOfNat 5, (19 : Int), uintOfNat 2) := by
  rw [actualRunTwo]
  rfl

/-- Genuine checked source arithmetic failure is ordinary revert. -/
theorem actualOverflow : Stmt.runSt (original (2^256-1))
    (.call "family2" args (.val .uint name (some .here)) (body 2)) =
      .error .revert := rfl

/-- Both modalities retain their original observation on actual source failure. -/
theorem sourceFailure :
    holds (original (2^256-1))
      (.modal .box (.cons (.call "family2" args (.val .uint name (some .here)) (body 2)) .nil)
        .nil (.ff : Fml C Γ)) ∧
    ¬ holds (original (2^256-1))
      (.modal .diamond (.cons (.call "family2" args (.val .uint name (some .here)) (body 2)) .nil)
        .nil (.tt : Fml C Γ)) := by
  constructor
  · rw [holds_modal_cons_iff, actualOverflow]
    exact ⟨trivial, by intro hh; cases hh⟩
  · rw [holds_modal_cons_iff, actualOverflow]
    intro hh
    cases hh.1

/-- Actual old summary and new shared leaf have identical observations in every
caller state/post, rather than only for the chosen successful input. -/
theorem assignmentTwo (m : Modality) (φ : Fml C Γ) (σ : State C Γ) :
    holds σ (leaf m name name name base 2 .here (.there .here) φ) ↔
      holds σ (.upd m (oldUpdate 2) φ) :=
  holds_assignment m name name name base rfl rfl rfl 2 .here (.there .here)
    (oldTerm 2) expansions.2.2.1 φ σ

private def failing : Tm C Γ (.val .uint) :=
  (Val.binop .div rfl rfl (.simple (.lit 1 rfl)) (.simple (.lit 0 rfl))).lower
private def ignoresArgument : Tm C (.val .uint :: Γ) (.val .uint) := .app0 (.lit (uintOfNat 7))

/-- A non-strict constant can drop a failed argument under substitution, so
its strict-read certificate is false and the producer must refuse this route. -/
theorem strictnessEssential : ignoresArgument.strictReads 0 = false ∧
    failing.eval (original 2) = none ∧
    inst? .refl ignoresArgument failing = some (.app0 (.lit (uintOfNat 7))) ∧
    (Tm.app0 (C := C) (Γ := Γ) (.lit (uintOfNat 7))).eval (original 2) = some (uintOfNat 7) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A same-named different body has a different actual summary: names are not
proof certificates for sharing an implementation. -/
private def changedBody : Prog C Γ Γ :=
  .cons (.assignLocal .here (.simple (.lit 0 rfl))) .nil
private def changedCaller : Prog C Γ Γ :=
  .cons (.call "previous" (.snoc .nil .uint name (.simple (.local (.there .here))))
    (.val .uint name (some .here)) changedBody) .nil

theorem changedBodyRejected :
    CallRet.summary? args (.val .uint name (some .here)) changedCaller ≠ some (oldUpdate 1) := by
  intro hh
  have he :
      (CallRet.summary? args (.val .uint name (some .here)) changedCaller).bind
        (fun U => (U.applyV (original 2)).map (fun r => r.2 _ .here)) =
      (some (oldUpdate 1) : Option (Upd C Γ Γ)).bind
        (fun U => (U.applyV (original 2)).map (fun r => r.2 _ .here)) :=
    congrArg (fun q : Option (Upd C Γ Γ) =>
      q.bind (fun U => (U.applyV (original 2)).map (fun r => r.2 _ .here))) hh
  change (some (uintOfNat 0) : Option Key) = some (uintOfNat 22) at he
  have bad : (0 : Int) = 22 := congrArg Subtype.val (Option.some.inj he)
  omega

end Solidity.Examples.Tactics.CallFunctionTermPower
