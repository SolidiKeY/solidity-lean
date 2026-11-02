import Solidity.Calculus.CallFunctionBase
import Solidity.Calculus.CallResultCapture
import Solidity.Calculus.ExactRun
import Solidity.Calculus.SoundSummary

/-! # Operational base clauses
These use actual capture updates, rather than identifying every theory
reading with evaluation. Non-exhaustion is proved from existing no-push
certificates supplied internally by the summary producer.
-/
namespace Solidity.CallFunctionOperationalBase
open CallFunctionTable CallFunctionBase
variable {C : Contract} {Γ : Ctx}

/-- The new table slot cannot change actual operational input evaluation. -/
theorem input_eval (t : Tm C (.val .uint :: Γ) (.val .uint))
    (σ : State C Γ) (L : Ledger) (x : Key) :
    (inputTerm t).eval ((σ.push (t := .oldNet) L).push (t := .val .uint) x) =
      t.eval (σ.push (t := .val .uint) x) := by
  rw [inputTerm, Tm.eval_wk]
  rfl

/-- Thinning preserves the existing no-push certificate. -/
theorem pushFree_wk {Δ : Ctx} (h : Thin Γ Δ) {s : Srt} (t : Tm C Γ s) :
    (t.wk h).pushFree = t.pushFree := by
  induction t with
  | pvV i => rfl
  | pvP i => rfl
  | pvS i => rfl
  | pvI i => rfl
  | pvZ i => rfl
  | app0 o => rfl
  | netOf i a ih => simp only [Tm.wk_netOf, Tm.pushFree, ih]
  | app1 o a ih => simp only [Tm.wk_app1, Tm.pushFree, ih]
  | app2 o a b iha ihb => simp only [Tm.wk_app2, Tm.pushFree, iha, ihb]
  | app3 o a b c iha ihb ihc => simp only [Tm.wk_app3, Tm.pushFree, iha, ihb, ihc]

/-- The actual capture lands on precisely its returned primitive value. -/
theorem capture_of_eval {p : PrimTy} (m : Modality) (name : Var)
    (t : Tm C Γ (.val p)) (φ : Fml C (.val p :: Γ))
    (σ : State C Γ) (v : p.Denote) (ht : t.eval σ = some v) :
    holds σ (.upd m (CallResultCapture.capture name t) φ) ↔
      holds (σ.push (t := .val p) v) φ := by
  have hr : (Rhs.val t).eval σ = some (LTy.VDen.ofT (H := σ.H) (.val p) v) := ht
  exact Upd.afterT_lands_iff (Upd.lands_decl (Upd.lands_nil σ) name hr) m (holds · φ)

/-- Nonreturn retains the exact modality/exhaustion predicate. -/
theorem capture_of_none {p : PrimTy} (m : Modality) (name : Var)
    (t : Tm C Γ (.val p)) (φ : Fml C (.val p :: Γ))
    (σ : State C Γ) (ht : t.eval σ = none) :
    holds σ (.upd m (CallResultCapture.capture name t) φ) ↔
      (m.onHalt ∨ (CallResultCapture.capture name t).exh σ = true) := by
  change Upd.afterT m σ (CallResultCapture.capture name t) _ ↔ _
  rw [Upd.afterT_applyV, CallResultCapture.capture_applyV, ht]
  rfl

/-- Existing no-push evidence establishes actual capture non-exhaustion. -/
theorem capture_noExh {p : PrimTy} (name : Var) (t : Tm C Γ (.val p))
    (hp : t.pushFree = true) (σ : State C Γ) :
    (CallResultCapture.capture name t).exh σ = false := by
  apply Upd.exh_of_pushFree
  simp only [CallResultCapture.capture, Upd.pushFree, Rhs.pushFree, hp, Bool.true_and]

/-- The existing concrete summary certificate supplies no-push internally.
This is not an additional source-call validity premise. -/
theorem summary_term_pushFree {ps Γf : Ctx} {r : Var} {j : Idx Γ (.val .uint)}
    {args : Args C Γ ps} {body : Prog C ([.val .uint] ++ ps) Γf}
    {t : Tm C Γ (.val .uint)}
    (h : CallRet.summary? args (.val .uint r (some j)) body =
      some (Upd.nil.snoc (.local j (.val t)))) (σ : State C Γ) :
    t.pushFree = true := by
  have hu : (Upd.nil.snoc (.local j (.val t))).pushFree = true :=
    (CallRet.summary_agrees h σ).2.2
  simpa only [Upd.pushFree, UpdElem.pushFree, Rhs.pushFree, Bool.true_and] using hu

/-- The actual captured result is the code stored at the original input. -/
def returnedEq : Fml C (.val .uint :: .val .uint :: .oldNet :: Γ) :=
  CallFunctionGraph.equalZ
    (.netOf (.there (.there .here)) (.pvV (.there .here)))
    (.app1 .toInt (.pvV .here))

/-- The failed input has the distinguished failure code. -/
def failedEq : Fml C (.val .uint :: .oldNet :: Γ) :=
  CallFunctionGraph.equalZ (.netOf (.there .here) (.pvV .here)) (.app0 (.zlit (-1)))

theorem holds_returnedEq (σ : State C Γ) (L : Ledger) (x r : Key) :
    holds (((σ.push (t := .oldNet) L).push (t := .val .uint) x).push
      (t := .val .uint) r) returnedEq ↔ L.at x = r.val := by
  change ((some (decide (L.at x = r.val)) : Option Bool) = some true) ↔ _
  simp only [Option.some.injEq, decide_eq_true_eq]

theorem holds_failedEq (σ : State C Γ) (L : Ledger) (x : Key) :
    holds ((σ.push (t := .oldNet) L).push (t := .val .uint) x) failedEq ↔ L.at x = -1 := by
  change ((some (decide (L.at x = -1)) : Option Bool) = some true) ↔ _
  simp only [Option.some.injEq, decide_eq_true_eq]

/-- The two operational observations at one input. -/
def atInput (resultName : Var) (t : Tm C (.val .uint :: Γ) (.val .uint)) :
    Fml C (.val .uint :: .oldNet :: Γ) :=
  .and
    (.upd .box (CallResultCapture.capture resultName (inputTerm t)) returnedEq)
    (.imp (.not (.upd .diamond (CallResultCapture.capture resultName (inputTerm t)) .tt)) failedEq)

/-- Success constrains actual capture; nonreturning diamond selects failure.
The producer supplies existing no-push evidence, not a user validity premise. -/
def clause (inputName resultName : Var)
    (t : Tm C (.val .uint :: Γ) (.val .uint)) : Fml C (.oldNet :: Γ) :=
  .all inputName .uint (atInput resultName t)

/-- Actual capture observations exactly determine the operational function.
No theory/evaluation agreement premise is used. -/
theorem holds_clause (inputName resultName : Var)
    (t : Tm C (.val .uint :: Γ) (.val .uint)) (hp : t.pushFree = true)
    (σ : State C Γ) (L : Ledger) :
    holds (σ.push (t := .oldNet) L) (clause inputName resultName t) ↔
      Represents L (fun x => t.eval (σ.push (t := .val .uint) x)) := by
  have hpf : (inputTerm t).pushFree = true := by
    rw [inputTerm, pushFree_wk, hp]
  constructor
  · intro h x
    change L.at x = encode (t.eval (σ.push (t := .val .uint) x))
    have hc : holds ((σ.push (t := .oldNet) L).push (t := .val .uint) x)
        (atInput resultName t) := h x
    have he : (inputTerm t).eval ((σ.push (t := .oldNet) L).push (t := .val .uint) x) =
        t.eval (σ.push (t := .val .uint) x) := input_eval t σ L x
    cases ht : t.eval (σ.push (t := .val .uint) x) with
    | some v =>
      have hv : (inputTerm t).eval ((σ.push (t := .oldNet) L).push
          (t := .val .uint) x) = some v := he.trans ht
      have hr : holds (((σ.push (t := .oldNet) L).push (t := .val .uint) x).push
          (t := .val .uint) v) returnedEq :=
        (capture_of_eval .box resultName (inputTerm t) returnedEq _ v hv).mp hc.1
      exact (holds_returnedEq σ L x v).mp hr
    | none =>
      have hn : (inputTerm t).eval ((σ.push (t := .oldNet) L).push
          (t := .val .uint) x) = none := he.trans ht
      have hex : (CallResultCapture.capture resultName (inputTerm t)).exh
          ((σ.push (t := .oldNet) L).push (t := .val .uint) x) = false :=
        capture_noExh resultName (inputTerm t) hpf _
      have hd : ¬ holds ((σ.push (t := .oldNet) L).push (t := .val .uint) x)
          (.upd .diamond (CallResultCapture.capture resultName (inputTerm t)) .tt) := by
        rw [capture_of_none .diamond resultName (inputTerm t) .tt _ hn, hex]
        change ¬ (False ∨ false = true)
        simp only [Bool.false_eq_true, or_self, not_false_eq_true]
      exact (holds_failedEq σ L x).mp (hc.2 hd)
  · intro h x
    have hx : L.at x = encode (t.eval (σ.push (t := .val .uint) x)) := h x
    have he : (inputTerm t).eval ((σ.push (t := .oldNet) L).push (t := .val .uint) x) =
        t.eval (σ.push (t := .val .uint) x) := input_eval t σ L x
    cases ht : t.eval (σ.push (t := .val .uint) x) with
    | some v =>
      have hv : (inputTerm t).eval ((σ.push (t := .oldNet) L).push
          (t := .val .uint) x) = some v := he.trans ht
      constructor
      · apply (capture_of_eval .box resultName (inputTerm t) returnedEq _ v hv).mpr
        apply (holds_returnedEq σ L x v).mpr
        simpa only [ht, encode] using hx
      · intro hd
        have hdia : holds ((σ.push (t := .oldNet) L).push (t := .val .uint) x)
            (.upd .diamond (CallResultCapture.capture resultName (inputTerm t)) .tt) :=
          (capture_of_eval .diamond resultName (inputTerm t) .tt _ v hv).mpr trivial
        exact False.elim (hd hdia)
    | none =>
      have hn : (inputTerm t).eval ((σ.push (t := .oldNet) L).push
          (t := .val .uint) x) = none := he.trans ht
      constructor
      · apply (capture_of_none .box resultName (inputTerm t) returnedEq _ hn).mpr
        exact Or.inl trivial
      · intro _
        apply (holds_failedEq σ L x).mpr
        simpa only [ht, encode] using hx

/-- Every no-push base function has an actual operational table model.
The no-push certificate is derived internally from existing summary facts. -/
theorem satisfiable (inputName resultName : Var)
    (t : Tm C (.val .uint :: Γ) (.val .uint)) (hp : t.pushFree = true) (σ : State C Γ) :
    ∃ L : Ledger, holds (σ.push (t := .oldNet) L) (clause inputName resultName t) := by
  obtain ⟨L, hL⟩ := exists_represents (fun x => t.eval (σ.push (t := .val .uint) x))
  exact ⟨L, (holds_clause inputName resultName t hp σ L).mpr hL⟩

/-- Both operational captures and every comparison/connective are counted;
this is one base clause, not a complete call-family leaf. -/
theorem clause_size (inputName resultName : Var)
    (t : Tm C (.val .uint :: Γ) (.val .uint)) :
    (clause inputName resultName t).tmSize = 2 * t.size + 22 := by
  simp only [clause, atInput, returnedEq, failedEq, CallFunctionGraph.equalZ,
    CallResultCapture.capture, inputTerm, Fml.tmSize, Upd.tmSize, Rhs.size,
    Tm.size, CallFunctionBase.term_size_wk]
  omega

end Solidity.CallFunctionOperationalBase
