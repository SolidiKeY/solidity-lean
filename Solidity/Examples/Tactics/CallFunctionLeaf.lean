import Solidity.Calculus.CallFunctionLeafMetrics

/-! # Complete fresh-table/result leaf controls
These use actual checked intrinsic arithmetic and actual emitted Fml leaves.
Source-program correspondence and default walk dispatch are separate checks.
-/
namespace Solidity.Examples.Tactics.CallFunctionLeaf
open Solidity.CallFunctionTable Solidity.CallFunctionLeaf
private abbrev C := StandardExample
private abbrev Γ : Ctx := [.val .uint, .val .uint, .val .uint, .val .uint]
private def name : Var := .fresh "same" 0
private def original (a : Nat) : State C Γ :=
  (((({ State.init C with selfBalance := uintOfNat 5, net := [(uintOfNat 5, 19)] }).push
    (t := .val .uint) (uintOfNat a)).push (t := .val .uint) (uintOfNat 99)).push
    (t := .val .uint) (uintOfNat 1)).push (t := .val .uint) (uintOfNat 3)
private def target : Idx Γ (.val .uint) := .there (.there .here)
private def input : Idx Γ (.val .uint) := .there (.there (.there .here))
private def baseTerm : Tm C (.val .uint :: Γ) (.val .uint) :=
  (Val.binop .add rfl rfl
    (.binop .mul rfl rfl (.simple (.local .here)) (.simple (.local (.there .here))))
    (.simple (.local (.there (.there .here))))).lower
private def f (a : Key) : Option Key :=
  baseTerm.eval ((original 2).push (t := .val .uint) a)
private def post (n : Nat) : Fml C Γ :=
  .and (.eq (.pvV target) (.app0 (.lit (uintOfNat n))))
    (.and (.eq (.pvV input) (.app0 (.lit (uintOfNat 2))))
      (.and (.eq (.pvV .here) (.app0 (.lit (uintOfNat 3))))
        (.eq (.pvV (.there .here)) (.app0 (.lit (uintOfNat 1))))))
private def emitted (m : Modality) (k n : Nat) : Fml C Γ :=
  leaf m name name name baseTerm k target input (post n)

/-- Actual checked evaluations across several doubling levels. -/
theorem observations :
    power f 0 (uintOfNat 2) = some (uintOfNat 7) ∧
    power f 1 (uintOfNat 2) = some (uintOfNat 22) ∧
    power f 2 (uintOfNat 2) = some (uintOfNat 202) ∧
    power f 3 (uintOfNat 2) = some (uintOfNat 16402) ∧
    power f 4 (uintOfNat 2) = some (uintOfNat 107616802) ∧
    power f 5 (uintOfNat 2) = some (uintOfNat 4632550472129602) :=
  by decide +kernel

/-- The actual emitted leaf restores the result and preserves all old dependencies. -/
theorem returns (m : Modality) (k n : Nat)
    (he : power f k (uintOfNat 2) = some (uintOfNat n)) :
    holds (original 2) (emitted m k n) := by
  apply (holds_leaf m name name name baseTerm rfl k target input (post n) (original 2)).mpr
  change afterOption m (power f k (uintOfNat 2)) _
  rw [he]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Base level and several non-offset doubling levels certify both modalities. -/
theorem multipleLevels (m : Modality) :
    holds (original 2) (emitted m 0 7) ∧
    holds (original 2) (emitted m 1 22) ∧
    holds (original 2) (emitted m 2 202) ∧
    holds (original 2) (emitted m 3 16402) ∧
    holds (original 2) (emitted m 4 107616802) ∧
    holds (original 2) (emitted m 5 4632550472129602) :=
  ⟨returns m 0 7 observations.1, returns m 1 22 observations.2.1,
    returns m 2 202 observations.2.2.1, returns m 3 16402 observations.2.2.2.1,
    returns m 4 107616802 observations.2.2.2.2.1,
    returns m 5 4632550472129602 observations.2.2.2.2.2⟩

/-- A wrong output cannot hide behind universally guarded table definitions. -/
theorem wrongResult (m : Modality) : ¬ holds (original 2) (emitted m 2 203) := by
  intro hh
  have hr := (holds_leaf m name name name baseTerm rfl 2 target input (post 203) (original 2)).mp hh
  change holds ((original 2).setLocal target (uintOfNat 202)) (post 203) at hr
  have bad : (some (uintOfNat 202) : Option Key) = some (uintOfNat 203) := hr.1
  have hn : (202 : Int) = 203 := congrArg Subtype.val (Option.some.inj bad)
  omega

/-- The input may itself be the old target: every composition still reads
original captured dependencies, and the assignment happens only at the end. -/
theorem inputIsTarget (m : Modality) :
    holds (original 2) (leaf m name name name baseTerm 2 input input
      (.and (.eq (.pvV input) (.app0 (.lit (uintOfNat 202))))
        (.eq (.pvV target) (.app0 (.lit (uintOfNat 99)))))) := by
  apply (holds_leaf m name name name baseTerm rfl 2 input input _ (original 2)).mpr
  exact ⟨rfl, rfl⟩

/-- The target can alias a captured coefficient without changing intermediate calls. -/
theorem coefficientIsTarget (m : Modality) :
    holds (original 2) (leaf m name name name baseTerm 2 .here input
      (.and (.eq (.pvV .here) (.app0 (.lit (uintOfNat 202))))
        (.eq (.pvV input) (.app0 (.lit (uintOfNat 2)))))) := by
  apply (holds_leaf m name name name baseTerm rfl 2 .here input _ (original 2)).mpr
  exact ⟨rfl, rfl⟩

/-- An actual old-context update continuation is retained by result restoration. -/
theorem modalPost (m : Modality) : holds (original 2)
    (leaf m name name name baseTerm 1 target input (.upd m .nil (post 22))) := by
  apply (holds_leaf m name name name baseTerm rfl 1 target input _ (original 2)).mpr
  change holds ((original 2).setLocal target (uintOfNat 22)) (.upd m .nil (post 22))
  apply (Upd.afterT_lands_iff (Upd.lands_nil _) m (holds · (post 22))).mpr
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Program modalities also retain their original caller context. -/
theorem programModalPost (m : Modality) : holds (original 2)
    (leaf m name name name baseTerm 1 target input
      (.modal m (.nil : Prog C Γ Γ) .nil (post 22))) := by
  apply (holds_leaf m name name name baseTerm rfl 1 target input _ (original 2)).mpr
  change holds ((original 2).setLocal target (uintOfNat 22)) (post 22) ∧ _
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, by intro hh; cases hh⟩

private def partialTerm : Tm C (.val .uint :: Γ) (.val .uint) :=
  (Val.binop .div rfl rfl (.simple (.lit 1 rfl))
    (.binop .sub rfl rfl (.simple (.local .here)) (.simple (.lit 1 rfl)))).lower

/-- Distinct first and later failure paths, plus a genuine successful zero. -/
theorem partialObservations :
    power (fun a => partialTerm.eval ((original 2).push (t := .val .uint) a)) 1
      (uintOfNat 1) = none ∧
    power (fun a => partialTerm.eval ((original 2).push (t := .val .uint) a)) 1
      (uintOfNat 2) = none ∧
    power (fun a => partialTerm.eval ((original 2).push (t := .val .uint) a)) 0
      (uintOfNat 3) = some (uintOfNat 0) := ⟨rfl, rfl, rfl⟩

/-- Box retains ordinary revert even for a false post on the later failure path. -/
theorem laterFailureBox : holds (original 2)
    (leaf .box name name name partialTerm 1 target input .ff) := by
  apply (holds_leaf .box name name name partialTerm rfl 1 target input .ff (original 2)).mpr
  trivial

/-- Diamond rejects that same failure even with a true post. -/
theorem laterFailureDiamond : ¬ holds (original 2)
    (leaf .diamond name name name partialTerm 1 target input .tt) := by
  intro hh
  exact (holds_leaf .diamond name name name partialTerm rfl 1 target input .tt (original 2)).mp hh

/-- First failure has the same original modality distinction. -/
theorem firstFailure : holds (original 1)
    (leaf .box name name name partialTerm 1 target input .ff) ∧
    ¬ holds (original 1) (leaf .diamond name name name partialTerm 1 target input .tt) := by
  constructor
  · apply (holds_leaf .box name name name partialTerm rfl 1 target input .ff (original 1)).mpr
    trivial
  · intro hh
    exact (holds_leaf .diamond name name name partialTerm rfl 1 target input .tt (original 1)).mp hh

/-- Returning zero is a genuine diamond success, not the failure sentinel. -/
theorem returnsZero : holds (original 3)
    (leaf .diamond name name name partialTerm 0 target input
      (.eq (.pvV target) (.app0 (.lit (uintOfNat 0))))) := by
  apply (holds_leaf .diamond name name name partialTerm rfl 0 target input _ (original 3)).mpr
  rfl

/-- Complete emitted leaf sizes grow by 33 per doubling level, not 2^k.
This counts intrinsic formula syntax, separately from context/index metadata. -/
theorem actualSizes :
    (emitted .box 0 7).tmSize = 70 ∧
    (emitted .box 1 22).tmSize = 103 ∧
    (emitted .box 2 202).tmSize = 136 ∧
    (emitted .box 3 16402).tmSize = 169 ∧
    (emitted .box 4 107616802).tmSize = 202 ∧
    (emitted .box 5 4632550472129602).tmSize = 235 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Actual maximum formula contexts include both composition quantifiers,
not only the fresh result binder; depths are measured separately from nodes. -/
theorem actualContextPeaks :
    contextPeak (emitted .box 0 7) = 7 ∧
    contextPeak (emitted .box 1 22) = 8 ∧
    contextPeak (emitted .box 2 202) = 9 ∧
    contextPeak (emitted .box 3 16402) = 10 ∧
    contextPeak (emitted .box 4 107616802) = 11 ∧
    contextPeak (emitted .box 5 4632550472129602) = 12 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Solidity.Examples.Tactics.CallFunctionLeaf
