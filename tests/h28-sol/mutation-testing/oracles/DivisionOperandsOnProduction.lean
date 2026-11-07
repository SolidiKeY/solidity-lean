import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! Negative semantic control (division-minimum): the kill witness `DivisionOperandsKill` with its
premise definition replaced by the production premise (the production `1 / 0`, which fails as the run does).  The link
`source_link` must elaborate against the unchanged table, and the kill
argument, unchanged otherwise, must then fail: a witness that went through
here would show the production rule unsound.  The runner decides it
`semantic-witness-failed` only if every error lies after the link and
the failure reaches `checked_kill`. -/
namespace H28.DivisionOperandsOnProduction
open Solidity

def C : Contract := { vars := [] }
def Γ : Ctx := [.val .uint]
def start : State C Γ := (State.init C).push (t := .val .uint) ⟨9, rfl⟩
def statement : Stmt C Γ Γ :=
  .assignLocal .here (.binop .div rfl rfl (.simple (.lit 1 rfl)) (.simple (.lit 0 rfl)))
def update : Upd C Γ Γ := .snoc .nil (.local .here (.val
  (Tms.Term.binopS .div rfl rfl (Simple.lit (C := C) (Γ := Γ) 1 rfl).lower (Simple.lit 0 rfl).lower)))
def mutated : Premise C Γ Γ := .update update

/-- This instance links the witness to the actual mutated production rule. -/
theorem source_link : Taclet C 0 .diamond statement mutated := .binopAssignment

/-- A concrete inhabited input, not an assumed or empty relation. -/
theorem input_inhabited : Nonempty (State C Γ) := ⟨start⟩

/-- The typed run fails: `1 / 0`. -/
theorem actual_run : statement.runR start = .error .revert := by with_unfolding_all rfl

/-- The mutant's update computes `0 / 1` and returns. -/
theorem update_returns : update.globT start = some start.globG := by
  with_unfolding_all rfl

/-- So the mutant's premise admits a returning run. -/
theorem premise_accepts_true : holds start (mutated.fml .diamond .nil .nil .tt) := by
  change update.afterT .diamond start (fun _ => True)
  apply Upd.afterT_intro
  · intro h
    rw [update_returns] at h
    cases h
  · intro g τ h
    trivial

/-- The real execution fails, so it does not return. -/
theorem execution_rejects : ¬ holds start (.modal .diamond (.cons statement .nil) .nil .tt) := by
  change ¬ (THalt.revert = THalt.exhausted ∧ _)
  intro h
  cases h.1

/-- The linked mutated rule is semantically unsound at this inhabited input. -/
theorem checked_kill : ¬ Premise.Sound .diamond statement mutated start := by
  intro h
  exact execution_rejects (h .nil .nil .tt premise_accepts_true)

#print axioms source_link
#print axioms input_inhabited
#print axioms actual_run
#print axioms update_returns
#print axioms premise_accepts_true
#print axioms execution_rejects
#print axioms checked_kill
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @checked_kill
end H28.DivisionOperandsOnProduction
