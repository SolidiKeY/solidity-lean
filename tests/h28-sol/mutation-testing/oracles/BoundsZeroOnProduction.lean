import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! Negative semantic control (index-bounds): the kill witness `BoundsZeroKill` with its
premise definition replaced by the production premise (the production read of `d[1]`, which fails as the run does).  The link
`source_link` must elaborate against the unchanged table, and the kill
argument, unchanged otherwise, must then fail: a witness that went through
here would show the production rule unsound.  The runner decides it
`semantic-witness-failed` only if every error lies after the link and
the failure reaches `checked_kill`. -/
namespace H28.BoundsZeroOnProduction
open Solidity

def dynamicName : Name := String.singleton 'd'
def C : Contract := { vars := [(dynamicName, .ref (.array (.prim .uint)))] }
def Γ : Ctx := [.val .uint]
def path : SPath C Γ (.array (.prim .uint)) := .loc (.root dynamicName rfl)
def populated : State C Γ := ((State.init C).push (t := .val .uint) ⟨9, rfl⟩).withStorage
  (.cons (.array (.cons (.prim ⟨7, rfl⟩) .nil) .nil (by decide +kernel)) .nil)

def readValue (i : PrimTy.uint.Denote) : Val C Γ .uint :=
  .read (.index (.arr .dyn) path (.simple (.lit i.1 i.2)))
def statement : Stmt C Γ Γ := .assignLocal .here (readValue ⟨1, rfl⟩)
def zeroPath : Tm C Γ (.path (.prim .uint)) :=
  Tms.PTerm.at (.arr .dyn) path.lower (Simple.lit (C := C) (Γ := Γ) 1 rfl).lower
def update : Upd C Γ Γ := .snoc .nil (.local .here (.val (Tms.Term.find Tms.STerm.storage zeroPath)))
def mutated : Premise C Γ Γ := .update update

/-- This instance links the witness to the actual mutated production rule. -/
theorem source_link : Taclet C 0 .diamond statement mutated :=
  .storageIndexReadArrayFind (ak := .dyn) (arr := path) (v := .here) (ie := .lit 1 rfl) rfl

/-- A concrete inhabited input, not an assumed or empty relation. -/
theorem input_inhabited : Nonempty (State C Γ) := ⟨populated⟩

/-- The typed run reverts: `d[1]` is past the end of `[7]`. -/
theorem actual_run : statement.runR populated = .error .revert := by rfl

/-- The mutant's update reads `d[0]` and returns. -/
theorem update_returns : update.globT populated = some populated.globG := by
  with_unfolding_all rfl

/-- So the mutant's premise admits a returning run. -/
theorem premise_accepts_true : holds populated (mutated.fml .diamond .nil .nil .tt) := by
  change update.afterT .diamond populated (fun _ => True)
  apply Upd.afterT_intro
  · intro h
    rw [update_returns] at h
    cases h
  · intro g τ h
    trivial

/-- The real execution reverts, so it does not return. -/
theorem execution_rejects : ¬ holds populated (.modal .diamond (.cons statement .nil) .nil .tt) := by
  change ¬ (THalt.revert = THalt.exhausted ∧ _)
  intro h
  cases h.1

/-- The linked mutated rule is semantically unsound at this inhabited input. -/
theorem checked_kill : ¬ Premise.Sound .diamond statement mutated populated := by
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
end H28.BoundsZeroOnProduction
