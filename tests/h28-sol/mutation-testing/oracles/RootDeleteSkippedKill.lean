import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! A checked counterexample to `storageRootDelete` with its storage update
dropped (`{ storage := storage }`).  The root `x` holds 7; `delete x;`
really sets it to 0, while the mutant's identity update applies and keeps 7,
so its premise admits `x == 7`, which the run falsifies. -/
namespace H28.RootDeleteSkippedKill
open Solidity

def xName : Name := String.singleton 'x'
def C : Contract := { vars := [(xName, .prim .uint)] }
def root : Loc C [] (.prim .uint) := .root xName rfl
def start : State C [] := (State.init C).withStorage (.cons (.prim ⟨7, rfl⟩) .nil)
def statement : Stmt C [] [] := .delete root
def update : Upd C [] [] := .snoc .nil (.storage Tms.STerm.storage)
def mutated : Premise C [] [] := .update update
def post : Fml C [] := .eq (Tms.Term.find Tms.STerm.storage (Tms.PTerm.root xName rfl)) (Tms.Term.nat 7)

/-- This instance links the witness to the actual mutated production rule. -/
theorem source_link : Taclet C 0 .box statement mutated := .storageRootDelete

/-- A concrete inhabited input, not an assumed or empty relation. -/
theorem input_inhabited : Nonempty (State C []) := ⟨start⟩

def deleted : State C [] := (State.init C).withStorage (.cons (.prim ⟨0, rfl⟩) .nil)

/-- The typed run clears the root. -/
theorem actual_run : statement.runR start = .ok ⟨deleted, List.prefix_refl _⟩ := by
  with_unfolding_all rfl

/-- The mutant's update applies and returns the unchanged globals. -/
theorem update_returns : update.globT start = some start.globG := by rfl

/-- Every state the mutant's update lands in still reads 7 at the root. -/
theorem premise_accepts_post : holds start (mutated.fml .box .nil .nil post) := by
  rw [show holds start (mutated.fml .box .nil .nil post) =
    Upd.afterT .box start update (fun τ => holds τ post) from rfl]
  rw [Upd.afterT_applyV]
  intro τ hg hl
  have hs := congrArg (fun g => g.storage) hg
  simp only at hs
  change Tm.denote τ _ = Tm.denote τ _
  have h' : τ.storage = start.storage := hs
  obtain ⟨st, H, hp, env, net, sb, tx⟩ := τ
  simp only at h'
  subst h'
  rfl

theorem real_frames : Prog.runFrames start (.cons statement .nil) .nil = .ok deleted := by
  with_unfolding_all rfl

/-- The real execution reads 0 at the root, falsifying the postcondition. -/
theorem execution_rejects_post : ¬ holds start (.modal .box (.cons statement .nil) .nil post) := by
  change ¬ Modality.afterRunTR .box (fun τ => holds τ post) (Prog.runFrames start (.cons statement .nil) .nil)
  rw [real_frames]
  intro h
  cases h.1

/-- The linked mutated rule is semantically unsound at this inhabited input. -/
theorem checked_kill : ¬ Premise.Sound .box statement mutated start := by
  intro h
  exact execution_rejects_post (h .nil .nil post premise_accepts_post)

#print axioms source_link
#print axioms input_inhabited
#print axioms actual_run
#print axioms update_returns
#print axioms premise_accepts_post
#print axioms real_frames
#print axioms execution_rejects_post
#print axioms checked_kill
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @checked_kill
end H28.RootDeleteSkippedKill
