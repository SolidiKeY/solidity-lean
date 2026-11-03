import Solidity.Lowering.StorageOps.SourceWriteRollback
import Solidity.Lowering.StorageOps.SourceWordCommutationControls

/-! Actual captured Source operations, with a nonempty journal/log prefix and
nonempty locals. Refusal retains the earlier write; a failed bind skips its
rollback continuation. A separately invoked rollbackTo uses the original mark.
The wrong mark removes a valid older write/log prefix. No implicit rollback,
Source AST call sequence, general heap restoration or target claim follows. -/
namespace Solidity.Lowering.StorageOps.SourceWriteRollbackControls
open Solidity
open SourceWordCommutationControls

def seed : Source.St env :=
  {SourceWordCommutationControls.seed with logs := [(address,[9,8]),(frame.sender,[7])]}
def mark := (seed.ex.journal.length,seed.logs.length,seed.heap)
def marked := (Source.mark : Source.EM env Γ (Nat × Nat × Source.Heap env.layout)).run (locals,seed)
def rejector : Source.Fr := {frame with static:=true}
def written := SourceWordWrite.after frame left v seed
def failed := (SourceWriteRollback.refusedAfter (E:=env) (Γ:=Γ) frame rejector left v flag w).run (locals,seed)
def naive := ((do
  SourceWriteRollback.refusedAfter frame rejector left v flag w
  Source.rollbackTo mark) : Source.EM env Γ Unit).run (locals,seed)
def restored := (Source.rollbackTo mark : Source.EM env Γ Unit).run failed.2
def wrongMark := (Source.rollbackTo (0,0,seed.heap) : Source.EM env Γ Unit).run failed.2
def transientValue : Source.Val env.layout (env.cellTy scratch) := .int 89 (by decide)
def transientFailure := (SourceWriteRollback.refusedAfter (E:=env) (Γ:=Γ)
  frame rejector left v scratch transientValue).run (locals,seed)
def wrongTyped := ((do
  Source.writeAt frame left v
  Source.writeAt rejector flag v) : Source.EM env Γ Unit).run (locals,seed)
def logsView (s : Source.St env) := s.logs.map fun (a,bytes) => (a.val,bytes.map UInt8.toNat)

def prefix_certificate := SourceWordWrite.source_write frame left v locals seed rfl rfl
def refusal_certificate := SourceWriteRollback.static_write rejector flag w locals written rfl
def rollback_certificate := SourceWriteRollback.rollback_once frame left v locals seed

def outcomes : Prop :=
  (marked,failed,naive,transientFailure,wrongTyped,restored) =
  ((.ok mark,(locals,seed)),
   (.error (.revert []),(locals,written)),
   (.error (.revert []),(locals,written)),
   (.error (.revert []),(locals,written)),
   (.error (.stuck "storage cell type"),(locals,written)),
   (.ok (),(locals,seed)))

def ordered : Prop :=
  (view seed,view written,view wrongMark.2.2,
    logsView seed,logsView written,logsView restored.2.2,logsView wrongMark.2.2,
    journalView written,journalView restored.2.2,journalView wrongMark.2.2) =
  (([some 11,some 0,some 101],some 41,1,19,3,some 0,0,true,0,2,[.bool]),
   ([some 83,some 0,some 101],some 41,2,19,3,some 0,0,true,0,2,[.bool]),
   ([some 11,some 0,some 97],some 41,0,19,3,some 0,0,true,0,0,[.bool]),
   [(7,[9,8]),(13,[7])],[(7,[9,8]),(13,[7])],[(7,[9,8]),(13,[7])],[],
   [(true,7,[some 11,some 0,some 101],some (19,3,some 0)),
    (true,7,[some 11,some 0,some 97],some (19,3,some 0))],
   [(true,7,[some 11,some 0,some 97],some (19,3,some 0))],[])

theorem outcome_certificate : outcomes := by
  unfold outcomes restored
  rw [show failed=(.error (.revert []),(locals,written)) from rfl]
  dsimp only [mark,written]
  rw [rollback_certificate]
  rfl

theorem observations : ordered := by rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceWriteRollbackControls.prefix_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceWriteRollbackControls.refusal_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms refusal_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceWriteRollbackControls.rollback_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rollback_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceWriteRollbackControls.outcome_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outcome_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceWriteRollbackControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observations

end Solidity.Lowering.StorageOps.SourceWriteRollbackControls
