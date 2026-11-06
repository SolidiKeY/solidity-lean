import Solidity.Backend.StorageOps.NestedPopTransport
import Solidity.Backend.StorageOps.NumericClearCommutation

/-! Generated access/log certificates and commutation of ACTUAL nested pops.
Current outer and selected-child headers drive execution. Exact original per-run
coverage and cross-set separation derive read/guard/count/log stability. -/
namespace Solidity.Backend.StorageOps.NestedPopCommutation
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

private theorem header_bound (N : Nat) (hash : Solidity.Storage.Pre → Nat)
 (base : Solidity.Storage.Loc) (initial : WordStore) :
 LifecycleNumeric.headerLength N hash base initial<2^256 := by
 have bound := (initial (base.word N hash)).property
 simp only [PrimTy.inRange,decide_eq_true_eq] at bound
 unfold LifecycleNumeric.headerLength
 omega

def selected (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (initial : WordStore) : Solidity.Storage.Loc :=
 .data base (LifecycleNumeric.headerLength N hash base initial-1)

def decremented (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (initial : WordStore) : WordStore :=
 writeWord initial (base.word N hash) (lengthWord (LifecycleNumeric.headerLength N hash base initial-1)
  (by have bound:=header_bound N hash base initial; omega))

/-- Outer root is always read; child and runtime live grandchildren are touched
ONLY when the original outer guard succeeds. No fixed count/depth cap. -/
def touches (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (initial : WordStore) : List Solidity.Storage.Loc :=
 base :: if 0<LifecycleNumeric.headerLength N hash base initial then
 NumericClearCommutation.touches N hash (selected N hash base initial) (decremented N hash base initial) else []

/-- Exact successful operation log; empty failure contributes no writes. Child
clear length is read AFTER the original outer-root decrement, just as execute. -/
def writeLog (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (initial : WordStore) : List (Solidity.Storage.Loc × Semantics.Word) :=
 if 0<LifecycleNumeric.headerLength N hash base initial then
 (base,lengthWord (LifecycleNumeric.headerLength N hash base initial-1) (by have bound:=header_bound N hash base initial; omega)) ::
 NumericClearCommutation.writeLog N hash (selected N hash base initial) (decremented N hash base initial) else []

/-- Certificate DERIVED from actual numeric nested-pop execution, not a new
operation evaluator or assumed preservation theorem. BOTH Option outcomes. -/
theorem execute_log (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (initial : WordStore) :
 NestedPopTransport.execute N hash base initial =
 if 0<LifecycleNumeric.headerLength N hash base initial then
 some ((writeLog N hash base initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial) else none := by
 by_cases live : 0<LifecycleNumeric.headerLength N hash base initial
 · unfold NestedPopTransport.execute
   dsimp only
   rw [dif_pos live,if_pos live,writeLog,if_pos live]
   simp only [List.foldl_cons]
   rw [NumericClearCommutation.clear_log]
   rfl
 · unfold NestedPopTransport.execute
   dsimp only
   rw [dif_neg live,if_neg live]

/-- Every generated successful write belongs to the original operation set. -/
theorem log_touched (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (initial : WordStore)
 (op : Solidity.Storage.Loc × Semantics.Word) (member : op ∈ writeLog N hash base initial) :
 op.1 ∈ touches N hash base initial := by
 by_cases live : 0<LifecycleNumeric.headerLength N hash base initial
 · rw [writeLog,if_pos live] at member
   rcases List.mem_cons.mp member with same | inside
   · subst op; exact List.mem_cons_self
   · exact List.mem_cons_of_mem _ (by rw [if_pos live]; exact NumericClearCommutation.log_touched N hash _ _ op inside)
 · rw [writeLog,if_neg live] at member
   cases member

/-- Successful actual operation frames arbitrary covered observers. No
post-frame premise is supplied; separation is exactly the original finite run. -/
theorem execute_frames {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (base : Solidity.Storage.Loc) (initial result : WordStore)
 (performed : NestedPopTransport.execute N hash base initial=some result)
 (observers : List Solidity.Storage.Loc)
 (covered : ∀ l ∈ touches N hash base initial ++ observers, l ∈ locations)
 (separate : ∀ w ∈ touches N hash base initial, ∀ r ∈ observers, w ≠ r) :
 ∀ r ∈ observers, result (r.word N hash)=initial (r.word N hash) := by
 rw [execute_log] at performed
 split at performed
 · cases performed
   intro r observed
   apply sequence_outside_frame
   intro op inside same
   have written:=log_touched N hash base initial op inside
   exact separate op.1 written r observed (run.word_inj
    (covered _ (List.mem_append.mpr (Or.inl written)))
    (covered _ (List.mem_append.mpr (Or.inr observed))) same.symm)
 · cases performed

/-- OLD generated read agreement derives actual selection, child count, guard
and complete log stability. It does not assume desired result preservation. -/
theorem log_stable (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc)
 (old current : WordStore)
 (agree : ∀ l ∈ touches N hash base old, current (l.word N hash)=old (l.word N hash)) :
 writeLog N hash base current=writeLog N hash base old := by
 have root := agree base List.mem_cons_self
 by_cases live : 0<LifecycleNumeric.headerLength N hash base old
 · have childMember : selected N hash base old ∈ touches N hash base old := by
    unfold touches
    rw [if_pos live]
    exact List.mem_cons_of_mem _ List.mem_cons_self
   have child := agree _ childMember
   simp only [selected,LifecycleNumeric.headerLength] at child
   simp only [writeLog,NumericClearCommutation.writeLog,selected,decremented,LifecycleNumeric.headerLength,writeWord,root,child]
 · have currentEmpty : ¬ 0<LifecycleNumeric.headerLength N hash base current := by
    simpa only [LifecycleNumeric.headerLength,root] using live
   rw [writeLog,if_neg currentEmpty,writeLog,if_neg live]

/-- Actual operation after a framed update reuses its OLD guard and log,
while its writes execute over CURRENT storage. No captured-source oracle. -/
theorem execute_stable (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc)
 (old current : WordStore)
 (agree : ∀ l ∈ touches N hash base old, current (l.word N hash)=old (l.word N hash)) :
 NestedPopTransport.execute N hash base current=
 if 0<LifecycleNumeric.headerLength N hash base old then
 some ((writeLog N hash base old).foldl (fun m op => writeWord m (op.1.word N hash) op.2) current) else none := by
 rw [execute_log,log_stable N hash base old current agree]
 simp only [LifecycleNumeric.headerLength,agree base List.mem_cons_self]

/-- Disjoint ACTUAL nested pops commute at every raw numeric word and BOTH
Option outcomes. All reads, selected addresses/counts, guards and generated logs
are framed from the ORIGINAL run/footprints; no middle-state assumption. -/
theorem pop_pop {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (left right : Solidity.Storage.Loc) (initial : WordStore)
 (covered : ∀ l ∈ touches N hash left initial ++ touches N hash right initial, l ∈ locations)
 (separate : ∀ a ∈ touches N hash left initial, ∀ b ∈ touches N hash right initial, a ≠ b) :
 (NestedPopTransport.execute N hash left initial).bind (NestedPopTransport.execute N hash right)=
 (NestedPopTransport.execute N hash right initial).bind (NestedPopTransport.execute N hash left) := by
 have afterLeft : ∀ current, NestedPopTransport.execute N hash left initial=some current →
  NestedPopTransport.execute N hash right current=
  if 0<LifecycleNumeric.headerLength N hash right initial then
   some ((writeLog N hash right initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2) current) else none := by
  intro current performed
  exact execute_stable N hash right initial current
   (execute_frames run left initial current performed (touches N hash right initial) covered separate)
 have reverseCovered : ∀ l ∈ touches N hash right initial ++ touches N hash left initial, l ∈ locations := by
  intro l member
  rcases List.mem_append.mp member with rightMember | leftMember
  · exact covered l (List.mem_append.mpr (Or.inr rightMember))
  · exact covered l (List.mem_append.mpr (Or.inl leftMember))
 have afterRight : ∀ current, NestedPopTransport.execute N hash right initial=some current →
  NestedPopTransport.execute N hash left current=
  if 0<LifecycleNumeric.headerLength N hash left initial then
   some ((writeLog N hash left initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2) current) else none := by
  intro current performed
  exact execute_stable N hash left initial current
   (execute_frames run right initial current performed (touches N hash left initial) reverseCovered
    (fun a ha b hb => Ne.symm (separate b hb a ha)))
 by_cases leftLive : 0<LifecycleNumeric.headerLength N hash left initial
 · have leftPerformed : NestedPopTransport.execute N hash left initial=
    some ((writeLog N hash left initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial) := by
    rw [execute_log,if_pos leftLive]
   rw [leftPerformed]
   simp only [Option.bind_some]
   rw [afterLeft _ leftPerformed]
   by_cases rightLive : 0<LifecycleNumeric.headerLength N hash right initial
   · have rightPerformed : NestedPopTransport.execute N hash right initial=
      some ((writeLog N hash right initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial) := by
      rw [execute_log,if_pos rightLive]
     rw [rightPerformed]
     simp only [Option.bind_some]
     rw [afterRight _ rightPerformed,if_pos rightLive,if_pos leftLive]
     apply congrArg some
     apply NumericCopyCommutation.write_logs_commute
     intro a ha b hb same
     have aTouched:=log_touched N hash left initial a ha
     have bTouched:=log_touched N hash right initial b hb
     exact separate a.1 aTouched b.1 bTouched (run.word_inj
      (covered _ (List.mem_append.mpr (Or.inl aTouched)))
      (covered _ (List.mem_append.mpr (Or.inr bTouched))) same)
   · rw [if_neg rightLive,execute_log N hash right initial,if_neg rightLive]
     rfl
 · have leftFailed : NestedPopTransport.execute N hash left initial=none := by
    rw [execute_log,if_neg leftLive]
   rw [leftFailed]
   simp only [Option.bind_none]
   by_cases rightLive : 0<LifecycleNumeric.headerLength N hash right initial
   · have rightPerformed : NestedPopTransport.execute N hash right initial=
      some ((writeLog N hash right initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial) := by
      rw [execute_log,if_pos rightLive]
     rw [rightPerformed]
     simp only [Option.bind_some]
     rw [afterRight _ rightPerformed,if_neg leftLive]
   · rw [execute_log N hash right initial,if_neg rightLive]
     rfl

/-- Original Transport and coverage of every ACTUAL generated write derive
post-Transport. The symbolic fold is a log certificate, not new source meaning. -/
theorem execute_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (base : Solidity.Storage.Loc)
 (captured : Store) (initial result : WordStore)
 (before : Transport N hash locations captured initial)
 (performed : NestedPopTransport.execute N hash base initial=some result)
 (covered : ∀ l ∈ touches N hash base initial, l ∈ locations) :
 Transport N hash locations
 ((writeLog N hash base initial).foldl (fun store op => Representation.write store op.1 op.2) captured) result := by
 rw [execute_log] at performed
 split at performed
 · cases performed
   exact transport_sequence run before (writeLog N hash base initial)
    (fun op member => covered op.1 (log_touched N hash base initial op member))
 · cases performed

/-- info: 'Solidity.Backend.StorageOps.NestedPopCommutation.execute_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms execute_transport
/-- info: 'Solidity.Backend.StorageOps.NestedPopCommutation.execute_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms execute_stable
/-- info: 'Solidity.Backend.StorageOps.NestedPopCommutation.pop_pop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pop_pop
/-- info: 'Solidity.Backend.StorageOps.NestedPopCommutation.execute_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms execute_log
/-- info: 'Solidity.Backend.StorageOps.NestedPopCommutation.log_touched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms log_touched
/-- info: 'Solidity.Backend.StorageOps.NestedPopCommutation.execute_frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms execute_frames
/-- info: 'Solidity.Backend.StorageOps.NestedPopCommutation.log_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms log_stable
end Solidity.Backend.StorageOps.NestedPopCommutation
