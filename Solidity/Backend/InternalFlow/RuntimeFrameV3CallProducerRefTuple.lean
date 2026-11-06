import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRef

/-! Existing typed tuple return binders use ascending physical result copies
when private parameters are removed. Source and destination can overlap. This
module emits existing Instr only; no source or intermediate representation is
introduced. A full tuple-call certificate remains a separate next step. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.Tuple
open Evm Evm.Memory

/-- Low addresses first: a destination is never above its source. -/
def copyCode : Nat → Nat → Nat → List Instr
 | _,_,0 => []
 | source,destination,count+1 =>
   [.mload source,.mstore destination] ++ copyCode (source+1) (destination+1) count

def code (b : Nat) (Γ ps : Ctx) {rs : Ctx} (_ : RetBinders rs) : List Instr :=
 copyCode (b+Γ.length+ps.length) (b+Γ.length) rs.length

def CopyResult (source destination count : Nat) (before : Machine) : Prop :=
 ∃ after, Evm.run (copyCode source destination count) before=.ok after 0 ∧
 after.stack=before.stack ∧
 (∀ i, i<count → after.mem (destination+i)=before.mem (source+i)) ∧
 (∀ address, address<destination ∨ destination+count≤address → after.mem address=before.mem address) ∧
 {after with mem:=before.mem,stack:=before.stack}=before

/-- Ascending copies preserve unread source cells even with overlapping
parameter/result intervals. Every word and every other machine field is exact. -/
theorem copy_run (count source destination : Nat) (before : Machine)
 (ordered : destination≤source) : CopyResult source destination count before := by
 induction count generalizing source destination before with
 | zero =>
  refine ⟨before,rfl,rfl,?_,?_,rfl⟩
  · intro i bound
    omega
  · intro address outside
    rfl
 | succ count ih =>
  let first := writeMachine before destination (before.mem source)
  have firstRun : Evm.run [.mload source,.mstore destination] before=.ok first 0 := rfl
  obtain ⟨after,tailRun,stack,values,outside,fields⟩ :=
   ih (source+1) (destination+1) first (by omega)
  refine ⟨after,?_,stack,?_,?_,?_⟩
  · change Evm.run ([.mload source,.mstore destination] ++
      copyCode (source+1) (destination+1) count) before=.ok after 0
    rw [Evm.run_append_ok firstRun]
    exact tailRun
  · intro i bound
    cases i with
    | zero =>
      have kept := outside destination (.inl (by omega))
      simpa only [Nat.add_zero] using kept.trans (upd_same _ _ _)
    | succ i =>
      have value := values i (by omega)
      have different : source+1+i≠destination := by omega
      have same : after.mem (destination+1+i)=before.mem (source+1+i) :=
       value.trans (upd_other _ _ different)
      simpa only [Nat.add_assoc,Nat.add_comm 1 i,Nat.succ_eq_add_one] using same
  · intro address oldOutside
    have tailOutside : address<destination+1 ∨ destination+1+count≤address := by omega
    have different : address≠destination := by omega
    exact (outside address tailOutside).trans (upd_other _ _ different)
  · have same := congrArg (fun m : Machine => {m with mem:=before.mem,stack:=before.stack}) fields
    exact same

namespace Checks

def binders : RetBinders [.val .uint,.val .uint,.val .uint] :=
 .snoc (.snoc (.snoc .nil .uint (.user "a")) .uint (.user "b")) .uint (.user "c")
def input : Machine := {Machine.init with stack:=[w[77]],mem:=fun address =>
 if address=3 then w[11] else if address=4 then w[22] else if address=5 then w[33] else w[0]}
def observe : Evm.Out → Option (List Nat)
 | .ok after _ => (after.stack ++ [after.mem 1,after.mem 2,after.mem 3,after.mem 4,after.mem 5]).mapM
   (fun word => match word with | .val value => some value.val | _ => none)
 | _ => none

theorem overlapping_copy : observe (Evm.run (code 1 [] [.val .uint,.val .uint] binders) input)=
 some [77,11,22,33,22,33] := by
 first | rfl | decide +kernel

def descending : List Instr :=
 [.mload 5,.mstore 3,.mload 4,.mstore 2,.mload 3,.mstore 1]
theorem descending_corrupts : observe (Evm.run descending input)=some [77,33,22,33,22,33] := by
 first | rfl | decide +kernel
theorem descending_refused : observe (Evm.run descending input)≠some [77,11,22,33,22,33] := by
 rw [descending_corrupts]
 decide

end Checks

end Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.Tuple
