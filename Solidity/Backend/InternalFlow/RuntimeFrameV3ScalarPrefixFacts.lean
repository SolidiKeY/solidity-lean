import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarStop
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarUnwindFacts

/-! One fixed populated native descent supplies all inputs for every scalar
unwind horizon. Initialization and saved payloads are actual executions;
there is no chosen midpoint or target simulation premise. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPrefixes.Client
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource RecursiveActivation CountdownWitness
open ScalarUnwind.Client
noncomputable def down : Machine := available.choose
noncomputable def zero : Machine := available.choose_spec.choose
noncomputable def addresses : Nat → Fin W := available.choose_spec.choose_spec.choose

theorem preparation :
 run (descentCode (C:=P.C) 2 CountdownWitness.F 8) entered=.ok down 0 ∧
 run [.push w[0],.mstore 4] down=.ok zero 0 ∧
 StateRepr 1 2 16 ScalarUnwind.Client.F (state 0 W_pos) addresses zero ∧
 zero.stack=[w[77]] ∧ zero.mem 8=w[16] ∧ zero.mem 2=w[16] ∧
 (∀ j,j<3 → zero.mem (10+2*j)=zero.mem 2 ∧ zero.mem (10+2*j+1)=.val (wmod (3-j))) ∧
 (∀ x,x≠8 → x≠3 → x≠4 → (x<10 ∨ 16≤x) → zero.mem x=ScalarUnwind.Client.before.mem x) ∧
 BaseExtends origin.H P.base addresses ∧
 StructAllocatorRepr (state 0 W_pos).heap addresses 16 ⟨22,by decide⟩ zero :=
 available.choose_spec.choose_spec.choose_spec

noncomputable def input : Machine := writeMachine zero 7 w[10]

theorem initialization : run [.push w[10],.mstore 7] zero=.ok input 0 := rfl

theorem initial : StateRepr 1 2 16 ScalarUnwind.Client.F (state 0 W_pos) addresses input :=
 reserved_write preparation.2.2.1 7 (by decide) (by decide) w[10]

theorem owner : StructAllocatorRepr (state 0 W_pos).heap addresses 16 ⟨22,by decide⟩ input :=
 preparation.2.2.2.2.2.2.2.2.2.localWrite 7 (by decide) (by decide) w[10]

theorem current : input.mem 8=w[16] := (upd_other zero.mem w[10] (by decide : (8:Nat)≠7)).trans preparation.2.2.2.2.1

theorem reference : input.mem 2=w[16] := (upd_other zero.mem w[10] (by decide : (2:Nat)≠7)).trans preparation.2.2.2.2.2.1

theorem saved (j : Nat) (small : j<3) :
 input.mem (10+2*j)=input.mem 2 ∧ input.mem (10+2*j+1)=.val (wmod (3-j)) := by
 have words := preparation.2.2.2.2.2.2.1 j small
 exact ⟨(upd_other zero.mem w[10] (by omega)).trans (words.1.trans (upd_other zero.mem w[10] (by decide : (2:Nat)≠7)).symm),
   (upd_other zero.mem w[10] (by omega)).trans words.2⟩

theorem horizon (n : Nat) (within : n≤3) : ∃ last,
 loopIterN (run (PairedUnwind.condition 8 7))
   (run (ScalarUnwind.code (C:=P.C) 2 8 ScalarUnwind.Client.F)) n input=.inl last ∧
 StateRepr 1 2 16 ScalarUnwind.Client.F (state n (Nat.lt_of_le_of_lt within (by decide))) addresses last ∧
 last.stack=input.stack ∧ last.mem 8=.val (wmod (10+2*(3-n))) ∧ last.mem 2=input.mem 2 ∧
 GrowsAllocator 2 16 0 (state 0 W_pos) addresses input
   (state n (Nat.lt_of_le_of_lt within (by decide))) addresses last ∧
 (∀ x,x≠8 → x≠2 → x≠3 → x≠4 → last.mem x=input.mem x) := by
 have result := running_prefix (state 0 W_pos) addresses 3 n 3 within (Nat.le_refl _) (by decide)
   input initial 8 8 7 10 (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) (by decide) current rfl saved
 simpa only [Nat.sub_self,Nat.zero_add] using result

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPrefixes.Client
