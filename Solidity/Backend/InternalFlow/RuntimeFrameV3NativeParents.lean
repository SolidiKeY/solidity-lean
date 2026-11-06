import Solidity.Backend.InternalFlow.RuntimeFrameV3ParentStop

/-! Native child-call/return clauses for the SAME indexed parent family used
by target unwind. This consumes actual typed arguments and call execution;
it is not an independent trace evaluator or a general recursive compiler. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.NativeParents
open Evm Evm.Memory RecursiveSource ParentPrefixes

/-- Actual guard, argument order, child body and caller restoration, at every
native horizon. Insufficient unrolling remains exhaustion, not REVERT. -/
theorem clause {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (σ : State C (Parameters R)) (n : Nat) (bound : n+1<W) (ref : HRef σ.H R)
 (alias : σ.env.2.1=some ref) (depth : Nat) :
 (nextArgs R hm).evalT (sourceAt σ (n+1) bound)=.ok (sourceAt σ n (by omega)).env ∧
 nonzero.evalT (sourceAt σ (n+1) bound)=.ok true ∧
 (body R hm depth).run (sourceAt σ n (by omega))=
   (if n<depth then .ok ⟨sourceAt σ n (by omega),List.prefix_refl _⟩ else .error .exhausted) ∧
 (InterfaceV1.recursiveSource "countdown" (nextArgs R hm) .none (step R hm) depth).run
     (sourceAt σ (n+1) bound)=
   (if n<depth then .ok ⟨sourceAt σ (n+1) bound,List.prefix_refl _⟩ else .error .exhausted) := by
 have args := next_eval hm (sourceAt σ (n+1) bound) n bound ref rfl alias
 have tail : σ.env.2=(some ref,()) := Prod.ext alias (by cases σ.env.2.2;rfl)
 have entered : (nextArgs R hm).evalT (sourceAt σ (n+1) bound)=
     .ok (sourceAt σ n (by omega)).env := by
   change (nextArgs R hm).evalT (sourceAt σ (n+1) bound)=.ok (countValue n (by omega),σ.env.2)
   rw [tail]
   exact args
 have guard := guard_eval (sourceAt σ (n+1) bound) (n+1) rfl
 refine ⟨entered,?_,all_horizons hm depth (sourceAt σ n (by omega)) n (by omega) ref rfl alias,?_⟩
 · simpa only [show decide (0<n+1)=true from decide_eq_true (by omega)] using guard
 · exact call_all_horizons hm "countdown" (nextArgs R hm) depth (sourceAt σ (n+1) bound)
     n (by omega) ref args

/-- A genuine insufficient native child horizon cannot be promoted to
source success or matching successful transport, or relabeled as bare revert. -/
theorem insufficient {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (σ : State C (Parameters R)) (n : Nat) (bound : n+1<W) (ref : HRef σ.H R)
 (alias : σ.env.2.1=some ref) :
 (InterfaceV1.recursiveSource "countdown" (nextArgs R hm) .none (step R hm) n).run
   (sourceAt σ (n+1) bound)=.error .exhausted := by
 simpa only [Nat.lt_irrefl,if_false] using (clause hm σ n bound ref alias n).2.2.2

/-- Caller restoration must not export the child counter as the caller
local, even though both destinations have the same primitive type. -/
theorem not_child_return {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (σ : State C (Parameters R)) (n : Nat) (bound : n+1<W) (ref : HRef σ.H R)
 (alias : σ.env.2.1=some ref) (depth : Nat) (enough : n<depth) :
 (InterfaceV1.recursiveSource "countdown" (nextArgs R hm) .none (step R hm) depth).run
   (sourceAt σ (n+1) bound)≠.ok ⟨sourceAt σ n (by omega),List.prefix_refl _⟩ := by
 have actual := (clause hm σ n bound ref alias depth).2.2.2
 rw [if_pos enough] at actual
 rw [actual]
 intro bad
 have values := congrArg (fun out : Solidity.Out C σ.H (Parameters R) =>
   (TEnv.get (.here : Idx (Parameters R) (.val .uint)) out.st.env).val) (Except.ok.inj bad)
 change ((n+1:Nat):Int)=(n:Int) at values
 omega

namespace Checks
open CountdownWitness RecursiveActivation

/-- Actual positive native parent clauses and the actual represented target
unwind horizons agree on the SAME parent state and alias. No source/target
endpoint or entered state is supplied as a premise. -/
theorem coupled (k depth : Nat) (positive : 1≤k) (within : k≤2) (enough : k-1<depth) :
 ∃ down last addresses,
 (nextArgs A rfl).evalT (sourceAt callee k (Nat.lt_of_le_of_lt within (by decide)))=
   .ok (sourceAt callee (k-1) (Nat.lt_of_le_of_lt (Nat.sub_le k 1) (Nat.lt_of_le_of_lt within (by decide)))).env ∧
 (InterfaceV1.recursiveSource "countdown" (nextArgs A rfl) .none (step A rfl) depth).run
   (sourceAt callee k (Nat.lt_of_le_of_lt within (by decide)))=
   .ok ⟨sourceAt callee k (Nat.lt_of_le_of_lt within (by decide)),List.prefix_refl _⟩ ∧
 run (descentCode (C:=P.C) 2 F 8) ParentPrefixes.Checks.input=.ok down 0 ∧
 loopIterN (run (PairedUnwind.condition 8 7))
   (run (Restore.restoreCells 8 (Restore.contextCells 2 (Parameters A)))) k down=.inl last ∧
 StateRepr 1 2 16 F (sourceAt callee k (Nat.lt_of_le_of_lt within (by decide))) addresses last ∧
 last.stack=[w[77]] ∧ last.mem 8=.val (wmod (10+2*(2-k))) ∧ last.mem 2=w[16] ∧
 last.mem 3=.val (wmod k) ∧ StructAllocatorRepr callee.heap addresses 16 ⟨22,by decide⟩ last ∧
 [last.mem 16,last.mem 17,last.mem 18,last.mem 20,last.mem 21]=[w[2],w[7],w[9],w[1],w[4]] ∧
 [last.mem 0,last.mem 1,last.mem 7,last.mem 10,last.mem 11,last.mem 12,last.mem 13]=
 [w[22],w[16],w[10],w[16],w[2],w[16],w[1]] := by
 cases k with
 | zero => omega
 | succ n =>
   simp only [Nat.add_sub_cancel] at enough
   have wordBound : n+1<W := Nat.lt_of_le_of_lt within (by decide)
   have native := clause rfl callee n wordBound P.r0 rfl depth
   obtain ⟨down,last,addresses,descended,running,repr,stack,cursor,reference,counter,ownership,heap,words,negative⟩ :=
     ParentPrefixes.Checks.horizons (n+1) within
   refine ⟨down,last,addresses,?_,?_,descended,running,repr,stack,cursor,reference,counter,ownership,heap,words⟩
   · simpa only [Nat.add_sub_cancel] using native.1
   · simpa only [if_pos enough] using native.2.2.2

/-- Actual nontrivial child-call control: the represented parent-one clause
has a successful child at depth one but exhausts at depth zero. -/
theorem exhausted_not_revert :
 (InterfaceV1.recursiveSource "countdown" (nextArgs A rfl) .none (step A rfl) 0).run
   (sourceAt callee 1 (by decide))=.error .exhausted ∧
 (InterfaceV1.recursiveSource "countdown" (nextArgs A rfl) .none (step A rfl) 0).run
   (sourceAt callee 1 (by decide))≠.error .revert := by
 have actual := insufficient rfl callee 0 (by decide) P.r0 rfl
 refine ⟨actual,?_⟩
 rw [actual];intro bad;cases bad

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.NativeParents

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.NativeParents.Checks.coupled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.NativeParents.Checks.coupled
