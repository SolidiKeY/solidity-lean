import Solidity.Backend.InternalFlow.RuntimeFrameV3OrderedEffectfulClient

/-! Heap-reading scalar arguments can fail before the ordered callee write.
The existing checked argument prefix supplies target absorption. Source halts
remain exact; only bare revert is transported to the target here. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.OrderedArgumentFailure
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

theorem source_halt {C : Contract} {Γ : Ctx} (function : Name)
 (args : Args C Γ (Parameters EffectfulScalarSource.A)) (destination : Idx Γ (.val .uint))
 (depth : Nat) (caller : State C Γ) (halt : THalt) (failed : args.evalT caller=.error halt) :
 (EffectfulScalarSource.invoke function args destination depth).run caller=.error halt := by
 change TRun.call args (.val .uint (.user "result") (some destination))
   (EffectfulScalarSource.body (C:=C) depth).ext (EffectfulScalarSource.body depth).runR caller=_
 unfold TRun.call
 simp only [failed,error_bind]

/-- Reuse the checked entry-prefix failure, including its actual reference
copy and scalar argument code. No capacity for an unreachable callee is added. -/
theorem transport {C : Contract} {Γ : Ctx} {L b c frame : Nat} {F : Frag Γ}
 (caller : State C Γ) (reference : Idx Γ (.mem OrderedEffectfulScalar.A))
 (count : Val C Γ .uint) (value : CompiledVal b F count)
 (failed : count.evalT caller=.error .revert)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F caller base before)
 (disjoint : b+Γ.length≤c) (space : c+3≤frame) :
 (DisjointScalarEntry.args rfl reference count).evalT caller=.error .revert ∧
 (∀ (function : Name) (depth : Nat) (destination : Idx Γ (.val .uint)),
   (OrderedEffectfulScalar.call reference count destination function depth).run caller=.error .revert) ∧
 (∀ (destination : Idx Γ (.val .uint)) (pointer bottom : Nat) (suffix : List Instr),
   run (OrderedEffectfulScalar.code b c reference value destination pointer bottom++suffix) before=.revert) := by
 have checked := DisjointScalarEntry.revert rfl caller reference count value failed base before repr disjoint space
 refine ⟨checked.1,?_,?_⟩
 · intro function depth destination
   exact source_halt function (DisjointScalarEntry.args rfl reference count) destination depth caller .revert checked.1
 · intro destination pointer bottom suffix
   simpa only [OrderedEffectfulScalar.code,List.append_assoc] using
     checked.2 ((OrderedEffectfulScalar.calleeCode (C:=C) c ++
       (ScalarReturn.image (C:=C) c (Frag.init (Parameters OrderedEffectfulScalar.A)) pointer bottom ++
         [.mload (c+2),.mstore (cellOf b destination)])) ++ suffix)

namespace Client
open DisjointScalarReturn.Client (Γ F reference)
open OrderedEffectfulScalar.Client (count value)

theorem checked_failure :
 (DisjointScalarEntry.args rfl reference count).evalT SameCallInputs.caller=.error .revert ∧
 (∀ (function : Name) (depth : Nat) (destination : Idx Γ (.val .uint)),
   (OrderedEffectfulScalar.call reference count destination function depth).run SameCallInputs.caller=.error .revert) ∧
 (∀ (destination : Idx Γ (.val .uint)) (pointer bottom : Nat) (suffix : List Instr),
   run (OrderedEffectfulScalar.code 1 5 reference value destination pointer bottom++suffix) SameCallInputs.machine=.revert) :=
 transport (c:=5) SameCallInputs.caller reference count value SameCallInputs.count_fails
   SameCallInputs.addresses SameCallInputs.machine SameCallInputs.reached.2.2.1 (by decide) (by decide)

def image : List Instr := OrderedEffectfulScalar.code 1 5 reference value (.here : Idx Γ (.val .uint)) 9 8

theorem source (depth : Nat) :
 (OrderedEffectfulScalar.call reference count (.here : Idx Γ (.val .uint)) "orderedScalar" depth).run SameCallInputs.caller=.error .revert :=
 checked_failure.2.1 "orderedScalar" depth .here

theorem target_suffix (suffix : List Instr) : run (image++suffix) SameCallInputs.machine=.revert :=
 checked_failure.2.2 .here 9 8 suffix

theorem target : run image SameCallInputs.machine=.revert := by
 simpa only [List.append_nil] using target_suffix []

def program (depth : Nat) : Prog SameCallInputs.C Γ Γ :=
 .cons SameCallInputs.preparation
   (.cons (OrderedEffectfulScalar.call reference count (.here : Idx Γ (.val .uint)) "orderedScalar" depth) .nil)

theorem whole_source (depth : Nat) : (program depth).run SameCallInputs.origin=.error .revert := by
 rw [program,Prog.run_cons_ok SameCallInputs.reached.1]
 change (TRun.seq (OrderedEffectfulScalar.call reference count (.here : Idx Γ (.val .uint)) "orderedScalar" depth).runR
   TRun.nil SameCallInputs.caller).map _=_
 simp only [TRun.seq,show (OrderedEffectfulScalar.call reference count (.here : Idx Γ (.val .uint)) "orderedScalar" depth).runR
   SameCallInputs.caller=.error .revert from source depth,Except.map]

theorem whole_target : run (SameCallInputs.checked.code++image) SameCallInputs.before=.revert :=
 (run_append_ok SameCallInputs.reached.2.1).trans target

/-- The same reached input distinguishes failure of the heap-reading argument
from the previous literal-argument callee-write failure. -/
theorem failure_stages :
 (DisjointScalarEntry.args rfl reference count).evalT SameCallInputs.caller=.error .revert ∧
 (DisjointScalarEntry.args rfl reference DisjointScalarReturn.Client.count).evalT SameCallInputs.caller=
   .ok (countValue 3 (by decide),(some SameCallInputs.fresh,())) :=
 ⟨checked_failure.1,EffectfulScalarFailure.Client.arguments⟩

theorem source_not_exhausted (depth : Nat) :
 (OrderedEffectfulScalar.call reference count (.here : Idx Γ (.val .uint)) "orderedScalar" depth).run SameCallInputs.caller≠.error .exhausted := by
 rw [source]
 intro impossible
 cases impossible

theorem target_not_ok (last : Machine) (remaining : Nat) :
 run image SameCallInputs.machine≠.ok last remaining := by
 rw [target]
 intro impossible
 cases impossible

theorem target_not_fault : run image SameCallInputs.machine≠.fault := by
 rw [target]
 intro impossible
 cases impossible

theorem zero_control :
 (OrderedEffectfulScalar.call reference count (.here : Idx Γ (.val .uint)) "orderedScalar" 0).run
   OrderedEffectfulScalar.Client.caller=.error .exhausted ∧
 (OrderedEffectfulScalar.call reference count (.here : Idx Γ (.val .uint)) "orderedScalar" 0).run SameCallInputs.caller=.error .revert ∧
 run image OrderedEffectfulScalar.Client.before=.ok OrderedEffectfulScalar.Client.machine 0 ∧
 run image SameCallInputs.machine=.revert :=
 ⟨OrderedEffectfulScalar.Client.shallow_boundary.1,source 0,OrderedEffectfulScalar.Client.specification.1,target⟩

end Client

end Solidity.Backend.InternalFlow.RuntimeFrame.OrderedArgumentFailure
