import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveReturn
import Solidity.Evm.MemoryCompileExamples

/-! A populated, registered client of the intrinsic countdown return emitter.
All inputs come from the published memory fixture and actual prefix execution.
No test module or unproved representation/endpoint premise is imported. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness
open Evm Evm.Memory RecursiveSource RecursiveActivation RecursiveReturn
namespace P
abbrev C := Evm.Memory.CompileExamples.C
abbrev Γ := Evm.Memory.CompileExamples.Γ
abbrev σ := Evm.Memory.CompileExamples.σ
abbrev machine := Evm.Memory.CompileExamples.machine
abbrev base := Evm.Memory.CompileExamples.base
abbrev r0 := Evm.Memory.CompileExamples.r0
abbrev uint := Evm.Memory.CompileExamples.uint
end P
abbrev A : RefTy := .array (.prim .uint)
abbrev F := Frag.init (Parameters A)
def caller := P.σ.setLocal (.here : Idx P.Γ (.val .uint)) (P.uint 2 (by decide))
def machine := writeMachine (writeMachine (writeMachine {P.machine with stack:=[w[77]]} 3 w[2]) 8 w[10]) 9 w[99]
def callee := caller.withEnv (Δ:=Parameters A) (TEnv.take (Parameters A) caller.env)

theorem source_prefix : (Stmt.assignLocal (.here : Idx P.Γ (.val .uint)) (.simple (.lit 2 rfl))).run P.σ=
 .ok ⟨caller,List.prefix_refl _⟩ := by rfl

theorem target_prefix : run [.push w[2],.mstore 3,.push w[10],.mstore 8,.push w[99],.mstore 9]
 {P.machine with stack:=[w[77]]}=.ok machine 0 := by rfl

theorem caller_repr : StateRepr 1 0 16 (Frag.init P.Γ) caller P.base machine := by
 have changed := ((Evm.Memory.CompileExamples.fixture_six_cells).stack [w[77]]).setVal
   (.here : Idx P.Γ (.val .uint)) (P.uint 2 (by decide)) w[2] (ReprV.uint_of rfl)
 have widened : StateRepr 1 0 16 (Frag.init P.Γ) caller P.base
     (writeMachine {P.machine with stack:=[w[77]]} 3 w[2]) := by
   refine ⟨changed.core,⟨changed.heap.arrays,?_,changed.heap.separated⟩,
     changed.pointers,by decide,⟨changed.structs.objects,?_,changed.structs.separated⟩,
     changed.separated,changed.refs⟩
   · intro p r
     rcases r with ⟨i,hi⟩
     cases i with
     | zero => change 16≤16;decide
     | succ i => cases i with
       | zero => change 16≤20;decide
       | succ i => cases hi
   · intro name r
     rcases r with ⟨i,hi⟩
     cases i with
     | zero => cases hi
     | succ i => cases i with
       | zero => cases hi
       | succ i => cases hi
 exact reserved_write (reserved_write widened 8 (by decide) (by decide) w[10]) 9 (by decide) (by decide) w[99]

theorem callee_repr : StateRepr 1 2 16 F callee P.base machine :=
 parameter_projection (tail:=[.mem A,.mem A]) caller_repr

noncomputable def returned : Machine :=
 (initialized_endpoint rfl 2 (by decide) callee P.r0 rfl rfl P.base machine callee_repr 8 8 7 10
   (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
   (by decide) (by decide) rfl).choose

theorem specification :
 (∀ depth, 2<depth → (body A rfl depth).run callee=.ok ⟨callee,List.prefix_refl _⟩) ∧
 run (entryCode (C:=P.C) 2 F 8 7) machine=.ok returned 0 ∧
 StateRepr 1 2 16 F callee P.base returned ∧ returned.stack=machine.stack ∧ returned.mem 8=w[10] ∧
 (∀ x, x<10 → x≠7 → returned.mem x=machine.mem x) ∧
 (∀ x, 16≤x → returned.mem x=machine.mem x) ∧
 (∀ j, j<2 → returned.mem (10+2*j)=machine.mem 2 ∧ returned.mem (10+2*j+1)=.val (wmod (2-j))) ∧
 returned.mem 7=w[10] :=
 (initialized_endpoint rfl 2 (by decide) callee P.r0 rfl rfl P.base machine callee_repr 8 8 7 10
   (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
   (by decide) (by decide) rfl).choose_spec

theorem protected_arena : Footprint.Words 8 10 machine returned := by
 intro x above below
 exact specification.2.2.2.2.2.1 x below (by omega)

def args : Args P.C P.Γ (Parameters A) := entryArgs A rfl (.there .here) .here
def call (depth : Nat) : Stmt P.C P.Γ P.Γ :=
 InterfaceV1.recursiveSource "countdown" args .none (step A rfl) depth

theorem arguments : args.evalT caller=.ok callee.env := by rfl

theorem source_call (depth : Nat) : (call depth).run caller=
 if 2<depth then .ok ⟨caller,List.prefix_refl _⟩ else .error .exhausted :=
 call_all_horizons rfl "countdown" args depth caller 2 (by decide) P.r0 arguments

/-- Reconstruct the entire original caller, including both older aliases,
from the real reached callee globals/heap and proved caller-word equality. -/
theorem returned_caller : StateRepr 1 0 16 (Frag.init P.Γ) caller P.base returned := by
 rcases specification with ⟨source,run,reached,stack,cursor,low,high,rest⟩
 have locals : ∀ {t : LTy} (index : Idx P.Γ t), Restored.Observed (Frag.init P.Γ) index →
     returned.mem (cellOf 0 index)=machine.mem (cellOf 0 index) := by
   intro t index observed
   have small := lvl_lt 0 index
   change cellOf 0 index<0+P.Γ.length at small
   have len : P.Γ.length=4 := rfl
   rw [len] at small
   exact low _ (by omega) (by omega)
 have transported := Restored.memory_transport caller_repr returned.mem locals high
 refine ⟨⟨reached.core.store,transported.core.vals,transported.core.aliases,
   reached.core.net,reached.core.netSelf,caller_repr.core.bound,transported.core.fragile,
   reached.core.env,reached.core.funds,reached.core.oracle⟩,
   reached.heap,transported.pointers,transported.locals,reached.structs,reached.separated,reached.refs⟩

theorem call_endpoint (depth : Nat) (enough : 2<depth) :
 (call depth).run caller=.ok ⟨caller,List.prefix_refl _⟩ ∧
 run (entryCode (C:=P.C) 2 F 8 7) machine=.ok returned 0 ∧
 StateRepr 1 0 16 (Frag.init P.Γ) caller P.base returned := by
 refine ⟨?_,specification.2.1,returned_caller⟩
 simpa only [if_pos enough] using source_call depth

def observed (m : Machine) := (m.stack,[m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 8,m.mem 9,
 m.mem 10,m.mem 11,m.mem 12,m.mem 13,m.mem 16,m.mem 17,m.mem 18,m.mem 20,m.mem 21])

theorem observations :
 (observed returned,returned.mem 7)=
 (([w[77]],[w[20],w[16],w[16],w[2],w[10],w[99],w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[1],w[4]]),w[10]) := by
 rcases specification with ⟨source,run,repr,stack,cursor,low,high,saved,bottom⟩
 have p0 := saved 0 (by decide)
 have p1 := saved 1 (by decide)
 change ((returned.stack,[returned.mem 0,returned.mem 1,returned.mem 2,returned.mem 3,
   returned.mem 8,returned.mem 9,returned.mem 10,returned.mem 11,returned.mem 12,returned.mem 13,
   returned.mem 16,returned.mem 17,returned.mem 18,returned.mem 20,returned.mem 21]),returned.mem 7) = _
 rw [stack,cursor,bottom,low 0 (by decide) (by decide),low 1 (by decide) (by decide),
   low 2 (by decide) (by decide),low 3 (by decide) (by decide),low 9 (by decide) (by decide),
   high 16 (by decide),high 17 (by decide),high 18 (by decide),high 20 (by decide),high 21 (by decide)]
 change returned.mem 10=machine.mem 2 ∧ returned.mem 11=w[2] at p0
 change returned.mem 12=machine.mem 2 ∧ returned.mem 13=w[1] at p1
 rw [p0.1,p0.2,p1.1,p1.2]
 rfl

theorem wrong_alias : returned.mem 2≠w[20] := by
 have word := specification.2.2.2.2.2.1 2 (by decide) (by decide)
 change returned.mem 2=w[16] at word
 rw [word];decide

theorem wrong_cursor : returned.mem 8≠w[14] := by
 rw [specification.2.2.2.2.1];decide

theorem shallow_exhaustion : (call 2).run caller=.error .exhausted := by
 simpa only [show ¬ (2:Nat)<2 from by decide,if_false] using source_call 2

end Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.call_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.call_endpoint
