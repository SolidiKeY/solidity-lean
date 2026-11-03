import Solidity.Backend.InternalFlow.RuntimeFrameV3ArgumentCalleeFailure

/-! Uniform zero/return/read-failure transport for the existing allocating
countdown image. Demand is source-computed for this family; it is not an
approved-profile predicate or a replacement for the published loop cost.
Successful-return frame obligations are required only on the returning path. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOutcome
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes
abbrev A : RefTy := CountdownWitness.A

/-- A bad first read is reached after one allocation, not count allocations. -/
def demand (count length : Nat) : Nat := if count≤length then 4*count else 4

/-- Source quotation needed to observe this family's outcome. -/
def requiredDepth (count length : Nat) : Nat := if count≤length then count+1 else 1

/-- Only physical return-path obligations, not an executable semantics or an
approved domain. No condition here asserts a desired target execution. -/
structure ReturnRoom {Γ : Ctx} (b frame need lo pointer bottom start count : Nat)
 (F : Frag Γ) (before : Machine) : Prop where
 prefixBound : b+need≤lo
 boundary : lo≤frame
 pointerAbove : lo≤pointer
 pointerBelow : pointer<frame
 bottomAbove : lo≤bottom
 bottomBelow : bottom<frame
 current : before.mem pointer=.val (wmod start)
 bottomValue : before.mem bottom=.val (wmod start)
 localBound : 0<count → b+Γ.length+2<lo
 payload : 0<count → lo≤start
 pointerBefore : 0<count → pointer<start
 savedRoom : 0<count → start+2*count≤frame
 savedFits : 0<count → start+2*count<W
 bottomLocal : 0<count → b+Γ.length+2<bottom
 bottomBefore : 0<count → bottom<start
 separate : 0<count → bottom≠pointer
 notFragile : 0<count → ∀ {R : RefTy} (i : Idx Γ (.alias R)), F.get i≠.fragile

/-- The same real image handles zero, successful allocating return, and first
read failure. Source and physical resources are tied to the reached path;
no output state is created for the error alternative. -/
theorem after_arguments {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
 (name : Name) (args : Args C Γ (Parameters A))
 (compiled : Composition.Program b F (args.declsThen .nil)) (σ : State C Γ)
 (count : Nat) (bound : count<W) (ref : HRef σ.H A)
 (evaluated : args.evalT σ=.ok (countValue count bound,(some ref,())))
 (base : Nat → Fin W) (before : Machine) (initial : StateRepr L b frame F σ base before)
 (lo pointer bottom start : Nat) (prefixRoom : b+compiled.checked.need≤frame)
 (bodyRoom : 0<count → b+Γ.length+3≤frame)
 (returnRoom : count≤σ.heap.len ref .dyn → ReturnRoom b frame compiled.checked.need lo pointer bottom start count
   (compiled.checked.frag.restrict Γ) before)
 (capacity : AllocationInput b frame (compiled.checked.cost σ+demand count (σ.heap.len ref .dyn)) σ base before)
 (depth : Nat) (enough : requiredDepth count (σ.heap.len ref .dyn)≤depth) :
 GrowingResult L b frame (compiled.checked.cost σ+demand count (σ.heap.len ref .dyn)) (compiled.checked.frag.restrict Γ)
   σ base before ((InterfaceV1.recursiveSource name args .none AllocatingActivation.step depth).run σ)
   (run (compiled.checked.code++AllocatingReturn.image (C:=C) (b+Γ.length) (Frag.init (Parameters A)) pointer bottom) before) := by
 by_cases reads : count≤σ.heap.len ref .dyn
 · have room := returnRoom reads
   have budget : AllocationInput b frame (compiled.checked.cost σ+4*count) σ base before := by
     simpa only [demand,if_pos reads] using capacity
   have index : count<depth := by
     simp only [requiredDepth,if_pos reads] at enough
     omega
   cases count with
   | zero =>
     have input : AllocationInput b frame (compiled.checked.cost σ) σ base before := by
       simpa only [Nat.mul_zero,Nat.add_zero] using budget
     obtain ⟨target,addresses,source,executed,represented,stack,extended,growth⟩ :=
       AllocatingZero.after_arguments name args compiled σ (countValue 0 bound,(some ref,())) evaluated rfl depth index
         base before initial lo pointer bottom start room.prefixBound room.boundary room.pointerAbove room.pointerBelow
         room.bottomAbove room.bottomBelow room.current room.bottomValue input
     refine .inl ⟨⟨σ,List.prefix_refl _⟩,target,addresses,source,executed,represented,stack,extended,?_⟩
     simpa only [demand,if_pos reads,Nat.mul_zero,Nat.add_zero] using growth
   | succ n =>
     obtain ⟨out,target,addresses,mid,prefixRun,source,executed,represented,stack,extended,growth,words,current,saved⟩ :=
       AllocatingQuotations.after_arguments name args compiled σ (countValue (n+1) bound,(some ref,())) evaluated
         (n+1) (by omega) bound ref rfl rfl reads base before initial lo pointer bottom start room.prefixBound room.boundary
         (room.localBound (by omega)) room.pointerAbove room.pointerBelow (room.payload (by omega)) (room.pointerBefore (by omega))
         (room.savedRoom (by omega)) (room.savedFits (by omega)) room.current (room.bottomLocal (by omega)) room.bottomBelow
         (room.bottomBefore (by omega)) (room.separate (by omega)) room.bottomValue room.bottomAbove budget (room.notFragile (by omega))
     have actual : (InterfaceV1.recursiveSource name args .none AllocatingActivation.step depth).run σ=.ok out := by
       simpa only [if_pos index] using source depth
     refine .inl ⟨out,target,addresses,actual,executed,represented,stack,extended,?_⟩
     simpa only [demand,if_pos reads] using growth
 · have budget : AllocationInput b frame (compiled.checked.cost σ+4) σ base before := by
     simpa only [demand,if_neg reads] using capacity
   have index : 0<depth := by
     simp only [requiredDepth,if_neg reads] at enough
     omega
   cases count with
   | zero => omega
   | succ n =>
     have failed : ArrayProbe.value.evalT (σ.withEnv (Δ:=Parameters A) (countValue (n+1) bound,(some ref,())))=.error .revert :=
       (HeapDomain.failure_iff _ n bound ref rfl rfl).2 (by change σ.heap.len ref .dyn≤n;omega)
     obtain ⟨mid,addresses,prefixRun,parameters,caller,stack,extended,input,source,failedTarget⟩ :=
       ArgumentCalleeFailure.after_arguments name args compiled.checked σ n bound ref evaluated failed base before initial
         prefixRoom (bodyRoom (by omega)) budget pointer bottom
     cases depth with
     | zero => omega
     | succ depth =>
       exact .inr ⟨source depth,by simpa only [List.append_nil] using failedTarget []⟩

namespace Checks
open CountdownWitness
abbrev Γ := MemoryArgument.Γ
abbrev F := MemoryArgument.F
abbrev caller := MemoryArgument.caller
abbrev ref := Evm.Memory.CompileExamples.r1

namespace Positive
abbrev checked := ArgumentEntry.Checks.checked

theorem room : ReturnRoom 1 16 checked.need 7 8 7 10 1 (checked.frag.restrict Γ) MemoryArgument.input where
 prefixBound := by rw [ArgumentEntry.Checks.need_eq];decide
 boundary := by decide
 pointerAbove := by decide
 pointerBelow := by decide
 bottomAbove := by decide
 bottomBelow := by decide
 current := rfl
 bottomValue := rfl
 localBound := by intro positive;decide
 payload := by intro positive;decide
 pointerBefore := by intro positive;decide
 savedRoom := by intro positive;decide
 savedFits := by intro positive;decide
 bottomLocal := by intro positive;decide
 bottomBefore := by intro positive;decide
 separate := by intro positive;decide
 notFragile := by intro positive R i;cases i with | there i => cases i with | there i => cases i with | there i => cases i

theorem matched (depth : Nat) (enough : 1<depth) :
 GrowingResult 1 1 16 4 F caller P.base MemoryArgument.input
   ((InterfaceV1.recursiveSource "allocatingCountdown" MemoryArgument.args .none AllocatingActivation.step depth).run caller)
   (run ArgumentCall.code MemoryArgument.input) := by
 have reads : 1≤caller.heap.len ref .dyn := MemoryArgument.read_bound
 have capacity : AllocationInput 1 16 (checked.cost caller+demand 1 (caller.heap.len ref .dyn)) caller P.base MemoryArgument.input := by
   simpa only [demand,if_pos reads] using ArgumentCall.total_capacity
 have actual := after_arguments "allocatingCountdown" MemoryArgument.args ArgumentEntry.Checks.prepared caller
   1 (by decide) ref MemoryArgument.arguments P.base MemoryArgument.input MemoryArgument.initial 7 8 7 10
   (by change 1+checked.need≤16;rw [ArgumentEntry.Checks.need_eq];decide) (by intro positive;decide)
   (fun _ => room) capacity depth (by simp only [requiredDepth,if_pos reads];omega)
 simpa only [demand,if_pos reads,ArgumentEntry.Checks.cost_zero,Nat.zero_add,ArgumentCall.caller_fragment] using actual
theorem observations :
 (ArgumentCall.last.stack,[ArgumentCall.last.mem 0,ArgumentCall.last.mem 1,ArgumentCall.last.mem 2,ArgumentCall.last.mem 3,ArgumentCall.last.mem 4,ArgumentCall.last.mem 5,ArgumentCall.last.mem 7,ArgumentCall.last.mem 8,ArgumentCall.last.mem 9,
 ArgumentCall.last.mem 10,ArgumentCall.last.mem 11,ArgumentCall.last.mem 12,ArgumentCall.last.mem 13,ArgumentCall.last.mem 16,ArgumentCall.last.mem 17,ArgumentCall.last.mem 18,ArgumentCall.last.mem 20,ArgumentCall.last.mem 21])=
 ([w[77]],[w[26],w[20],w[16],w[9],w[20],w[1],w[10],w[10],w[99],w[20],w[1],w[0],w[0],w[2],w[7],w[9],w[1],w[4]]) := ArgumentCall.observations

end Positive

namespace Zero
abbrev Z := AllocatingZero.Checks.input
abbrev checked := AllocatingZero.Checks.checked

theorem room : ReturnRoom 1 16 checked.need 6 8 7 10 0 (checked.frag.restrict Γ) Z where
 prefixBound := by rw [AllocatingZero.Checks.need_eq];decide
 boundary := by decide
 pointerAbove := by decide
 pointerBelow := by decide
 bottomAbove := by decide
 bottomBelow := by decide
 current := rfl
 bottomValue := rfl
 localBound := by intro positive;omega
 payload := by intro positive;omega
 pointerBefore := by intro positive;omega
 savedRoom := by intro positive;omega
 savedFits := by intro positive;omega
 bottomLocal := by intro positive;omega
 bottomBefore := by intro positive;omega
 separate := by intro positive;omega
 notFragile := by intro positive;omega

theorem matched (depth : Nat) (positive : 0<depth) :
 GrowingResult 1 1 16 0 F caller P.base Z
   ((InterfaceV1.recursiveSource "allocatingCountdown" AllocatingZero.Checks.args .none AllocatingActivation.step depth).run caller)
   (run AllocatingZero.Checks.code Z) := by
 have reads : 0≤caller.heap.len ref .dyn := Nat.zero_le _
 have capacity : AllocationInput 1 16 (checked.cost caller+demand 0 (caller.heap.len ref .dyn)) caller P.base Z := by
   simpa only [demand,if_pos reads,Nat.mul_zero,Nat.add_zero] using AllocatingZero.Checks.capacity
 have actual := after_arguments "allocatingCountdown" AllocatingZero.Checks.args AllocatingZero.Checks.prepared caller
   0 W_pos ref AllocatingZero.Checks.arguments P.base Z AllocatingZero.Checks.initial 6 8 7 10
   (by change 1+checked.need≤16;rw [AllocatingZero.Checks.need_eq];decide) (by intro impossible;omega)
   (fun _ => room) capacity depth (by simp only [requiredDepth,if_pos reads];omega)
 simpa only [demand,if_pos reads,Nat.mul_zero,AllocatingZero.Checks.cost_zero,Nat.add_zero,AllocatingZero.Checks.caller_fragment] using actual

theorem no_owner (cursor : Fin W) : ¬StructAllocatorRepr caller.heap P.base 16 cursor Z := AllocatingZero.Checks.no_owner cursor
theorem observations :
 (AllocatingZero.Checks.target.stack,[AllocatingZero.Checks.target.mem 0,AllocatingZero.Checks.target.mem 1,AllocatingZero.Checks.target.mem 2,AllocatingZero.Checks.target.mem 3,AllocatingZero.Checks.target.mem 4,AllocatingZero.Checks.target.mem 5,AllocatingZero.Checks.target.mem 6,
 AllocatingZero.Checks.target.mem 7,AllocatingZero.Checks.target.mem 8,AllocatingZero.Checks.target.mem 9,AllocatingZero.Checks.target.mem 10,AllocatingZero.Checks.target.mem 11,AllocatingZero.Checks.target.mem 16,AllocatingZero.Checks.target.mem 17,AllocatingZero.Checks.target.mem 18,AllocatingZero.Checks.target.mem 20,AllocatingZero.Checks.target.mem 21])=
 ([w[77]],[w[0],w[20],w[16],w[9],w[20],w[0],w[0],w[10],w[10],w[99],w[0],w[0],w[2],w[7],w[9],w[1],w[4]]) := AllocatingZero.Checks.observations

end Zero

namespace Failure
abbrev B := ArgumentCalleeFailure.Checks.checked
abbrev input := MemoryArgument.input

theorem safe : Composition.ProgramSafe B := by
 intro L frame lo σ base m target repr room boundary capacity actual
 have same : target=writeMachine (writeMachine m 4 (m.mem 1)) 5 w[3] := by
   rw [ArgumentCalleeFailure.Checks.code_eq] at actual
   exact (Evm.Out.ok.inj actual).1.symm
 subst target
 rw [ArgumentCalleeFailure.Checks.need_eq] at room
 intro x above below
 exact (upd_other _ w[3] (by omega)).trans (upd_other _ (m.mem 1) (by omega))

def prepared : Composition.Program 1 F ArgumentCalleeFailure.Checks.program := ⟨B,safe⟩

theorem bad_domain : ¬3≤caller.heap.len ref .dyn := by
 change ¬3≤CountdownWitness.callee.heap.len ref .dyn
 rw [HeapDomain.Checks.length_one]
 decide

def code := B.code++AllocatingReturn.image (C:=P.C) 4 CountdownWitness.F 0 0

/-- No returning-frame capability exists for these overlapping zero addresses.
That capability is unreachable on the actual bare-revert path. -/
theorem no_return_room : ¬ReturnRoom 1 16 B.need 0 0 0 0 3 (B.frag.restrict Γ) input := by
 intro h
 have bound := h.prefixBound
 omega

theorem matched (depth : Nat) (positive : 0<depth) :
 GrowingResult 1 1 16 4 F caller P.base input
   ((ArgumentCalleeFailure.Checks.call depth).run caller) (run code input) := by
 have capacity : AllocationInput 1 16 (B.cost caller+demand 3 (caller.heap.len ref .dyn)) caller P.base input := by
   simpa only [demand,if_neg bad_domain] using ArgumentCalleeFailure.Checks.total_capacity
 have actual := after_arguments "allocatingCountdown" ArgumentCalleeFailure.Checks.args prepared caller
   3 (by decide) ref ArgumentCalleeFailure.Checks.args_succeed P.base input MemoryArgument.initial 0 0 0 0
   (by change 1+B.need≤16;rw [ArgumentCalleeFailure.Checks.need_eq];decide) (by intro positive;decide)
   (fun reads => (bad_domain reads).elim) capacity depth (by simp only [requiredDepth,if_neg bad_domain];omega)
 have fragment : B.frag.restrict Γ=F := rfl
 simpa only [demand,if_neg bad_domain,ArgumentCalleeFailure.Checks.cost_zero,Nat.zero_add,fragment] using actual

theorem target_revert : run code input=.revert := by
 rcases matched 1 (by decide) with ⟨out,m,addresses,source,rest⟩ | ⟨source,target⟩
 · rw [ArgumentCalleeFailure.Checks.source_failure 0] at source
   cases source
 · exact target

theorem wrong_cost : demand 3 (caller.heap.len ref .dyn)≠12 := by
 rw [demand,if_neg bad_domain]
 decide

theorem zero_unmatched : ¬GrowingResult 1 1 16 4 F caller P.base input
 ((ArgumentCalleeFailure.Checks.call 0).run caller) (run code input) := by
 rw [ArgumentCalleeFailure.Checks.source_zero]
 intro same
 rcases same with ⟨out,m,addresses,source,rest⟩ | ⟨source,rest⟩
 · cases source
 · cases source
theorem observations :
 (ArgumentCalleeFailure.Checks.reached.stack,[ArgumentCalleeFailure.Checks.reached.mem 0,ArgumentCalleeFailure.Checks.reached.mem 1,ArgumentCalleeFailure.Checks.reached.mem 2,ArgumentCalleeFailure.Checks.reached.mem 3,ArgumentCalleeFailure.Checks.reached.mem 4,ArgumentCalleeFailure.Checks.reached.mem 5,ArgumentCalleeFailure.Checks.reached.mem 6,
 ArgumentCalleeFailure.Checks.reached.mem 7,ArgumentCalleeFailure.Checks.reached.mem 8,ArgumentCalleeFailure.Checks.reached.mem 9,ArgumentCalleeFailure.Checks.reached.mem 16,ArgumentCalleeFailure.Checks.reached.mem 17,ArgumentCalleeFailure.Checks.reached.mem 18,ArgumentCalleeFailure.Checks.reached.mem 20,ArgumentCalleeFailure.Checks.reached.mem 21,
 ArgumentCalleeFailure.Checks.reached.mem 22,ArgumentCalleeFailure.Checks.reached.mem 23,ArgumentCalleeFailure.Checks.reached.mem 24,ArgumentCalleeFailure.Checks.reached.mem 25])=
 ([w[77]],[w[26],w[20],w[16],w[9],w[20],w[3],w[22],w[10],w[10],w[99],w[2],w[7],w[9],w[1],w[4],w[3],w[0],w[0],w[0]]) := ArgumentCalleeFailure.Checks.allocation_observations

end Failure

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOutcome
