import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatorReturn

/-! Actual intrinsic source and hand-written runtime execution packaged in the
existing GrowingResult relation. This is a success client, not compiler output
or a dual-outcome recursive producer. Native unrolling exhaustion is retained. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveResult
open Evm Evm.Memory RecursiveSource RecursiveReturn
open CountdownWitness

/-- All sufficient native horizons match the SAME actual runtime image,
including source output, representation, exact zero heap cost, old address map,
protected stack and allocator transport. Initial ownership is inhabited. -/
theorem success (depth : Nat) (enough : 2<depth) :
 GrowingResult 1 2 16 0 F callee P.base AllocatorReturn.Checks.input
   ((body A rfl depth).run callee)
   (run (entryCode (C:=P.C) 2 F 8 7) AllocatorReturn.Checks.input) := by
 obtain ⟨last,executed,represented,ownership,growth,stack,rest⟩ := AllocatorReturn.Checks.endpoint
 exact .inl ⟨⟨callee,List.prefix_refl _⟩,last,P.base,
   specification.1 depth enough,executed,represented,stack,BaseExtends.refl _,growth⟩

/-- A genuine native admission boundary: depth two exhausts, while the
runtime image still succeeds. The public matching relation must reject this
pair rather than relabel exhaustion as REVERT or success. -/
theorem shallow_refused :
 ¬ GrowingResult 1 2 16 0 F callee P.base AllocatorReturn.Checks.input
   ((body A rfl 2).run callee)
   (run (entryCode (C:=P.C) 2 F 8 7) AllocatorReturn.Checks.input) := by
 have source : (body A rfl 2).run callee=.error .exhausted := by
   simpa only [if_false,show ¬ (2:Nat)<2 from by decide] using
     all_horizons rfl 2 callee 2 (by decide) P.r0 rfl rfl
 intro matched
 rcases matched with ⟨out,last,addresses,ok,rest⟩ | ⟨reverted,rest⟩
 · rw [source] at ok
   cases ok
 · rw [source] at reverted
   cases reverted

end Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveResult

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveResult.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveResult.success
