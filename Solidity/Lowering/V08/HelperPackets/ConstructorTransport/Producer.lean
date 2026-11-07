import Solidity.Lowering.V08.HelperPackets.ConstructorTransport.MachineRelNat

/-! The concrete SS-NEW body duty derived from actual execution.
SlotRel is independent of constructor arguments and post-state definitions. -/
namespace Solidity.Lowering.V08.HelperPackets.ConstructorTransport
open Solidity
open Solidity.Lowering.V07

theorem initial_related (bytes : Roadmap.Bytes) : MachineRelNat bytes (initial bytes) entered := by
  refine ⟨?_,?_,rfl,rfl,rfl,rfl,rfl,HEq.rfl,rfl,rfl,rfl⟩
  · exact ⟨0,by decide +kernel,rfl,rfl⟩
  · exact ⟨0,by decide +kernel,rfl,rfl⟩

theorem reached_related (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    MachineRelNat bytes (reached bytes n h) (targetReached n h) := by
  refine ⟨?_,?_,rfl,rfl,rfl,rfl,rfl,HEq.rfl,rfl,rfl,rfl⟩
  · exact ⟨n,h,source_saved bytes n h,target_saved n h⟩
  · exact ⟨7,by decide +kernel,source_captured bytes n h,target_captured n h⟩

/-- Exactly the concrete producer duty, with an arbitrary reached Source
post-state. The source run determines that state; no body equality or output
relation appears among the premises. -/
theorem concrete_ssNew_body (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes)
    (n : Int) (h : range n) (after : Source.St E) :
    (Source.construct (global p) frame 16 "Cell" (locals n h)).run
      (Source.L0 E,initial bytes) = (.ok (),(Source.L0 E,after)) →
    ∃ out : Out Cell entered.H [],
      (targetBody n h).run entered = .ok out ∧ MachineRelNat bytes after out.st := by
  intro ran
  rw [source_actual p bytes n h] at ran
  have same : reached bytes n h = after := congrArg (fun x => x.2.2) ran
  subst after
  exact ⟨⟨targetReached n h,List.prefix_refl _⟩,target_body_actual n h,reached_related bytes n h⟩

/-- Both pipelines reach related complete machines and create the specified
address; Source.construct is a constructor phase, not code installation. -/
theorem complete_transport (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes)
    (n : Int) (h : range n) :
    (Source.construct (global p) frame 16 "Cell" (locals n h)).run
      (Source.L0 E,initial bytes) = (.ok (),(Source.L0 E,reached bytes n h)) ∧
    (targetBody n h).run entered = .ok ⟨targetReached n h,List.prefix_refl _⟩ ∧
    MachineRelNat bytes (reached bytes n h) (targetReached n h) ∧
    targetRun n h = .ok (targetNext n h,⟨Controls.self⟩) ∧
    ConstructorScalarTransport.FrameInputs frame Controls.self targetContext :=
  ⟨source_actual p bytes n h,target_body_actual n h,reached_related bytes n h,
    creation_actual n h,frame_inputs⟩
/-- Wiring at the published interface. This replaces its body duty and
caller-related fields with the independently proved concrete components.
The original admission/runtime/origin duties remain conditional inputs; this
theorem does not manufacture an inhabitant of the frozen P8a interface. -/
theorem creation_from_inputs
    {S : Solidity.Lowering.P8.P8a.Spec}
    {reference : Solidity.Lowering.P8.P8a.OperationalReference}
    {origins : Solidity.Lowering.P8.P8a.SourceOrigins S}
    {roots : Solidity.Lowering.P8.P8a.RootModel S}
    {resolved : S.Resolved} {wf : S.WellFormed resolved} {profile : S.InProfile resolved}
    {artifact : Roadmap.Artifact} {src : Source.SrcProg E}
    (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (n : Int) (h : range n)
    (inputs : CreationPremises.Inputs S reference origins roots resolved wf profile artifact src
      (Source.construct (global pipeline) frame 16 "Cell" (locals n h))
      (initial bytes) (reached bytes n h) targetInitial () Controls.self (targetBody n h)
      targetContext (MachineRelNat bytes)) :
    ∃ out : Out Cell entered.H [], (targetBody n h).run entered = .ok out ∧
      MachineRelNat bytes (reached bytes n h) out.st ∧
      targetRun n h = (do
        let next ← targetInitial.finish (k:=()) Controls.self out.st
        pure (next,(⟨Controls.self⟩ : ContractWorld.Handle ()))) := by
  let supplied : CreationPremises.Inputs S reference origins roots resolved wf profile artifact src
      (Source.construct (global pipeline) frame 16 "Cell" (locals n h))
      (initial bytes) (reached bytes n h) targetInitial () Controls.self (targetBody n h)
      targetContext (MachineRelNat bytes) :=
    {inputs with
      caller:=entered
      related:=initial_related bytes
      ssNew_body:=concrete_ssNew_body pipeline bytes n h (reached bytes n h)
      entered:=entry_actual}
  exact CreationPremises.creation supplied
end Solidity.Lowering.V08.HelperPackets.ConstructorTransport
