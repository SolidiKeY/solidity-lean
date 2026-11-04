import Solidity.Lowering.V08.HelperPackets.ConstructorTransport.Target

/-! The concrete SS-NEW body duty derived from actual execution.
SlotRel is independent of constructor arguments and post-state definitions. -/
namespace Solidity.Lowering.V08.HelperPackets.ConstructorTransport
open Solidity
open Solidity.Lowering.V07

def SlotRel (d : Source.Decl) (r : SRef Cell (.prim .uint))
    (s : Source.St E) (t : State Cell [])
    (hd : E.lay frame.this d.path = uint := by rfl) : Prop :=
  ∃ (v : Int) (hv : range v),
    (s.ex.world.accounts frame.this).storage.read d.path = some (hd.symm ▸ (Source.Val.int v hv : Source.Val E.layout uint)) ∧
    t.storage.find r = some (.prim (integerValue Source.IntTy.u256 v hv))

structure MachineRel (bytes : Roadmap.Bytes) (s : Source.St E) (t : State Cell []) : Prop where
  saved : SlotRel savedDecl (SRef.ofRoot "saved" rfl) s t
  captured : SlotRel capturedDecl (SRef.ofRoot "captured" rfl) s t
  sourceHeap : s.heap = (initial bytes).heap
  sourceEvents : s.events = (initial bytes).events
  sourceLogs : s.logs = (initial bytes).logs
  sourceLocals : s.fnLocals = (initial bytes).fnLocals
  targetHeap : t.H = entered.H
  heap : HEq t.heap entered.heap
  balance : (s.ex.world.accounts frame.this).balance.val = t.selfBalance.1.toNat
  net : t.net = entered.net
  tx : t.tx = entered.tx

theorem initial_related (bytes : Roadmap.Bytes) : MachineRel bytes (initial bytes) entered := by
  refine ⟨?_,?_,rfl,rfl,rfl,rfl,rfl,HEq.rfl,rfl,rfl,rfl⟩
  · exact ⟨0,by decide +kernel,rfl,rfl⟩
  · exact ⟨0,by decide +kernel,rfl,rfl⟩

theorem reached_related (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    MachineRel bytes (reached bytes n h) (targetReached n h) := by
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
      (targetBody n h).run entered = .ok out ∧ MachineRel bytes after out.st := by
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
    MachineRel bytes (reached bytes n h) (targetReached n h) ∧
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
      targetContext (MachineRel bytes)) :
    ∃ out : Out Cell entered.H [], (targetBody n h).run entered = .ok out ∧
      MachineRel bytes (reached bytes n h) out.st ∧
      targetRun n h = (do
        let next ← targetInitial.finish (k:=()) Controls.self out.st
        pure (next,(⟨Controls.self⟩ : ContractWorld.Handle ()))) := by
  let supplied : CreationPremises.Inputs S reference origins roots resolved wf profile artifact src
      (Source.construct (global pipeline) frame 16 "Cell" (locals n h))
      (initial bytes) (reached bytes n h) targetInitial () Controls.self (targetBody n h)
      targetContext (MachineRel bytes) :=
    {inputs with
      caller:=entered
      related:=initial_related bytes
      ssNew_body:=concrete_ssNew_body pipeline bytes n h (reached bytes n h)
      entered:=entry_actual}
  exact CreationPremises.creation supplied
end Solidity.Lowering.V08.HelperPackets.ConstructorTransport
