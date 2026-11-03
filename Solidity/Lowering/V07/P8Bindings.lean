import Solidity.Lowering.P8.FrozenInterface
import Solidity.Lowering.V07.DeclarationGraph
import Solidity.Lowering.V07.WrappedAssignmentPair

/-! Consumers of the EXACT relayed P8a interface. No parallel SourceSpec,
admission/failure premise structure or producer inhabitant is introduced.
These conditional laws do not supply Source reference adequacy or a graph
producer; the graph evidence remains an actual DeclarationGraph argument. Everything indexed by `P8a.Producer` is vacuous until P8-SPEC-LAW1 is
resolved: the frozen V1 `Producer` is uninhabited over the current `Nat`
resource (`Lowering/P8/ResourceContractLaw1.lean`).
`scalar_value` and `source_assignment_run` do not use the producer argument. -/
namespace Solidity.Lowering.V07.P8Bindings
open Solidity.Lowering.P8

variable {S : P8a.Spec} {reference : P8a.OperationalReference}
  {origins : P8a.SourceOrigins S} {roots : P8a.RootModel S}

/-- Admission evidence is extracted from the supplied producer, not a second
local frontend assumption. -/
theorem accepted (producer : P8a.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r) :
    S.Admitted i r := producer.admission.sound i r h

theorem accepted_profile (producer : P8a.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r) :
    S.WellFormed r ∧ S.InProfile r := by
  obtain ⟨parsed,parse,resolve,well,profile⟩ := accepted producer i r h
  exact ⟨well,profile⟩

def acceptedSource (producer : P8a.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
    (art : Roadmap.Artifact) : P8a.SourceProgram :=
  origins.meaning r (accepted_profile producer i r h).1 (accepted_profile producer i r h).2 art

theorem checked_certificate (producer : P8a.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r) :
    ∃ c, producer.checkedFrontend.produce i = some (r,c) ∧
      producer.checkedFrontend.check i r c = true := by
  obtain ⟨c,produced⟩ := producer.checkedFrontend.complete i r (accepted producer i r h)
  exact ⟨c,produced,producer.checkedFrontend.accepted i r c produced⟩

theorem checked_frontend_agrees (producer : P8a.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (c : producer.checkedFrontend.Cert)
    (h : producer.checkedFrontend.produce i = some (r,c)) :
    producer.admission.frontend i = some r := by
  rw [producer.frontend_agrees i,h]
  rfl

/-- The exact source-origin program, not the emitted intrinsic program. -/
theorem program_origin (producer : P8a.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
    (art : Roadmap.Artifact) :
    producer.realization.program (S.meaning r (accepted_profile producer i r h).1
      (accepted_profile producer i r h).2 art) = acceptedSource producer i r h art :=
  producer.realization.meaning_origin r _ _ art

/-- Reference execution remains relative to the EXTERNAL reference parameter.
This is not a proof that it is adequate for Source.evalE/evalS/session execution. -/
theorem execution (producer : P8a.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
    (art : Roadmap.Artifact) (env : S.lang.Env) (resource : S.lang.Res)
    (out : Roadmap.Prefix Roadmap.Event Roadmap.Outcome) :
    reference.Executes (acceptedSource producer i r h art) (S.session env)
      (producer.realization.resource resource) out ↔
      S.lang.sem (S.meaning r (accepted_profile producer i r h).1
        (accepted_profile producer i r h).2 art) env resource = out := by
  rw [← program_origin producer i r h art]
  exact producer.realization.exact _ env resource out

theorem failure_points (producer : P8a.Producer S reference origins roots) (r : S.lang.Res) :
    reference.points (producer.realization.resource r) = producer.failures.points (S.failures r) :=
  producer.realization.resource_points r

theorem no_failure_requests (producer : P8a.Producer S reference origins roots)
    (r : S.lang.Res) (h : S.NoFail (S.failures r)) (i : Nat) :
    ∃ balance, (reference.points (producer.realization.resource r)).tx i = .runs balance none := by
  rw [failure_points producer r]
  exact producer.failures.noFail_requests _ h i

theorem no_failure_frames (producer : P8a.Producer S reference origins roots)
    (r : S.lang.Res) (h : S.NoFail (S.failures r)) (k : Nat) :
    (reference.points (producer.realization.resource r)).frame k = none := by
  rw [failure_points producer r]
  exact producer.failures.noFail_frames _ h k

/-- G18.01 is now indexed by the actual P8 source origin. This is the existing
certificate predicate, not a supplied graph producer or a new admission guard. -/
abbrev AcceptedGraph (producer : P8a.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
    (art : Roadmap.Artifact) (loc : Source.DataLoc) {n : Nat} (G : TypeGraph.Schema n) :=
  DeclarationGraph (acceptedSource producer i r h art).1 loc G

/-- Transport an ACTUAL graph certificate along frozen meaning_origin.
The missing total producer is not concealed: c is required, not constructed. -/
def graphForRealization (producer : P8a.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
    (art : Roadmap.Artifact) (loc : Source.DataLoc) {n : Nat} (G : TypeGraph.Schema n)
    (c : AcceptedGraph producer i r h art loc G) :
    DeclarationGraph (producer.realization.program (S.meaning r
      (accepted_profile producer i r h).1 (accepted_profile producer i r h).2 art)).1 loc G := by
  rw [program_origin producer i r h art]
  exact c

theorem graph_exists_for_realization (producer : P8a.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
    (art : Roadmap.Artifact) (loc : Source.DataLoc) {n : Nat} (G : TypeGraph.Schema n)
    (c : AcceptedGraph producer i r h art loc G) :
    Nonempty (DeclarationGraph (producer.realization.program (S.meaning r
      (accepted_profile producer i r h).1 (accepted_profile producer i r h).2 art)).1 loc G) :=
  ⟨graphForRealization producer i r h art loc G c⟩

/-- G16's existing value relation at the EXACT accepted source-origin layout.
This binds the environment only; it does not claim expression/body extraction. -/
theorem scalar_value (producer : P8a.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (acceptedInput : producer.admission.frontend i = some r)
    (art : Roadmap.Artifact) (t : Source.IntTy) (n : Int)
    (h : t.lo ≤ n ∧ n ≤ t.hi) :
    IntValueRel t (.int n h : Source.Val (acceptedSource producer i r acceptedInput art).1.layout (.int t))
      (integerValue t n h) := integer_related t n h

/-- Actual G17 assignment clause in the accepted source-origin environment.
G, frame and expression membership/settings alignment are NOT supplied by P8a. -/
theorem source_assignment_run (producer : P8a.Producer S reference origins roots)
    (input : S.Input) (r : S.Resolved) (h : producer.admission.frontend input = some r)
    (art : Roadmap.Artifact) {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob (acceptedSource producer input r h art).1) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState (acceptedSource producer input r h art).1 Γ)
    (i a : Source.Idx Γ τ)
    (v : Source.Val (acceptedSource producer input r h art).1.layout τ)
    (read : source.1.get a = v) :
    (Source.evalE G F (fuel+2) (.assign (.local i) (.local a))).run source =
      (.ok (.val v),(source.1.set i v,source.2)) :=
  source_assign_local_run G F fuel source i a v read

end Solidity.Lowering.V07.P8Bindings
