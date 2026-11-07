import Solidity.Roadmap.Frontend
namespace Solidity.H62.AuditRoadmap.FrontendWitnesses
open Solidity.Roadmap.Frontend

theorem pipeline_joint : ∃ q, (Settings.ofPipeline q).Ok :=
  ⟨.viaIR, Settings.ok_ofPipeline _⟩

end Solidity.H62.AuditRoadmap.FrontendWitnesses
#print axioms Solidity.H62.AuditRoadmap.FrontendWitnesses.pipeline_joint
