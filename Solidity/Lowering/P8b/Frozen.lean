import Solidity.Roadmap.Contracts

/-! H12 FROZEN P8b consumer interface, version1.
This module declares types and explicitly undischarged record obligations ONLY.
It constructs no SourceSpec, admission proof, emitter, Lowering or Cert.
Changing these public signatures requires telling the coordinator first.
P8a is owned by copy-recovery; its delivered concrete package must instantiate
SourceInput. A SourceSpec argument is not evidence that P8a has been delivered.
-/
namespace Solidity.Lowering.P8b.Frozen
open Roadmap

/-- EXPLICIT P8a PREMISE. The concrete independent Source specification and
its admitted-profile interpretation must come from the P8a producer. -/
structure SourceInput where
  source : SourceSpec

/-- Exactly G01 admission; no residual fragment/domain restriction is added. -/
abbrev Admission (A : SourceInput) (i : A.source.Input) (r : A.source.Resolved) : Prop :=
  A.source.Admitted i r

/-- REQUIRED PRODUCER OUTPUT, not an implemented or assumed instance.
The inherited G01 obligations are EXACTLY:
* lower: resolved + wellformed + in-profile + artifact -> intrinsic World;
* pass: actual Pass over the two existing languages;
* dom: EVERY supplied wellformed in-profile meaning belongs to pass.Dom;
* agrees: pass.run equals ofWorld of that lower result;
* cert: the FULL G01 Cert, including environment soundness/surjectivity,
  need/need_ok and back, with original observations/admissibility/Forward/Guard.
All fields remain obligations until an actual concrete inhabitant is proved.
This structure creates no new execution semantics or semantic theorem. -/
structure Producer (A : SourceInput) (I : IntrinsicSpec) extends Lowering A.source I

end Solidity.Lowering.P8b.Frozen
