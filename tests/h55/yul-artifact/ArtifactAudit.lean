import Solidity.Yul.Compilation.Artifact
/-! Explicit axiom reports for the additive shared completion header and artifact.
These reports do not certify the remaining producer migrations. -/
#print axioms Solidity.Yul.Compilation.CompletionControls.sourceLocals_injective
#print axioms Solidity.Yul.Compilation.CompletionControls.frame_locals_injective
#print axioms Solidity.Yul.Compilation.CompletionControls.frame_height
#print axioms Solidity.Yul.Compilation.CompletionControls.completion_iff
#print axioms Solidity.Yul.Compilation.Artifact.normal_to_model
#print axioms Solidity.Yul.Compilation.Artifact.completion_iff
#print axioms Solidity.Yul.Compilation.Artifact.source_roundtrip
#print axioms Solidity.Yul.Compilation.Artifact.image_roundtrip
