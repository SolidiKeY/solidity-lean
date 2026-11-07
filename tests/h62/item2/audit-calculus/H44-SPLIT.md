# H44 reviewable split

The generated 361-path scope inventory and six-case semantic classification dataset are preserved outside Git. The committed BULK-INPUTS.md gives their absolute VM paths, sizes and SHA256 hashes. Source data is unchanged: scope75913 bytes SHA256 c6d26b9f50936dec304b19e226e069be8f9f9f6e4229ac016cb73b156caf6c92; roles9206 bytes SHA256 bcb4f5c718e686dcce1a518a2583448b95ba05751902147d66f3b5463e491fc7.

Both tools consume exact verified external bytes and fail if inputs are missing or tampered. There is no fallback to an omitted payload. The frozen scope SHA pin, full census digest, classification fidelity rules and --require-complete behavior remain unchanged. Scripts, small controls, Lean modules, documentation and pointer manifests remain reviewable in the live branch delta. Historical metadata commits remain preserved; this is not history removal.

Validation:65 Python controls pass. Census recovery remains byte-identical at a2aa6d5e5837eac11ad80fc4eb59e4c3903e9d7f9d52e41bcbccb1e24dccc2da. Classification completeness still FAILS exit1 with6 reviewed,5277 pending and all5283 semantic owners unresolved. No Lean file changed or Lean gate ran for this data relocation. Prior RuleShapes reserve-stop exit88 and all timing/trust holds remain. No theorem, exclusion, axiom set, proof budget or gate was changed.

Independent read-only finder and skeptic passed the externalization; neither used Lean/server or writes. Both verified the preserved bytes and fail-closed loading; skeptic explicitly limited the result to the live-tree split. Existing proof acceptance-tool findings remain open. Exact gate records: /workspace/h62-successor-evidence/h44-split-v1/gates.json. The full assignment and all unfinished proof/semantic/final-gate obligations continue.
