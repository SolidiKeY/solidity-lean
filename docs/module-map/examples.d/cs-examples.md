| Module | Its examples |
|---|---|
| `Examples/Summaries/Vault.lean` | Both callers and the bounded diamond result consume the cached typed math certificate. Actual unrelated/callee source edits test cache hit/miss. |
| `Examples/Summaries/Token.lean` | Both transfer callers consume the cached storage-writing certificate, retaining the allowance frame and bounded diamond result. Actual unrelated/callee source edits test cache hit/miss. |
| `Examples/Summaries/Library.lean` | Both recursion-free library-style callers consume the same cached increment certificate twice. Actual unrelated/callee source edits test cache hit/miss. |
| `Examples/Summaries/Pricing.lean` | Both quote callers and the bounded diamond result consume one cached typed certificate. Actual unrelated/callee source edits test cache hit/miss. |
| `Examples/Summaries/CallChain.lean` | The original three-edge value chain and repeated intermediate call consume the cached leaf certificate; intermediate wrappers are expanded. Actual unrelated/callee source edits test cache hit/miss. |
| `Examples/Summaries/StorageChain.lean` | Three call edges with seed, middle and outer each certified once; callers reuse the cached outer certificate once/twice, and leaf edits invalidate its transitive dependency key. Actual unrelated/callee source edits test cache hit/miss. |
| `Examples/Summaries/Support.lean` | Example-only typed certification, semantic wrapper expansion, bounded certificate-use-count checks, cache evidence retrieval and actual source-edit controls. Fixture serialization and edited-contract transport are not asserted. |
