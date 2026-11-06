
### SOL-QN final target, C3 and normalization adequacy

| Module | Purpose |
|---|---|
| `Frontend/QualifiedUnits/Linearization.lean` | Independent C3 hierarchy judgment on original declaration identities; `order_iff` (the `idUniverse` bound never refuses a hierarchy), precedence and acyclicity. |
| `Frontend/QualifiedUnits/Target.lean` | The final SOL-QN target relation, including inherited overloads; `target_iff` against the public signature-aware resolver. |
| `Frontend/QualifiedUnits/NormalizationAdequacy.lean` | Structural adequacy of signature normalization against Source elaboration on every supported signature category. |
| `Frontend/QualifiedUnits/TargetControls.lean` | Kernel controls for the independent C3 judgment, the final target relation and normalization adequacy. |
