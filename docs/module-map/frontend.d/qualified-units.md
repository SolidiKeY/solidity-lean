
### SOL-QN final target, C3 and normalization adequacy
| Module | Purpose |
|---|---|
| `Frontend/QualifiedUnits/Linearization.lean` | Independent C3 hierarchy judgment on original declaration identities; `order_iff` (the `idUniverse` bound never refuses a hierarchy), precedence and acyclicity. |
| `Frontend/QualifiedUnits/Target.lean` | The final SOL-QN target relation, including inherited overloads; `target_iff` against the public signature-aware resolver. |
| `Frontend/QualifiedUnits/NormalizationAdequacy.lean` | Structural adequacy of signature normalization against Source elaboration on every supported signature category. |
| `Frontend/QualifiedUnits/TargetControls.lean` | Kernel controls for the independent C3 judgment, the final target relation and normalization adequacy. |
| `Frontend/QualifiedUnits/ConstructorFixtures.lean` | One typed specimen and literal expected traversal per existing Source constructor (all 112). |
| `Frontend/QualifiedUnits/Layout.lean` | Original owner-body layout: universal frozen source-layout theorem and actual owner-body member correspondence. |
| `Frontend/QualifiedUnits/MergeSpecification.lean` | Independent deterministic C3 merge judgment on original declaration identities; `merge_iff` against `mergeOwners`. |
| `Frontend/QualifiedUnits/ReferenceCoverage.lean` | Universal preservation of frozen explicit references and all finite identifier/member paths. |
| `Frontend/QualifiedUnits/SignatureResolution.lean` | Signature-aware declaration resolution over original Source identities (the public consumer `resolve`). |
| `Frontend/QualifiedUnits/SignatureResolutionControls.lean` | Kernel observations for the actual signature-aware resolver, paired with each main compiler query. |
