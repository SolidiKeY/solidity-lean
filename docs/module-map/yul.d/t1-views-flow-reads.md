| `Yul/Views/GenericFlow/Following.lean` | Intrinsic checked preparation and following over existing typed Plan constructors; shared freshness, readiness and preparation equations. |
| `Yul/Views/GenericFlow/FollowingLaws.lean` | Shared decoder-failure law for checked following; consumers avoid concrete dependent-match splitting. |
| `Yul/Views/GenericFlow/FollowingPlan.lean` | Shared intrinsic Plan adapter for checked following, preserving lazy state and journal and an explicit effective checker. |
| `Yul/Views/GenericFlow/Reads.lean` | Shared typed Plan read/preservation proofs and saved-header read equation; actual bank metadata remains explicit. |
| `Yul/Views/GenericFlow/Batch.lean` | Shared intrinsic Plan preparation runner and batch laws; exact failure-prefix state and finite request recursion are preserved. |
