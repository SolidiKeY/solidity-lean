| `Backend/InternalFlow/RuntimeFrameP1LangV2.lean` | Canonical P1 `Lang Event Outcome` pair, version 2, over the V2 machine: revert data, call events from the journal, frame classes. |
| `Backend/InternalFlow/RuntimeFrameP1BridgeV2.lean` | `p1_frame_bridge` (V2) for the guarded revert-with-data family: actual source/target runs, full `PassCorrect`, per-input `Local`. |
| `Backend/InternalFlow/RuntimeFrameP1BridgeV2Controls.lean` | Admitted witnesses of both classes, observed payload, refused mismatch, other-payload disagreement, call events, satisfiability. |
| `Backend/InternalFlow/RuntimeFrameP1LangV2Migration.lean` | V2 → V12 `P1Lang` migration: `coarse` (forget events/data), `source_coarse`, `target_coarse`, `lift_coarse`, input conversions. |
