| `Correctness/Lowering/Sim/Session/Forward.lean` | The forward session diagram and the shape of its `ForwardResources` record over the hypothesis of matched frames, which the session semantics do not currently satisfy in every environment. |
| `Correctness/Lowering/Sim/Session/Forward/Frames.lean` | The provisional per-frame hypothesis of the forward session diagram and the session-level match. |
| `Correctness/Lowering/Sim/Session/Forward/Within.lean` | A reachable target session state observes a prefix of the run at every horizon above its issued actions. |
| `Examples/Lowering/Sim/Session/Forward.lean` | Type-level uses of the forward session diagram and its resource record on the session of `spin`, under the unmet hypothesis of matched frames. |
