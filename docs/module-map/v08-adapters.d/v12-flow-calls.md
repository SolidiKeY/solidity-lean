
### P1 paired allocating scalar transport

| Module | Purpose |
|---|---|
| `Backend/InternalFlow/RuntimeFrameV3ScalarDescentInterfaceV1.lean` | Frozen typed public-guard and allocating three-cell prefix obligations, parameterized by an existing compiler certificate. |
| `Backend/InternalFlow/RuntimeFrameV3ScalarAllocatingDescent.lean` | Actual scalar allocating descent horizons with reached representation, exact ownership growth and derived three-cell parent history. |
| `Backend/InternalFlow/RuntimeFrameV3ScalarDescentControls.lean` | Populated zero/one/two descent horizons, old-array observations, capture-order negatives and the actual terminal guard. |
| `Backend/InternalFlow/RuntimeFrameV3ScalarPairedExecution.lean` | Actual allocating descent history feeds the same-state scalar return loop. |
| `Backend/InternalFlow/RuntimeFrameV3ScalarPairedTransport.lean` | All-count descent and return execution against the frozen producer, with derived history and allocator transport. |
| `Backend/InternalFlow/RuntimeFrameV3ScalarPairedTransportControls.lean` | Populated actual producer, scalar result and restored pointer controls for paired transport. |
| `Backend/InternalFlow/RuntimeFrameV3NativeScalarAgreement.lean` | All-count actual native recursive source and paired target scalar observation agreement, with heap identity separate. |
| `Backend/InternalFlow/RuntimeFrameV3NativeScalarAgreementControls.lean` | Populated source/target scalar result and distinct native exhaustion versus target success controls. |
| `Backend/InternalFlow/RuntimeFrameV3NativeAllocationCoherence.lean` | Complete native allocating-recursive output coherence across all sufficient quotation indices; target heap identity remains separate. |
| `Backend/InternalFlow/RuntimeFrameV3NativeAllocationCoherenceControls.lean` | Exact populated two-allocation output at two sufficient indices and genuine insufficient-index exhaustion. |
| `Backend/InternalFlow/RuntimeFrameV3FreshAllocationContents.lean` | Exact fresh private array source contents and physical words after arbitrary allocating descent tails. |
| `Backend/InternalFlow/RuntimeFrameV3FreshAllocationContentsControls.lean` | Populated one/two-turn fresh object observations and header/payload ordering negatives. |
