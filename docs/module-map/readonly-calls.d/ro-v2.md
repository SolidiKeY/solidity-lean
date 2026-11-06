| `Backend/Passes/SourceCallProducer.lean` | G42.02 reached-call/frame producer: `Premises` for every invocation, total reached CALL and frame return, `FetchedPremises` from one RETURNDATA placeholder duty (unconstrained relation) ([G42.02](../feature-work/g42-02-source-call-producer.md)). |
| `Backend/Passes/SourceCallProducerControls.lean` | Producer controls on the payment invocation: produced raw outcome, inhabited step, spoofed identity/raw/target refusals. |
| `Lowering/Readonly/SourceDispatchInterfaceV2.lean` | H69 reachable three-way dispatch selection and total classification, with frozen V1 unchanged. |
| `Lowering/Readonly/SourceDispatchInterfaceV2Controls.lean` | Actual branch witnesses, empty-selection refusals and migrated V2 history controls. |
| `Lowering/Readonly/SourceAllHistoriesV2.lean` | Versioned mutual Source history induction through reachable V2 dispatch. |
