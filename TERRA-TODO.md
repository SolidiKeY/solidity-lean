# New routine handoff

Only the new NJ1 item is recorded here; no earlier excluded Terra file or
completed proof is restored. This is pending work, not a Lean declaration.
No placeholder, axiom or budget increase is authorized.

## NJ1 — concrete nested JSON certificate

Proposed module: `SolidityBridge.Yul.StructuredSwitchJsonKernelControls`.
Import the actual `SolidityBridge.Yul.StructuredSwitchJsonControls` module.
Construct these exact declarations (names may be namespace-qualified there):

```lean
def raw_nested_packet : SolidityBridge.Yul.StructuredJson.Packet [] 20 16
    (SolidityBridge.Yul.StructuredSwitchJson.Controls.fixture "1")

theorem raw_nested_compiles :
    SolidityBridge.Yul.StructuredJson.checkCompile [] 20 16
      (SolidityBridge.Yul.StructuredSwitchJson.Controls.fixture "1") =
    .ok raw_nested_packet
```

Why routine: compose actual decoder/span/name/literal equations, the existing
`Solidity.Frontend.YulJson.Words.Checked.complete` API, and the already-proved
nested compiler. Source/target soundness stays with VY3 and is unchanged.
The old `StructuredJsonControls` certificate illustrates the explicit route.
Standard rfl/decide/omega/simp-only/sol_prove/sol_chain attempts on the exact
success Boolean did not reduce; preserve their evidence and use actual
producer equations rather than a stronger premise. Until this task is proved,
the new raw JSON guards are evaluations, not a named kernel parse certificate.
Keep fixture bounds20/16 and expected prefix values21/999/42/17 unchanged.
