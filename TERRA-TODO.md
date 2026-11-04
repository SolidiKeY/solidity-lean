# New routine handoff

Only NJ1 is recorded here; no earlier excluded Terra file is restored.
No placeholder, axiom, budget increase or changed fixture is authorized.

## NJ1 — remaining exact raw decoder equality

Actual module: `SolidityBridge.Yul.StructuredSwitchJsonKernelControls`.
Namespace: `SolidityBridge.Yul.StructuredSwitchJson.KernelControls`.
`tree`, `prepared`, `lowered`, `checkedFromParse`, `compiledFromParse`,
`packetFromParse` and `compilesFromParse` are implemented and kernel-checked.
Preparation/lowering is inhabited independently; raw JSON attachment is NOT.

The remaining declaration must prove this exact statement:

```lean
theorem raw_nested_parsed :
    Solidity.Frontend.YulJson.blockAux 20 ast = .ok tree
```

Then construct the original requested declarations using the existing builders:

```lean
def raw_nested_packet : SolidityBridge.Yul.StructuredJson.Packet [] 20 16
    (SolidityBridge.Yul.StructuredSwitchJson.Controls.fixture "1") :=
  packetFromParse raw_nested_parsed

theorem raw_nested_compiles :
    SolidityBridge.Yul.StructuredJson.checkCompile [] 20 16
      (SolidityBridge.Yul.StructuredSwitchJson.Controls.fixture "1") =
    .ok raw_nested_packet := compilesFromParse raw_nested_parsed
```

These are pending statements, not declarations in a Lean module. Do not infer
that the explicit parser premise has been inhabited. The builders already
construct metadata, flags, span (using the real earlier span equation), syntax
precision, typed preparation and concrete target fields without other premises.

Why routine: prove actual span/name/literal/child decoder equations with the
published parser definitions and compose them. The old `StructuredJsonControls`
certificate illustrates the explicit route. Direct reduction and recursive
simplification attempts remain failed evidence; keep all proof/fuel/recursion
budgets unchanged. Source/target soundness remains with VY3. Preserve bounds20/16
and prefix outcomes21/999/42/17. Until this is proved, raw JSON success guards
remain evaluations, not a named unconditional kernel packet certificate.
