# Coordinator registration proposal (not applied)

Isolated audit test library `H62AbiWorld`, source directory
`tests/h62/item2/audit-abi-world`, is declared in serial.lakefile.toml only.

| Module | Purpose |
|---|---|
| H62AbiWorld.WitnessSchema | Elaborated simultaneous-binder schema; positive/contradictory controls. Audit tooling imports Lean; never import into intrinsic core. |
| H62AbiWorld.CodecWitnesses | 19 exact-type packages for unchanged ErrorLayout/ErrorRoundtrip declarations. |
| H62AbiWorld.WindowWitnesses | 27 exact-type packages for unchanged error/Panic windows and result/return-word transport. |

No production root, core layer, central module map or axiom pin edit is requested
by this checkpoint. Keep these as audit-only targets unless the area producer
and coordinator approve an explicit registration change.
