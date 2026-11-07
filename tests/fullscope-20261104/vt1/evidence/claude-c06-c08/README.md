# VT1 C06–C08 evidence (Claude cloud VM, 2026-11-05/06)

Runtime: Lean 4.24.0 (`lean-toolchain` leanprover/lean4:v4.24.0), 4 cores,
15 GiB RAM, no swap, no prebuilt Lake cache. Lean checks ran through the Lean
MCP server (`lean_diagnostic_messages`, per file); `lake build`/`lake env`/
`lean` are denied in this session's shell. No compiler ran here (see the feature
doc, "Moved lane on a Claude VM"); all solc data are the committed fixtures.

## Per-file diagnostics (0 errors, 0 warnings unless noted)
Solidity/SolcValidation/{IrSyntax,IrParse,IrCensus,IrEval,IrEvalFuel,IrHelpers,
IrHelperSim,IrHelperSource}.lean; tests/fullscope-20261104/vt1/{IrParseChecks,
IrEvalChecks,IrHelperChecks,IrLeanGen}.lean.

## Outputs recorded from the server
IrParseChecks: 47 kernel controls (rfl/decide), and
  IR_PARSE_PASS Census.unoptimized: 4679 tokens, 2 objects, 130 functions, 303 operation uses
  IR_PARSE_PASS Census.optimized: 4552 tokens, 2 objects, 124 functions, 302 operation uses
  IR_PARSE_PASS LinkedMath.unoptimized: 633 tokens, 2 objects, 22 functions, 48 operation uses
  IR_PARSE_PASS LinkedMath.optimized: 605 tokens, 2 objects, 20 functions, 44 operation uses
  IR_PARSE_PASS ObjectData.yul: 33 tokens
  IR_REFUSED ×7 (rename builtin, drop argument, memoryguard variable,
  unbalanced brace, leave at top level, shadow local, undeclared target)
IrEvalChecks: 32 Census lines + 6 LinkedMath lines + 1 missing-label line, all
  IR_EVAL_PASS (constructor bytes 2870/405, storage, arithmetic, overflow and
  division panics, signed division, clz, loadimmutable seed read back from the
  constructor output, push, echo, non-payable, unknown selector, short calldata)
IrHelperChecks:
  IR_HELPER_PASS 576 helper/source agreements on edge words (add, sub, mul, int div)
  IR_HELPER_PROVENANCE_PASS 8 whole functions verbatim from the saved IR

## Axioms (`#print axioms`, appended temporarily)
Parsed.sound, helpers_certified: [propext]
eval_succ, runCode_stable, datasize_exact, datasize_missing, setimmutable_stores: [propext, Quot.sound]
checked_add_matches_source, checked_mul_matches_source: [propext, Classical.choice, Quot.sound]

## Gates
- `VT1_SKIP_LEAN=1 tests/fullscope-20261104/vt1/check-ir.sh`: ARTIFACTS_CHECK_PASS,
  HELPERS_CHECK_PASS, VT1_IR_CHECKS_PASS.
- `./run-lean.sh`: its static stages passed ("857 core modules, 0 reach the
  elaborator", "… 0 reach the checked parser adapters", `register.sh --check`,
  `fragments.sh --check`); the cold `lake build` reached 143/3808 modules in
  about 10 minutes with 2 GiB free and was stopped. Not run to completion.
- `scripts/check-doc-paths.sh`: 1 failure, pre-existing at the base
  (`docs/feature-work/after-roadmap-va1.md`), none from this lane.
