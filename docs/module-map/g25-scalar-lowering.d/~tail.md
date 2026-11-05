
Memory-loop validation helpers: `scripts/memory-loop-evm.mjs` records actual
four-mode upstream EVM observations and refusal controls;
`scripts/check-memory-loop-timing.py` freshly checks the entire original
`Derived17` group; `scripts/check-memory-loop-timing.mjs` validates cumulative
300-second evidence, with negative controls in its `.test.mjs` companion.
