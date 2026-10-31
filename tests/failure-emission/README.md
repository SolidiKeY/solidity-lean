# G38 component checks

Kernel proofs and inhabited controls live in `Solidity/Backend/Failure`.
`check-imports.mjs` checks the exact owned-module closure without editing the
shared checker. `Export.lean` exports actual Backend.encode bytes; vectors.json
is that exact export, including nonzero offset/before-after markers, boundary
payloads, ignored suffix and1022/1023 operand-stack cases.

Optional external replay uses the existing pinned dependency lock from
scripts/evm-reference. Copy its package.json and package-lock.json to a private
external directory and run npm ci --ignore-scripts there. Copy replay.mjs to
that directory so Node resolves those exact dependencies, then run it with the
absolute vectors.json path. Keep core free of npm dependencies. The worker used
an offline12 GiB/no-swap container,100,000,000 gas,5,000,000 host instructions and
120-second process timeout; none is an increased test budget. A host timeout is
inconclusive, never a matching EVM failure.

The runner independently states expected finite ABI payloads and status by
name. It compares the exported original payload and external output, checks
RETURN/REVERT/stack-overflow separately, every after marker and the before marker where the offset is nonzero, every
retained stack value and maximum intermediate height. Finite vectors are
emission agreement, not generic ABI coverage or a kernel bridge theorem.

osaka-report.json records exact results and dependency/input/runner hashes.
provenance.json pins source files, actual toolchain and source parent. The owning
document is docs/feature-work/backend-failure-emission.md. The original worker
VM evidence and resource runner are saved at
/workspace/scratch/failure-emission-evidence. Full parent source/world/call
composition remains open with its owners.
