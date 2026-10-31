# V14 independent consumer controls

The owned modules under `Solidity/Backend/Executable/` contain the kernel proofs
and controls. See the [owned lane document](../../docs/feature-work/roadmap-v14-executable.md)
for their exact premises and the open G43/G36.03/G44/G45 obligations.

Run the two focused targets serially, under the assigned 12 GiB/no-swap scope,
with `LEAN_NUM_THREADS=1` and explicit Lean `-j1` in the session configuration.
The session alternate lakefile copies the tracked configuration and adds `-j1`
to existing `weakLeanArgs`; its exact saved copy is in the VM evidence directory:

```sh
lake -f v14-runtime.lakefile.toml build Solidity.Backend.Executable.AssemblyChecks
lake -f v14-runtime.lakefile.toml build Solidity.Backend.Executable.PaymentCheckpointChecks
node scripts/check-v14-executable.mjs
```

The new structural guard checks ownership, append-only registration and import
boundaries. It is not a proof or an external compiler/EVM test. Creation byte
execution returns runtime bytes; the world fixtures independently execute the
existing unmetered API. No theorem here connects those two models or closes
compiled payment, source constructor, runtime-jump or pinned-decoder agreement.


Recovery scalar checks additionally build
`Solidity.Backend.Executable.ScalarSequenceChecks` using the same bounded
session configuration. `node --test tests/v14-executable/guard.test.mjs` exercises
the actual guard helpers, including a real isolated Git rename/untracked census;
zero modules and skipped scans are failures, not passing controls. The source
scanner conservatively refuses unsupported owned interpolation/quoted-identifier
forms; it is independent of the Solidity admission profile.
