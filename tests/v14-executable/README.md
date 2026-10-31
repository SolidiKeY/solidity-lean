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


Further recovery targets, checked serially with the same runtime configuration,
are `Solidity.Backend.Executable.ScalarArtifactChecks`,
`Solidity.Backend.Executable.WorldPrefixChecks`,
`Solidity.Backend.Executable.LocalFrameChecks`,
`Solidity.Backend.Executable.CreationAttempt`,
`Solidity.Backend.Executable.PatchedPayloadChecks`,
`Solidity.Backend.Executable.SourceJournal` and
`Solidity.Backend.Executable.SourceInitializerChecks`. Source semantics are
permitted read-only through an exact pure dependency allowlist; all raw and
published edges and reserved-write boundaries remain checked. The guard tests
now pass17/17 (with multiple approved-root cases), zero skips. Run filesystem
fixture tests with write access to their temporary directory.

Source-journal installation is an account update, not Source.deploy; the
initializer controls separately execute existing source deploy and preserve
legacy/viaIR order. Standalone base-argument metadata is not Program.Derived
or constructor argument lowering. Published source fixtures use toyFixed;
no Keccak, account-byte or pinned-EVM agreement follows from these controls.

Published creation-frame recovery adds `Solidity.Backend.Executable.CreationFrame`:
actual paid world plus separate typed caller, decoded Error catch allocation,
old aliases, heap-dependent tail, exact outer rollback and handle observation.
The fixed incorporation baseline preserves the frozen assignment identity;
behavioral guard tests cover ancestry/parent rejection and post-baseline edits.
These are intrinsic semantics, with no paid execute/finish or EVM claim.
