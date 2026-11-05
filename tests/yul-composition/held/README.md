# Held VY5 composition modules

These three modules are byte-identical to their Codex-VM versions at lane head
`5209dc728a5d230d31e1345d383bb87bb67120b3`, moved here from
`Solidity/Yul/Composition/` on 2026-11-05 (move to a Claude VM, H37). They are
not part of any library and are not built.

Each imports a VY4 producer module that exists only in the Codex VM's private
dependency tree (`/workspace/vy5-dependencies-20261101`) and in no pushed ref:

| Module | Missing producer import |
|---|---|
| `FailurePhysical.lean` | `Solidity.Yul.World.FailureFuel` (and `ReturningPhysical`) |
| `IndexedWritePhysical.lean` | `Solidity.Yul.World.IndexedEmitHeap` |
| `ReturningPhysical.lean` | `Solidity.Yul.World.GeneralReturningOutput` |

The test driver `FailureDriver.lean` (moved from `tests/yul-composition/`)
imports `FailurePhysical` and is held with it. The ledgers and validators for
these modules under `tests/yul-composition/` and `scripts/yul-composition/`
still name the pre-move paths; their hashes bind provenance, so they are left
unchanged.

All three also open `PhysicalCompletion`. They need the missing producers
`Solidity.Yul.World.PhysicalCompletion` and `Solidity.Yul.World.ScalarEmitPort`, which
are in no ref either.

They return to `Solidity/Yul/Composition/` once VY4 publishes those producers
on master; until then their kernel facts are not part of the checked tree.
