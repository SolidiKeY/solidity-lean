# H6: `TypeExamples` split

Decision H6: a performance-only split of
`Solidity/Frontend/Checked/TypeExamples.lean` (the G09 type and declaration
controls), with every statement, observation and budget kept. The split was
made by VA1 (its VM commit `fb58217b`) and integrated onto master `ed7c42a7`.

## What changed

`TypeExamples.lean` is now an entry point that imports the split modules and
keeps the two axiom guards. The ten helpers and the corpus data moved to
`TypeExampleCore.lean`; the nineteen theorems moved, text unchanged, to
`TypeNameExamples`, `TypeDeclarationExamples`, `TypeCorpusAcceptance`,
`TypeCorpusCoverage`, `TypeCorpusProfile`, `TypePrintText`,
`TypePrintRoundtrip` and `TypePrintChecksum` (`TypeCorpusExamples` and
`TypePrintExamples` only re-export). All stay in namespace
`Solidity.Frontend.Checked` under `open Solidity.Source`.

Four proofs changed, not their statements: `declCorpus_accepted`,
`declCtors_covered`, `declCorpus_in_profile` and `print_roundtrip` now
compose eleven new per-member declarations in
`Solidity.Frontend.Checked.TypeCorpusCertificates` (`TypeCorpusFirst`,
`TypeCorpusSecond`, `TypeCorpusMembers`, `TypeCorpusObservations`,
`TypeCorpusProfileFirst/Second`, `TypeCorpusRoundtripFirst/Second`): the
constructor list, profile and round trip of each of the two corpus members,
each by `decide +kernel` against the parser, and `declCorpus` as the list of
its two members (`rfl`). `profileObservation` and `roundtripObservation` are
the original predicates, named so the parser is not reduced at elaboration.
No new axiom, `sorry`, `native_decide` or heartbeat option.

## Timings

Measured on the coordinator host (Lean 4.24.0), each by
`LEAN_NUM_THREADS=1 ./run-lean.sh` (one Lake job at a time, one thread per
file), with no other build running; the times are Lake's per-module times.

| | `TypeExamples` | split modules | `ExprExamples` |
|---|---|---|---|
| before (master `ed7c42a7`) | 37 s | — | 13 s |
| after | 0.16 s (entry point) | 34.9 s in total, slowest `TypePrintChecksum` 6.9 s, `TypeCorpusRoundtripSecond` 6.5 s | 13 s |

The total work is about the same; what changes is that no single module
takes more than 7 s, and the twenty modules check in parallel. VA1's own
measurement in its VM (12 GiB container) was 97.9 s before, 88.7 s in total
and 19.6 s at most after.

## Reviews

A read-only finder and skeptic (no Lean server) found no source defect. They
found documentation defects, fixed on integration: the module-map rows
called re-export and certificate modules "controls", the H6 note sat under
the wrong `docs/automation.md` section, and this record cited VM paths and
had run-together numbers. `docs/feature-work/frontend-parse.md` no longer
lists `TypeExamples.lean` as an open checking cost.
