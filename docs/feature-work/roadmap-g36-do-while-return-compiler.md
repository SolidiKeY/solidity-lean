# G36 actual compiler of mapped do-while assignment and bare return

[The adapter](../../Solidity/Backend/StructuredFlow/DoWhileReturnCompiler.lean)
compiles the actual typed code from the committed G19 do-while component with
`Evm.compileProg`. The Source body assigns a mapped Boolean local, then
bare-returns, skipping its arbitrary trailing condition. The fresh true capture
classifies that return even when the assigned value is false.

`correct` retains nine initial propositions: alignment, Boolean reflection, two
map-slot type equalities, two exact map equations, native `Sim` entry, the exact
fragment check and capacity. The theorem composes the actual Source result and
reached map relation with `Evm.prog_sim`; it proves Source/typed runs, the full
weakened map relation, captured true flag, unchanged globals and `Evm.StmtOut`.
It supplies no P8 inhabitant, desired-run oracle or Source/world adequacy premise.
No Source, compiler, syntax, observation or admission definition changes.

[Inhabited controls](../../Solidity/Backend/StructuredFlow/DoWhileReturnCompilerControls.lean)
close the entry/fragment/capacity premises for both pipelines, checked modes,
arbitrary extra fuel and both body values, with an arbitrary trailing Source
condition. The body genuinely changes its caller destination. The ordered native
snapshot is cells 0,1,2,3,5 followed by the entire stack:
`[flag,flag,!flag,1,99,77]`. The return capture is always true; caller locals,
canary and full stack are observed through actual compiled execution.

Two genuine compiled-code mutations are rejected. Omitting the independent true
capture on a false-valued body produces cell3=0 instead of1. Erroneously executing
the trailing local write after a true-valued return produces cell1=0 instead of1.
Both countercontrols use the actual mutated typed program and `Evm.compileProg`,
then successful native witnesses and represented cell values; neither assumes an
expected failure or compares only names. The Source fixture separately proves
that the skipped condition really writes when evaluated.

The capture is not an emitted EVM RETURN or enclosing function-exit dispatcher.
The result is one immediate-return do-while shape, not general recursive loop,
modifier or constructor lowering, external CALL/RETURNDATA, solc/Ethereum tests,
bytecode/gas adequacy or full-profile Source-to-EVM correspondence. The evaluator
fuel offset is a cost for this shape, not an unrolling limit on admitted Source.

The failed standard automation attempt is retained; explicit composition of the
existing two actual correctness theorems closes the statement. All16 declarations
retain complete structural types, values and dependencies at100000nodes/depth512,
actual standard-axiom lists and mandatory live replay. All16 printed axiom lists
are guarded. Focused checks use the existing serial12GiB/no-swap/300s wrapper,
Lean -j1 and LEAN_NUM_THREADS=1. Source/import/tool/object/settings bindings are
unchanged before/after. Parent execution plus final owned-byte binding is
explicitly separate from a new-HEAD/full gate or clean-cache claim.

Independent read-only finder/skeptic reviews inspect actual source, nine premises,
non-vacuity, mutations, metadata/replay/pins and the final committed seal without
Lean/server/builds. Full results and actual commands/exits/resources are retained
in the external handoff. H1 cleanup removes only mutable byte-identical records
verified against unchanged prior sealed archives; earlier failures remain intact.

G19 and complete G36.01 integration, G54.02 and Backfills A/B remain partial.
G52/G54.01 remain H12-paused. G53 still needs actual same-revision selected473da894
strict/corpus/TestSuite proof evidence; historical048a74de lacks Lean binding.
The ten Derived17 values need their reserved owner's same-statement smaller proof
under100000nodes/512depth. G54.03/G55 await all original proof children and final
clean/cache/joint/import/executable/trust gates. All457 release rows remain open.
SS-NEW/getters await VY5 H16/H19. No goal/pin/profile/budget change or push/merge.
