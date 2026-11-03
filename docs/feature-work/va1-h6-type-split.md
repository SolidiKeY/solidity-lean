# H6 type-control split relay

Human H6: “VA1 splits it”. This performance-only checkpoint cherry-picks
fb58217bc5b421997eb689c7e47b4802c5294333 onto published master
ed7c42a7e7964315dc14d0ca76557067b5a24a35. The obsolete deleted VA1 handoff stays
deleted. No dependency on 60dd172d (UnitExamples is outside the import closure).

All29 public declaration headers, observations, original data and budgets are
retained. Four aggregate proofs compose certified per-corpus facts. The original
TypeExamples, TypeCorpusExamples and TypePrintExamples import entrypoints remain.
All20 split files and their32-module source import closure are byte-identical to
the original VA1 checked tree. No source implementation is newly substituted.

Fresh file elaboration with existing exact-source dependency outputs, one file
at a time via gate.sh per-file, Lean4.24.0/Lake5.0.0-src+797c613, -j1 and
LEAN_NUM_THREADS=1: baseline 97.913s, split maximum 19.599s and split total
88.742s. This is not a fresh full-tree cold build. Each file remains under300s.
Docker memory.max=12884901888, memory.swap.max=0; H1 reserve4294967296bytes.
Maximum sampled aggregate RSS 5034200KiB; minimum sampled host available 11622682624bytes.
No LSP overlapped builds. Existing two axiom guards pass.

Independent read-only finder and skeptic found no source issue. The finder
identified the stale cherry-picked handoff link; this document replaces it.
Full AU01/AU02, Residue/DecisionTheorem-prime, exhaustive hash bridge, remaining
pipeline children and full validation remain open. This relay passes only its
focused performance checks; MRS/MIC must replay their own concrete full gates.

Raw evidence: /workspace/va1-evidence/h6-relay-20261103. The coordinator integrates
the sealed package; no push, merge or tag publication is authorized here.
