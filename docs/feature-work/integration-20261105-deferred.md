# Deferred module checkpoints, 2026-11-05

Follow-on to the published 8495f1deb0a9 packet, from master `b26a5a8fc25b77f86fd62bb57447491da47ae73c`.
These bounded increments retain all statements, premises, refusals and budgets.
Each passed focused/checkpoint gates and separate read-only finder and skeptic reviews.
Full combined gates and final reviews remain publication requirements.

- type-grammar (`b00b91a9de659091f64c0bc4e1809b252365d1d7`): `Solidity/Frontend/TypeGrammarH28/ParserBasics.lean`, `Solidity/Frontend/TypeGrammarH28/ParserChecks.lean`.
- shared-translator (`c3bc7282b8c7c3243c304045ecd665a063a46044`): `Solidity/Frontend/ExecutableAst/Shared/Intrinsic.lean`.
- expression-uniqueness (`debf4c2665af826360e3e840c12bf356a9b966d8`): `Solidity/Frontend/ExpressionUniqueness/Statement.lean`.
- readonly-external (`f54cf65e0ce809c47fcddfbc72c2139fd7a1e04f`): `Solidity/Calculus/StorageOnlyHavoc.lean`.

The expression module freezes the original uniqueness target only; its exhaustive
proof remains outside this increment. Its scope docstring is corrected without
changing the definition. Shared obligation callbacks remain explicit producer
dependencies; reference parameters remain refused. The storage-havoc helper
composes existing typed updates/formulas and does not change ExtCall execution,
restrict callbacks or establish Source/native adequacy. Frozen CallResume and
ExtCall-dependent changes remain excluded, as do H16 Source modules.
