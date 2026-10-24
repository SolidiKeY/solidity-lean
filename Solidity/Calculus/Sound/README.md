# One file per new rule's soundness

A rule added to `Calculus/Rules.lean` proves its arm here, in
`<Arm>.lean`, one file per new `Stmt.step` arm (a taclet of an existing
statement extends that statement's lemma where it is).  The template and how to
register it are in `.claude/rules/soundness.md` ("A new rule: one file in
`Calculus/Sound/`"); the existing arms stay in `Calculus/SoundArms.lean` …
`Calculus/SoundLoops.lean`.
