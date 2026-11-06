# H70 Raw prerequisite overlay

Owner: solidity-h62-6-20261106/migrate-syntax. Exact published base:
c6f550e281a7e5affa9a99bc2cdaed556dec00e4. This checkpoint changes
Solidity/Syntax/Raw.lean only in production; it is not completion of H62.

Use the exact-file patch and receipt at
/workspace/migrate-syntax-evidence/continuation-2/raw-prerequisite.patch and
/workspace/migrate-syntax-evidence/continuation-2/raw-overlay.json.
The coordinator retrieves and relays these; no push, merge or publication.

Official pinned Lean4.35.0 archive SHA256:
7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d.
Raw compiles on that build with -j1 -M11000 --tstack=131072.
Both independent read-only reviewers confirm character-count semantics,
empty-drop saturation, explicit suffix predicate and String construction.
All 65 explicitly named original source declaration types compare unchanged
under canonical binder-name/metadata normalization; frozen type SHA256:
3b0c725d47643695bbf11f38aa518d6826ecd6a802c90d7cb33faac08c977e1b.
Evidence: raw-interfaces.json, raw-api-old-command/, raw-api-new-command/.

New-toolchain kernel controls include 20 Raw cases plus two context/row cases
and two universal slice-copy laws; controls-new-command/ passes. The baseline
original directory build passes all29 modules; all22 identical new finite
control predicates also pass as explicit old-runtime assertions. Old String
primitives blocked reduction in exploratory old kernel controls, so no old
formal control certificate is claimed. Twelve separate executable observations
are equal across versions. These runtime observations supplement proofs.

Full compiler-generated API drift (including generated noConfusion and
ToExpr implementation names) is retained in raw-interfaces.json for root-gate
audit. This is not a claim that compiler-generated interfaces are identical.
No frozen statement, premise, constructor, proof budget or axiom pin changed;
no sorry/new axiom/native_decide. The whole-directory migration, full gates,
matched timing acceptance and final root-gate disposition remain pending.
