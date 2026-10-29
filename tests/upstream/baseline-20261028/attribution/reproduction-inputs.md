# Historical attribution inputs

The integration changes the feature manifest and cited source files. The original
attribution report remains a record of its original tree, not a current merged
baseline. Its reproduction test uses `reproduction-inputs.tar.gz`, with every
member and the archive itself checked against `reproduction-inputs.json`.

The capsule contains the original manifest, generator, reviewed table, gap index,
unresolved list, cited files and local-evidence files from commit `13edcbe4`.
Each input was checked against the existing attribution report's SHA-256 ledger
before packaging. The two unchanged corpus archives are linked into the temporary
reproduction root and checked by the original generator. Extraction admits only
regular files with the exact recorded member set.

The test compares the generated JSON and Markdown with the retained report
exactly. Its old observations, hashes and claims have not been updated. Current
baseline generation separately requires the merged runner, compiler adapter and
compilation-unit adapter hashes to match a newly produced report.
