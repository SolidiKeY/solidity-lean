# H44 evidence split and verification

The committed evidence-manifest.json is a compact index containing absolute
retrieval paths, byte sizes and SHA256 hashes for the external full manifest
and bulk archive. Generated census records, expanded pins, fixtures and logs
remain outside Git. Lean modules, scripts and documentation remain reviewable.

Download the bulk archive named in CLOUDVM-RESULT and run from this checkout:

```sh
python3 scripts/h62/item2/audit-evm-compiler/verify_evidence.py --archive /path/to/bulk-evidence.tar.gz
```

The verifier authenticates the archive and its embedded full manifest against
the committed index, then performs the unchanged 181-source and 113-artifact
checks. No tar extraction or original VM path is needed for this mode.
For unpacked evidence use `--artifact-root /path/to/continuation-2`; that directory
must contain the authenticated full evidence-manifest.json from the archive.

Source-only mode still checks zero artifacts. Because the expanded source pins
are now off Git under H44, download the full manifest first:

```sh
python3 scripts/h62/item2/audit-evm-compiler/verify_evidence.py --sources-only --full-manifest /path/to/full-evidence-manifest.json
```

That file is authenticated against the committed index. On the original VM,
source-only mode can use the indexed full-manifest path by default. Hash checks
do not re-run Lean or prove provenance. The legacy full-manifest verification
rules and proof gates are unchanged; the compact index adds transport integrity.

The preserved data records 555 checked candidates, 235 direct closed equalities,
320 unpromoted candidates and 300 total classified statements. Original proofs
are retained without replacement True lemmas. Closed-input accounting proves
no semantic nonvacuity, supported-source totality or execution-gas theorem.
The 1,530 remaining statements and 1,793 producer owners remain unfinished.

closed_census.py and reconcile.py reproduce the data from the manifested seed,
kernel capture and ownership snapshot with serial configurations. Compile the
unregistered audit helper imports first with explicit -j1 and --tstack=131072.
manifest_evidence.py writes the expanded manifest and archive only outside the
repository and writes just the compact index inside it. Use --evidence for the
existing external receipts, --output for the external full manifest, and
--archive for the external archive. Proofs, gate commands and budgets do not
change in this packaging split. Archive ordering and gzip/tar metadata are
normalized, so identical source/evidence bytes produce identical archives.
