# H44 compact increment

The held dc787dca checkpoint is preserved by the pre-h44-split backup ref and the VM snapshot manifest. This split keeps code, documentation and small validation manifests in Git; raw evidence, logs, full generated registration data and expanded review records remain VM-only.

The committed h44-bulk-manifest.json records absolute archive/index paths, byte sizes and SHA256 digests. Its external files.json enumerates every logical repository path, payload path, size and SHA256. After verifying archive and index digests, extract payload.tar.gz into the repository to materialize the same data paths. Set SOL_NL_BULK_DIR to the downloaded directory if it differs from the recorded VM path. Preserve unexpected local work before extraction.

Gate commands, theorem statements, source pins, fixture expectations and budgets are unchanged. The committed-input check now binds relocated direct data byte-for-byte through HEAD's committed hash manifest. It accepts no uncommitted manifest, code path, traversal or digest mismatch. Generated evidence keeps its existing policy. On the managed VM, or with an explicit SOL_NL_BULK_DIR, missing bulk fails closed. Off the VM with no bulk directory, the H44 binding reports VM-only evidence unavailable and is omitted from tree acceptance; this does not claim VM evidence or full-runtime completion. When bulk is present, direct data must match its committed hashes. All47 Lean proof files remain unchanged.

The 34-row module-map proposal and prior full-runtime/resource obligations remain open. H55-H58 reserved source files are untouched. No new goal, scope, HOLD or runtime-completion claim is introduced. H41 cache packs remain on the VM for coordinator pull; no VM shipping.

The sealed packet records the compact full head, exact parent/base, archive and file-index hashes, passing gate commands, independent reviews and remaining obligations. The older held head and all older seals remain available.
