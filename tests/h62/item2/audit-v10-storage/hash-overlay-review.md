# H70 partial Hash overlay static review

Routed owner head: 78c110f83dc1a30700acd1b5bd34b19f61da6ccd.
Routed source head: 2a18afcdba00a85645b0b3079704f78ffcd78860.
Neither head was fetched, merged or assumed to have verified ancestry here.
The canonical message-derived patch bytes match supplied SHA256
3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff.
The patch remains off Git. The first worker transcription added one context-space
before the comment text distinct preimages; its failed hash/application receipt is
retained separately and must not be confused with the canonical artifact result.

Static results on the unchanged frozen file:

- Original Git blob: b54c93a5b24340a19160c1fb378d057ccee60f84.
- git apply --check on canonical bytes: exit 0, no application performed.
- Pure in-memory hunk reconstruction: new blob
  092971eda8c7d6997276a92ba19b25b7ce05844e, matching the patch index prefix.
- All 65 scanned theorem/lemma names and exact source signatures compare equal.
- No original file was modified and no Lean/Lake/MCP command ran.

Reproducer: scripts/h62/item2/audit-v10-storage/review_hash_overlay.py.
It requires the advertised checksum, frozen source bytes and exact target path;
it rejects changed source signatures and records the explicit proof boundary.

The hunks change proof bodies: conditional simplifier names, List.contains_cons,
and explicit extraction/unfolding of Near/Covers from decidable hypotheses.
They do not add or remove theorem statement binders in the scanned headers. This
is NOT kernel validation, axiom-set validation, expected-message validation, or a
passing full migration gate. The earlier expected-message failures are not repaired
or discharged by this inspection. Syntax.Raw/full migration remain pending per
the owner's routed message; Hash stays a held dependency. A relay establishes no
owner agreement, permission, or validation beyond what that message explicitly says.

These 65 dependency-header comparisons are not added to the v10-storage census or
manual witness-plan count. No unrelated Hash proof work was undertaken.
