# Original frozen rendered prompt: missing exact bytes

The launcher identifies the original rendered prompt by SHA-256
`7e682e5d42ceee4b805057cc9966598e66b65cf5d586924cf044f46715d2fc75`.
No exposed tool in this worker retrieves the original thread or its rendered
prompt bytes, and no original-prompt file was found in the VM. This file is
not a byte-for-byte copy and must not be substituted for that prompt. The
successor must obtain and hash-check the complete original rendered prompt
from the coordinator before relying on this reconstruction.

The original work and backfill queue text and owned write paths available in
this session are preserved in `scope-manifest.json`. The coordinator-supplied
decisions, refactor audit, toolchain pin and owner snapshot metadata are also
included or separately checksummed in the evidence archive. The complete
original prompt, including the full launcher instruction and owner-key mapping,
is not reproduced here; the coordinator must provide it.
