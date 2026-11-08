# TF-mcp: checkout isolation and disconnect regression fixtures

H151: the missing corrected runtime-fixtures final delivery at
`f8975f25b12a5e9723b00ec794b261708280092c` and unavailable original captures are
**UNVERIFIABLE**. This is a fresh reconstruction from the authenticated original
assignment, not recovery or integration of that historical head.

The frozen acceptance is byte-identical to the original contract (SHA256
`6bd1dcafc20e6007997b9bd4f149d87b521ab20a5261e16d53e5a0d8e1dffa2d`). The real
production `scripts/coord-tools/lean-mcp` is copied unchanged, checked against its
frozen SHA256, and run through actual subprocesses and Unix sockets in disposable
Git checkouts. A recording JSON-RPC server substitutes only for the heavy Lean
server. No Lean, external network, containers, host daemon, host cache or real proof runs.
The environment and socket directory are private; cleanup stops only fixture
processes and deletes only its temporary directory. Reported PIDs are bound to
recorded RPC server identities, exact private command lines and process start
identities. Stop, idle exit, server death and cleanup require bounded termination;
a failed-stop negative control cannot silently pass. Failure cleanup signals
only those recorded fixture identities, never an unrelated host process.

Every frozen case has exactly one unittest:

- `usage`: absent/unknown commands reject without starting a server.
- `start_status_stop`: real lifecycle, exact tools/output, socket mode and inventory.
- `same_checkout_single_daemon`: concurrent starts share one server and socket.
- `different_checkouts_isolated`: distinct checkout identities use distinct daemons;
  stopping one preserves the other.
- `closed_probe_survives`: a connect-and-close probe leaves the daemon alive.
- `abandoned_client_survives`: client closes during a held call before its reply;
  the same daemon survives after release.
- `busy_status`: a genuinely held server call yields the real bounded busy status;
  release restores normal status with the same daemon identity.
- `tool_error`: MCP tool errors, wrapper diagnostic errors and JSON-RPC errors
  remain failures, and the daemon survives them.
- `diagnostic_error`: errors print exact locations and fail; warning-only/empty
  error lists do not manufacture errors.
- `server_death`: real fake-server termination fails the call and removes its socket;
  the next start creates a distinct server and recovers tools access.
- `idle_shutdown`: the real idle timer removes the socket and status reports stopped.
- `tactic_success`: mixed snippet results preserve every row and all RPC arguments.
- `tactic_failure`: remaining goals, diagnostic errors, snippet timeout, partial
  responses and global timeout never become a successful attempt.
- `invalid_json`: malformed CLI JSON rejects without a tool call; malformed socket
  JSON returns an error while preserving the daemon.

Common assertions enumerate every recorded JSON-RPC message, its complete params,
sequence ID, startup notification and checkout identity. The server and command
outputs are records, not proof results: mock PASS establishes wrapper classification
only. The named cases do not establish real Lean-server compatibility, differential
correctness, production runtime qualification or arbitrary external-server behavior.
The optional acceptance commit argument checks the exact three-file item commit;
coordinator acceptance remains separate.

Run `python3 -B tests/terra-20261103/mcp/accept.py` at readiness. Optional
`TF_MCP_EVIDENCE` writes per-case command/RPC records outside the checkout for private
review. Raw logs, resource measurements, manifests and handoffs belong only in the
H145 private archive. No production tool, statement, budget or axiom is changed.

Fresh frozen acceptance passed all 14 named cases. Independent read-only finder
and skeptic identified a lifecycle cleanup gap; the fixture now binds and checks
owned daemon/server identities through shutdown, records cleanup outcomes and
rejects a failed stop. A missing warning-only diagnostic probe was also added.
The strengthened acceptance passed with no cleanup failures or surviving owned
processes in any case. Both reviewers confirmed no remaining static blocker,
without rerunning tests or using Lean. Coordinator rerun and item-commit acceptance
remain separate; the inherited assignment is not declared complete.
