# Boolean local negation initializer agreement

The actual Source `unary .not (local ...)` and model `unop .not` operate on
corresponding arbitrary-prefix boolean locals. The operational Source helper
exposes the real lookup as a premise; `bool_not_init_step` derives it internally
from the actual related states. `bool_not_init_client` derives its own initial
locals, read and successful Source run, with no desired operand/result premise.

The Source proof factors actual local-read, unary evaluation, conversion and
`EM.sub` runs using a forward bind law over unchanged `ExceptT`/`StateM`. It
retains intermediate locals/state exactly; it adds no evaluator or oracle.
The final local is the inverse of the old selected boolean, followed by the
unchanged old locals. Source horizon two is timeout; horizon three supplies
both true-to-false and false-to-true concrete controls. Omitting negation is
incompatible with the actual true-input result.

Scope remains explicit resolved expression/statement pairs and normal primitive
locals, not generic state/error simulation, parsing/elaboration/compiler
selection, native fixtures or original source adequacy. H16 Source and Core
ExtCall are unchanged. Original installed-input/heap/storage/liveness/nu-before-
rho/call/ABI/catch/rollback/modal/native and whole-assignment gates remain open.
Full gates are deferred under H12. All failed proof attempts and the one broad
simp candidate's real 60-second EXIT124 are retained; the successful factoring
does not repeat that candidate or raise any bound.

Final validation: two complete-clean owning MCP responses, four per-file
passes, 61-job importing leaf with cached dependencies, nine public reports
(eight permitted-standard-only, one axiom-free) and five static checks at EXIT0.
Global fragments remain EXIT1 with four exact-master inherited findings, bound
by full commits, checker blob and comparison-time working diff hash. The owned
source map is generated; no unrelated-owner edit or forced drop was used.

Independent read-only finder and skeptic reviewed source, doc and actual raw
MCP/build/audit evidence without Lean/check replay; no confirmed findings. Their
supplement did not independently certify final static receipts or all protected
hashes. The verifier retained 1,298 records, eight configs and 182 archive
members. The scratch runner's EXIT0 denotes orchestration completion only:
all three candidates failed, including EXIT124 at 60.07 seconds. Final proof
uses a distinct successful bind-run factoring. All drafts, errors and real
limits remain retained; no cold/full-lane timing or original completion follows.
