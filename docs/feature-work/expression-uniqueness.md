# SOL-EU: certified expression yield uniqueness

Status: blocked before Lean work by EU-R1 (resource enforcement). This is an
inventory checkpoint, not completion of work queue item 1 or of the assignment.
Base: `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`.
Branch: `codex/solidity-sol2-20261104/expression-uniqueness`.
Repository: `/workspace/solidity-lean`.

## Original theorem target (open)

The intended statement, over the existing intrinsic syntax, is:

```lean
∀ (a b : Solidity.Source.Syn .expr) (ts : List Solidity.Frontend.Checked.Tok),
  a.Derives ts → a.prec = true →
  b.Derives ts → b.prec = true → a = b
```

Equivalently quantify independent layouts `La Lb` and require
`a.toks La = some ts` and `b.toks Lb = some ts`. Layout equality is neither
a premise nor a conclusion. `Syn.toks` consumes the whole layout; a successful
`Syn.yield` with unconsumed choices is insufficient. No second AST is proposed.
No root split or uniqueness assumption may be added to prove this target.

The accepted-tree corollary must combine `parseCat_sound` with this theorem:
if `parseCat expr src = .ok (a, La)`, and a certified `b` derives the tokens
of that same successful lexical result, then `a = b`. Parser determinism alone
does not supply this conclusion. Both results remain open, with no Lean
declaration claiming them. No ambiguity or counterexample has been established.

## Constructor and dependency inventory

`tests/sol-expression-uniqueness/constructors.json` records all 29 expression
constructors in intrinsic declaration order, root levels, boundaries and root
conditions. Root conditions must be conjoined with recursive `Syn.prec` for
all children; they are not standalone certificates. The ten left-associative
binary levels require left level at least p and right level at least p+1.
Exponentiation requires left at least 13, right at least 12. Conditional
requires condition at least 2 and false branch at least 1; assignment requires
left at least 2. The unrestricted children still satisfy recursive precedence.

Reconstruction must also handle `nil`/`cons`, `none`/`some`, positional/named
arguments and namedArg, type names (`elem`, `fnType`, `mapping`, `userType`,
`array`) and parameters. These are dependencies within expressions, not an
extension to statement/function/unit uniqueness. In particular, type arrays
carry optional expression lengths; function type parameters and returns can
contain types. The public expression theorem must cover those dependencies.

The spelling `member e "address"` yields `Tok.elem .address`; other member
names yield `Tok.ident name`. Identifiers and tokens are existing data, not
raw source strings to be reparsed by a second syntax representation.
Tuple parentheses are actual syntax, with one optional component and a list
of remaining optional components. `(e)` must retain its tuple node. Empty
tuple components, empty positional arguments and empty named arguments must
be distinguished by their delimiters and commas. Inline arrays and call options
have an intrinsic first element, so are nonempty.

Layout choices are consumed in preorder. String literal bytes are reconstructed
from `Choice.frags`: fragments may have length zero but the length list is
nonempty and must consume the bytes exactly. The three string families remain
distinct token constructors. Type descendants can consume `Choice.attrs` at
function types, recording visibility/mutability order. Other expression nodes
do not consume a choice at their own node. `Choice.layoutFirst` is for contracts
and cannot occur in a successful expression derivation. Proof fields such as
`elemType`'s exclusion are proof irrelevant and do not introduce tree identity
differences. Numeric spellings, elementary type aliases, comments and whitespace
are already abstracted below tokens; uniqueness is over token yields.

## Preserved refusals (execution pending)

The frozen `Prec` and `ExprExamples` inputs record prefix-over-postfix refusal,
postfix used as base of index/slice/member/options/call or another postfix,
and assignment as a conditional false branch. The new lane has not rerun
these controls. Their expected verdicts remain refusal. Tests must include both
competing readings of prefix/postfix and conditional-assignment examples;
parenthesized variants are separate accepted controls. No producer edit or
changed expected verdict is authorized. Greedy new-type boundaries must also
retain the existing index/slice/member prohibition on a direct `new` base.

## Proof plan and open obligations

`obligations.json` enumerates the complete queue as open/pending, including
balanced delimiter disjointness, length-independent token splitting, every
precedence root, type/list/option/argument dependencies, all association
boundaries, arbitrary-family controls, axiom pins, runtime and fixture gates,
reviews and sealed proof handoff. No proof or arbitrary-family result exists
at this checkpoint. Nearest-else-independent expression helpers are authorized
backfill, but cannot be checked until resource enforcement is available.

`registration-manifest.json` has no modules/declarations because none were
added. Shared roots and module maps remain unchanged; future registrations
must go through the coordinator. `check-sol-expression-uniqueness.py --inventory`
checks all constructor names/order and exact source/base hashes. It is a static
inventory audit only. Its default mode deliberately exits 1 until actual proof,
axiom and fixture validation is implemented; changing ledger statuses alone
cannot turn that into acceptance.

## Runtime blocker EU-R1

Sources: assignment runtime policy; AGENTS.md verification; resource bounds in
`docs/refactoring-progress.md`. The VM cgroup limit is 17179869184 bytes with
no swap. PID 1 is `tail`, not systemd. Both system and user systemd scope probes
failed; `/sys/fs/cgroup` is root-owned and not writable by the worker. Thus the
required `MemoryMax=12G`, `MemorySwapMax=0` scope cannot be established. A 16 GiB
container limit alone does not reserve the required 4 GiB for the VM. No Lean
check, LSP or build was started. Tool version commands only reported Lean
4.24.0 (commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b) and Lake
5.0.0-src+797c613. The permitted KeySort check is pending, so
RUNTIME_GATE_PASS is not claimed.

Self-contained question EU-R1: Which enforcement path should this same VM use?

1. Provide working systemd or a delegated cgroup on this same VM, preserving
   the mandatory 12 GiB/no-swap enforcement and 4 GiB reserve.
2. Explicitly authorize a replacement process-tree memory guard on this VM,
   changing the mandated enforcement mechanism; limits and reserve stay binding.

No recommendation is made without an enforceable replacement. Scope questions
are not authorization. No new theorem premise, exclusion or weakened target
has been introduced. No automatic approval rejection occurred.

## Validation and handoff

Only static inventory and source-pin validation can pass at this checkpoint.
No new theorem signatures or axiom sets exist. Proof validation, all Lean
fixtures, compiler controls, KeySort, import closure and final repository gate
remain pending. Commands, exits, wall times and peak RSS for the static audit
are saved under `tests/sol-expression-uniqueness/evidence/`. Independent read-only
finder and skeptic reviews and their resolutions are recorded in `reviews.json`.
Both identified the missing pin-key-set check (F1/S1); it was fixed, negative
controls passed, and both independently accepted the corrected static inventory.
These reviews do not close the future proof checkpoint reviews.
The final full-proof seal remains open; an inventory patch/bundle is explicitly
a partial artifact. No push, merge or PR is authorized or performed.
