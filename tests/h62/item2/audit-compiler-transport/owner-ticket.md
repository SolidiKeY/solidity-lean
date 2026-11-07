# Q-NEG-01: frozen negative controls and the universal witness requirement

Sources: H62 checkpoint 2; frozen base c6f550e281a7e5affa9a99bc2cdaed556dec00e4;
compiler-transport map; coordinator ownership snapshot (SHA256 verified).

Consumer owner: V09 (`v07-v11/v09-compiler-passes`, G24–G31).
Request-structure producer: V07 (`v07-v11/v07-lowering`, P12).
No original file was edited; no permission to edit an owner file is inferred.
The coordinator retrieves this saved ticket on the same VM. This checkout has
no `scripts/coord-tools/relay.sh`; no message was sent to another service.

The exact public declarations are:

- `Solidity.Backend.Passes.P12MemoryCapture.nonempty_revert_incompatible`,
  `Solidity/Backend/Passes/P12MemoryCapture.lean:75`, signature SHA256
  `4b5219bc6bf2ab1a6bb5e073a913040c571546472cea0bdf9541d9e57b17789f`.
- `Solidity.Backend.Passes.P12StorageCapture.nonempty_revert_incompatible`,
  `Solidity/Backend/Passes/P12StorageCapture.lean:64`, signature SHA256
  `fcb8ca50a99b5f802b39fe997ce8b9db185444c845d763dde12c70234f6a031e`.

Each frozen statement concludes `False`. Therefore its complete tuple of
parameters and proof hypotheses cannot be inhabited if the frozen proof is
sound. Both are intentional compatibility controls: a reached nonempty Source
revert cannot coexist with the coarse internal compiled boundary and its
original request, alignment, input and payment-freedom hypotheses. This does
not establish that `MemoryCapture`/`StorageCapture` is globally uninhabited,
and does not establish vacuity of either positive `execution` theorem.

Two private support negatives also occur in the conservative source census:
`Solidity.Backend.Passes.MemoryCallControls.noRefs` and
`Solidity.Backend.Passes.LoopReframedFailureControls.stale_pointer`. They
remain explicitly accounted for; private support is distinguished from public
interfaces. Their exact kernel names require the elaborated census.

Resolved by H69 (human, 2026-11-06): checked joint-impossibility is the audit
result for deliberate negative controls; ordinary interfaces still require
joint witnesses. No statement is changed. Q-NEG-01 is closed, with no request
to edit an owner file. The two public proofs and the two private refutations
are checked. The exact 68-case registry additionally includes reviewed generated
False-branch helpers; their ordinary parents retain independent obligations.
