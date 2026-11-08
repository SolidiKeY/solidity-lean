# Loop proofs

Execution and proof metadata are separate. `invariant`, `decreases` and `unwind`
annotations select proof rules; they do not alter program execution. The rules
and their exact premises are in [Calculus/Blocks.lean](../Solidity/Calculus/Blocks.lean)
and the implementations under [Semantics](../Solidity/Semantics/).

## Typed tuple measures

The ordinary tuple-diamond rule requires an admitted body frame, no break flag
and no quantified invariant clauses. Components are unsigned and capture-free;
the rule requires defined components and strict lexicographic decrease after
every successful body turn, including the final turn. Later
components may increase when an earlier component decreases. Box safety can
use the admitted erasure path; it supplies no metric decrease. Callback diamonds
have no general lexicographic bridge.

Ordinary diamonds accept exhaustion. Strict successful termination requires
`LoopMetrics.SourceCertificate` for the tuple actually stored on the loop,
an initial invariant proof, defined components at every invariant head,
successful invariant-preserving bodies and strict decrease. The certificate's
semantic invariant/postcondition are explicit parameters, not automatically the
source annotation clauses. An abstract havoc state is not necessarily reachable.

A lowered `do … while` has a synthetic first-iteration flag. An invariant must
relate that phase to source data; a metric rule cannot silently assume the
initial guard or invent an entry-phase relation.

## Execution

The mathematical loop run is the sole semantic reference. The compiled
implementation of that run is not kernel reduction. Finite `runF` observations
transport to the run only through the actual approximation theorem; failure to
finish within fuel does not prove divergence or termination.

## Proof rules

`unwind k` bounds proof exploration, not execution. A completed symbolic walk
may leave obligations; an exhausted search is not a proof. Use the suggestion
twin's selected budget for replay. Do not increase global proof budgets to
hide failed search.

Invariant rules owe initialization, preservation, exit and their stated frame
conditions. Havoc must cover every location the body can change, including
calls, aliases and payment effects. Diamond variants must be defined where
the rule requires and decrease on continued iterations. Unsupported frames or
annotations remain unsupported rather than being weakened.

## Compiler boundary

Loop correctness applies only to the admitted compiler path and its state,
allocation and resource premises. It is not a gas bound or whole-Solidity
termination theorem. See [correctness.md](correctness.md).
