-- Root of the `SoliditySpec` library: the SolSpec assertion layer,
-- the `sol_spec` tactic, its metatheory, the `sol!` surface syntax, and
-- the worked obligations that pin the shape the front-end generates.
--
-- Deliberately not imported by `Solidity.lean`, for the same
-- reason `SolidityCorpus` is not: the examples are symbolic
-- executions with a `simp` normalization each, so folding them into the
-- default build would make every `./run-lean.sh` pay for them. Build
-- this target with `./scripts/check-spec.sh`.
--
-- The VS Code extension needs only
-- `Solidity.Spec.Tactic` (and its imports), which is
-- what `./scripts/check-spec.sh --tactic` builds. The `sol!` surface
-- syntax is for writing specifications in Lean directly and is not on
-- that path.
import Solidity.Spec.Assertion
import Solidity.Spec.Tactic
import Solidity.Spec.Metatheory
import Solidity.Spec.Syntax
import Solidity.Spec.Examples
import Solidity.Spec.SyntaxExamples
