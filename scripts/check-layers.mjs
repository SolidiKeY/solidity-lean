#!/usr/bin/env node
// The core does not reach the elaborator: no core module imports, even
// transitively, a module of the source elaborator (`Syntax/{Elab,Quote,Splice}`)
// or of the printers and tactic front ends (`Calculus/{Print*,Surface*,
// TacticSyntax,Quote,NamedTerm}`). An edit to those then rebuilds the meta
// layer, the tactics and the examples, not the calculus and its soundness.
// The core is listed in `docs/parallelism.md`, "The core"; it is `CORE` below.
//
// Usage: node scripts/check-layers.mjs
// Exit 0 = no core module reaches the elaborator, 1 = at least one does
// (each printed with one import path down to it).
import { loadGraph, findPath, reach } from "./import-fanout.mjs";

const CORE = [
  /^Solidity\.(KeySort|Eqns|AST|TypeGraph|Scope|SpecSyntax|Hashes|Keccak|ERC7201|Secp256k1|RevertBytes|Syntax|Semantics|Signature|Update)$/,
  /^Solidity\.Syntax\.(Raw|Grammar|Contract|Scoped|Checked|Inlined|PushSource|Join)$/,
  /^Solidity\.(Semantics|Typing|Theory)\./,
  /^Solidity\.Calculus\.(Fml|Rules|RuleSyntax|RuleKit|KeyTaclets|Step|Arms|Blocks|Taclet|Proves|Logic|Preconditions|FiniteMembership|FilteredMembership|Hyp|Correct|FirstOrder|Transient|Lifetime|ContractWorld|PaymentWitness|PaymentConditions)$/,
  /^Solidity\.Calculus\.(Sound.*|StmtSound|ProvesSound|PremiseSound|UpdRuleScoped|UpdateRules|TermLib\.Rules)$/,
  /^Solidity\.Calculus\.RuleSyntax\./,
  /^Solidity\.Roadmap\./, // The roadmap's contracts are statements below the elaborator.
  /^Solidity\.Hash\.CollisionBound$/,
  /^Solidity\.Backend\.(Opcode|Jumpdest|Assembler|Control)$/,
  /^Solidity\.Hash\.Adaptive$/,
  /^Solidity\.Storage\.HashedLayout$/,
  /^Solidity\.Storage\.HashedKeccak$/,
  /^Solidity\.Storage\.HashedSeparation$/,
  /^Solidity\.Calculus\.(TermEval|TermEq|TermWk|LoopInvariantWk|Lower|LowerRun|Shift|WkOver|Lands|StateFacts|ReadWrite|DataIn|SeqRewrite|SyntaxSize|Graft|CallSummary|KIntTwoAnchors)$/,
];
const ELABORATOR = [
  /^Solidity\.Tools\.SolCases$/, // External-source printer stays outside the core.
  /^Solidity\.Syntax\.(Elab|Quote|Splice)(\.|$)/,
  /^Solidity\.Calculus\.(Print[^.]*|Surface[^.]*|TacticSyntax|Quote|NamedTerm)(\.|$)/,
];

const { graph } = loadGraph();
const isCore = (m) => CORE.some((r) => r.test(m)) && !ELABORATOR.some((r) => r.test(m));
const isElab = (m) => ELABORATOR.some((r) => r.test(m));
const core = [...graph.keys()].filter(isCore).sort();
let bad = 0;
for (const m of core) {
  const hit = [...reach(graph, m)].filter(isElab).sort()[0];
  if (!hit) continue;
  bad++;
  console.log(`LAYER  ${findPath(graph, m, hit).map((x) => x.replace(/^Solidity\./, "")).join(" → ")}`);
}
console.log(`${core.length} core modules, ${bad} reach the elaborator`);
process.exit(bad ? 1 : 0);
