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
  /^Solidity\.Yul\.(LocalDefaultDoWhile|Checks\.LocalDefaultDoWhile)$/, // Actual body-first iteration of typed default scopes.
  /^Solidity\.Yul\.(LocalDefaultWhile|Checks\.LocalDefaultWhile)$/, // Concrete iteration of typed default scopes.
  /^Solidity\.Yul\.(LocalDefaultIfElse|Checks\.LocalDefaultIfElse)$/, // Conditional selection of typed default scopes.
  /^Solidity\.Yul\.(LocalItemWorld|Checks\.LocalItemWorld)$/, // World preservation for actual pure local runners.
  /^Solidity\.Yul\.(LocalDefaultUnchecked|Checks\.LocalDefaultUnchecked)$/, // Actual unchecked default-scope composition.
  /^Solidity\.Yul\.(LocalDefaultItems|Checks\.LocalDefaultItems)$/, // Typed constant-default declaration sequences.
  /^Solidity\.Yul\.(LocalDefaultBinding|Checks\.LocalDefaultBinding)$/, // Actual constant-default declaration/body composition.
  /^Solidity\.Yul\.(LocalBoolUnchecked|Checks\.LocalBoolUnchecked)$/, // Concrete unchecked and ordinary scope composition.
  /^Solidity\.Yul\.(LocalBoolForNoGuard|Checks\.LocalBoolForNoGuard)$/, // Exact omitted-guard transport and concrete adapters.
  /^Solidity\.Yul\.(LocalBoolPostIter|LocalBoolForPost|Checks\.LocalBoolForPost)$/, // Scoped Boolean for posts.
  /^Solidity\.Yul\.(LocalBoolDivergence|Checks\.LocalBoolDivergence)$/, // No finite normal completion of constant-true scoped loops.
  /^Solidity\.Yul\.(LocalBoolDoDivergence|Checks\.LocalBoolDoDivergence)$/, // No finite normal completion of literal-true do/while.
  /^Solidity\.Yul\.(LocalBoolFor|Checks\.LocalBoolFor)$/, // Context-growing Boolean for initializer and scoped body.
  /^Solidity\.Yul\.(LocalBoolDoWhile|Checks\.LocalBoolDoWhile)$/, // Body-first iteration of certified Boolean scopes.
  /^Solidity\.Yul\.(LocalBoolWhile|Checks\.LocalBoolWhile)$/, // Iteration of context-growing Boolean scopes.
