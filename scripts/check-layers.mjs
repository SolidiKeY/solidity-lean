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
  /^Solidity\.Yul\.(LocalBoolWhile|Checks\.LocalBoolWhile)$/, // Iteration of context-growing Boolean scopes.
