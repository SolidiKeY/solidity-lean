#!/usr/bin/env node
// Reuse the repository's published lexical import inventory, read only.
import {loadGraph, reach} from './import-fanout.mjs';
const {graph} = loadGraph();
const modules = [...reach(graph, 'Solidity'), 'Solidity'].sort();
console.log(JSON.stringify({schema:1, root:'Solidity', modules,
  boundary:'Lexical core public imports only; joint kernel import and Bridge gates remain required.'}));
