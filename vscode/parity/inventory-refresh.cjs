#!/usr/bin/env node
'use strict';
// Append only. Never overwrite an existing assessment or erase a retired row.
const fs=require('node:fs'),path=require('node:path');
const {staticRows,traceRows}=require('./mechanical.cjs'),{root,options}=require('./inventory-check.cjs');
const config=options(process.argv.slice(2)),file=path.join(root,'docs/dafny-editor-features.json'),inventory=require('./inventory.cjs').loadInventory(file);
const trace='tests/editor-parity/lifecycle/dafny-lsp.jsonl';
const discovered=[...staticRows(config.extension),...traceRows(path.join(root,trace),trace)];
const previous=inventory.mechanical?.rows||[],known=new Set([...inventory.features,...previous].map(r=>r.id));
const appended=discovered.filter(r=>!known.has(r.id)).map(row=>({...row,assessment:{status:'unexamined',reason:row.kind==='visual'?
  'Paired phase screenshots unavailable: official VS Code download returned HTTP 403 through the session proxy. No visual parity claim.':
  'Discovered obligation; candidate reproduction and independently judged evidence remain required.',localSource:[],scenarioIds:[],testEvidence:[],evidenceFiles:[]}}));
inventory.mechanical={schemaVersion:1,trace,rows:[...previous,...appended]};
require('./inventory.cjs').saveInventory(inventory,file);console.log(`Appended ${appended.length} rows; retained ${previous.length} mechanical rows and ${inventory.features.length} original features.`);
