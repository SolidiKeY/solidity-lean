#!/usr/bin/env node
// Actual CLI stale-preflight cleanup; expected rejection is NOT authentication.
import * as fs from 'node:fs';
import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
const out=process.argv[2];assert(out?.startsWith('/'));
const registry=JSON.parse(fs.readFileSync('tests/internal-flow/fixture-axiom-pins.json','utf8'));
const fixtures=Object.keys(registry).sort().map(n=>`tests/internal-flow/${n}.lean`);assert.equal(fixtures.length,27);
const bin=out+'/sentinel-bin',marker=out+'/UNEXPECTED_LEAN';fs.mkdirSync(bin,{recursive:true});assert(!fs.existsSync(marker));
fs.writeFileSync(bin+'/lake',`#!/bin/sh\necho unexpected > '${marker}'\nexit 97\n`,{mode:0o755});
const r=spawnSync(process.execPath,['tests/internal-flow/fixture-cache.mjs','batch',out,...fixtures],{encoding:'utf8',env:{...process.env,PATH:bin+':'+process.env.PATH}});
fs.writeFileSync(out+'/stale-preflight.stdout',r.stdout??'');fs.writeFileSync(out+'/stale-preflight.stderr',r.stderr??'');
assert.notEqual(r.status,0);assert.match(r.stderr,/stale or altered/);assert(!fs.existsSync(marker));
const rows=fs.readFileSync(out+'/fixture-stages.jsonl','utf8').trim().split('\n').map(JSON.parse);
const release=rows.find(x=>x.event==='object-digests.preflight-released');assert(release?.closed);assert.equal(release.retained_payload_bytes,0);
assert(!rows.some(x=>x.event==='child-spawn'));assert(rows.some(x=>x.stage==='batch'&&x.state==='failed'));
console.log(JSON.stringify({host_only:true,expected_stale_rejection_not_authentication:true,actual_exit:r.status,no_Lean:true,preflight_exception_cleanup:true,release},null,2));
