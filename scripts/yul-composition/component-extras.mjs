#!/usr/bin/env node
/** Fail-closed selected component catalogs and isolated integration registration. */
import {readFileSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {isDeepStrictEqual as eq} from 'node:util';
import {ROOT,sha} from './harness.mjs';
import {validateLocalLedger,verifyLocalInputs} from './local-source.mjs';
import {findings} from '../check-trust.mjs';
const LOOP='tests/yul-composition/loop-component-ledger.json',TRUST='tests/yul-composition/local-trust-registration.json';
const FROZEN={"tests/yul-composition/loop-component-ledger.json": "832f7ab680b4bd26b4ef99a13ba8443f248218f8ab3c3c8973b9b44265a37410", "tests/yul-composition/local-trust-registration.json": "7622c6481d75e31acbbb3df396e394e8476dd2860d14aa959f7e9bccf986683d"};
const read=p=>readFileSync(join(ROOT,p));
export function validateLoopLedger(bytes=read(LOOP)){
 if(sha(bytes)!==FROZEN[LOOP])throw Error('stale/incomplete loop facts');const l=JSON.parse(bytes);
 if(sha(read(l.source))!==l.sourceSha256||l.localLedgerSha256!==sha(read('tests/yul-composition/local-component-ledger.json')))throw Error('stale loop source/dependencies');return l;
}
export function validateExtrasRoot(root){
 for(const [key,path]of Object.entries({localComponentEvidence:'tests/yul-composition/local-component-ledger.json',loopComponentEvidence:LOOP,localTrustRegistration:TRUST}))if(root[key]!==path)throw Error('missing selected local/loop/trust registration');
 if(root.obligations?.length!==24||root.combinations?.length!==6||[...root.obligations,...root.combinations].some(r=>r.status!=='pending'||r.proof!==null))throw Error('missing/closed full obligations');return root;
}
export function validateTrustRegistration(dependency,bytes=read(TRUST)){
 if(sha(bytes)!==FROZEN[TRUST])throw Error('trust registration drift');const record=JSON.parse(bytes),base=read('tests/trust-inventory.json');
 if(sha(base)!==record.baseInventorySha256||!eq(JSON.parse(readFileSync(join(dependency,'tests/trust-inventory.json'))),JSON.parse(base).concat(record.entries))||!read('scripts/check-trust.mjs').equals(readFileSync(join(dependency,'scripts/check-trust.mjs'))))throw Error('unreviewed shared inventory/checker change');
 const receipt=JSON.parse(read('tests/yul-composition/local-producer-input.json'));
 const actual=receipt.added.flatMap(file=>findings(readFileSync(join(dependency,file),'utf8')).map(({kind,code})=>({file,kind,code})));
 const sorted=rows=>rows.map(x=>JSON.stringify(x)).sort();
 if(!eq(sorted(actual),sorted(record.entries))||actual.length!==6||actual.some(r=>r.kind!=='recovery'))throw Error('unregistered or forbidden producer trust site');return record;
}
export function validateComponentExtras(dependency){
 verifyLocalInputs(dependency);validateExtrasRoot(JSON.parse(read('tests/yul-composition/ledger.json')));const local=validateLocalLedger(),loop=validateLoopLedger();
 if(!read(loop.source).equals(readFileSync(join(dependency,loop.source))))throw Error('actual loop consumer drift');validateTrustRegistration(dependency);
 return {localFacts:local.facts.length,loopFacts:loop.facts.length,privateMethodSites:6,fullObligationsClosed:0,fullCombinationsClosed:0};
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url))console.log(JSON.stringify(validateComponentExtras(process.argv[2])));
