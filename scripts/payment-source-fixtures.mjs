#!/usr/bin/env node
/** Reproduce the payment source AST witnesses from the verified upstream pin. */
import {readFileSync,writeFileSync,mkdirSync,mkdtempSync,rmSync} from 'node:fs';
import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';
import {join} from 'node:path';
import {preparePaymentSource} from './payment-source.mjs';
import {parseFixture,withPreamble,runtimePipelines,semanticVectors,evmCompatible,verifySnapshot,COMPILER_SHA} from './solidity-upstream.mjs';
import {referenceCompiler} from './test-compiler.mjs';
const compiler=referenceCompiler();
const check=process.argv.includes('--check'),sha=x=>createHash('sha256').update(x).digest('hex');
if(sha(readFileSync(compiler))!==COMPILER_SHA)throw Error('pinned compiler SHA mismatch');
const c=createRequire(import.meta.url)(compiler).cwrap('solidity_compile','string',['string','number','number']);
const compile=input=>JSON.parse(c(JSON.stringify(input),0,0));
const {directory}=verifySnapshot();mkdirSync('.lake/payment-source',{recursive:true});
const work=mkdtempSync('.lake/payment-source/generate-');
try{for(const [name,path] of [['Send','functionCall/send_zero_ether.sol'],['Transfer','revertStrings/transfer.sol']]){
 const pinned='test/libsolidity/semanticTests/'+path,raw=readFileSync(join(directory,pinned));
 const jobs=preparePaymentSource(pinned,parseFixture(raw.toString()),compile,work,{withPreamble,runtimePipelines,semanticVectors,evmCompatible,
 COMPILER_SHA,VERSION:'0.8.38+commit.1835d247.Emscripten.clang',fixtureSha256:sha(raw)}).jobs;
 const bytes=readFileSync(jobs.find(j=>j.pipeline==='legacy').fixture);const target='tests/payment-source/'+name+'.ast.json';
 if(check){if(!readFileSync(target).equals(bytes))throw Error('payment AST drift: '+target);}
 else {mkdirSync('tests/payment-source',{recursive:true});writeFileSync(target,bytes);}
 let h=0xcbf29ce484222325n;for(const b of bytes)h=BigInt.asUintN(64,(h^BigInt(b))*0x100000001b3n);
 console.log(name+' hash0x'+h.toString(16)+' sha256='+sha(bytes));
}}finally{rmSync(work,{recursive:true,force:true});}
