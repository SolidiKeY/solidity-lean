#!/usr/bin/env node
// Extend reader diagnostics with every emitted member and dropped-declaration
// reason. Original reader observations are preserved as separate files.
import {readFileSync,writeFileSync,readdirSync,existsSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {createHash} from 'node:crypto';
import {runTool} from './test-solidity.mjs';
const base=resolve(process.env.BASELINE_PROBE_OUT??'tests/upstream/baseline-20261028/probes/rechecked');
const inv=[];
for(const name of readdirSync(join(base,'runs')).sort())for(const pipeline of ['legacy','viaIR']){
 const job=join(base,'runs',name,pipeline),old=join(job,'Reader.lean');if(!existsSync(old))continue;
 const file=join(job,'ReaderMetadata.lean'),output=join(job,'reader-complete.json');if(existsSync(output))throw Error('refuse overwrite');
 let code=readFileSync(old,'utf8').replaceAll(join(job,'reader.json'),output);
 const target='("functions",toJson functions)]';
 if(!code.includes(target))throw Error('unknown original wrapper');
 code=code.replace(target,'("functions",toJson functions),("members",toJson c.members),("functionMembers",toJson c.funMembers),("initializationMembers",toJson c.initMembers),("dropped",toJson (c.dropped.map fun (e : String × Gap) => Json.mkObj [("name",toJson e.1),("reason",toJson e.2.msg),("line",toJson e.2.line)])),("initializationGap",match c.initGap with | none => Json.null | some g => toJson g.msg)]');
 writeFileSync(file,code);const args=['--quiet','--no-build','lean',file,'--','--tstack=131072','-j1'];let log='',tool={exitCode:0},start=performance.now();
 try{log=runTool('lake',args,120000);}catch(e){log=e.message;tool=e.tool??{exitCode:null};}
 writeFileSync(join(job,'metadata.log'),log);inv.push({case:name,pipeline,stage:'source-reader-complete-metadata',command:['lake',...args],...tool,elapsedMs:performance.now()-start,logSha256:createHash('sha256').update(log).digest('hex')});
 writeFileSync(join(base,'metadata-invocations.json'),JSON.stringify(inv,null,2)+'\n');
 if(tool.exitCode!==0||!existsSync(output))throw Error('metadata stage failed '+name+'/'+pipeline);
 const result=JSON.parse(readFileSync(output));const original=JSON.parse(readFileSync(join(job,'reader.json')));
 if(JSON.stringify(result.functions)!==JSON.stringify(original.functions))throw Error('original observations changed');
 console.log(JSON.stringify({case:name,pipeline,dropped:result.dropped.length,initializationGap:result.initializationGap}));
}
