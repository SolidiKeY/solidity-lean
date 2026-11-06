#!/usr/bin/env node
'use strict';
const fs=require('node:fs'),path=require('node:path'),{spawnSync}=require('node:child_process');
const mechanical=require('./mechanical.cjs'),{validate}=require('./discover.cjs');
const root=path.resolve(__dirname,'../..');
function check({extension,server,liveTrace,inventory=require('./inventory.cjs').loadInventory()}={}){
  const errors=validate(inventory),rows=inventory.mechanical?.rows||[],ids=new Set();
  for(const row of [...inventory.features,...rows]){if(ids.has(row.id))errors.push('duplicate row '+row.id);ids.add(row.id);}
  for(const [name,dir]of Object.entries({extension,server})){
    if(!dir){errors.push('Missing '+name+' source checkout');continue;}
    const r=spawnSync('git',['-C',dir,'rev-parse','HEAD'],{encoding:'utf8'});
    if(r.status!==0||r.stdout.trim()!==inventory.upstream[name].commit)errors.push('Wrong upstream pin '+name);
    const dirty=spawnSync('git',['-C',dir,'status','--porcelain','--untracked-files=no'],{encoding:'utf8'});
    if(dirty.status!==0||dirty.stdout.trim())errors.push('Modified upstream checkout '+name);
  }
  const expected=[];
  try{expected.push(...mechanical.staticRows(path.resolve(extension)));}catch(e){errors.push(e.message);}
  try{
    const rel=inventory.mechanical?.trace;
    if(!rel||path.isAbsolute(rel)||!path.resolve(root,rel).startsWith(root+path.sep))throw Error('Missing or escaping live trace');
    const file=fs.realpathSync(path.join(root,rel));if(!file.startsWith(root+path.sep))throw Error('Escaping live trace symlink');
    expected.push(...mechanical.traceRows(file,rel));
  }catch(e){errors.push(e.message);}
  const byId=new Map(rows.map(r=>[r.id,r]));
  if(liveTrace)try{for(const row of mechanical.traceRows(path.resolve(liveTrace),'live discovery')){
    const actual=byId.get(row.id);
    if(!actual||JSON.stringify(actual.detail)!==JSON.stringify(row.detail))errors.push('Uninventoried live trace hit '+row.id);
  }}catch(e){errors.push(e.message);}
  for(const row of rows){if(!['complete','partial','missing','broken','unexamined'].includes(row.assessment?.status))errors.push('Invalid row status '+row.id);
    if(!row.assessment?.reason)errors.push('Missing assessment reason '+row.id);}
  for(const row of expected){const actual=byId.get(row.id);if(!actual)errors.push('Uninventoried '+row.id);
    else {const {assessment,...discovery}=actual;if(JSON.stringify(discovery)!==JSON.stringify(row))errors.push('Changed discovery '+row.id);}}
  // Retired hits stay inventoried and judged. Nothing is deleted during refresh.
  if(!rows.length)errors.push('Missing mechanical inventory');
  return {status:errors.length?'failed':'passed',rows:inventory.features.length+rows.length,discovered:expected.length,errors};
}
function options(args){const get=(flag,fallback)=>{const i=args.indexOf(flag);return i<0?fallback:args[i+1];};return{liveTrace:get('--live-trace',undefined),extension:path.resolve(get('--extension',path.join(root,'.cache/dafny-extension'))),server:path.resolve(get('--server',path.join(root,'.cache/dafny-server')))};}
if(require.main===module){try{const report=check(options(process.argv.slice(2)));console.log(JSON.stringify(report,null,2));process.exitCode=report.status==='passed'?0:1;}catch(e){console.error(e.stack);process.exitCode=1;}}
module.exports={check,options,root};
