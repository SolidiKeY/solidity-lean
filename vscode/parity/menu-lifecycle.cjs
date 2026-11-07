// Native contribution observations. These checks certify recorded endpoints,
// not raster glyphs, hidden mutations, macOS or command execution.
'use strict';
const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),{createHash}=require('node:crypto');
const phases=['source','unrelated','untitled','tab','restored'];
function forbidden(events){return events.filter(e=>e.kind==='terminal.start'||e.kind==='clipboard.write'||e.kind==='command.start'&&/^(dafny|solidityLean)\.(build|buildCustomArgs|run|test|verify|showVerificationTrace|hideVerificationTrace|copyVerificationTrace)$/.test(e.data?.id));}
async function preparation(task,deadline,now=Date.now){const remaining=deadline-now();if(remaining<=0)throw Error('Original3s menu readiness exhausted');let timer;try{const value=await Promise.race([task(),new Promise((_,reject)=>{timer=setTimeout(()=>reject(Error('Original3s menu readiness exhausted')),remaining);})]);if(now()>=deadline)throw Error('Late menu readiness response refused');return value;}finally{clearTimeout(timer);}}
function validate(value,runId,target,workspace){
 const errors=[];if(value?.runId!==runId||value?.target!==target)errors.push('foreign menu run/target');
 if(JSON.stringify(value?.phases?.map(p=>p.phase))!==JSON.stringify(phases))errors.push('missing/reordered menu phases');
 for(const row of value?.phases||[]){const b=row.binding,m=row.capture?.capture?.contributionMenu,kind=row.phase==='tab'?'tab':'editor';
  if(!b||typeof b.uri!=='string'||!b.session||!Number.isSafeInteger(b.version)||!/^[a-f0-9]{64}$/.test(b.sourceHash||'')||JSON.stringify(row.after)!==JSON.stringify(b))errors.push('source/session changed');
  const visible=row.phase==='source'||row.phase==='restored'||row.phase==='untitled'&&target==='dafny';
  const sourcePhase=['source','tab','restored'].includes(row.phase),expectedLanguage=row.phase==='unrelated'?'plaintext':target==='local'?'solidity':'dafny';
  const expectedText=row.phase==='unrelated'?'Menu language isolation.\n':require('./workloads.cjs').workload(target,1);
  if(b?.sourceHash!==createHash('sha256').update(expectedText).digest('hex')||b?.language!==expectedLanguage||b?.scheme!==(row.phase==='untitled'?'untitled':'file')||b?.trusted!==true)errors.push('wrong source/language/scope');
  if(workspace&&row.phase!=='untitled'){const expectedUri=require('node:url').pathToFileURL(path.join(workspace,row.phase==='unrelated'?'unrelated.txt':'menus.'+(target==='local'?'sol':'dfy'))).href;if(b?.uri!==expectedUri)errors.push('wrong resource');}
  const label=target==='local'?'Solidity Lean':'Dafny',custom=target==='local'?'Build Compiler Artifact with Import Options':'Build with Custom Arguments';
  if(m?.kind!==kind||!!m?.before?.items?.some(i=>i.label===label)!==visible||visible&&!m?.before?.items?.some(i=>i.label.includes(custom))||row.capture?.runId!==runId||row.capture?.phase!=='menus-'+row.phase||row.capture?.metadataHash!==createHash('sha256').update(JSON.stringify({binding:b,target,kind,visible})).digest('hex'))errors.push('wrong menu/phase ownership');
  if(sourcePhase&&JSON.stringify(b)!==JSON.stringify(value?.phases?.[0]?.binding))errors.push('source lifetime changed');
  if(!m?.before?.items?.every(i=>typeof i.label==='string'&&Object.hasOwn(i,'ariaDisabled')&&[null,'true','false'].includes(i.ariaDisabled)&&Object.hasOwn(i,'className')&&i.withinViewport===true&&['left','top','right','bottom'].every(k=>Number.isFinite(i.bounds?.[k]))&&i.bounds.right>i.bounds.left&&i.bounds.bottom>i.bounds.top))errors.push('incomplete/clipped raw menu state');
  if(row.error||row.capture?.error||row.capture?.status!=='captured')errors.push('failed menu phase');
  if(!Array.isArray(row.events)||!Number.isSafeInteger(row.eventStart)||!Number.isSafeInteger(row.eventEnd)||row.eventStart<0||row.eventEnd<row.eventStart||!Array.isArray(value.events)||row.eventEnd>value.events.length||JSON.stringify(row.events)!==JSON.stringify(value.events.slice(row.eventStart,row.eventEnd))||forbidden(row.events||[]).length)errors.push('missing/forbidden raw events');
  if(!m||m.binding?.session!==b?.session||JSON.stringify(m.binding)!==JSON.stringify(b)||m.before?.activeUri!==b?.uri||JSON.stringify(m.before)!==JSON.stringify(m.after)||!m.before?.items?.length||m.submenuVisible!==visible||!row.capture?.capture?.captured||!row.capture.capture.screenshot)errors.push('missing/stale/menu capture');
 }
 if(!Array.isArray(value?.events)||!Array.isArray(value?.forbiddenActions)||value.forbiddenActions.length||forbidden(value?.events||[]).length||JSON.stringify(value.forbiddenActions)!==JSON.stringify(forbidden(value.events||[])))errors.push('command side effects or missing audit');
 return errors;
}
async function run({vscode,config,events,sessionFor,requestPhase=require('./phase-capture.cjs').requestPhase}){
 const begin=events.length,target=config.target,language=target==='local'?'solidity':'dafny',source=require('./workloads.cjs').workload(target,1),file=path.join(config.workspace,'menus.'+(target==='local'?'sol':'dfy'));
 fs.writeFileSync(file,source);const doc=await vscode.workspace.openTextDocument(file),rows=[];
 const binding=d=>({uri:d.uri.toString(),version:d.version,sourceHash:createHash('sha256').update(d.getText()).digest('hex'),session:sessionFor(d),language:d.languageId,scheme:d.uri.scheme,trusted:vscode.workspace.isTrusted});
 const result={status:'partial',runId:config.runId,target,phases:rows,untrusted:{status:'missing',reason:'Existing pinned runner disables workspace trust UI; this launch cannot evidence an untrusted window.'},scope:'Actual Linux menu endpoint/AX/PNG observations only; no command, proof, raster/ABA or macOS equivalence.'};
 const save=()=>fs.writeFileSync(path.join(config.dir,'menu-observations.json'),JSON.stringify(result,null,2));
 async function capture(phase,d,kind='editor'){
  await vscode.window.showTextDocument(d,{preview:false});await vscode.commands.executeCommand('workbench.action.focusActiveEditorGroup');
  const before=binding(d);assert.equal(vscode.window.activeTextEditor?.document,d);
  const start=events.length,row={phase,binding:before,eventStart:start-begin};rows.push(row);save();
  try{row.capture=await requestPhase(config.dir,config.runId,'menus-'+phase,{binding:before,target,kind,visible:phase==='source'||phase==='restored'||phase==='untitled'&&target==='dafny'},config.operationTimeoutMs);row.after=binding(d);assert.deepEqual(row.after,before);row.eventEnd=events.length-begin;row.events=events.slice(start);save();}
  catch(error){row.error=error.message;error.observation=result;throw error;}
  finally{row.eventEnd=events.length-begin;row.events=events.slice(start);save();}
 }
 try{await capture('source',doc);const textFile=path.join(config.workspace,'unrelated.txt');fs.writeFileSync(textFile,'Menu language isolation.\n');const unrelated=await vscode.workspace.openTextDocument(textFile);await capture('unrelated',unrelated);
  const untitled=await vscode.workspace.openTextDocument({language,content:source});await capture('untitled',untitled);await capture('tab',doc,'tab');await capture('restored',doc);
  assert.equal(doc.getText(),source);assert.equal(fs.readFileSync(file,'utf8'),source);result.events=events.slice(begin);result.forbiddenActions=forbidden(result.events);assert.deepEqual(validate(result,config.runId,target,config.workspace),[]);save();return result;
 }catch(error){error.observation=result;throw error;}
 finally{result.events=events.slice(begin);result.forbiddenActions=forbidden(result.events);save();}
}
module.exports={phases,validate,run,preparation};
