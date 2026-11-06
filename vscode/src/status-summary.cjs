// Presentation of reported outcomes only: no proof, stage or certificate is inferred.
'use strict';
const {offset}=require('./language-services.cjs'),{validRange}=require('./model.cjs');
function nameOf(row,doc){
 if(typeof row.name==='string'&&row.name.trim())return row.name.trim().replace(/\s+/g,' ');
 try{if(validRange(row.range)){const text=doc.getText();return text.slice(offset(text,row.range.start),offset(text,row.range.end)).trim().replace(/\s+/g,' ')||'a declaration';}}catch{}
 return 'a declaration';
}
function summarize(params,doc){
 const rows=(params.functions||[]).map(row=>({...row,name:nameOf(row,doc)})),counts={proved:0,direct:0,failed:0,unknown:0,unsupported:0,stale:0,cancelled:0,skipped:0,unverified:0,running:0,queued:0};
 const classify=row=>row.status==='proved'?(row.verification==='direct'?'direct':'proved'):['error','refuted'].includes(row.status)?'failed':['pending','unknown'].includes(row.status)?'unknown':['skip','skipped','internal','excluded','notRun'].includes(row.status)?'skipped':row.status==='ready'?'unverified':['queued','running','stale','cancelled','unsupported'].includes(row.status)?row.status:'unknown';
 rows.forEach(row=>counts[classify(row)]++);
 const total=rows.length,completed=counts.proved+counts.direct+counts.failed,running=rows.filter(row=>row.status==='running'),queued=counts.queued,failed=rows.filter(row=>classify(row)==='failed');
 const audits=rows.filter(row=>row.verification!=='direct'&&['unknown','notRun','impossible'].includes(row.preconditions));
 const incomplete=counts.unknown+counts.unsupported+counts.stale+counts.cancelled+counts.skipped+counts.unverified;
 const parts=[['proved','proved'],['direct','direct correct'],['failed','failed'],['unknown','unknown'],['unsupported','unsupported'],['stale','stale'],['cancelled','cancelled'],['skipped','skipped'],['unverified','unverified']].filter(([key])=>counts[key]).map(([key,label])=>`${counts[key]} ${label}`);
 let text,help=false;
 if(params.state==='cancelled')text='$(circle-slash) Document operation cancelled';
 else if(params.state==='compiling')text='$(sync~spin) Compiling Solidity';
 else if(params.state==='ready')text='$(book) Resolved (not verified)';
 else if(running.length||queued){text=`$(sync~spin) Completed ${completed}/${total}`+(running.length?`, verifying ${running.map(row=>row.name).join(', ')}`:', preparing verification');help=true;}
 else if(['queued','running'].includes(params.state)){text=params.state==='queued'?'$(sync~spin) Document verification queued':'$(sync~spin) Verifying document';help=true;}
 else if(params.state==='error'||params.errors>0){text=(params.phase==='compilation'?'$(error) Compilation failed':'$(error) Verification error')+(params.errors?`: ${params.errors} backend errors`:'');help=true;}
 else if(params.state!=='complete')text='$(circle-outline) Solidity Lean: '+String(params.state||'unknown');
 else if(failed.length){text='$(thumbsdown) Could not prove '+(failed.length===1?failed[0].name:failed.length+' declarations');if(incomplete)text+='; '+parts.filter(part=>!part.endsWith('failed')).join(', ');help=true;}
 else if(!total)text='$(circle-outline) Verification complete: no verification results';
 else text=(incomplete?'$(circle-outline)':counts.direct?'$(beaker)':'$(thumbsup)')+' Verification complete: '+parts.join(', ');
 if(audits.length){text=text.replace(/\$\(thumbsup\)/,'$(warning)');text+='; '+audits.map(row=>row.preconditions==='impossible'?'vacuous specification':row.preconditions==='unknown'?'entry audit unknown':'entry audit incomplete').filter((value,i,all)=>all.indexOf(value)===i).join(', ');help=true;}
 const tooltip=[`Document phase: ${params.state}`,`Completed ${completed}/${total} counts reported proved/direct-correct/failed outcomes, not a count of proofs.`,parts.join(', ')||'No function results.',...(params.progressScope==='document'?['Per-function execution progress is unavailable for this document job.']:[]),...rows.map(row=>`${row.name}: ${row.status}; ${row.verification==='direct'?'direct check, not a kernel certificate':row.verification?'reported mode '+row.verification:'verification mode unspecified'}${row.preconditions?' ; entry audit '+row.preconditions:''}`),...(params.message?[String(params.message)]:[])].join('\n');
 return{text,tooltip,help,counts,total,completed};
}
function issueURL(identity,state){
 const pkg=require('../package.json'),repository=typeof pkg.repository==='string'?pkg.repository:pkg.repository?.url;
 if(typeof repository!=='string'||!/^https:\/\/github\.com\/[\w.-]+\/[\w.-]+(?:\.git)?$/.test(repository))return null;
 const url=new URL(repository.replace(/\.git$/,'')+'/issues/new');url.searchParams.set('title','Verification issue');
 url.searchParams.set('body',`Steps to reproduce\n------------------\n\n* Server: ${identity?.serverInfo?.name||'unknown'} ${identity?.serverInfo?.version||'unknown'}\n* Extension: ${pkg.version}\n* Node.js: ${identity?.runtimeInfo?.version||'unknown'}\n* Document phase: ${state?.state||'unknown'}\n\nExpected behavior\n-----------------\n\nActual behavior\n---------------\n\nAdd a minimal example manually. No source code is attached automatically.\n`);return url.toString();
}
module.exports={summarize,nameOf,issueURL};
