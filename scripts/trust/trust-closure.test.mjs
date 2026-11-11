// Regression controls: proof edits must not grow trust, missing positions and
// lost roots must fail, and declaration/line growth needs a baseline reason.
import {test} from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,mkdirSync,writeFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {execFileSync} from 'node:child_process';
import {statementEnd,summarize,compare,validateRevision,sha,sourceIndex,historyBase,checkHistory} from './trust-closure.mjs';
const source='theorem headline (n : Nat := 0) : n = n := by\n  rfl\n';
const raw={schema:1,roots:['headline'],declarations:[{name:'headline',module:'Control',theorem:true,start:1,end:2}]};
test('proof bodies do not enter statement lines',()=>{
 assert.equal(statementEnd(source,1,2),1);
 assert.equal(statementEnd(source.replace('rfl','exact Eq.refl _'),1,2),1);
 assert.equal(statementEnd('theorem x : let n := 1; n = n := by rfl',1,1),1);
 assert.equal(summarize(raw,()=>source).totalLines,1);
});
test('missing positions fail closed',()=>assert.throws(()=>summarize({...raw,declarations:[{...raw.declarations[0],start:null}]},()=>source),/missing/));
test('roots cannot silently disappear',()=>{const b=summarize(raw,()=>source);assert.throws(()=>compare({...b,roots:[]},b),/lost/);});
test('new dependencies and source-line growth fail',()=>{
 const b=summarize(raw,()=>source);
 assert.throws(()=>compare({...b,declarations:[...b.declarations,{name:'extra'}]},b),/growth/);
 assert.throws(()=>compare({...b,modules:[{module:'Control',lines:2}]},b),/growth/);
 compare(b,b);
});

test('baseline growth needs a fresh reason and predecessor checksum',()=>{
 const old={...summarize(raw,()=>source),change:{reason:'initial',previousSha256:null}};
 const text=JSON.stringify(old,null,2)+'\n';
 const grown={...old,modules:[{module:'Control',lines:2}]};
 assert.throws(()=>validateRevision(grown,text),/fresh reason/);
 validateRevision({...grown,change:{reason:'new semantic definition',previousSha256:sha(text)}},text);
 assert.throws(()=>validateRevision({...grown,change:{reason:'initial',previousSha256:sha(text)}},text),/fresh reason/);
});

test('equation-style proofs and delimiter-only lines are excluded',()=>{
 assert.equal(statementEnd('theorem t : True\n  | _ => True.intro',1,2),1);
 assert.equal(statementEnd('theorem t : True\n := by\n  trivial',1,3),1);
 assert.equal(statementEnd('  mp : a → b',1,1),1);
 assert.throws(()=>statementEnd('theorem t : True',1,1),/boundary/);
});

test('type match branches and bitwise notation are not proof boundaries',()=>{
 assert.equal(statementEnd('theorem t : match true with\n  | true => True\n  | false => False\n := by trivial',1,4),3);
 assert.equal(statementEnd('theorem t (a b : Nat) : a ||| b = a ||| b := rfl',1,1),1);
});

test('serialized name-only baselines validate without artificial growth',()=>{
 const b=summarize(raw,()=>source);
 const compact={...b,declarations:b.declarations.map(d=>d.name),change:{reason:'initial',previousSha256:null}};
 compare(compact,compact);
 validateRevision(compact,JSON.stringify(compact,null,2)+'\n');
 compare(b,compact);
});

test('literal delimiters and multiline bitwise operators cannot shrink statements',()=>{
 assert.equal(statementEnd('theorem text :\n  "a := b" =\n  "a := b" := by rfl',1,3),3);
 assert.equal(statementEnd('theorem raw :\n  r###"a := b"### =\n  r###"a := b"### := by rfl',1,3),3);
 assert.equal(statementEnd('theorem bits (a b : Nat) : a\n ||| b = a ||| b := rfl',1,2),2);
 assert.throws(()=>statementEnd('theorem x : s!"{1}" = "1" := rfl',1,1),/interpolated/);
});

test('comments cannot confuse literal masking',()=>{
 assert.equal(statementEnd('/- dangling " /- nested -/ -/\ntheorem t : True := by trivial',1,2),2);
});
// H420 guards: the opt-in ceiling must include the full module while removing
// proof bodies outside the headline closure too, with every fallback named.
test('H420 source ceilings are explicit and exclude unrelated theorem proofs',()=>{
 const code='def meaning := 0\ntheorem headline : True := by\n  trivial\ntheorem unused : True := by\n  trivial\n';
 const input={schema:1,roots:['headline'],declarations:[
  {name:'headline',module:'Control',theorem:true,start:2,end:3},
  {name:'generated',module:'Control',theorem:false,start:null,end:null}],
  ceilingProofs:[{name:'headline',module:'Control',start:2,end:3},
    {name:'_private.Control.0.unused',module:'Control',start:null,end:null}]};
 assert.throws(()=>summarize(input,()=>code),/missing/);
 const result=summarize(input,()=>code,{sourceCeilings:true,
  proofRangesFor:()=>new Map([['unused',{start:4,end:5}]])});
 assert.equal(result.totalDeclarations,2);
 assert.equal(result.totalLines,3);
 assert.equal(result.ceilings[0].excludedProofLines,2);
 assert.equal(result.fallbacks[0].name,'generated');
 assert.match(result.sourceLineMetric,/H420 conservative upper bound/);
 assert.throws(()=>summarize(input,()=>code,{sourceCeilings:true}),/written proof lacks/);
 assert.throws(()=>summarize({...input,ceilingProofs:undefined},()=>code,{sourceCeilings:true}),/complete proof inventory/);
});

test('ceiling proof exclusions preserve trusted executable auxiliary source',()=>{
 const code='theorem outer : True := by\n  trivial\nwhere\n  semantic : Nat := 7\n';
 const input={schema:1,roots:['outer.semantic'],declarations:[
  {name:'outer.semantic',module:'Control',theorem:false,start:4,end:4},
  {name:'generated',module:'Control',theorem:false,start:null,end:null}],
  ceilingProofs:[{name:'outer',module:'Control',start:1,end:4}]};
 const result=summarize(input,()=>code,{sourceCeilings:true});
 assert.equal(result.totalLines,2);
 assert.deepEqual(result.ceilings[0].retainedTrustedDefinitionLines,[4]);
 assert.throws(()=>summarize({...input,declarations:[{...input.declarations[0],statementOnly:true}]},()=>code,{sourceCeilings:true}),/precise source ownership/);
});

test('class fields with binders and theorem where bodies have distinct spans',()=>{
 assert.equal(statementEnd('  antisymm (a b : α) : r a b → r b a → a = b',1,1),1);
 assert.equal(statementEnd('theorem t : True where\n  intro := True.intro',1,2),1);
 assert.equal(statementEnd('@[foo [0]] structure P : Prop where\n  p : True',1,2),2);
});

test('generated deriving proofs have no independent source proof body',()=>{
 assert.equal(statementEnd('  deriving Inhabited, Nonempty',1,1),1);
});
test('source exclusions use explicitly resolved index rather than stale trace/local positions',()=>{
 const root=mkdtempSync(join(tmpdir(),'trust-index-'));
 try{
  mkdirSync(join(root,'.lake/build/lib/lean'),{recursive:true});
  mkdirSync(join(root,'cache/artifacts'),{recursive:true});
  const index=end=>({references:{x:{usages:[[0,0,0,1,'proof',0,0,end,4]]}}});
  writeFileSync(join(root,'.lake/build/lib/lean/Control.trace'),JSON.stringify({outputs:{i:'123'}}));
  writeFileSync(join(root,'.lake/build/lib/lean/Control.ilean'),JSON.stringify(index(8)));
  writeFileSync(join(root,'cache/artifacts/123.ilean'),JSON.stringify(index(1)));
  assert.equal(sourceIndex(root,'Solidity.Control',{indexPaths:new Map([['Solidity.Control',join(root,'cache/artifacts/123.ilean')]])}).get('proof').end,2);
 }finally{rmSync(root,{recursive:true,force:true});}
});

test('one-line equation theorems retain their complete source line',()=>{
 assert.equal(statementEnd('theorem iff_not_self : ¬(a ↔ ¬a) | H => let f h := H.1 h h; f (H.2 f)',1,1),1);
});

test('dropping an executable auxiliary range cannot erase its proof-owner source',()=>{
 const source='theorem outer : True := by\n  trivial\nwhere\n  semantic : Nat := 7\n';
 const input={schema:1,roots:['outer.semantic'],declarations:[
  {name:'outer.semantic',module:'Control',theorem:false,sourceOwner:'outer',ownerStart:1,ownerEnd:4,start:null,end:null}],
  ceilingProofs:[{name:'outer',module:'Control',start:1,end:4}]};
 assert.throws(()=>summarize(input,()=>source,{sourceCeilings:true}),/inside a proof needs precise/);
 assert.throws(()=>summarize({...input,declarations:[{...input.declarations[0],ownerStart:null}]},()=>source,{sourceCeilings:true}),/owner provenance/);
});

// Guards master-push self-comparison accepting growth, lost roots or stale pins.
// Real Git fixtures put origin/master at the changed HEAD, as actions/checkout does.
function historyFixture(action) {
 const root=mkdtempSync(join(tmpdir(),'trust-history-')),cwd=process.cwd();
 const git=(...args)=>execFileSync('git',args,{cwd:root,encoding:'utf8',stdio:['ignore','pipe','pipe']}).trim();
 try {
  git('init','-q');git('config','user.name','control');git('config','user.email','control@example.invalid');
  mkdirSync(join(root,'scripts/trust'),{recursive:true});
  const baseline=join(root,'scripts/trust/trust-closure-baseline.json');
  const previous={...summarize(raw,()=>source),change:{reason:'initial',previousSha256:null}};
  const previousText=JSON.stringify(previous,null,2)+'\n';
  writeFileSync(baseline,previousText);git('add','.');git('commit','-qm','initial baseline');
  const before=git('rev-parse','HEAD');git('update-ref','refs/remotes/origin/master',before);
  const commit=next=>{writeFileSync(baseline,JSON.stringify(next,null,2)+'\n');git('add','.');git('commit','-qm','changed baseline');git('update-ref','refs/remotes/origin/master',git('rev-parse','HEAD'));};
  process.chdir(root);
  action({git,before,previous,previousText,commit,baseline});
 } finally {process.chdir(cwd);rmSync(root,{recursive:true,force:true});}
}
test('push history rejects baseline growth even when origin/master equals HEAD',()=>historyFixture(({git,before,previous,previousText,commit})=>{
 const grown={...previous,modules:[{module:'Control',lines:2}]};commit(grown);
 assert.equal(git('rev-parse','origin/master'),git('rev-parse','HEAD'));
 const push={GITHUB_EVENT_NAME:'push',TRUST_BASE_REF:before};
 assert.equal(historyBase({env:push}),before);
 assert.throws(()=>checkHistory(grown,{env:push}),/fresh reason/);
 assert.throws(()=>checkHistory({...grown,change:{reason:'fresh',previousSha256:'0'.repeat(64)}},{env:push}),/checksum/);
 assert.throws(()=>checkHistory(grown,{env:{}}),/fresh reason/);
 const valid={...grown,change:{reason:'new definition',previousSha256:sha(previousText)}};
 writeFileSync('scripts/trust/trust-closure-baseline.json',JSON.stringify(valid,null,2)+'\n');git('add','.');git('commit','--amend','-qm','valid growth');git('update-ref','refs/remotes/origin/master',git('rev-parse','HEAD'));
 checkHistory(valid,{env:push});
}));
test('PR target and push predecessor both preserve lost-root refusal',()=>historyFixture(({before,previous,commit})=>{
 const lost={...previous,roots:[]};commit(lost);
 for(const event of ['push','pull_request'])
  assert.throws(()=>checkHistory(lost,{env:{GITHUB_EVENT_NAME:event,TRUST_BASE_REF:before}}),/lost public root/);
}));
test('event history refuses missing, zero, self, unavailable and unrelated anchors',()=>historyFixture(({git,before,previous,commit})=>{
 commit({...previous,change:{reason:'unchanged allowance',previousSha256:sha(JSON.stringify(previous,null,2)+'\n')}});
 for(const event of ['push','pull_request']) {
  assert.throws(()=>historyBase({env:{GITHUB_EVENT_NAME:event}}),/needs TRUST_BASE_REF/);
  assert.throws(()=>historyBase({env:{GITHUB_EVENT_NAME:event,TRUST_BASE_REF:'0'.repeat(40)}}),/zero event SHA/);
  assert.throws(()=>historyBase({env:{GITHUB_EVENT_NAME:event,TRUST_BASE_REF:'HEAD'}}),/itself/);
 }
 assert.throws(()=>historyBase({env:{TRUST_BASE_REF:'not-a-ref'}}));
 const unrelated=git('commit-tree','HEAD^{tree}','-m','unrelated root');
 assert.throws(()=>historyBase({env:{TRUST_BASE_REF:unrelated}}));
 assert.equal(historyBase({env:{GITHUB_EVENT_NAME:'schedule'}}),before);
 assert.equal(historyBase({env:{GITHUB_EVENT_NAME:'workflow_dispatch'}}),before);
}));
test('initial root commit needs null predecessor without a self-comparison escape',()=>historyFixture(({previous,git,baseline})=>{
 assert.equal(historyBase({env:{}}),null);
 checkHistory(previous,{env:{}});
 const bad={...previous,change:{reason:'initial',previousSha256:'a'.repeat(64)}};
 writeFileSync(baseline,JSON.stringify(bad,null,2)+'\n');git('add','.');git('commit','--amend','-qm','bad initial');git('update-ref','refs/remotes/origin/master',git('rev-parse','HEAD'));
 assert.throws(()=>checkHistory(bad,{env:{}}),/null predecessor/);
}));

// Guards initial adoption and multi-commit PRs hiding bad intermediate history.
test('initial adoption checks each actual predecessor instead of final HEAD',()=>{
 const root=mkdtempSync(join(tmpdir(),'trust-initial-history-')),cwd=process.cwd();
 const git=(...args)=>execFileSync('git',args,{cwd:root,encoding:'utf8',stdio:['ignore','pipe','pipe']}).trim();
 try {
  git('init','-q');git('config','user.name','control');git('config','user.email','control@example.invalid');
  git('commit','--allow-empty','-qm','before baseline');const before=git('rev-parse','HEAD');
  mkdirSync(join(root,'scripts/trust'),{recursive:true});
  const path=join(root,'scripts/trust/trust-closure-baseline.json');
  const put=next=>{const text=JSON.stringify(next,null,2)+'\n';writeFileSync(path,text);git('add','.');git('commit','-qm','baseline revision');git('update-ref','refs/remotes/origin/master',git('rev-parse','HEAD'));return text;};
  const initial={...summarize(raw,()=>source),change:{reason:'initial',previousSha256:null}};
  const first=put(initial),firstCommit=git('rev-parse','HEAD');
  const grown={...initial,modules:[{module:'Control',lines:2}],change:{reason:'first growth',previousSha256:sha(first)}};
  const second=put(grown);
  process.chdir(root);
  const env={GITHUB_EVENT_NAME:'push',TRUST_BASE_REF:before};
  checkHistory(grown,{env});
  checkHistory(grown,{env:{GITHUB_EVENT_NAME:'pull_request',TRUST_BASE_REF:firstCommit}});
  const bad={...grown,modules:[{module:'Control',lines:3}],change:{reason:'second growth',previousSha256:sha(first)}};
  put(bad);assert.throws(()=>checkHistory(bad,{env}),/checksum/);
  assert.throws(()=>checkHistory(bad,{env:{GITHUB_EVENT_NAME:'pull_request',TRUST_BASE_REF:firstCommit}}),/checksum/);
  const fixed={...bad,change:{reason:'second growth',previousSha256:sha(second)}};
  writeFileSync(path,JSON.stringify(fixed,null,2)+'\n');git('add','.');git('commit','--amend','-qm','valid second growth');git('update-ref','refs/remotes/origin/master',git('rev-parse','HEAD'));
  checkHistory(fixed,{env});
  const lost={...fixed,roots:[]};put(lost);assert.throws(()=>checkHistory(lost,{env}),/lost public root/);
 } finally {process.chdir(cwd);rmSync(root,{recursive:true,force:true});}
});
