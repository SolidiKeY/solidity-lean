import test from 'node:test';
import assert from 'node:assert/strict';
import {readFile, access} from 'node:fs/promises';
import {runtimePath, decode, transport} from './transport.mjs';
const ir = 'object "C" { code { } object "C_deployed" { code { stop() } } }';
const request = {ir,calldata:'0x12345678',slots:['0','1'],initialStorage:['0','9']};
const ok = JSON.stringify({status:'ok',reverted:true,returnData:'0011',storage:[['0','0'],['1','9']]});
test('runtime selection ignores comments and strings and refuses ambiguity',()=>{
  assert.equal(runtimePath('// object "bad_deployed" {}\n'+ir),'C_deployed');
  assert.equal(runtimePath(ir.replace('stop()', 'pop("object fake_deployed")')),'C_deployed');
  assert.throws(()=>runtimePath('object "C_deployed" { code {} }'));
  assert.throws(()=>runtimePath(ir.replace('code { }','code { } object "D_deployed" { code {} }')));
  assert.throws(()=>runtimePath('object "C" {code{}}'));
});
test('response preserves revert bytes and rejects incomplete observations',()=>{
  assert.deepEqual(decode(ok),{status:'ok',observation:{failed:true,returnData:'0x0011',slots:['0','1'],storage:['0','9']}});
  assert.equal(decode('{"status":"error","error":"fuel exhausted"}').status,'blocked');
  for (const patch of [{reverted:0},{returnData:'0x11'},{storage:[['1','9'],['0','0']]},{storage:[['0',String(2n**256n)],['1','0']]}])
    assert.throws(()=>decode(JSON.stringify({...JSON.parse(ok),...patch})));
});
test('transport passes exact IR, selected child, input, resource limits and cleans temporary file',async()=>{
  let file;
  const lean=transport({executable:'/explicit/driver',invoke:async(exe,args,options)=>{
    assert.equal(exe,'/explicit/driver'); file=args[0];
    assert.equal(await readFile(file,'utf8'),ir);
    assert.deepEqual(args.slice(1),['C_deployed','10000','4096','12345678','0=0,1=9']);
    assert.equal(options.env.LEAN_NUM_THREADS,'1'); assert.equal(options.timeout,60000);
    return {stdout:ok};
  }});
  assert.equal((await lean(request)).status,'ok');
  await assert.rejects(access(file));
});
test('refusals and process failures never become agreement',async()=>{
  for (const error of [Object.assign(Error('exit'),{code:1,stdout:ok}),Object.assign(Error('timeout'),{code:1,killed:true,stdout:ok}),Error('spawn')]) {
    const lean=transport({executable:'driver',invoke:async()=>{throw error}});
    assert.equal((await lean(request)).status,'blocked');
  }
  const lean=transport({executable:'driver',invoke:async()=>{throw Object.assign(Error('exit'),{code:1,stdout:'{"status":"error","error":"unsupported"}'})}});
  assert.deepEqual(await lean(request),{status:'blocked',reason:'unsupported'});
  await assert.rejects(lean({...request,initialStorage:['-1','0']}));
});

test('driver cannot exceed configured return-data limit',async()=>{
  const lean=transport({executable:'driver',outputLimit:1,invoke:async()=>({stdout:ok})});
  await assert.rejects(lean(request),/exceeds output limit/);
});
test('checkout TMPDIR is rejected before creating temporary IR',async()=>{
  const before=process.env.TMPDIR;
  process.env.TMPDIR=process.cwd();
  try {
    const lean=transport({executable:'driver',invoke:async()=>{throw Error('must not invoke')}});
    await assert.rejects(lean(request),/outside checkout/);
  } finally { if(before===undefined) delete process.env.TMPDIR; else process.env.TMPDIR=before; }
});
