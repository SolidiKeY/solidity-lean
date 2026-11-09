
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),os=require('node:os'),path=require('node:path'),{spawn}=require('node:child_process');
const {processState}=require('../src/process-state.cjs');
const root=path.resolve(__dirname,'../..'),wrapper=path.join(root,'vscode/parity/mcp-stdio.py');
function bounded(promise,label){let timer;return Promise.race([promise,new Promise((_,reject)=>{timer=setTimeout(()=>reject(Error(label+' deadline')),1000);})]).finally(()=>clearTimeout(timer));}
function line(child,expected){return new Promise((resolve,reject)=>{let data='';const clean=()=>{clearTimeout(timer);child.stdout.off('data',read);child.off('exit',exit);};const read=b=>{data+=b;if(data.includes(expected)){clean();resolve();}},exit=()=>{clean();reject(Error('fixture exited before '+expected));};const timer=setTimeout(()=>{clean();reject(Error('fixture '+expected+' deadline'));},1000);child.stdout.on('data',read);child.once('exit',exit);});}
// Injected stdio module, not Lean/native closure evidence. All accepted close
// waits retain1000ms; deadline failures still force and confirm owned cleanup.
for(const mode of ['default','wrapped','double-term','hung-control'])test('MCP SIGTERM '+mode,async()=>{
 const dir=fs.mkdtempSync(path.join(os.tmpdir(),'mcp-finally-')),marker=path.join(dir,'closed'),release=path.join(dir,'release');
 fs.mkdirSync(path.join(dir,'lean_lsp_mcp'));fs.writeFileSync(path.join(dir,'lean_lsp_mcp','__init__.py'),'');
 const pause=mode==='double-term'?` print('CLEANUP',flush=True)\n while not pathlib.Path(${JSON.stringify(release)}).exists(): time.sleep(.01)\n`:'';
 const source=mode==='hung-control'?`import signal,time\nsignal.signal(signal.SIGTERM,signal.SIG_IGN)\nprint('READY',flush=True)\nwhile True: time.sleep(.01)\n`:`import pathlib,time\ntry:\n print('READY',flush=True)\n while True: time.sleep(.01)\nexcept KeyboardInterrupt: pass\nfinally:\n${pause} pathlib.Path(${JSON.stringify(marker)}).write_text('finally')\n`;
 fs.writeFileSync(path.join(dir,'lean_lsp_mcp','__main__.py'),source);
 const wrapped=mode!=='default',code=`import sys,runpy;sys.path.insert(0,${JSON.stringify(dir)});`+(wrapped?`runpy.run_path(${JSON.stringify(wrapper)},run_name='__main__')`:`runpy.run_module('lean_lsp_mcp',run_name='__main__')`);
 const child=spawn('python3',['-c',code],{stdio:['ignore','pipe','pipe']});const birth=processState(child.pid)?.birth;const signal=name=>{if(process.platform==='linux'){const state=processState(child.pid);if(!state)return false;assert.ok(birth,'missing owned process birth');assert.equal(state.birth,birth,'owned process identity changed');}return child.kill(name);};let stderr='';child.stderr.on('data',b=>stderr+=b);
 const closed=new Promise((resolve,reject)=>{child.once('error',reject);child.once('close',(code,signal)=>resolve({code,signal}));});
 try{
  await line(child,'READY');
  const cleanup=mode==='double-term'?line(child,'CLEANUP'):null;
  assert.equal(signal('SIGTERM'),true);
  if(cleanup){await cleanup;assert.equal(signal('SIGTERM'),true);await new Promise(resolve=>setTimeout(resolve,20));fs.writeFileSync(release,'release');}
  if(mode==='hung-control'){await assert.rejects(bounded(closed,'close'),/close deadline/);assert.equal(fs.existsSync(marker),false);return;}
  const result=await bounded(closed,'close');assert.equal(fs.existsSync(marker),wrapped,stderr);
  if(wrapped)assert.deepEqual(result,{code:0,signal:null});else assert.equal(result.signal,'SIGTERM');
 }finally{
  if(child.exitCode===null&&child.signalCode===null)assert.equal(signal('SIGKILL'),true);
  await bounded(closed,'forced cleanup close');fs.rmSync(dir,{recursive:true,force:true});
 }
});
