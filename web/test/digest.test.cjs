const {test}=require('node:test'),assert=require('node:assert/strict'),crypto=require('node:crypto');
const fs=require('node:fs'),os=require('node:os'),path=require('node:path'),{buildSync}=require('esbuild');
test('offline opaque workers hash distinct concurrent assets without WebCrypto',async()=>{
 const dir=fs.mkdtempSync(path.join(os.tmpdir(),'direct-hash-test-')),saved=Object.getOwnPropertyDescriptor(globalThis,'crypto');
 try{
  buildSync({entryPoints:[path.resolve(__dirname,'../browser/digest.mjs')],outfile:path.join(dir,'digest.cjs'),bundle:true,platform:'node',format:'cjs'});
  Object.defineProperty(globalThis,'crypto',{configurable:true,value:undefined});
  const {digest}=require(path.join(dir,'digest.cjs')),inputs=[Buffer.from('offline'),Buffer.from('verifier'),Buffer.alloc(65537,23)];
  assert.deepEqual(await Promise.all(inputs.map(digest)),inputs.map(x=>crypto.createHash('sha256').update(x).digest('hex')));
 }finally{if(saved)Object.defineProperty(globalThis,'crypto',saved);else delete globalThis.crypto;fs.rmSync(dir,{recursive:true,force:true});}
});
