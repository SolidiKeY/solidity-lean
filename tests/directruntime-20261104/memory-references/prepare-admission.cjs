// Only restore signed builtin IDs as the repository compiler transport does.
// These are developer test inputs; no source equivalence or proof is asserted.
const fs=require('node:fs'),path=require('node:path'),crypto=require('node:crypto');
const root=__dirname, hash=b=>crypto.createHash('sha256').update(b).digest('hex');
const normalize=x=>{
 if(Array.isArray(x)) return x.map(normalize);
 if(x&&typeof x==='object') return Object.fromEntries(Object.entries(x).map(([k,v])=>[k,k==='referencedDeclaration'&&Number.isInteger(v)&&v>=2**31?v-2**32:normalize(v)]));
 return x;
};
const rows=JSON.parse(fs.readFileSync(path.join(root,'manifest.json'))).cases.map(r=>({input:r.output,accept:true,typed:true,initialModelHalt:r.initialModelHalt,id:r.id}));
for(const f of fs.readdirSync(path.join(root,'malformed')).filter(f=>f.endsWith('.output.json'))) rows.push({input:'malformed/'+f,accept:false,id:f});
for(const f of fs.readdirSync(path.join(root,'type-errors')).filter(f=>f.endsWith('.output.json'))) rows.push({input:'type-errors/'+f,accept:true,typed:false,id:f});
const evidence=[];
for(const row of rows) {
 const bytes=fs.readFileSync(path.join(root,row.input));
 const out=Buffer.from(JSON.stringify(normalize(JSON.parse(bytes)))+'\n');
 const destination='runtime/admission/'+row.input;
 fs.mkdirSync(path.dirname(path.join(root,destination)),{recursive:true});fs.writeFileSync(path.join(root,destination),out);
 evidence.push({...row,path:destination,rawSha256:hash(bytes),normalizedSha256:hash(out)});
}
fs.writeFileSync(path.join(root,'evidence/admission-inputs.json'),JSON.stringify(evidence,null,2)+'\n');
console.log(`Prepared ${evidence.length} admission inputs; raw/normalized hashes recorded; no verdicts`);
