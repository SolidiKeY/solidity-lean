'use strict';
const fs=require('node:fs');
const {resolve,relative,dirname,isAbsolute,posix}=require('node:path');
const {createHash}=require('node:crypto');
const {imports}=require('./solidity-text.cjs');
const hash=text=>createHash('sha256').update(text).digest('hex');
const identity=path=>fs.existsSync(path)?fs.realpathSync(path):resolve(path);
const slash=p=>p.replaceAll('\\','/');
const inside=(root,path)=>{const r=relative(root,path);return r===''||!r.startsWith('..')&&!isAbsolute(r);};

/** Resolve a finite original compilation unit, preserving every source identity.
 * Open editor buffers override disk; no source is concatenated or rewritten. */
function snapshot(source,text,configuration={},documents=[]){
  const root=resolve(configuration.projectRoot||dirname(source));
  const includePaths=(configuration.includePaths||[]).map(p=>resolve(root,p));
  const roots=[root,...includePaths];
  const remappings=(configuration.remappings||[]).map((r,index)=>{
    const at=r.indexOf('=');if(at<1)throw new Error('Invalid Solidity remapping: '+r);
    const head=r.slice(0,at),colon=head.indexOf(':');
    return {context:colon<0?'':head.slice(0,colon),prefix:colon<0?head:head.slice(colon+1),target:slash(r.slice(at+1)),original:r,index};
  });
  const open=new Map();for(const doc of documents){const key=identity(doc.path),old=open.get(key);if(old&&old.text!==doc.text)throw new Error('Conflicting open buffers for aliased Solidity source: '+doc.path);open.set(key,doc);}
  open.set(identity(source),{...open.get(identity(source)),path:resolve(source),text});
  const mainSource=slash(relative(root,resolve(source))),files=Object.create(null),sources=Object.create(null);let size=0;
  const visit=(name,path)=>{
    if(sources[name])return;
    const actual=fs.existsSync(path)?fs.realpathSync(path):resolve(path);
    if(!roots.some(r=>inside(fs.existsSync(r)?fs.realpathSync(r):r,actual)))throw new Error('Import is outside configured project/include roots: '+name);
    const doc=open.get(actual);const bytes=doc?Buffer.from(doc.text):fs.readFileSync(path);
    const content=new TextDecoder('utf-8',{fatal:true,ignoreBOM:true}).decode(bytes);
    size+=bytes.length;if(size>16*1024*1024||Object.keys(sources).length>=256)throw new Error('Compilation unit exceeds 256 files or 16 MiB');
    sources[name]={content};files[name]={path:doc?.path??resolve(path),canonicalPath:actual,text:content,version:doc?.version,hash:hash(content)};
    for(const spelling of imports(content)){
      let key=spelling;
      if(spelling.startsWith('.'))key=posix.normalize(posix.join(posix.dirname(name),spelling));
      const rule=remappings.filter(r=>key.startsWith(r.prefix)&&name.startsWith(r.context)).sort((a,b)=>b.context.length-a.context.length||b.prefix.length-a.prefix.length||b.index-a.index)[0];if(rule)key=rule.target+key.slice(rule.prefix.length);
      const candidates=[resolve(root,key),...includePaths.map(p=>resolve(p,key))];
      const target=candidates.find(p=>open.has(identity(p))||fs.existsSync(p));if(!target)throw new Error('Cannot resolve Solidity import '+spelling+' from '+name);
      visit(slash(key),target);
    }
  };
  visit(mainSource,resolve(source));
  const digest=hash(JSON.stringify(Object.entries(files).map(([name,f])=>[name,f.path,f.hash]).sort()));
  return {mainSource,sources,files,digest,remappings:remappings.map(r=>r.original)};
}
function current(project,documents=[],checkVersions=false){
  const open=new Map();for(const doc of documents){const key=identity(doc.path);if(open.has(key)&&open.get(key)!==doc.text)return false;open.set(key,doc.text);}
  const versions=new Map(documents.map(d=>[identity(d.path),d.version]));
  return Object.values(project.files).every(file=>{try{return (!checkVersions||versions.get(identity(file.path))===file.version)&&hash(open.get(identity(file.path))??fs.readFileSync(file.path))===file.hash;}catch{return false;}});
}
module.exports={snapshot,current,hash,identity};
