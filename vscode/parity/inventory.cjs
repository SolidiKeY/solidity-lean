// H44: citations stay tracked; executable readers require the exact full payload.
'use strict';
const fs=require('node:fs'),path=require('node:path'),{createHash,randomUUID}=require('node:crypto');
const root=path.resolve(__dirname,'../..'),descriptorPath=path.join(root,'docs/dafny-editor-features.json');
const hash=bytes=>createHash('sha256').update(bytes).digest('hex');
const ids=value=>[...(value.features||[]),...(value.mechanical?.rows||[])].map(row=>row.id);
function read(descriptor=descriptorPath,repo=root){
 const data=JSON.parse(fs.readFileSync(descriptor,'utf8')),entry=data.inventory;
 if(data.schemaVersion!==1||data.kind!=='external-dafny-parity-inventory'||!entry||!/^tests\/editor-parity\/inventory\/[^/]+\.json$/.test(entry.path)||!Number.isSafeInteger(entry.bytes)||entry.bytes<1||!/^[a-f0-9]{64}$/.test(entry.sha256))throw Error('Invalid tracked parity inventory digest');
 const file=path.resolve(repo,entry.path),base=path.resolve(repo);let bytes;
 try{const real=fs.realpathSync(file);if(!real.startsWith(base+path.sep))throw Error('Escaping parity inventory path');bytes=fs.readFileSync(real);}
 catch(error){throw Error('Full parity inventory unavailable: '+file+'. Restore the checksum-bound bundle: '+data.restoreCommand+'; cause: '+error.message);}
 if(bytes.length!==entry.bytes||hash(bytes)!==entry.sha256)throw Error('Parity inventory checksum/size mismatch: '+file+'; preserve changed bytes and reconcile the tracked digest; no fallback inventory accepted');
 const inventory=JSON.parse(bytes),features=inventory.features?.length,mechanical=inventory.mechanical?.rows?.length;
 if(!Number.isSafeInteger(features)||!Number.isSafeInteger(mechanical)||features!==entry.features||mechanical!==entry.mechanicalRows||ids(inventory).length!==entry.rows)throw Error('Parity inventory count mismatch');
 return {inventory,data,file};
}
function loadInventory(descriptor=descriptorPath,repo=root){return read(descriptor,repo).inventory;}
// Offline CI may validate the committed transport contract, never substitute it for rows.
// A present, corrupt or escaping payload still goes through the strict loader.
function checkOffline(descriptor=descriptorPath,repo=root){
 const data=JSON.parse(fs.readFileSync(descriptor,'utf8')),entry=data.inventory;
 if(data.schemaVersion!==1||data.kind!=='external-dafny-parity-inventory'||!entry||!/^tests\/editor-parity\/inventory\/[^/]+\.json$/.test(entry.path)||!Number.isSafeInteger(entry.bytes)||entry.bytes<1||!/^[a-f0-9]{64}$/.test(entry.sha256)||![entry.features,entry.mechanicalRows,entry.rows].every(n=>Number.isSafeInteger(n)&&n>0)||entry.features+entry.mechanicalRows!==entry.rows)throw Error('Invalid tracked parity inventory digest');
 if(require('./input-presence.cjs').inputPresent(path.resolve(repo,entry.path),repo))return {mode:'full',...read(descriptor,repo)};
 if(!/^docs\/[^/]+\.json$/.test(data.restoreManifest||''))throw Error('Invalid parity restore manifest path');
 const manifestFile=fs.realpathSync(path.resolve(repo,data.restoreManifest));if(!manifestFile.startsWith(path.resolve(repo)+path.sep))throw Error('Escaping parity restore manifest');
 const manifest=JSON.parse(fs.readFileSync(manifestFile,'utf8'));
 if(manifest.schemaVersion!==1||manifest.fileCount!==1||manifest.rawInventory?.bytes!==entry.bytes||manifest.rawInventory?.sha256!==entry.sha256||manifest.uncompressedBytes!==entry.bytes||manifest.rowCount!==entry.rows||!Number.isSafeInteger(manifest.frozenRowCount)||manifest.frozenRowCount<1||manifest.frozenRowCount>entry.rows||!/^[a-f0-9]{64}$/.test(manifest.frozenSha256||'')||![manifest.archive,manifest.index].every(x=>x&&Number.isSafeInteger(x.bytes)&&x.bytes>0&&/^[a-f0-9]{64}$/.test(x.sha256)))throw Error('Committed parity digest/restore manifest mismatch');
 return {mode:'digest-only',data,file:path.resolve(repo,entry.path)};
}

function saveInventory(inventory,descriptor=descriptorPath,repo=root){
 const previous=read(descriptor,repo),oldIds=ids(previous.inventory),nextIds=ids(inventory);
 if(new Set(nextIds).size!==nextIds.length||oldIds.some(id=>!nextIds.includes(id)))throw Error('Refusing inventory shrinkage or duplicate IDs');
 const bytes=Buffer.from(JSON.stringify(inventory,null,2)+'\n');
 const data={...previous.data,inventory:{...previous.data.inventory,bytes:bytes.length,sha256:hash(bytes),rows:nextIds.length,features:inventory.features.length,mechanicalRows:inventory.mechanical.rows.length}};
 // A crash between replacements fails the checksum check; it never accepts stale data.
 const replace=(file,bytes)=>{const temp=file+'.'+randomUUID()+'.tmp';fs.writeFileSync(temp,bytes);fs.renameSync(temp,file);};
 replace(previous.file,bytes);replace(descriptor,JSON.stringify(data,null,2)+'\n');
}
module.exports={loadInventory,saveInventory,checkOffline};
