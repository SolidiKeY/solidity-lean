// Refuse incomplete artifact snapshots when a runtime ignores recursive enumeration.
'use strict';
const fs=require('node:fs'),path=require('node:path');
function recursiveCapability(directory,io=fs){
 const owned=io.mkdtempSync(path.join(directory,'.parity-fs-'));try{io.mkdirSync(path.join(owned,'nested'));io.writeFileSync(path.join(owned,'nested','sentinel'),'owned capability probe');const names=io.readdirSync(owned,{recursive:true});if(!names.includes(path.join('nested','sentinel')))throw Object.assign(Error('Native parity requires recursive fs.readdirSync support; nested artifact enumeration was not confirmed'),{code:'PARITY_FS_CAPABILITY'});return{node:process.version,feature:'fs.readdirSync recursive',confirmed:true};}finally{io.rmSync(owned,{recursive:true,force:true});}
}
module.exports={recursiveCapability};
