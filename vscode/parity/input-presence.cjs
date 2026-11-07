// An absent optional input must not hide partial transport or broken/escaping links.
'use strict';
const fs=require('node:fs'),path=require('node:path');
function inputPresent(file,root){
 const base=path.resolve(root),absolute=path.resolve(file),relative=path.relative(base,absolute);
 if(!relative||relative==='..'||relative.startsWith('..'+path.sep)||path.isAbsolute(relative))throw Error('Unsafe input path');
 const baseStat=fs.lstatSync(base);if(baseStat.isSymbolicLink()||!baseStat.isDirectory())throw Error('Unsafe input root');
 let current=base;const parts=relative.split(path.sep);
 for(let i=0;i<parts.length;i++){
  current=path.join(current,parts[i]);let stat;
  try{stat=fs.lstatSync(current);}catch(error){if(error.code==='ENOENT')return false;throw error;}
  if(stat.isSymbolicLink())throw Error('Unsafe symbolic input path: '+current);
  if(i<parts.length-1?!stat.isDirectory():!stat.isFile())throw Error('Unsafe input path type: '+current);
 }
 return true;
}
module.exports={inputPresent};
