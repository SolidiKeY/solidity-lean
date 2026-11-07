// Optional native test recordings are never replaced with injected success.
'use strict';
const fs=require('node:fs'),path=require('node:path'),{inputPresent}=require('../parity/input-presence.cjs');
function recordings(files,root=path.resolve(__dirname,'../..')){
 const present=files.map(file=>inputPresent(file,root));
 if(present.every(value=>!value))return null;
 if(present.some(value=>!value))throw Error('Incomplete native recording inputs: '+files.join(', '));
 return files.map(file=>fs.readFileSync(file,'utf8'));
}
module.exports={recordings};
