import {Buffer} from 'buffer';
import path from 'path-browserify';
import {sha256} from '@noble/hashes/sha256';

// A private in-memory platform for the unchanged compiler/frontend helpers.
// These adapters cannot access host files, open sockets or spawn processes.
export {Buffer};
export const files=new Map();
const directories=new Set(['/','/workspace','/output','/runtime','/runtime/scripts']);
export const process={argv:[],env:{SOLKEY_ROOT:'/runtime/solkey'},cwd:()=>'/workspace',platform:'browser'};
export function mkdirSync(name){for(let p=path.resolve(name);;p=path.dirname(p)){directories.add(p);if(p==='/')break;}}
export function writeFileSync(name,value){const file=path.resolve(name);mkdirSync(path.dirname(file));files.set(file,Buffer.from(value));}
export function readFileSync(name,encoding){const value=files.get(path.resolve(name));if(!value)throw new Error('Browser workspace file not found: '+name);return encoding?value.toString(typeof encoding==='string'?encoding:encoding.encoding):value;}
export const existsSync=name=>files.has(path.resolve(name))||directories.has(path.resolve(name));
export const realpathSync=name=>path.resolve(name);
export function statSync(name){const file=path.resolve(name);if(!existsSync(file))throw new Error('Unknown browser file');return {size:files.get(file)?.length||0,mtimeMs:0,isFile:()=>files.has(file),isDirectory:()=>directories.has(file),isSymbolicLink:()=>false};}
export function readdirSync(name,options){const root=path.resolve(name)+'/';const names=[...new Set([...files.keys(),...directories].filter(p=>p.startsWith(root)&&p!==root).map(p=>p.slice(root.length).split('/')[0]))];return options?.withFileTypes?names.map(name=>({name,isDirectory:()=>directories.has(root+name),isFile:()=>files.has(root+name),isSymbolicLink:()=>false})):names;}
export function rmSync(name){files.delete(path.resolve(name));}
export function createHash(algorithm){if(algorithm!=='sha256')throw new Error('Unsupported browser digest');const hash=sha256.create();return {update(value){hash.update(typeof value==='string'?new TextEncoder().encode(value):value);return this;},digest(encoding){const bytes=Buffer.from(hash.digest());return encoding?bytes.toString(encoding):bytes;}};}
export function createRequire(){return name=>{if(String(name).endsWith('soljson-v0.8.34+commit.80d5c536.js'))return globalThis.Module;throw new Error('Module is not bundled for the browser: '+name);};}
export function execFileSync(){throw new Error('Child processes are unavailable in the browser');}
export const fileURLToPath=url=>decodeURIComponent(new URL(url).pathname);
export const pathToFileURL=file=>new URL('file://'+path.resolve(file));
export const {resolve,join,dirname,basename,extname,isAbsolute,relative,normalize,parse,sep,posix}=path;
export const fs={readFileSync,writeFileSync,mkdirSync,existsSync,realpathSync,statSync,readdirSync,rmSync};
