// Reuse the existing numeric fixture checker with an off-git compiler cache.
// No cases, expected outputs, hashes, or compiler settings are changed.
import {readFileSync, writeFileSync, mkdtempSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join,resolve} from 'node:path';
import {pathToFileURL,fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
if(process.argv.length!==3) throw Error('usage: node scripts/check-feature-citations-solc.mjs SOLJSON.js');
const original=new URL('../tests/sol-numeric-literals/run-fixtures.mjs',import.meta.url);
const here=new URL('./',original),compiler=pathToFileURL(resolve(process.argv[2]));
const line="const here=new URL('./',import.meta.url), compiler=new URL('./runtime/.cache/soljson-v0.8.38.js',here);";
const source=readFileSync(original,'utf8');
if(source.split(line).length!==2) throw Error('existing fixture checker configuration changed');
const configured=source.replace(line,`const here=new URL(${JSON.stringify(here.href)}), compiler=new URL(${JSON.stringify(compiler.href)});`);
const dir=mkdtempSync(join(tmpdir(),'feature-citations-solc-'));
try {
 const file=join(dir,'run.mjs');writeFileSync(file,configured);
 const r=spawnSync(process.execPath,[file],{stdio:'inherit'});
 if(r.error) throw r.error;
 process.exitCode=r.status??1;
} finally {rmSync(dir,{recursive:true,force:true});}
