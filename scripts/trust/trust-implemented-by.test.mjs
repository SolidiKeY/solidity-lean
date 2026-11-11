// Regression guards: an inventory baseline must never excuse a missing link,
// and an unimported source escape must not disappear from the kernel census.
import {test} from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,writeFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {sourceAttributes,reconcile,requireLinks} from './trust-implemented-by.mjs';
const row={module:'Control',declaration:'Control.logical',implementation:'Control.compiled',extern:false,links:['Control.logical_eq_compiled']};
const src={module:'Control',kind:'implemented_by'};
test('missing and external links fail',()=>{
 assert.throws(()=>requireLinks([{...row,links:[]}]),/missing/);
 assert.throws(()=>requireLinks([{...row,extern:true}]),/missing/);
 requireLinks([row]);
});
test('source census cannot vanish from imports',()=>{
 assert.throws(()=>reconcile([], [src]),/empty/);
 assert.throws(()=>reconcile([row],[src,src]),/mismatch/);
 assert.throws(()=>reconcile([row,row],[src]),/duplicate/);
 assert.equal(reconcile([row],[src]).length,1);
});
test('base source inventory is nonempty',()=>assert.ok(sourceAttributes().length>0));

test('nested attribute brackets cannot hide a new source escape',()=>{
 const dir=mkdtempSync(join(tmpdir(),'trust-attribute-'));
 try{writeFileSync(join(dir,'Control.lean'),'@[other_attr [0], implemented_by twin]\ndef logical := 0\n');
  const rows=sourceAttributes(dir);assert.equal(rows.length,1);assert.equal(rows[0].kind,'implemented_by');
 }finally{rmSync(dir,{recursive:true,force:true});}
});

test('compiler-generated bridges stay inventoried and never excuse missing links',()=>{
 const generated={module:'Generated',declaration:'Generated.f.unsafe_impl_3',implementation:'Generated.f.unsafe_1',
  opaque:true,unsafe:false,implementationUnsafe:true,extern:false,links:[]};
 const rows=reconcile([{...row},generated],[src]);
 assert.equal(rows.find(r=>r.declaration===generated.declaration).compilerGenerated,true);
 assert.throws(()=>requireLinks(rows),/missing/);
 assert.throws(()=>reconcile([{...row},{...generated,unsafe:true}],[src]),/mismatch/);
});
