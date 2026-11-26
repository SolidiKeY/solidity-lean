import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,readFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {encodeSource,decodeSource,resultHtml,highlight} from '../../site/playground.mjs';
import {exportPlayground,playgroundAssets} from './export.mjs';
test('export includes the complete offline shell and picker sources',()=>{
  const dir=mkdtempSync(join(tmpdir(),'playground-export-'));
  try { exportPlayground(dir);for(const file of playgroundAssets)assert.equal(readFileSync(join(dir,file),'utf8'),readFileSync(new URL('../../site/'+file,import.meta.url),'utf8'));assert.ok(JSON.parse(readFileSync(join(dir,'examples.json'))).playground[0].source.includes('contract Identity')); }
  finally {rmSync(dir,{recursive:true,force:true});}
});
test('compressed URL round trip includes Unicode and fragment characters',async()=>{
  const source='// λ 💡 # &= +\ncontract Test {}\n'.repeat(100);
  const hash=await encodeSource(source);assert.match(hash,/^#source=[A-Za-z0-9_-]+$/);assert.ok(hash.length<source.length);assert.equal(await decodeSource(hash),source);assert.equal(await decodeSource(''),null);assert.equal(await decodeSource(await encodeSource('')),'');
  await assert.rejects(decodeSource('#source=bad!'));await assert.rejects(decodeSource('#source=aaaa'));await assert.rejects(encodeSource('a'.repeat(1048577)));
});
test('results preserve unknown statuses and escape model values and function names',()=>{
  const html=resultHtml({results:[{function:'<script>',status:'proved'},{function:'bad',status:'refuted',counterexample:{arguments:[{value:'<img>'}]}},{function:'pending',status:'unsupported',reason:'<unsafe>'}],errors:[{reason:'<error>'}]});
  assert.match(html,/: proved/);assert.match(html,/: wrong/);assert.match(html,/: unknown/);assert.match(html,/&lt;img&gt;/);assert.doesNotMatch(html,/<script>|<unsafe>|<error>/);assert.match(resultHtml({results:[]}),/Unknown/);
});
test('highlighting preserves escaped source and marks source lines',()=>{
  const html=highlight('contract X {\n // <script>\n}',{start:{line:1,character:0},end:{line:1,character:8}});assert.match(html,/class="kw">contract/);assert.match(html,/line marked/);assert.match(html,/&lt;script&gt;/);assert.equal((html.match(/class="no"/g)||[]).length,3);
});
