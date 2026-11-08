// Injected ARIA ancestry controls; actual native replay is separate evidence.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{assertRenderedTree}=require('../parity/hierarchy-lifecycle.cjs');
const metadata={visible:true,binding:{uri:'file:///tmp/Hierarchy.sol'}};
function fixture(){return{rootClass:'test-explorer',rootVisible:true,activeUri:metadata.binding.uri,toolbar:[{label:'More Filters...'}],rows:[['Hierarchy.sol','1','true'],['Base','2','true'],['f','3',null],['f','3',null],['Derived','2','true'],['g','3',null]].map(([label,level,expanded])=>({label,level,expanded}))};}
test('Testing labels require actual ordered owned ARIA ancestry and expanded parents',()=>{
 assert.equal(assertRenderedTree(fixture(),metadata).rows.length,6);
 for(const mutate of [v=>v.rows.forEach(r=>r.level='1'),v=>v.rows.forEach(r=>delete r.level),v=>v.rows[5].level='2',v=>[v.rows[2],v.rows[4]]=[v.rows[4],v.rows[2]],v=>v.rows[1].expanded='false',v=>v.rows[2].expanded='true',v=>v.rows.push({...v.rows[0]})]){const v=fixture();mutate(v);assert.throws(()=>assertRenderedTree(v,metadata));}
});
test('another file subtree cannot supply missing owned declarations; unrelated subtrees remain separate',()=>{
 const v=fixture();v.rows.splice(1,0,{label:'Other.sol',level:'1',expanded:'true'});assert.throws(()=>assertRenderedTree(v,metadata));const good=fixture();good.rows.push({label:'Other.sol',level:'1',expanded:'true'},{label:'Other',level:'2',expanded:'true'});assert.equal(assertRenderedTree(good,metadata),good);
});
test('hidden current source file row is stale even when declaration labels disappeared',()=>{
 const v=fixture();v.rows=[v.rows[0]];assert.throws(()=>assertRenderedTree(v,{...metadata,visible:false}));v.rows=[{label:'Other.sol',level:'1',expanded:'true'}];assert.equal(assertRenderedTree(v,{...metadata,visible:false}),v);
});

test('malformed or numeric ARIA levels cannot terminate the source-label subtree',()=>{
 for(const level of [null,undefined,'','0','-1',1,0,-1]){const v=fixture();v.rows.push({label:'Unexpected',level,expanded:null});assert.throws(()=>assertRenderedTree(v,metadata));}
});
