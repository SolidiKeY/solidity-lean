#!/usr/bin/env python3
"""Enumerate grammar fixtures independently of the Lean parser implementation.
Run under the repository writer lock. Generated source identities are explicit.
"""
import hashlib,itertools,json,pathlib
area=pathlib.Path(__file__).resolve().parent
fixtures=[]
def add(name,body,expect,clauses,parameter_context=False):
    path=area/'fixtures'/('positive' if expect else 'negative')/(name+'.sol')
    path.parent.mkdir(parents=True,exist_ok=True)
    type_sources=body['types'] if isinstance(body,dict) else None
    body=body['body'] if isinstance(body,dict) else body
    src='// SPDX-License-Identifier: UNLICENSED\npragma solidity 0.8.38;\ncontract C {\n'+body+'\n}\n'
    path.write_text(src)
    fixtures.append(dict(id=name,file=str(path.relative_to(area)),expect_accept=expect,clauses=clauses,sha256=hashlib.sha256(src.encode()).hexdigest()))
    if type_sources is not None:fixtures[-1]['type_sources']=type_sources
def fields(types):return {'body':'\n'.join(t+' v'+str(i)+';' for i,t in enumerate(types)), 'types':types}
elementary=['address','address payable','bool','string','bytes']
elementary += [sign+str(bits) for sign in ['int','uint'] for bits in range(8,257,8)]
elementary += ['bytes'+str(n) for n in range(1,33)]
elementary += ['fixed','ufixed']
elementary += [sign+str(bits)+'x'+str(digits) for sign in ['fixed','ufixed'] for bits in range(8,257,8) for digits in range(81)]
add('elementary-all-dimensions',fields(elementary+['int','uint']),True,['elem:all8families','integer:all64widths','fixedBytes:all32lengths','fixed:all5184dimensions+2aliases','integer:2aliases'])
keys=[e for e in elementary if e!='address payable']
add('mapping-all-elementary-keys',fields(['mapping('+key+' => bool)' for key in keys]),True,['mapping:key.elem:notPayable:all5286spellings'])
add('qualified-paths',fields(['A','A.B','A.B.C.D']),True,['userType:head','userType:tail:multiple','SOL-QN:unresolved-is-parsing-only'])
mappings=['mapping('+key+kn+' => '+value+vn+')' for key in ['bool','A.B'] for kn in ['',' key'] for vn in ['',' value'] for value in ['uint','A.B','uint[][N+1]','mapping(address=>bool)','function(uint memory x) external view returns(bool y)']]
add('mapping-names-values',fields(mappings),True,['mapping:key.elem','mapping:key.path','mapping:keyName:none+some','mapping:valueName:none+some','mapping:value:all5constructors','mapping:nested-boundary'])
vis=['internal','external','private','public'];mut=['pure','view','payable']
attrs=['']+vis+mut+[v+' '+m for v in vis for m in mut]+[m+' '+v for v in vis for m in mut]
params=['']+['uint'+loc+name for loc in ['',' memory',' storage',' calldata'] for name in ['',' p']]
returns=['']+[' returns (bool'+loc+name+')' for loc in ['',' memory',' storage',' calldata'] for name in ['',' r']]
fn=['function ('+p+')'+(' '+a if a else '')+r for a,p,r in itertools.product(attrs,params,returns)]
add('function-layouts-params-returns',fields(fn),True,['fnType:all32attributevalues+orders','params:nil+cons','param:location:none+all3','param:name:none+some','returns:nil+cons','return:location:none+all3','return:name:none+some'])
arrays=['bool[]','bool[17]','A.B[][N+1][]','mapping(uint key=>function(uint[] memory x) internal returns(mapping(address a=>bool b)) value)[][f(1,2)]','function(mapping(A.B k=>uint[] v) storage x,function() external cb) internal view returns(function(uint calldata y) external pure,uint[][N])[][1+2*3][]']
arrays+=['bool'+'[]'*n for n in [1,2,8,32]]
add('nested-arrays-functions-mappings',fields(arrays),True,['array:dynamic','array:static:readOnlyAtoms','array:base:all5constructors','param:list:multiple','return:list:multiple','boundary:nestedMappingFunctionArray','boundary:atom-call-comma','boundary:depth32'])
neg={
'payable-mapping-key':'mapping(address payable=>bool) x;',
'array-mapping-key':'mapping(uint[]=>bool) x;',
'function-mapping-key':'mapping(function()=>bool) x;',
'mapping-mapping-key':'mapping(mapping(uint=>bool)=>bool) x;',
'mapping-missing-arrow':'mapping(uint bool) x;',
'mapping-two-key-names':'mapping(uint a b=>bool) x;',
'mapping-two-value-names':'mapping(uint=>bool a b) x;',
'mapping-missing-close':'mapping(uint=>bool x;',
'array-missing-close':'uint[1 x;',
'array-length-comma':'uint[1,2] x;',
'function-trailing-param-comma':'function(uint,) internal x;',
'function-leading-param-comma':'function(,uint) internal x;',
'function-empty-returns':'function() returns() x;',
'function-repeat-mutability':'function() view pure x;',
'function-repeat-visibility':'function accept(function() internal external cb) external {}',
'parameter-repeat-location':'function(uint memory storage p) internal x;',
'return-trailing-comma':'function() returns(uint,) x;',
'qualified-trailing-period':'function bad(A. ) external {}',
'qualified-double-period':'A..B x;',
'qualified-keyword-part':'A.bool x;',
'function-missing-close':'function(uint x;',
'array-wrong-close':'uint[1) x;',
'function-wrong-close':'function(uint} x;'
}
for name,body in neg.items():
    add(name,body,False,['negative:'+name])
    fixtures[-1]['type_source'] = {'function-repeat-visibility':'function() internal external','qualified-trailing-period':'A.'}.get(name,body[:-3])

manifest=dict(compiler=dict(version='0.8.38+commit.1835d247.Emscripten.clang',filename='soljson-v0.8.38+commit.1835d247.js',sha256='6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390'),phase='parsing',proof_boundary='External solc syntax fixtures only; no Lean proof, name resolution, constant evaluation, type admission, lowering or compiler equivalence.',expected_type_nodes=['ElementaryTypeName','UserDefinedTypeName','ArrayTypeName','Mapping','FunctionTypeName'],enumeration=dict(elementary_spellings=len(elementary),mapping_elementary_keys=len(keys),function_attribute_variants=len(attrs),function_parameter_variants=len(params),function_return_variants=len(returns),function_cross_product=len(fn)),fixtures=fixtures)
(area/'fixtures.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Generated',len(fixtures),'fixtures;',manifest['enumeration'])
