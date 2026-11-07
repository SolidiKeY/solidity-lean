import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFileSync, writeFileSync} from 'node:fs';
import {createRequire} from 'node:module';
import {COMPILERS} from '../../scripts/solc-unit.mjs';

const pin = COMPILERS.find(p => p.version.startsWith('0.8.38+'));
const compilerPath = '/workspace/.setup/soljson/' + pin.file;
const sha = x => createHash('sha256').update(x).digest('hex');
assert.equal(sha(readFileSync(compilerPath)), pin.sha256);
const solc = createRequire(import.meta.url)(compilerPath);
assert.equal(solc.cwrap('solidity_version', 'string', [])(), pin.version);
const compile = solc.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);
const settings = {stopAfter:'parsing', outputSelection:{'*':{'':['ast']}}};
const observations = [];
const cases = [];
const add = (id, expression, expected) => cases.push({id, expression, expected});
const ops = ['||','&&','==','<','|','^','&','<<','+','*','**'];
for (let i=0; i<ops.length; ++i) {
  const op = ops[i];
  add('association-'+op, `a ${op} b ${op} c`, op === '**' ?
    [op,'a',[op,'b','c']] : [op,[op,'a','b'],'c']);
  for (let j=i+1; j<ops.length; ++j) {
    const hi = ops[j];
    add(`precedence-${op}-${hi}-right`, `a ${op} b ${hi} c`, [op,'a',[hi,'b','c']]);
    add(`precedence-${op}-${hi}-left`, `a ${hi} b ${op} c`, [op,[hi,'a','b'],'c']);
  }
}
add('assignment-association','a = b = c',['=','a',['=','b','c']]);
add('conditional-association','a ? b : c ? d : e',['?:','a','b',['?:','c','d','e']]);
add('prefix-postfix-solc-reading','-a++',['pre','-',['post','++','a']]);
add('conditional-assignment-solc-reading','a ? b : c = d',['?:','a','b',['=','c','d']]);
add('postfix-member-refused','a++.f',null);
add('postfix-postfix-refused','a++ ++',null);
add('group-prefix-postfix','-(a++)',['pre','-',['tuple',['post','++','a']]]);
add('group-conditional-assignment','a ? b : (c = d)',['?:','a','b',['tuple',['=','c','d']]]);
add('group-postfix-member','(a++).f',['.',['tuple',['post','++','a']],'f']);

function shape(n) {
  if (n.nodeType === 'Identifier') return n.name;
  if (n.nodeType === 'BinaryOperation') return [n.operator,shape(n.leftExpression),shape(n.rightExpression)];
  if (n.nodeType === 'Assignment') return [n.operator,shape(n.leftHandSide),shape(n.rightHandSide)];
  if (n.nodeType === 'Conditional') return ['?:',shape(n.condition),shape(n.trueExpression),shape(n.falseExpression)];
  if (n.nodeType === 'UnaryOperation') return [n.prefix?'pre':'post',n.operator,shape(n.subExpression)];
  if (n.nodeType === 'TupleExpression') return ['tuple',...n.components.map(x=>x===null?null:shape(x))];
  if (n.nodeType === 'MemberAccess') return ['.',shape(n.expression),n.memberName];
  throw Error('unhandled AST node '+n.nodeType);
}
for (const control of cases) {
  const source = `contract C { function f() public { ${control.expression}; } }`;
  const input = {language:'Solidity',sources:{'control.sol':{content:source}},settings};
  const output = JSON.parse(compile(JSON.stringify(input),0,0));
  const errors = (output.errors??[]).filter(e=>e.severity==='error');
  let actual = null;
  if (control.expected === null) assert(errors.some(e=>e.type==='ParserError'), control.id);
  else {
    assert.equal(errors.length,0, control.id+': '+JSON.stringify(errors));
    const contract = output.sources['control.sol'].ast.nodes.find(n=>n.nodeType==='ContractDefinition');
    const fn = contract.nodes.find(n=>n.nodeType==='FunctionDefinition');
    actual = shape(fn.body.statements[0].expression);
    assert.deepEqual(actual,control.expected,control.id);
  }
  observations.push({...control,actual,source,sourceSha256:sha(source),
    errors:errors.map(e=>({type:e.type,message:e.message,errorCode:e.errorCode}))});
}
const result = {pin,settings,boundary:'External solc parsing observations only; no kernel proof or semantic compilation claim.',observations};
writeFileSync('tests/sol-expression-uniqueness/evidence/compiler-0.8.38.json',JSON.stringify(result,null,2)+'\n');
console.log(`COMPILER_CONTROLS_PASS: ${observations.length} pinned solc ${pin.version} parsing observations`);
