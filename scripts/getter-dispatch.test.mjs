import {test} from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync, readFileSync, writeFileSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {execFileSync} from 'node:child_process';
import {runSolidityTests} from './test-solidity.mjs';

function withSource(source, action) {
  const directory = mkdtempSync(join(tmpdir(), 'solidity-getter-dispatch-'));
  try {
    const input = join(directory, 'GetterDispatch.sol');
    writeFileSync(input, '// SPDX-License-Identifier: MIT\npragma solidity ^0.8.0;\n' + source);
    return action(input, directory);
  } finally { rmSync(directory, {recursive:true, force:true}); }
}

// Check real production admission, including its specification/loop callbacks.
// Mutations model malformed compiler-boundary data, never alternate lowering.
function productionCheck(source, body, mutate) {
  withSource(source, (input, directory) => {
    const fixture = join(directory, 'GetterDispatch.ast.json');
    execFileSync(process.execPath, ['scripts/solc-ast.mjs', '--source', input,
      '--out', fixture, '--no-wrapper'], {stdio:'pipe'});
    if (mutate) {
      const json = JSON.parse(readFileSync(fixture, 'utf8'));
      mutate(json.ast.nodes.find(node => node.nodeType === 'ContractDefinition' && node.name === 'C'));
      writeFileSync(fixture, JSON.stringify(json));
    }
    let hash = 0xcbf29ce484222325n;
    for (const byte of readFileSync(fixture))
      hash = BigInt.asUintN(64, (hash ^ BigInt(byte)) * 0x100000001b3n);
    const check = join(directory, 'Check.lean');
    writeFileSync(check, `import Solidity.Frontend.Import
open Solidity Solidity.Frontend
solc_import "GetterDispatch.ast.json" hash 0x${hash.toString(16)} as Imported.C testing
${body}
`);
    execFileSync('lake', ['--quiet', '--no-build', 'lean', check, '--', '--tstack=131072'],
      {stdio:'pipe', encoding:'utf8', timeout:180000});
  });
}

const rejected = name => `#guard (Imported.C.report.find? (·.name == "${name}")).any fun row =>
  row.admissionChecked && row.status == .unsupported &&
    (row.sourceDiagnostic.map (·.name)) == some \`solidity.functionDispatch`;
const admitted = name => `#guard (Imported.C.report.find? (·.name == "${name}")).any fun row =>
  row.admissionChecked && row.status == .elaborated && row.sourceDiagnostic.isNone`;

function proved(source, name = 'entry') {
  withSource(source, input => {
    const report = runSolidityTests([input], {build:false, contract:'C', function:name});
    assert.deepEqual(report.errors, []);
    assert.equal(report.results.find(row => row.function === name)?.status, 'proved',
      JSON.stringify(report.results));
  });
}

test('compatible primitive getters remain dynamic external candidates and run their real body', () => {
  proved(`contract C {
    mapping(uint => uint) public values;
    /// @custom:key box
    function entry() public {
      values[7] = 11;
      function(uint) external view returns(uint) h = this.values;
      assert(h(7) == 11);
    }
  }`);
});

test('a compatible getter coexists with an ordinary external function target', () => {
  proved(`contract C {
    mapping(uint => uint) public values;
    function identity(uint x) external pure returns(uint) { return x; }
    /// @custom:key box
    function entry() public view {
      function(uint) external pure returns(uint) h = this.identity;
      assert(h(3) == 3);
    }
  }`);
});

test('native internal dispatch excludes getters even when their erased ABI kinds collide', () => {
  proved(`contract C {
    mapping(address => uint) public values;
    function identity(uint x) internal pure returns(uint) { return x; }
    function entry() public pure {
      function(uint) internal pure returns(uint) h = identity;
      assert(h(3) == 3);
    }
  }`);
});

test('getter mapping-key address/uint erasure collisions fail closed', () => {
  productionCheck(`contract C {
    mapping(address => uint) public values;
    function identity(uint x) external pure returns(uint) { return x; }
    function entry() public view {
      function(uint) external pure returns(uint) h = this.identity;
      h(3);
    }
  }`, rejected('entry'));
});

test('getter return address/uint erasure collisions fail closed', () => {
  productionCheck(`contract C {
    address public owner;
    function identity() external pure returns(uint) { return 0; }
    function entry() public view {
      function() external pure returns(uint) h = this.identity;
      h();
    }
  }`, rejected('entry'));
});

test('unsupported getter plans cannot silently disappear from external dynamic admission', () => {
  productionCheck(`contract C {
    bytes public data;
    function identity(uint x) external pure returns(uint) { return x; }
    function dynamicEntry() public view {
      function(uint) external pure returns(uint) h = this.identity;
      h(3);
    }
    function staticEntry() public view { this.identity(3); }
  }`, rejected('dynamicEntry') + '\n' + admitted('staticEntry'));
});

test('malformed getter selector metadata refuses dynamic admission while static unrelated calls remain usable', () => {
  productionCheck(`contract C {
    mapping(uint => uint) public values;
    function identity(uint x) external pure returns(uint) { return x; }
    function dynamicEntry() public view {
      function(uint) external pure returns(uint) h = this.identity;
      h(3);
    }
    function staticEntry() public view { this.identity(3); }
  }`, rejected('dynamicEntry') + '\n' + admitted('staticEntry'), contract => {
    contract.nodes.find(node => node.nodeType === 'VariableDeclaration' && node.name === 'values')
      .functionSelector = 'not-a-selector';
  });
});

test('missing getter type metadata is not an absent target', () => {
  productionCheck(`contract C {
    mapping(uint => uint) public values;
    function identity(uint x) external pure returns(uint) { return x; }
    function entry() public view {
      function(uint) external pure returns(uint) h = this.identity;
      h(3);
    }
  }`, rejected('entry'), contract => {
    delete contract.nodes.find(node => node.nodeType === 'VariableDeclaration' && node.name === 'values').typeName;
  });
});

test('getter dependency scope follows declaration headers without executing mutable initializers', () => {
  productionCheck(`contract C {
    uint public value = block.number;
    function entry() public view {
      function() external view returns(uint) h = this.value;
      assert(h() == value);
    }
    constructor() {}
  }`, admitted('entry') + `
#guard (Imported.C.report.find? (·.name == "constructor")).any fun row =>
  row.status == .excluded &&
    (row.sourceDiagnostic.map (·.name)) == some \`solidity.blockField.number`);
});
