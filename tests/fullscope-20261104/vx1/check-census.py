#!/usr/bin/env python3
"""Verify the VX1 census against pinned source text; no compiler/proof claims."""
import argparse, hashlib, json, re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
parser = argparse.ArgumentParser()
parser.add_argument('--upstream', required=True, type=Path)
parser.add_argument('--census', type=Path, default=HERE / 'environment-census.json')
args = parser.parse_args()
census = json.loads(args.census.read_text())
EXPECTED_SOURCE_PATHS = {
    'libsolidity/ast/Types.cpp', 'libsolidity/analysis/GlobalContext.cpp',
    'libsolidity/analysis/TypeChecker.cpp', 'liblangutil/EVMVersion.h',
    'docs/units-and-global-variables.rst', 'libsolidity/codegen/ExpressionCompiler.cpp',
    'libevmasm/Instruction.h',
}
EXPECTED_FORK_BOUNDARIES = {
    'hasChainID': 'istanbul', 'hasBaseFee': 'london',
    'hasBlobBaseFee': 'cancun', 'hasBlobHash': 'cancun',
    'hasSlotNum': 'amsterdam', 'hasPrevRandao': 'paris',
}
source_paths = [pin['path'] for pin in census['upstream']['sources']]
assert len(source_paths) == 7 and set(source_paths) == EXPECTED_SOURCE_PATHS, 'SOURCE_IDENTITY_CENSUS_MISMATCH'
assert census['forkBoundaries'] == EXPECTED_FORK_BOUNDARIES, 'FORK_BOUNDARY_CENSUS_MISMATCH'
manifest = json.loads((ROOT / 'docs/solidity-features.json').read_text())
assert census['upstream']['commit'] == manifest['upstream']['commit']
pins = {x['path']: x for x in manifest['upstream']['sources']}
texts = {}
for pin in census['upstream']['sources']:
    data = (args.upstream / pin['path']).read_bytes()
    assert hashlib.sha256(data).hexdigest() == pin['sha256'], pin['path']
    blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    assert blob == pin['gitBlobSha'], pin['path']
    if pin['existingManifestPin']:
        assert (pin['sha256'], pin['gitBlobSha']) == (pins[pin['path']]['sha256'], pins[pin['path']]['gitBlobSha'])
    texts[pin['path']] = data.decode()
rows = census['fields']
assert len(rows) == 14 and len({x['spelling'] for x in rows}) == 14
features = {x['id'] for x in manifest['features']}
assert {x['feature'] for x in rows} <= features
native = texts['libsolidity/ast/Types.cpp'].split('MemberList::MemberMap MagicType::nativeMembers')[1]
block = native.split('case Kind::Block:')[1].split('case Kind::Message:')[0]
tx = native.split('case Kind::Transaction:')[1].split('case Kind::ABI:')[0]
source_members = {'block.' + x for x in re.findall(r'^\s*\{"(\w+)",', block, re.M) if x != 'blockhash'}
source_members |= {'tx.' + x for x in re.findall(r'^\s*\{"(\w+)",', tx, re.M)}
assert {x['spelling'] for x in rows} == source_members | {'blockhash', 'blobhash'}
expected_types = {'payableAddress()': 'address payable', 'address()': 'address', 'uint256()': 'uint256', 'uint(64)': 'uint64'}
for row in rows:
    ref = row['source']
    line = texts[ref['path']].splitlines()[ref['line'] - 1]
    name = row['spelling'].split('.')[-1]
    assert '"' + name + '"' in line, row
    if '.' in row['spelling']:
        assert any('TypeProvider::' + call in line and result == row['resultType'] for call, result in expected_types.items()), row
    else:
        assert 'strings{"uint256"}, strings{"bytes32"}' in line, row
    if row['backendOsakaOpcode']:
        opcode = (ROOT / 'Solidity/Backend/Opcode.lean').read_text()
        assert re.search(r'^  \| ' + re.escape(row['backendOsakaOpcode']) + r'$', opcode, re.M), row
codegen = texts['libsolidity/codegen/ExpressionCompiler.cpp']
selection = {}
for first, second, opcode in re.findall(r'(?:else )?if \(member == "(\w+)"(?: \|\| member == "(\w+)")?\)\s*m_context << Instruction::(\w+);', codegen):
    selection[first] = opcode
    if second:
        selection[second] = opcode
for row in rows:
    spelling = row['spelling']
    if '.' in spelling:
        assert row['argumentTypes'] == [], row
        assert row['upstreamOpcode'] == selection[spelling.split('.')[-1]], row
    else:
        assert row['argumentTypes'] == ['uint256'], row
        kind = {'blockhash': 'BlockHash', 'blobhash': 'BlobHash'}[spelling]
        assert row['upstreamOpcode'] == spelling.upper(), row
        assert 'FunctionType::Kind::' + kind in codegen
        assert 'Instruction::' + row['upstreamOpcode'] in codegen
    assert row['backendOsakaOpcode'] == (None if spelling == 'block.slotnum' else row['upstreamOpcode']), row
assert 'SLOTNUM = 0x4b' in texts['libevmasm/Instruction.h']
assert not re.search(r'^  \| SLOTNUM$', (ROOT / 'Solidity/Backend/Opcode.lean').read_text(), re.M)
header = texts['liblangutil/EVMVersion.h']
for capability, fork in census['forkBoundaries'].items():
    assert re.search(r'bool ' + capability + r'\(\) const \{ return \*this >= ' + fork + r'\(\); \}', header), capability
checker = texts['libsolidity/analysis/TypeChecker.cpp']
assert '9432_error' in checker and '8417_error' in checker
gates = dict(re.findall(r'memberName == "(\w+)" && !m_evmVersion\.(\w+)\(\)', checker))
for row in rows:
    name = row['spelling'].split('.')[-1]
    expected = gates.get(name) if name in {'chainid', 'basefee', 'blobbasefee', 'slotnum'} else ('hasBlobHash' if name == 'blobhash' else None)
    assert row['capability'] == expected, row
for spelling in ['chainid', 'basefee', 'blobbasefee', 'slotnum']:
    assert 'memberName == "' + spelling + '" && !m_evmVersion.' in checker
context = texts['libsolidity/analysis/GlobalContext.cpp']
assert 'if (_evmVersion >= langutil::EVMVersion::cancun())' in context
assert len(census['expectedBoundaryControls']) == 11
for control in census['expectedBoundaryControls']:
    if control['kind'] == 'blockhash':
        available = control['query'] < control['current'] and control['current'] - control['query'] <= 256
    else:
        assert control['kind'] == 'blobhash'
        available = control['index'] < control['length']
    assert control['available'] == available, control
assert len(census['combinationFixtures']) == 5
print(f"CENSUS_PASS: {len(rows)} fields/functions; {len(texts)} source identities; {len(census['forkBoundaries'])} fork boundaries; {len(census['expectedBoundaryControls'])} boundary expectations; {len(census['combinationFixtures'])} combination fixtures")
print('Boundary arithmetic is fixture consistency only; combinations are expectations, not production execution results.')
