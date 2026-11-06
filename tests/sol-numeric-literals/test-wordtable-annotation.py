#!/usr/bin/env python3
"""Deterministic reproduction and fail-closed annotation controls in isolated copies."""
import pathlib,shutil,subprocess,tempfile
ROOT=pathlib.Path(__file__).resolve().parents[2]
PARTS=[f'Solidity/Frontend/NumericLiteralProofs/WordTable/Part{i:02}.lean' for i in range(30)]
FACADE='Solidity/Frontend/NumericLiteralProofs/WordTable.lean'
MARKER='-- H55 reproduction: scripts/h55/vectors-tables/word_table.py (proof text remains authoritative).\n'
with tempfile.TemporaryDirectory(prefix='wordtable-annotation-') as td:
 root=pathlib.Path(td)
 (root/'Solidity/Frontend/NumericLiteralProofs').mkdir(parents=True)
 for relative in ['tests/sol-numeric-literals/generate-wordtable.py','Solidity/Frontend/Checked/Tables.lean']:
  dst=root/relative;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/relative,dst)
 def run(check=False):return subprocess.run(['python3','-B','tests/sol-numeric-literals/generate-wordtable.py']+(['--check'] if check else []),cwd=root,capture_output=True,text=True)
 assert run().returncode==0
 baseline={name:(root/name).read_bytes() for name in PARTS+[FACADE]}
 assert all(raw==(ROOT/name).read_bytes() for name,raw in baseline.items())
 assert run().returncode==0 and baseline=={name:(root/name).read_bytes() for name in baseline}
 assert run(True).returncode==0
 for name in PARTS:
  raw=baseline[name];assert raw.count(MARKER.encode())==1
  path=root/name
  for changed in [raw.replace(MARKER.encode(),b'',1),raw.replace(MARKER.encode(),(MARKER+MARKER).encode(),1),raw.replace(b'intro h',b'intro altered_proof',1)]:
   assert changed!=raw;path.write_bytes(changed);assert run(True).returncode!=0;path.write_bytes(raw)
 extra=root/'Solidity/Frontend/NumericLiteralProofs/WordTable/Part30.lean';extra.write_text('unexpected')
 assert run(True).returncode!=0;extra.unlink()
 missing=root/PARTS[-1];missing.unlink();assert run(True).returncode!=0;missing.write_bytes(baseline[PARTS[-1]])
 assert run(True).returncode==0
print('PASS: complete30part+facade reproduction twice;90missing/duplicate-marker/changed-proof refusals plus missing/extra-module refusals')
