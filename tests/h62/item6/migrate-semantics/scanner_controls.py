#!/usr/bin/env python3
"""Negative controls for lexical census; not semantic proof acceptance."""
import importlib.util, re
from pathlib import Path
root=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location('census',root/'scripts/h62/item6/migrate-semantics/census.py')
m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
for s in ['/- import Fake /- nested -/ -/\nimport Solidity.Real', '-- import Fake\nimport Solidity.Real', 'def marker := "/-"\nimport Solidity.Real', 'def marker := "--"\nimport Solidity.Real', 'def marker := "\nimport Solidity.Fake\ndef fake := 1\n"\nimport Solidity.Real']:
    assert re.findall(r'^import\s+([\w.]+)',m.strip_comments(s),re.M)==['Solidity.Real']
print('PASS: 5 lexical negative controls (comments, nested comments, ordinary and multiline strings)')
