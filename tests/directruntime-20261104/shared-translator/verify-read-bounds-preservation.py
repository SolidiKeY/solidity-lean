"""Guard H126 ReadBounds repair against altered specifications or budgets.

Old source is authenticated by its immutable Git object. Only the registered
implementation import and two compiled-twin attributes may differ in the old
module; new implementation/proof modules are checked separately by Lean.
"""
from pathlib import Path
import hashlib, json, re, subprocess
ROOT = Path(__file__).resolve().parents[3]
BASE = '9ef9482d550ee45efb7660e2dd961bfe3f1e8e98'
SOURCE = 'Solidity/Calculus/ReadBounds.lean'
old = subprocess.check_output(['git', 'show', BASE + ':' + SOURCE], cwd=ROOT)
new = (ROOT / SOURCE).read_bytes()
for family in ['LTm', 'LFml']:
    attachment = ('@[implemented_by ' + family + '.fitsStack]\ndef ' + family + '.fitsM').encode()
    if new.count(attachment) != 1:
        raise ValueError('compiled twin attribute is not attached to the original counter')
projected = new
for addition in [b'import Solidity.Calculus.ReadBoundsStack\n',
                 b'@[implemented_by LTm.fitsStack]\n',
                 b'@[implemented_by LFml.fitsStack]\n']:
    if projected.count(addition) != 1:
        raise ValueError('missing/duplicate authorized addition')
    projected = projected.replace(addition, b'', 1)
if projected != old:
    raise ValueError('existing ReadBounds source changed beyond import/compiled twin selection')
for name in ['ReadBoundsStack', 'ReadBoundsStackCorrect']:
    text = (ROOT / ('Solidity/Calculus/' + name + '.lean')).read_text()
    if re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*(?:(?:private|protected|noncomputable)\s+)*(?:axiom|unsafe|partial|opaque|constant)\b', text, re.M):
        raise ValueError('new trust shortcut')
print(json.dumps({'guardedRegression': __doc__.splitlines()[0],
 'authority': 'H126 semantic ownership and H82 statement-preserving module split',
 'specificationBase': BASE, 'baseSourceSha256': hashlib.sha256(old).hexdigest(),
 'currentSourceSha256': hashlib.sha256(new).hexdigest(),
 'oldSourceByteIdenticalAfterAuthorizedProjection': True,
 'limitsUnchanged': {'normalizationSize': 24000, 'normalizationDepth': 12,
                     'concreteSize': 96000, 'concreteDepth': 40},
 'boundary': 'Source/specification preservation only. New generic equality proofs and emitted-code/runtime checks remain separate; no native/WASM or performance acceptance.'}, indent=2))
