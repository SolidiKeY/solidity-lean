"""Read-only reuse of repository DAG codecs; no model or external package dependency."""
import hashlib
import types
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[4]
CODEC = 'scripts/h62/item6/migrate-testsuite/dag_codec.py'
ENCODER = 'scripts/h62/item6/migrate-testsuite/expr_dag.py'


def load(relative):
    path = ROOT / relative
    module = types.ModuleType('examples_' + path.stem)
    module.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec'), module.__dict__)
    return module


def validate_scope(scope):
    from census import BASE
    from dependencies import Tree
    base = Tree(ROOT, BASE)
    expected = sorted(path for path in base.blobs if path.startswith('Solidity/Examples/') and path.endswith('.lean'))
    if scope['base'] != BASE or len(expected) != 354 or sorted(row['path'] for row in scope['modules']) != expected:
        raise ValueError('WRONG_FROZEN_SCOPE')
    for row in scope['modules']:
        if row['module'] != row['path'][:-5].replace('/', '.') or hashlib.sha256(base.read(row['path'])).hexdigest() != row['source_sha256']:
            raise ValueError('WRONG_FROZEN_SOURCE_HASH')


INPUTS = (ENCODER, CODEC, 'scripts/h62/item6/migrate-examples/generate-dag-inventory.py',
          'scripts/h62/item6/migrate-examples/dag_support.py',
          'scripts/h62/item6/migrate-examples/dag_inventory.py',
          'scripts/h62/item6/migrate-examples/census.py',
          'scripts/h62/item6/migrate-examples/dependencies.py')
OLD_VERSION = '4.24.0'
OLD_COMMIT = '797c613eb9b6d4ec95db23e3e00af9ac6657f24b'


codec = load(CODEC)
