#!/usr/bin/env python3
"""Export a single-file owner patch; never apply it to the read-only family.

The production proposal keeps the helper/table in the existing control module
to avoid adding an import/load step. Its whole combined body is checked and
measured separately from the standalone helper/candidate test modules.
"""
import argparse
import difflib
from pathlib import Path
import re
import subprocess
import census
from make_candidate import candidate, SOURCE

HELPER = Path('tests/h62/item4/generic-p10/GenericP10/ByteFixture.lean')
OWNER_NAMESPACE = 'SolidityBridge.RoadmapV15.P10.ByteObservationControls'
TABLE_NAMESPACE = 'SolidityBridge.RoadmapV15.P10.ByteTable'
NEW_NAMES = {'execute','ByteFixture','ByteCase','fixturePayload','fixtureValues','fixture_word','fixture','table_case'}


def owner_source(repo):
    original = (repo/SOURCE).read_bytes()
    frozen = subprocess.check_output(['git','-C',str(repo),'show',f'{census.BASE}:{SOURCE.as_posix()}'])
    if original != frozen: raise ValueError('owner source changed; request a relay')
    original = original.decode()
    helper = (repo/HELPER).read_text()
    expected_import = 'import SolidityBridge.RoadmapV15.P10.ByteObservation\n'
    if not helper.startswith(expected_import): raise ValueError('helper import boundary changed')
    helper = helper[len(expected_import):]
    helper = helper.replace('namespace GenericP10\n',f'namespace {TABLE_NAMESPACE}\n',1)
    helper = helper.replace('end GenericP10\n',f'end {TABLE_NAMESPACE}\n',1)
    helper = helper.replace("'GenericP10.","'"+TABLE_NAMESPACE+'.')
    helper = re.sub(r'\bpayload\b','fixturePayload',helper)
    controls = candidate(original)
    if not controls.startswith('import GenericP10.ByteFixture\n'): raise ValueError('candidate import changed')
    controls = controls.split('\n',1)[1]
    controls = controls.replace('GenericP10.ByteControls',OWNER_NAMESPACE)
    controls = controls.replace('open SolidityBridge.RoadmapV15.P10\n','',1)
    for name in ['execute','ByteCase','fixture']:
        controls = controls.replace('GenericP10.'+name,TABLE_NAMESPACE+'.'+name)
    result = expected_import+helper+'\n'+controls.lstrip('\n')
    old = {r['name']:r for r in census.declarations(original,str(SOURCE))}
    new = {r['name']:r for r in census.declarations(result,str(SOURCE))}
    if set(new)-set(old) != NEW_NAMES: raise ValueError('unexpected added/omitted helper inventory')
    for name,row in old.items():
        if name not in new or row['statement_sha256'] != new[name]['statement_sha256']:
            raise ValueError(f'original statement changed: {name}')
    return original,result


def wrapped(source, prefix):
    """Fresh namespace forces fresh body checking while imports stay warm."""
    if not re.fullmatch('[A-Za-z][A-Za-z0-9_]*',prefix): raise ValueError('invalid wrapper namespace')
    header,body = source.split('\n',1)
    if header != 'import SolidityBridge.RoadmapV15.P10.ByteObservation': raise ValueError('unexpected import boundary')
    body = body.replace("'"+TABLE_NAMESPACE+'.',"'"+prefix+'.'+TABLE_NAMESPACE+'.')
    return header+'\nnamespace '+prefix+'\nopen _root_.SolidityBridge.RoadmapV15.P10\n'+body+'\nend '+prefix+'\n'


def validation_code(repo, proposed):
    original = (repo/SOURCE).read_text()
    public = [r['name'] for r in census.declarations(original,str(SOURCE)) if r['kind']=='theorem' and not r['private']]
    code = wrapped(proposed,'OwnerValidation')
    code = 'import SolidityBridge.RoadmapV15.P10.ByteObservationControls\n'+code
    code += '\nnamespace OwnerCorrespondence\nprivate def proposition {P : Prop} (_proof : P) : Prop := P\n'
    for name in public:
        code += f'''theorem {name} :
    proposition (@_root_.{OWNER_NAMESPACE}.{name}) =
      proposition (@_root_.OwnerValidation.{OWNER_NAMESPACE}.{name}) := rfl
'''
    return code+'end OwnerCorrespondence\n'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[4])
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    repo=args.repo.resolve()
    artifacts=repo.parent/'generic-p10-artifacts'
    original,proposed=owner_source(repo)
    patch=''.join(difflib.unified_diff(original.splitlines(True),proposed.splitlines(True),
        fromfile='a/'+SOURCE.as_posix(),tofile='b/'+SOURCE.as_posix()))
    # Git accepts empty context lines without the lone context-marker space.
    # This keeps the nested patch itself free of trailing-whitespace warnings.
    patch=''.join('\n' if line==' \n' else line for line in patch.splitlines(True))
    outputs={repo/'tests/h62/item4/generic-p10/owner-migration.patch':patch,
             artifacts/'evidence/owner-candidate.lean':proposed,
             artifacts/'evidence/owner-validation.lean':validation_code(repo,proposed)}
    for path,content in outputs.items():
        if args.check:
            if path.read_text()!=content: raise ValueError(f'export is not reproducible: {path}')
        else: path.write_text(content)
    print('OWNER_PATCH_SOURCE_PASS: all32original signatures plus8helpers; original source untouched; owner permission still required')


if __name__=='__main__':main()
