"""Guard project ledger omissions, refusal promotion and post-child packet drift."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

import test_declaration_accounting as controls
sys.path.insert(0,str(controls.SCRIPTS))
try:
    import account_project_declarations as driver
finally:sys.path.pop(0)


class ProjectAccountingControls(unittest.TestCase):
    def sample(self,target):
        fixture=controls.DeclarationAccountingControls();fixture.setUp()
        path,module=driver.profile(target)
        legacy=copy.deepcopy(fixture.legacy)
        for key in ('census','locations'):legacy[key]['module']=module
        lexical=driver.binder.scanner.scan(driver.binder.ROOT/path,driver.binder.ROOT,fixture.source.encode())
        bindings=driver.leaf.source_binding.join_locations(fixture.source,lexical,legacy['census'],legacy['locations'],module)
        return fixture.source,lexical,legacy,bindings,path,module

    def test_all_targets_preserve_every_row_and_refusal(self):
        for target in ('keysort','ast','scope'):
            with self.subTest(target=target):
                value=driver.common.account(*self.sample(target))
                self.assertEqual((value['kernel_total'],value['lexical_total'],value['legacy_links']),(6,2,2))
                self.assertEqual(value['legacy_type_statuses'],{'serialized':5,'unsupported':1})
                self.assertTrue(all('metadata_v2' not in r and r['ownership']=='unverified' for r in value['constants']))
                self.assertEqual(sum(value['source_evidence_counts'].values()),6)

    def test_parent_and_generated_ranges_never_promoted(self):
        value=driver.common.account(*self.sample('ast'))
        for row in value['constants']:
            if row['source_evidence']['status']!='existing-direct-source-link':self.assertIsNone(row['source_evidence']['lexical_index'])
        self.assertEqual(value['source_evidence_counts'],{'existing-direct-source-link':2,'direct-range-without-legacy-link':1,'range-name-differs':2,'no-compiler-range':1})

    def test_omitted_lexical_kernel_or_location_rows_rejected(self):
        for part in ('lexical','kernel','location'):
            args=list(self.sample('ast'))
            if part=='lexical':args[1].pop()
            elif part=='kernel':args[2]['census']['rows'].pop()
            else:args[2]['locations']['rows'].pop()
            with self.subTest(part=part),self.assertRaises(ValueError):driver.common.account(*args)

    def test_wrong_source_module_and_duplicate_identity_rejected(self):
        for part in ('path','module','duplicate'):
            args=list(self.sample('keysort'))
            if part=='path':args[4]='Other.lean'
            elif part=='module':args[5]=driver.closure.encoded(['Other'])
            else:args[2]['census']['rows'].append(copy.deepcopy(args[2]['census']['rows'][0]))
            with self.subTest(part=part),self.assertRaises(ValueError):driver.common.account(*args)

    def fake_producer(self,directory):
        source,lexical,legacy,bindings,path,module=self.sample('keysort')
        (directory/'sources/Solidity').mkdir(parents=True);(directory/'fixtures').mkdir()
        (directory/'sources'/path).write_text(source)
        for filename,value in [('metadata.json',legacy),('source-bindings.json',bindings),('fixtures/receipt.json',{'steps':[]})]:
            (directory/filename).write_text(json.dumps(value,indent=2)+'\n')
        live={'status':'pass','keysort_gate':'pass','steps':[],'source_sha256':hashlib.sha256(source.encode()).hexdigest(),
              'metadata_sha256':driver.binder.sha(directory/'metadata.json'),'bindings_sha256':driver.binder.sha(directory/'source-bindings.json'),
              'fixture_receipt_sha256':driver.binder.sha(directory/'fixtures/receipt.json')}
        (directory/'receipt.json').write_text(json.dumps(live,indent=2)+'\n')
        return live

    def test_parent_rechecks_child_metadata_after_accounting(self):
        with tempfile.TemporaryDirectory() as tmp:
            output=Path(tmp)/'new';original=driver.common.account
            def mutate(*args):
                result=original(*args);(output/'capture/metadata.json').write_text('{}');return result
            with mock.patch.object(driver.leaf,'run',side_effect=self.fake_producer),mock.patch.object(driver.common,'account',side_effect=mutate):
                with self.assertRaises(ValueError):driver.run(output)
            self.assertFalse((output/'ledger.json').exists())
            self.assertEqual(json.loads((output/'receipt.json').read_text())['status'],'failed')

    def test_parent_keeps_child_refusals_without_promoting_signatures(self):
        with tempfile.TemporaryDirectory() as tmp:
            output=Path(tmp)/'new'
            with mock.patch.object(driver.leaf,'run',side_effect=self.fake_producer):result=driver.run(output)
            self.assertEqual(result['summary']['legacy_type_statuses'],{'serialized':5,'unsupported':1})
            self.assertEqual(result['summary']['kernel_total'],6)

    def test_replay_and_unknown_target_do_not_start_child(self):
        with tempfile.TemporaryDirectory() as tmp,mock.patch.object(driver.leaf,'run') as child:
            with self.assertRaises(FileExistsError):driver.run(Path(tmp))
            with self.assertRaises(ValueError):driver.run(Path(tmp)/'new','foreign')
            child.assert_not_called()


if __name__=='__main__':unittest.main()
