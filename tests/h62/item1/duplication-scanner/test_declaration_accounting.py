"""Guard dropped kernel/source declarations and guessed range-based identities."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

ROOT=Path(__file__).resolve().parents[4];SCRIPTS=ROOT/"scripts/h62/item1/duplication-scanner"
sys.path.insert(0,str(SCRIPTS))
try:
    import account_observed_declarations as ledger
finally:sys.path.pop(0)


def name(*parts):return ledger.closure.encoded(list(parts))


class DeclarationAccountingControls(unittest.TestCase):
    def setUp(self):
        self.source='def a := 0\ninductive T where\n  | ctor\n'
        self.lexical=ledger.binder.scanner.scan(ledger.binder.ROOT/ledger.SOURCE,ledger.binder.ROOT,self.source.encode())
        signature=['declaration-type',0,['const',name('Nat'),[]]]
        entries=[(name('a'),'definition'),(name('T'),'inductive'),(name('T','ctor'),'constructor'),
                 (name('T','rec'),'recursor'),(name('generated'),'definition'),(name('a','eq_1'),'theorem')]
        rows=[{'declaration':n,'kind':k,'status':'serialized','signature':signature} for n,k in entries]
        rows[-1]={'declaration':entries[-1][0],'kind':'theorem','status':'unsupported','reason':'expression metadata'}
        def location(line,start,end,length):return {'start':{'line':line,'column':start},'end':{'line':line,'column':end},'range_start':{'line':line,'column':0},'range_end':{'line':line,'column':length}}
        selections=[location(1,4,5,10),location(2,10,11,17),location(3,4,8,8),location(2,10,11,17),None,location(1,4,5,10)]
        module=ledger.closure.profile('scope')['module']
        self.legacy={'census':{'format':1,'module':module,'total':6,'rows':rows},'locations':{'format':1,'module':module,'rows':[{'declaration':n,'selection':s} for (n,_),s in zip(entries,selections)]}}
        self.bindings=ledger.closure.leaf.source_binding.join_locations(self.source,self.lexical,self.legacy['census'],self.legacy['locations'],module)
        newer=[]
        for row in rows:
            old={k:v for k,v in row.items() if k not in ('declaration','kind')}
            new={'status':'serialized','signature':['declaration-type-with-metadata-v2',0,['const',name('Nat'),[]]]}
            newer.append({'declaration':row['declaration'],'kind':row['kind'],'legacy':old,'metadata_v2':new})
        self.observation={'census':{'format':2,'module':module,'total':6,'rows':newer},'locations':self.legacy['locations']}

    def run_ledger(self):return ledger.account(self.source,self.lexical,self.legacy,self.bindings,self.observation)

    def test_every_kernel_and_source_row_retained_once(self):
        value=self.run_ledger()
        self.assertEqual((value['kernel_total'],value['lexical_total'],value['legacy_links']),(6,2,2))
        self.assertEqual(len(value['constants']),6);self.assertEqual(len(value['sources']),2)
        self.assertEqual(sum(value['source_evidence_counts'].values()),6)
        self.assertTrue(all(r['ownership']=='unverified' for r in value['constants']+value['sources']))

    def test_parent_ranges_and_missing_ranges_are_not_identity_guesses(self):
        value=self.run_ledger();counts=value['source_evidence_counts']
        self.assertEqual(counts,{'existing-direct-source-link':2,'direct-range-without-legacy-link':1,'range-name-differs':2,'no-compiler-range':1})
        for row in value['constants']:
            if row['source_evidence']['status']!='existing-direct-source-link':self.assertIsNone(row['source_evidence']['lexical_index'])

    def test_legacy_refusal_retained_despite_v2_serialization(self):
        value=self.run_ledger()
        self.assertEqual(value['legacy_type_statuses'],{'serialized':5,'unsupported':1})
        self.assertEqual(value['metadata_v2_type_statuses'],{'serialized':6})
        refused=[r for r in value['constants'] if r['legacy']['status']=='unsupported']
        self.assertEqual(refused[0]['source_evidence']['status'],'range-name-differs')

    def test_source_or_observation_omission_refused(self):
        self.lexical.pop()
        with self.assertRaisesRegex(ValueError,'correspondence drift'):self.run_ledger()
        self.setUp();self.observation['census']['rows'].pop()
        with self.assertRaises(ValueError):self.run_ledger()

    def test_duplicate_or_foreign_kernel_identity_refused(self):
        for transform in (lambda r:r.append(copy.deepcopy(r[0])),lambda r:r[0].update(declaration=name('Foreign'))):
            old=copy.deepcopy(self.legacy);transform(self.legacy['census']['rows'])
            with self.assertRaises(ValueError):self.run_ledger()
            self.legacy=old

    def test_modified_binding_or_source_bytes_cannot_be_reused(self):
        self.bindings['rows'][0]['signature']=['forged']
        with self.assertRaisesRegex(ValueError,'correspondence drift'):self.run_ledger()
        self.setUp();self.source='-- inserted\n'+self.source
        with self.assertRaises(ValueError):self.run_ledger()

    def test_failure_receipt_identifies_shared_accounting_core(self):
        with tempfile.TemporaryDirectory() as tmp:
            output=Path(tmp)/'new'
            with mock.patch.object(ledger.observer,'run',side_effect=ValueError('producer failure')):
                with self.assertRaisesRegex(ValueError,'producer failure'):ledger.run(output)
            receipt=json.loads((output/'receipt.json').read_text())
            self.assertEqual(receipt['core_sha256'],ledger.binder.sha(Path(ledger.common.__file__)))
            self.assertEqual(receipt['status'],'failed')

    def test_saved_ledger_directory_does_not_trigger_observation(self):
        with tempfile.TemporaryDirectory() as tmp:
            with mock.patch.object(ledger.observer,'run') as observe:
                with self.assertRaises(FileExistsError):ledger.run(Path(tmp))
            observe.assert_not_called()


if __name__=='__main__':unittest.main()
