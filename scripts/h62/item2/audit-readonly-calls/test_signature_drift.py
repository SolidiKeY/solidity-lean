"""Guard recorded migration labels being mistaken for statement fidelity."""
import copy
import hashlib
import importlib.util
from pathlib import Path
import unittest

spec=importlib.util.spec_from_file_location('drift_dossier',Path(__file__).with_name('signature_drift.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


def sign(row,text):
    row['signature']=text;row['signature_sha256']=hashlib.sha256(text.encode()).hexdigest();return row


class SignatureDriftControls(unittest.TestCase):
    def setUp(self):
        self.rows=[sign({'file':'A.lean','source_name':f'N.t{i}','owner':'historical RO','visibility':'private' if i==3 else 'public','variable_context':[],'kernel_name':None,'witness_status':'pending'},f'theorem t{i} : True') for i in range(792)]
        self.rows[0]=sign(self.rows[0],'theorem t0 : x.balance.val = 0')
        self.rows[1]=sign(self.rows[1],'theorem t1 (b : Word) : P b')
        self.rows[2]=sign(self.rows[2],'theorem t2 (h : Conv E.isBase a b) : P h')
        self.now=copy.deepcopy(self.rows)
        for i,text in [(0,'theorem t0 : x.balance = 0'),(1,'theorem t1 (b : Monetary.Balance) : P b'),(2,'theorem t2 (h : Conv E.isBase E.mapFree a b) : P h')]:sign(self.now[i],text)
        del self.now[3]
        kinds=['H19-balance-projection','H19-balance-domain','H60-typing-parameter','removed-private-identity']
        by={r['source_name']:r for r in self.now}
        self.pins={'cases':[{'file':old['file'],'source_name':old['source_name'],'kind':kinds[i],
            'original_signature_sha256':old['signature_sha256'],'original_context_sha256':m.context(old),
            'observed_signature_sha256':by[old['source_name']]['signature_sha256'] if old['source_name'] in by else None,
            'observed_context_sha256':m.context(by[old['source_name']]) if old['source_name'] in by else None} for i,old in enumerate(self.rows[:4])]}
        self.frozen={'declarations':self.rows}

    def test_all_originals_pending_despite_exact_lexical_pairs(self):
        result=m.dossier(self.frozen,self.now,self.pins)
        self.assertEqual(len(result['original_rows']),792);self.assertEqual(len(result['changes']),4)
        self.assertTrue(all(r['exact_observed_pair'] for r in result['changes']))
        self.assertEqual(result['original_obligations_discharged'],0);self.assertFalse(result['runtime_gate_pass'])
        self.assertTrue(all(r['current_kernel_fidelity']=='pending' and r['live_ownership']=='unverified' and not r['original_obligation_discharged'] for r in result['original_rows']))
        self.assertTrue(all(r['statement_transport'].startswith('pending') for r in result['changes']))

    def test_additional_premise_or_context_never_hidden(self):
        changed=copy.deepcopy(self.now);sign(changed[0],changed[0]['signature'].replace(': x.balance', '(extra : False) : x.balance'))
        result=m.dossier(self.frozen,changed,self.pins)
        self.assertEqual(result['changes'][0]['lexical_review'],'unreviewed-drift')
        forged=copy.deepcopy(self.pins);forged['cases'][0]['observed_signature_sha256']=changed[0]['signature_sha256']
        self.assertFalse(m.matches(self.rows[0],changed[0],forged['cases'][0]))
        changed=copy.deepcopy(self.now);changed[0]['variable_context']=['variable (h : False)']
        self.assertEqual(m.dossier(self.frozen,changed,self.pins)['changes'][0]['lexical_review'],'unreviewed-drift')

    def test_unrecorded_same_text_pattern_is_not_promoted(self):
        old=copy.deepcopy(self.rows);now=copy.deepcopy(self.now)
        sign(old[4],'theorem t4 : y.balance.val = 0');row=next(r for r in now if r['source_name']=='N.t4');sign(row,'theorem t4 : y.balance = 0')
        result=m.dossier({'declarations':old},now,self.pins)
        found=next(r for r in result['changes'] if r['source_name']=='N.t4')
        self.assertEqual(found['lexical_review'],'unreviewed-drift');self.assertFalse(found['exact_observed_pair'])

    def test_private_replacement_name_does_not_close_gap(self):
        now=copy.deepcopy(self.now);shared=copy.deepcopy(self.rows[3]);shared['source_name']='Hoare.run_bind';now.append(shared)
        result=m.dossier(self.frozen,now,self.pins);missing=next(r for r in result['changes'] if r['source_name']=='N.t3')
        self.assertIsNone(missing['current']);self.assertEqual(missing['source_status'],'absent-upstream');self.assertEqual(len(result['added_declarations']),1)
        public=copy.deepcopy(self.rows[3]);public['visibility']='public';self.assertFalse(m.matches(public,None,self.pins['cases'][3]))

    def test_duplicate_foreign_and_lost_identities_refused(self):
        for now in [self.now+[self.now[0]]]:
            with self.assertRaises(ValueError):m.dossier(self.frozen,now,self.pins)
        for cases in [self.pins['cases']+[self.pins['cases'][0]],[dict(self.pins['cases'][0],source_name='Foreign')]]:
            with self.assertRaises(ValueError):m.dossier(self.frozen,self.now,{'cases':cases})
        with self.assertRaises(ValueError):m.dossier({'declarations':self.rows[:-1]},self.now,self.pins)

    def test_pair_digest_and_parser_share_one_buffer(self):
        class Changing:
            reads=0
            def read_bytes(self):
                self.reads+=1
                return b'{"cases":[]}' if self.reads==1 else b'{"cases":["forged"]}'
        path=Changing();raw,digest,pairs=m.read_pairs(path)
        self.assertEqual(path.reads,1);self.assertEqual(digest,hashlib.sha256(raw).hexdigest());self.assertEqual(pairs,{'cases':[]})

    def test_reverted_observation_is_visible_and_full_raw_diff_retained(self):
        result=m.dossier(self.frozen,self.rows,self.pins)
        self.assertEqual(len(result['recorded_pairs_now_retained']),4);self.assertEqual(result['changes'],[])
        result=m.dossier(self.frozen,self.now,self.pins)
        row=result['changes'][0];self.assertEqual(row['original']['signature'],self.rows[0]['signature'])
        self.assertEqual(row['current']['signature'],self.now[0]['signature']);self.assertTrue(row['signature_diff'])


if __name__=='__main__':unittest.main()
