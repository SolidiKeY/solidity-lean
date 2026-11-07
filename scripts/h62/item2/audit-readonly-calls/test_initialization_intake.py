"""Guard lexical producer refusals being promoted to semantic/compiler credit."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest import mock
spec=importlib.util.spec_from_file_location('compiler_intake',Path(__file__).with_name('compiler_success_intake.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class IntakeControls(unittest.TestCase):
    def test_header_span_not_namespace_or_kernel_signature(self):
        raw=b'namespace Other\ntheorem sample (x : Nat) : x = x := rfl\nend Other\n'
        row=m.candidate_header(raw,'Requested.sample')
        self.assertIn('namespace-and-kernel-binding-pending',row['status'])
        self.assertEqual(raw[row['byte_start']:row['byte_end']].decode(),row['header_span'])
        with self.assertRaises(ValueError):m.candidate_header(raw+raw,'Requested.sample')
        with self.assertRaises(ValueError):m.candidate_header(b'theorem sample : True','Requested.sample')

    def test_refused_file_stays_present_without_credit(self):
        with tempfile.TemporaryDirectory() as temp:
            with mock.patch.object(m.gate.original.export.census,'declarations_text',side_effect=ValueError('controlled refusal')):
                r=m.run('f994997c163fa341adab6bb872f24dde7857c42c',Path(temp)/'intake')
            self.assertEqual(len(r['files']),len(m.FILES));self.assertEqual(len(r['requested_headers']),len(m.REQUESTED))
            self.assertTrue(all(x.get('lexical_status','').startswith('refused') for x in r['files'] if x['file'].endswith('.lean')))
            self.assertEqual(r['original_obligations_discharged'],0);self.assertFalse(r['compiler_success_kernel_validation']);self.assertFalse(r['runtime_gate_pass'])

    def test_frozen_owner_kernel_and_witness_defaults_never_inherited(self):
        row={'file':'file','line':1,'signature':'theorem x : True','signature_sha256':'text-only','variable_context':[],'visibility':'public','source_name':'Fake.x','kernel_name':'False.certified','owner':'RO','owner_source':'frozen map','dependency_owners':['invented'],'witness_status':'joint-witness','premise_assessment':'proved'}
        result=m.surface_rows([row])[0]
        for key in ['owner','owner_source','dependency_owners','kernel_name','witness_status','premise_assessment']:self.assertNotIn(key,result)
        self.assertEqual(result['candidate_source_name'],'Fake.x');self.assertIn('unverified',result['binding_status'])

    def test_nonexact_commit_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            for head in ['HEAD','--all','f994997']:
                with self.assertRaises(ValueError):m.run(head,Path(temp)/head)

if __name__=='__main__':unittest.main()
