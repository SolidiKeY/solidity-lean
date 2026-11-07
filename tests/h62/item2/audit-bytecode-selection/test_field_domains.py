"""Guard omission of projection self/capacity binders and stale field types."""
from pathlib import Path
import copy,json,sys,unittest,hashlib,types,subprocess
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'scripts/h62/item2/audit-bytecode-selection'))
import exact_domains as renderer
import test_kernel_metadata as fixtures

class FieldDomainTests(unittest.TestCase):
    def fixture(self):
        row=fixtures.MetadataSchemaTests().row()
        row.update(module='Solidity.Backend.Selection.InterfaceV2',interface_or_premises_module=True,
                   is_projection=True,kind='field')
        witnesses={'joint':{'target':row['name'],'proof':'⟨True.intro⟩'}}
        return row,witnesses
    def test_reuses_extractor_and_pins_full_field_snapshot(self):
        row,w=self.fixture();source,pins=renderer.projection_domain_source(ROOT,[row],w)
        self.assertIn(renderer.macro_fragment((ROOT/renderer.MACRO_PATH).read_text()),source)
        self.assertIn('env.getProjectionFnInfo? name',source)
        self.assertIn('explicitDomain info.type',source)
        self.assertIn('field_hypotheses_named%',source)
        self.assertIn('empty_field_domain_refuted',source)
        self.assertIn('field_hypotheses_of% PolyFieldToy.good',source)
        self.assertEqual(pins['targets']['joint']['observed_type']['type_expr'],row['type_expr'])
        self.assertFalse(pins['original_conclusions_proved'])
        self.assertFalse(pins['global_witness_ledger_linked'])
        changed=copy.deepcopy(row);changed['type_expr']='another expression'
        self.assertNotEqual(renderer.projection_domain_source(ROOT,[changed],w)[1]['generated_lean_sha256'],pins['generated_lean_sha256'])
    def test_refuse_data_nonprojection_universes_and_forbidden_proof(self):
        row,w=self.fixture()
        for key,value in [('proof_type',False),('is_projection',False),('level_params',['u'])]:
            bad=copy.deepcopy(row);bad[key]=value
            if key=='is_projection':bad['kind']='constant'
            with self.subTest(key=key),self.assertRaises(ValueError):renderer.projection_domain_source(ROOT,[bad],w)
        for proof in ['', 'by sorry', 'by native_decide', 'by admit']:
            bad=copy.deepcopy(w);bad['joint']['proof']=proof
            with self.subTest(proof=proof),self.assertRaises(ValueError):renderer.projection_domain_source(ROOT,[row],bad)
        with self.assertRaises(ValueError):renderer.projection_domain_source(ROOT,[row],{'bad name':w['joint']})
        with self.assertRaises(ValueError):renderer.projection_domain_source(ROOT,[row],{'one':w['joint'],'two':w['joint']})
        bad=copy.deepcopy(w);bad['joint']['target']=[]
        with self.assertRaises(ValueError):renderer.projection_domain_source(ROOT,[row],bad)
    def test_real_fixture_retains_v2_and_adds_selection_domains(self):
        w=json.loads((ROOT/'tests/h62/item2/audit-bytecode-selection/selection-field-witnesses.json').read_text())
        prefix='Solidity.Backend.Selection.V2.FrameCertificate.'
        self.assertEqual({p['target'] for p in w.values() if p['target'].startswith(prefix)},{prefix+x for x in ['inputRoom','frame','capacity']})
        self.assertTrue(all('duplicateHead 7' in p['proof'] for p in w.values() if 'FrameCertificate.' in p['target']))
        self.assertIn('[11,99]',w['frame_capacity_joint_domain']['proof'])
        self.assertIn('by decide',w['frame_capacity_joint_domain']['proof'])
        self.assertEqual(len(w),7)
        self.assertIn('rfl, rfl, True.intro',w['legacy_prefixes_joint_domain']['proof'])
        self.assertTrue(all('literalCertificate value' in w[k]['proof'] for k in ['instruction_success_joint_domain','instruction_refusal_joint_domain']))


    def test_compiler_fixture_retains_global_self_and_relation(self):
        w=json.loads((ROOT/'tests/h62/item2/audit-bytecode-selection/compiler-field-witnesses.json').read_text())
        self.assertEqual({p['target'] for p in w.values()},{
            'Solidity.Backend.Selection.CompilerPremise.preserves',
            'Solidity.Backend.Selection.V2.CompilerPremise.preserves',
            'Solidity.Backend.Selection.V2.CompilerPremise.inhabited'})
        self.assertTrue(all('identityCompiler' in p['proof'] for p in w.values()))
        for name in ['compiler_v1_preserves_joint_domain','compiler_v2_preserves_joint_domain']:
            self.assertIn('irStack [11]',w[name]['proof'])
            self.assertIn('caller, caller, rfl, True.intro',w[name]['proof'])
        self.assertTrue(all('False' not in p['proof'] for p in w.values()))


    def test_shared_support_is_pinned_once_and_default_output_unchanged(self):
        row,w=self.fixture()
        support=(ROOT/'tests/h62/item2/audit-bytecode-selection/decoder-field-support.lean.txt').read_text()
        source,pins=renderer.projection_domain_source(ROOT,[row],w,support_source=support)
        self.assertEqual(source.count('def referenceDecoder ('),1)
        self.assertEqual(pins['support_source_sha256'],hashlib.sha256(support.encode()).hexdigest())
        for bad in [False, 'axiom invented : True', 'unsafe def invented := 1']:
            with self.subTest(bad=bad),self.assertRaises(ValueError):renderer.projection_domain_source(ROOT,[row],w,support_source=bad)
        old=types.ModuleType('old_field_renderer');old.__file__=str(ROOT/'scripts/h62/item2/audit-bytecode-selection/exact_domains.py')
        raw=subprocess.check_output(['git','show','87b874958cc3d509e688b7ec3f867b613750e737:scripts/h62/item2/audit-bytecode-selection/exact_domains.py'],cwd=ROOT)
        exec(compile(raw,old.__file__,'exec'),old.__dict__)
        self.assertEqual(renderer.projection_domain_source(ROOT,[row],w),old.projection_domain_source(ROOT,[row],w))
    def test_decoder_fixture_has_actual_closed_step_and_shared_self(self):
        w=json.loads((ROOT/'tests/h62/item2/audit-bytecode-selection/decoder-field-witnesses.json').read_text())
        self.assertEqual({x['target'] for x in w.values()},{'Solidity.Backend.Selection.DecoderPremise.'+x for x in ['entry','closed','agrees','zero','succ']})
        self.assertTrue(all('referenceDecoder [0x5b] 1' in x['proof'] for x in w.values()))
        self.assertIn('reference_jumpdest_step',w['decoder_closed_joint_domain']['proof'])
        support=(ROOT/'tests/h62/item2/audit-bytecode-selection/decoder-field-support.lean.txt').read_text()
        self.assertIn('theorem decoder_missing_supported_step_refused',support)
        self.assertIn('decoder_jumpdest_reject_all_refused',support)
        self.assertIn('⟨1,[11]⟩',w['decoder_closed_joint_domain']['proof'])

if __name__=='__main__':unittest.main()
