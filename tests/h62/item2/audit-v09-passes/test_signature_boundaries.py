#!/usr/bin/env python3
"""Guard equation bodies swallowing following declarations; preserve raw census."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT/'scripts/h62/item2/audit-v09-passes'))
import signature_boundaries as sb
from selected_heap_inventory import source_inventory_keys


def extract(source):
    matches = list(sb.DECL.finditer(sb.masked(source)))
    return [sb.header(source,m.start(),m.end(),matches[i+1].start() if i+1<len(matches) else len(source)) for i,m in enumerate(matches)]


class HeaderBoundaries(unittest.TestCase):
    def test_equations_do_not_consume_next_theorem(self):
        text = 'theorem first : (n : Nat) → n = n\n  | 0 => rfl\n  | n+1 => rfl\ntheorem second : True := by trivial\n'
        first, second = extract(text)
        self.assertEqual(first['header'], 'theorem first : (n : Nat) → n = n')
        self.assertEqual(first['body_kind'], 'equations')
        self.assertEqual(second['header'], 'theorem second : True')

    def test_nested_pipes_and_lets_are_retained(self):
        statement = 'theorem t : (match 0 with\n | 0 => True\n | _ => False) ∧\n let x := 0; let y := x; y = x'
        row, = extract(statement+' := by simp\n')
        self.assertEqual(row['header'], statement)
        self.assertEqual(row['body_kind'], 'assignment')

    def test_comments_strings_and_identifier_let(self):
        text = 'theorem outlet : ("| := match") = "| := match" /- := /- nested -/ | -/ := by rfl'
        row, = extract(text)
        self.assertEqual(row['header'], text[:text.rfind(':=')].strip())

    def test_ambiguous_forms_refused(self):
        for text, reason in [('theorem t : match 0 with\n | 0 => True\n | _ => False := by trivial','top-level-match-before-body'),
                             ('theorem t : «a:=b» = «a:=b» := by rfl','quoted-identifier-before-body'),
                             ('theorem t : True\n |x => x','ambiguous-leading-pipe')]:
            with self.subTest(text=text):
                row, = extract(text)
                self.assertEqual((row['status'],row['reason']),('unresolved',reason))

    def test_missing_body_cannot_borrow_next_assignment(self):
        first, second = extract('theorem first : True\ntheorem second : True := by trivial')
        self.assertEqual(first['status'],'unresolved')
        self.assertEqual(second['status'],'recognized-source-header')

    def test_frozen_equation_oracle_and_membership(self):
        report = sb.frozen_report(ROOT)
        self.assertEqual((report['files'],report['summary']['rows']),(179,1259))
        self.assertFalse(any(r['name']=='Solidity.Backend.Passes.typed_sequencing_assoc' for r in report['rows']))
        import subprocess
        path = 'Solidity/Backend/Passes/Sequence.lean'
        source = subprocess.check_output(['git','show',sb.BASE+':'+path],cwd=ROOT,text=True)
        row, = [r for r in sb.supplement(path,source) if r['name']=='Solidity.Backend.Passes.typed_sequencing_assoc']
        self.assertEqual(row['body_kind'],'equations')
        self.assertNotIn('compilation_sequence_associative',row['header'])
        self.assertNotIn('=>',row['header'])
        self.assertTrue(row['differs_from_legacy'])
        self.assertEqual(len(row['legacy_signature_sha256']),64)


    def test_supplemental_maps_cannot_reduce_selected_census(self):
        import json
        report = sb.frozen_report(ROOT)
        selected = {(r['path'],r['name']) for r in report['rows']}
        supplemental = set()
        for family in ['boundary','stack','core-boundary','private-stack','sequence']:
            mapping = json.loads((Path(__file__).parent/(family+'-witness-map.json')).read_text())
            self.assertEqual(mapping['original_census_accounting']['covered_selected_rows_by_this_map'],0)
            self.assertEqual(mapping['original_census_accounting']['remaining_selected_rows'],1259)
            for row in mapping['covered_premise_bundles']:
                key = (row['path'],row['name'])
                self.assertNotIn(key,selected)
                self.assertNotIn(key,supplemental)
                self.assertFalse(row['original_census_membership'])
                supplemental.add(key)
        self.assertEqual(len(supplemental),19)


    def test_portable_held_inventory_is_exactly_selected(self):
        selected = {(r['path'],r['name']) for r in sb.frozen_report(ROOT)['rows']}
        keys = source_inventory_keys()
        self.assertEqual(len(keys),225)
        self.assertTrue(keys <= selected)

    def test_joined_witnesses_frozen_membership_and_disjointness(self):
        import hashlib
        import json
        import subprocess
        selected = {(r['path'],r['name']):r for r in sb.frozen_report(ROOT)['rows']}
        seen = source_inventory_keys()
        families = [
            ('joined-memory', 'AuditJoinedMemory', ['public_shared','public_failure']),
            ('joined-allocation', 'AuditJoinedAllocation', ['whole_some','whole_public','whole_tail','complete_result','wrong_cursor','wrong_new_reference','stale_initial_map','corrupted_saved_tail'])]
        for stem, namespace, names in families:
            mapping = json.loads((Path(__file__).parent/(stem+'-witness-map.json')).read_text())
            source = subprocess.check_output(['git','show',sb.BASE+':'+mapping['interface']],cwd=ROOT)
            self.assertEqual(hashlib.sha256(source).hexdigest(),mapping['interface_sha256'])
            keys = set()
            for row in mapping['rows']:
                key = (row['path'],row['name'])
                self.assertIn(key,selected)
                self.assertNotIn(key,seen)
                self.assertNotIn(key,keys)
                self.assertEqual(row['signature_sha256'],selected[key]['legacy_signature_sha256'])
                self.assertEqual(row['simultaneous_witness'],'Solidity.Backend.Passes.'+namespace+('.joint_admission' if namespace=='AuditJoinedAllocation' else '.joint'))
                self.assertEqual(row['witness_status'],'checked-original-proof-reuse')
                self.assertEqual(row['exercised_witness'],'Solidity.Backend.Passes.'+namespace+'.'+row['name'].rsplit('.',1)[-1])
                keys.add(key)
            self.assertEqual({name.rsplit('.',1)[-1] for _,name in keys},set(names))
            seen.update(keys)
        private = mapping['checked_private_rows']
        self.assertEqual(private['kernel_prefix'],'_private.Solidity.Backend.Passes.MemoryJoinedAllocationControls.0.')
        self.assertEqual(private['witness_status'],'checked-original-private-signature-and-axioms')
        self.assertEqual(private['simultaneous_witness'],'Solidity.Backend.Passes.AuditJoinedAllocation.joint_admission')
        self.assertEqual(mapping['joint_contract'],'actual-public-whole-selection-full-input-cost-and-source-success')
        self.assertEqual(private['axioms'],['propext','Quot.sound','Classical.choice'])
        self.assertEqual({r['name'].rsplit('.',1)[-1] for r in private['rows']},{'cell'+str(i) for i in range(16)})
        for row in private['rows']:
            key = (private['path'],row['name'])
            self.assertIn(key,selected)
            self.assertNotIn(key,seen)
            self.assertEqual(row['signature_sha256'],selected[key]['legacy_signature_sha256'])
            seen.add(key)
        self.assertEqual((len(seen),1259-len(seen)),(251,1008))
        self.assertEqual(mapping['uncovered_private_rows']['count'],0)
        self.assertEqual(mapping['uncovered_private_rows']['names'],[])

    def test_join_families_frozen_rows_are_distinct_and_complete(self):
        import hashlib
        import json
        import subprocess
        def load(stem):
            return json.loads((Path(__file__).parent/(stem+'-witness-map.json')).read_text())
        selected = {(r['path'],r['name']):r for r in sb.frozen_report(ROOT)['rows']}
        seen = source_inventory_keys()
        for stem in ['joined-memory','joined-allocation']:
            prior = load(stem)
            seen.update((r['path'],r['name']) for r in prior['rows'])
            if 'checked_private_rows' in prior:
                group = prior['checked_private_rows']
                seen.update((group['path'],r['name']) for r in group['rows'])
        self.assertEqual(len(seen),251)
        families = [('join-cost',18,8,'Solidity.Backend.Passes.AuditJoinedAllocation.joint'),
                    ('join-frame',10,0,'Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.joint'),
                    ('triple-admission',30,17,'Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.joint'),
                    ('memory-association',2,0,'Solidity.Backend.Passes.AuditJoinedAllocation.AssociationControls.joint'),
                    ('memory-call',14,4,'Solidity.Backend.Passes.AuditMemoryCall.joint'),
                    ('memory-call-scope',9,1,'Solidity.Backend.Passes.AuditMemoryCall.Scope.joint'),
                    ('returned-memory-capture',6,0,'Solidity.Backend.Passes.AuditJoinedAllocation.ReturnedCapture.joint'),
                    ('allocated-reference-read',21,16,'Solidity.Backend.Passes.AuditJoinedAllocation.AllocatedRead.joint'),
                    ('positive-allocation-failure',10,0,'Solidity.Backend.Passes.AuditPositiveAllocationFailure.joint'),
                    ('preserved-allocator',10,1,'Solidity.Backend.Passes.AuditPreservedAllocator.joint'),
                    ('heap-boundary',14,3,'Solidity.Backend.Passes.AuditHeapBoundary.joint'),
                    ('reframed',11,0,'Solidity.Backend.Passes.AuditReframed.joint'),
                    ('reframed-triple',7,0,'Solidity.Backend.Passes.AuditReframedTriple.joint'),
                    ('loop-scope',18,1,'Solidity.Backend.Passes.AuditLoopScope.joint'),
                    ('loop-prefix',18,0,'Solidity.Backend.Passes.AuditLoopPrefix.joint'),
                    ('loop-call',9,0,'Solidity.Backend.Passes.AuditLoopCall.joint')]
        for stem, total, private_count, joint in families:
            mapping = load(stem)
            source = subprocess.check_output(['git','show',sb.BASE+':'+mapping['interface']],cwd=ROOT)
            self.assertEqual(hashlib.sha256(source).hexdigest(),mapping['interface_sha256'])
            self.assertEqual(mapping['joint_witness'],joint)
            visibility = {r['name']:r['visibility'] for r in sb.declarations(mapping['interface'],source.decode())}
            keys = set()
            for row in mapping['rows']:
                key = (mapping['interface'],row['name'])
                self.assertIn(key,selected)
                self.assertNotIn(key,seen)
                self.assertNotIn(key,keys)
                self.assertEqual(row['signature_sha256'],selected[key]['legacy_signature_sha256'])
                self.assertEqual(row['kind'],'private-exact-kernel-signature' if visibility[row['name']]=='private' else 'public-original-proof-reuse')
                keys.add(key)
            uncovered = {(mapping['interface'],name) for name in mapping.get('uncovered_private_names',[])}
            self.assertFalse(keys & uncovered)
            self.assertEqual(keys|uncovered,{key for key in selected if key[0]==mapping['interface']})
            if stem == 'triple-admission':
                self.assertFalse(uncovered)
                self.assertEqual({r['name'].rsplit('.',1)[-1] for r in mapping['rows'] if r['kind']=='private-exact-kernel-signature'},{'cell'+str(i) for i in range(17)})
                self.assertEqual(mapping['private_axioms'],['propext','Quot.sound','Classical.choice'])
            if stem == 'memory-call':
                self.assertEqual(len(mapping['intentional_refutations']),1)
                self.assertEqual({name.rsplit('.',1)[-1] for _,name in uncovered},{'noRefs'})
                self.assertEqual(set(mapping['checked_private_names']),{'first_some','second_some','final_some','source_get'})
                self.assertEqual(mapping['private_axioms'],['propext','Classical.choice','Quot.sound'])
                for row in mapping['rows']:
                    if row['kind']=='private-exact-kernel-signature':
                        self.assertEqual(row['simultaneous_witness'],'Solidity.Backend.Passes.AuditMemoryCall.'+('source_get_joint' if row['name'].endswith('.source_get') else 'joint'))
            for refutation in mapping.get('intentional_refutations',[]):
                ref_key = (mapping['interface'],refutation['name'])
                self.assertIn(ref_key,uncovered)
                self.assertEqual(refutation['signature_sha256'],selected[ref_key]['legacy_signature_sha256'])
                self.assertEqual(refutation['classification'],'checked-intentional-empty-heap-refutation')
                self.assertEqual(refutation['kernel_name'],mapping['private_kernel_prefix']+refutation['name'])
                self.assertEqual(refutation['premise_impossibility'],mapping['exercised_public_namespace']+'.noRefs_premises_impossible')
                self.assertIsNone(refutation['joint_witness'])
                self.assertEqual(refutation['selected_witness_credit'],0)
                self.assertEqual(refutation['axioms'],['propext'])
            if stem == 'memory-call-scope':
                self.assertFalse(uncovered)
                self.assertEqual(mapping['checked_private_names'],['final_some'])
                self.assertEqual(mapping['private_axioms'],['propext','Classical.choice','Quot.sound'])
                row, = [r for r in mapping['rows'] if r['kind']=='private-exact-kernel-signature']
                self.assertEqual(row['simultaneous_witness'],mapping['joint_witness'])
            if stem == 'returned-memory-capture':
                self.assertEqual(mapping['auxiliary_selected_rows'],0)
                self.assertNotIn('application',{row['name'].rsplit('.',1)[-1] for row in mapping['rows']})
            if stem == 'allocated-reference-read':
                self.assertEqual({r['name'].rsplit('.',1)[-1] for r in mapping['rows'] if r['kind']=='private-exact-kernel-signature'},{'cell'+str(i) for i in range(16)})
                self.assertEqual(mapping['private_axioms'],['propext','Quot.sound','Classical.choice'])
            if stem == 'preserved-allocator':
                self.assertEqual(mapping['joint_contract'],'actual-initial-input-source-success-and-mapped-prefix-output')
                self.assertEqual(mapping['checked_private_names'],['suffix_some'])
                self.assertEqual(mapping['private_axioms'],['propext','Classical.choice','Quot.sound'])
            if stem == 'heap-boundary':
                self.assertEqual({name.rsplit('.',1)[-1] for _,name in uncovered},{'noRefs'})
                self.assertEqual(set(mapping['checked_private_names']),{'first_some','second_some','third_some'})
                self.assertEqual(mapping['private_axioms'],['propext','Classical.choice','Quot.sound'])
                self.assertEqual(len(mapping['intentional_refutations']),1)
            if stem == 'reframed':
                self.assertEqual(mapping['auxiliary_definition_credit'],0)
                self.assertNotIn('words',{r['name'].rsplit('.',1)[-1] for r in mapping['rows']})
            if stem == 'reframed-triple':
                self.assertEqual(mapping['joint_contract'],'actual-preparation-input-source-and-reached-middle-three-word-capacity')
                self.assertEqual(mapping['auxiliary_definition_credit'],0)
                self.assertFalse({'observed','observedRun'} & {r['name'].rsplit('.',1)[-1] for r in mapping['rows']})
            if stem == 'loop-scope':
                self.assertEqual(mapping['joint_contract'],'actual-input-public-loop-recognition-source-body-and-positive-cost-with-distinct-zero-legacy-metric')
                self.assertEqual(mapping['checked_private_names'],['source_get'])
                self.assertEqual(mapping['private_axioms'],['propext','Classical.choice','Quot.sound'])
                row, = [r for r in mapping['rows'] if r['kind']=='private-exact-kernel-signature']
                self.assertEqual(row['simultaneous_witness'],'Solidity.Backend.Passes.AuditLoopScope.extraction_premise')
            self.assertEqual(len(keys),total)
            self.assertEqual(sum(r['kind']=='private-exact-kernel-signature' for r in mapping['rows']),private_count)
            if private_count:
                self.assertEqual(mapping['private_kernel_prefix'],'_private.Solidity.Backend.Passes.'+Path(mapping['interface']).stem+'.0.')
            seen.update(keys)
        self.assertEqual((len(seen),1259-len(seen)),(458,801))



















if __name__ == '__main__':
    unittest.main()
