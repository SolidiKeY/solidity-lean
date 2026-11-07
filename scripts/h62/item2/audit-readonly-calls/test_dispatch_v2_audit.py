"""Guard dropping original obligations or promoting a source mapping to proof."""
import copy
import unittest
import dispatch_v2_audit as audit


class DispatchSupplementControls(unittest.TestCase):
    def sample(self):
        old={"base":audit.census.BASE,"theorem_count":792,"declarations":[{"file":"Original.lean","source_name":"Original.n"+str(i),"witness_status":"pending"} for i in range(792)]}
        rows=[{"file":audit.FILES[0] if n in audit.NAMES[:6] else audit.FILES[1],"source_name":audit.PREFIX+n} for n in audit.NAMES]
        return old,rows

    def test_all_original_records_preserved_independently(self):
        old,rows=self.sample();value=audit.assemble(old,rows)
        self.assertEqual(value['original_snapshot'],old)
        old['declarations'][0]['witness_status']='changed'
        self.assertEqual(value['original_snapshot']['declarations'][0]['witness_status'],'pending')
        self.assertEqual(value['theorem_count'],9)

    def test_missing_duplicate_or_unknown_interface_refused(self):
        for kind in ('missing','duplicate','unknown'):
            old,rows=self.sample()
            if kind=='missing':rows.pop()
            elif kind=='duplicate':rows[-1]=copy.deepcopy(rows[0])
            else:rows[-1]['source_name']='Other.theorem'
            with self.subTest(kind=kind),self.assertRaises(ValueError):audit.assemble(old,rows)

    def test_wrong_original_base_count_or_identity_refused(self):
        for kind in ('base','count','duplicate'):
            old,rows=self.sample()
            if kind=='base':old['base']='wrong'
            elif kind=='count':old['declarations'].pop()
            else:old['declarations'][-1]=copy.deepcopy(old['declarations'][0])
            with self.subTest(kind=kind),self.assertRaises(ValueError):audit.assemble(old,rows)

    def test_wrong_interface_module_refused(self):
        old,rows=self.sample();rows[0]['file']=audit.FILES[1]
        with self.assertRaisesRegex(ValueError,'module drift'):audit.assemble(old,rows)

    def test_three_joint_clients_are_pending_checks_not_proof_stamps(self):
        value=audit.assemble(*self.sample())
        clients=[r for r in value['declarations'] if r['joint_client']]
        self.assertEqual(len(clients),3)
        self.assertTrue(all(r['witness_status']=='joint-client-pending-check' for r in clients))
        self.assertEqual(len([r for r in value['declarations'] if r['witness_status']=='no-named-input-proof-binder']),6)


if __name__=='__main__':unittest.main()
