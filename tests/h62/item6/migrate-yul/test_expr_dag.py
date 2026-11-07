import copy,importlib.util,json,pathlib,unittest
p=pathlib.Path(__file__).resolve().parents[4]/'scripts/h62/item6/migrate-yul/expr_dag.py'
s=importlib.util.spec_from_file_location('dag',p);d=importlib.util.module_from_spec(s);s.loader.exec_module(d)
class DagCodec(unittest.TestCase):
    def leaf(self):return ['const',['str',['anonymous'],'leaf'],[]]
    def test_shared_diamond_stays_linear(self):
        nodes=[self.leaf()]+[['app',i,i] for i in range(64)]
        self.assertEqual(len(d.validate([d.TAG,64,nodes])[2]),65)
    def test_all_binders_and_names_preserved(self):
        versions=[d.from_tree(json.dumps(['lam',['str',['anonymous'],name],['sort',['zero']],['bvar',0],info])) for name in ['x','y'] for info in ['default','implicit','strictImplicit','instImplicit']]
        self.assertEqual(len({d.canonical(x) for x in versions}),8)
    def test_let_flag_preserved(self):
        xs=[d.from_tree(json.dumps(['let',['str',['anonymous'],'x'],['sort',['zero']],self.leaf(),['bvar',0],flag])) for flag in [False,True]]
        self.assertNotEqual(xs[0],xs[1])
    def test_projection_index_preserved(self):
        self.assertNotEqual(d.from_tree(json.dumps(['proj',['anonymous'],0,self.leaf()])),d.from_tree(json.dumps(['proj',['anonymous'],1,self.leaf()])))
    def test_forward_and_self_reference_rejected(self):
        for x in [[d.TAG,0,[['app',0,0]]],[d.TAG,1,[['app',1,1],self.leaf()]]]:
            with self.assertRaises(ValueError):d.validate(x)
    def test_duplicate_and_unreachable_rejected(self):
        other=['const',['str',['anonymous'],'other'],[]]
        for x in [[d.TAG,1,[self.leaf(),self.leaf()]],[d.TAG,1,[self.leaf(),other]]]:
            with self.assertRaises(ValueError):d.validate(x)
    def test_noncanonical_order_rejected(self):
        x=[d.TAG,2,[self.leaf(),['const',['str',['anonymous'],'other'],[]],['app',1,0]]]
        with self.assertRaises(ValueError):d.validate(x)
    def test_invalid_primitives_and_variables_rejected(self):
        for node in [['bvar',True],['nat',-1],['nat',1.0],['string',0],['fvar','x'],['mvar','x'],['sort',['mvar','u']],['const',['num',['anonymous'],True],[]]]:
            with self.assertRaises(ValueError):d.validate([d.TAG,0,[node]])
    def test_invalid_root_rejected(self):
        for root in [-1,True,1.0,1]:
            with self.assertRaises(ValueError):d.validate([d.TAG,root,[self.leaf()]])
    def test_sharing_and_independent_copies_agree(self):
        atom=self.leaf();shared=['app',atom,atom];copies=['app',copy.deepcopy(atom),copy.deepcopy(atom)]
        self.assertEqual(d.from_tree(json.dumps(shared)),d.from_tree(json.dumps(copies)))
if __name__=='__main__':unittest.main()
