#!/usr/bin/env python3
import copy,importlib.util,sys,unittest
from pathlib import Path
root=Path(__file__).resolve().parents[4] if 'tests/h62' in str(Path(__file__).resolve()) else Path('/workspace/solidity-lean')
sys.path.insert(0,str(root/'scripts/h62/item6/migrate-testsuite'))
from dag_codec import DagStore
NAT=['str',['anonymous'],'Nat']
def node(index,tag,data,children=(),module='M'):
    return {'module':module,'id':index,'tag':tag,'data':data,'children':list(children)}
class DagControls(unittest.TestCase):
    def test_root_independent_of_node_numbering(self):
        a=DagStore({'M'});b=DagStore({'N'})
        a.add(node(0,'const',[NAT,[]]));a.add(node(1,'nat','3'));a.add(node(2,'app',None,[0,1]))
        b.add(node(0,'str','unused',module='N'));b.add(node(1,'const',[NAT,[]],module='N'));b.add(node(2,'nat','3',module='N'));b.add(node(3,'app',None,[1,2],module='N'))
        self.assertEqual(a.root('M',2),b.root('N',3))
    def test_changed_literal_changes_hash(self):
        a=DagStore({'M'});a.add(node(0,'nat','3'));a.add(node(1,'nat','4'))
        self.assertNotEqual(a.root('M',0),a.root('M',1))
    def test_binder_name_preserved(self):
        a=DagStore({'M'});a.add(node(0,'const',[NAT,[]]));a.add(node(1,'bvar','0'))
        a.add(node(2,'lam',[['str',['anonymous'],'x'],'default'],[0,1]));a.add(node(3,'lam',[['str',['anonymous'],'y'],'default'],[0,1]))
        self.assertNotEqual(a.root('M',2),a.root('M',3))
    def test_forward_or_cyclic_edge_rejected(self):
        with self.assertRaisesRegex(ValueError,'INVALID_NODE_EDGES'): DagStore({'M'}).add(node(0,'app',None,[0,0]))
    def test_wrong_arity_rejected(self):
        a=DagStore({'M'});a.add(node(0,'nat','0'))
        with self.assertRaisesRegex(ValueError,'INVALID_NODE_EDGES'): a.add(node(1,'app',None,[0]))
    def test_duplicate_id_rejected(self):
        a=DagStore({'M'});a.add(node(0,'nat','0'))
        with self.assertRaisesRegex(ValueError,'INVALID_NODE_ID_OR_TAG'): a.add(node(0,'nat','1'))
    def test_malformed_name_rejected(self):
        with self.assertRaisesRegex(ValueError,'INVALID_NODE_PAYLOAD'): DagStore({'M'}).add(node(0,'const',[['str','bad','x'],[]]))
    def test_noncanonical_nat_rejected(self):
        with self.assertRaisesRegex(ValueError,'INVALID_NODE_PAYLOAD'): DagStore({'M'}).add(node(0,'nat','01'))
    def test_extra_fields_rejected(self):
        row=node(0,'nat','0');row['ignored']='semantic field'
        with self.assertRaisesRegex(ValueError,'INVALID_NODE_SCHEMA'): DagStore({'M'}).add(row)
    def test_missing_root_rejected(self):
        with self.assertRaisesRegex(ValueError,'INVALID_EXPRESSION_ROOT'): DagStore({'M'}).root('M',0)
    def test_closed_module_rejects_late_nodes(self):
        a=DagStore({'M'});a.finish('M')
        with self.assertRaisesRegex(ValueError,'INVALID_NODE_MODULE'): a.add(node(0,'nat','0'))
    def test_metadata_order_normalized_and_content_preserved(self):
        a=DagStore({'M'});a.add(node(0,'nat','0'))
        x=[NAT,['syntax',['atom','x']]];y=[['str',['anonymous'],'flag'],['bool',True]]
        a.add(node(1,'mdata',[x,y],[0]));a.add(node(2,'mdata',[y,x],[0]))
        self.assertEqual(a.root('M',1),a.root('M',2))
        z=copy.deepcopy(x);z[1][1][1]='y'
        a.add(node(3,'mdata',[z,y],[0]));self.assertNotEqual(a.root('M',1),a.root('M',3))
    def test_duplicate_metadata_wire_keys_rejected(self):
        a=DagStore({'M'});a.add(node(0,'nat','0'));x=[NAT,['bool',True]]
        with self.assertRaisesRegex(ValueError,'INVALID_NODE_PAYLOAD'): a.add(node(1,'mdata',[x,x],[0]))
if __name__=='__main__': unittest.main()
