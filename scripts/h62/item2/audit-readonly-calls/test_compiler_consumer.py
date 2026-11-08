"""Guard duplicate identities, forged source locations and extra axioms in kernel links."""
import copy
import importlib.util
from pathlib import Path
import unittest
spec=importlib.util.spec_from_file_location('consumer',Path(__file__).with_name('compiler_consumer.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class KernelControls(unittest.TestCase):
    def fixture(self):
        file='Solidity/Fixture.lean';raw=b''.join(('theorem f'+str(i)+' : True := True.intro\n').encode() for i in range(9));c=[];s=[];t=[];loc=[]
        start=0
        for i,line in enumerate(raw.splitlines(keepends=True)):
            short='f'+str(i);name='Fixture.'+short;a=start+8;b=a+len(short);end=start+len(line)
            c.append({'candidate_source_name':name,'file':file,'name_span':short,'signature_range':{'start':b,'end':end},'header_span_sha256':'surface'})
            s.append({'name':short,'name_range':{'start':a,'end':b},'signature_range':c[-1]['signature_range']})
            t.append({'source_name':name,'kernel_name':name,'module':'Solidity.Fixture','raw_type_expr':'True','pretty_type':'True'})
            loc.append({'source_name':name,'start':{'line':i+1,'column':8},'end':{'line':i+1,'column':8+len(short)}})
            start=end
        return c,[{'path':file,'records':s}],t,loc,{file:raw}

    def test_complete_direct_binding_and_no_ownership_claim(self):
        rows=m.bind_rows(*self.fixture());self.assertEqual(len(rows),9)
        self.assertTrue(all(not r['ownership_verified'] for r in rows))

    def test_missing_duplicate_wrong_module_and_empty_type_refused(self):
        for kind in ['missing','duplicate','module','kernel','empty']:
            args=list(self.fixture());types=args[2]
            if kind=='missing':types.pop()
            if kind=='duplicate':types[-1]=copy.deepcopy(types[0])
            if kind=='module':types[0]['module']='Wrong.Module'
            if kind=='kernel':types[0]['kernel_name']='Wrong.name'
            if kind=='empty':types[0]['raw_type_expr']=''
            with self.assertRaises(ValueError):m.bind_rows(*args)

    def test_source_selection_and_syntax_substitution_refused(self):
        args=list(self.fixture());args[3][0]['start']['column']=7
        with self.assertRaises(ValueError):m.bind_rows(*args)
        args=list(self.fixture());args[1][0]['records'][0]['name_range']['start']=0
        with self.assertRaises(ValueError):m.bind_rows(*args)

    def test_multiline_axioms_missing_duplicate_or_extra_refused(self):
        names=['A.x','A.y'];lines=["'"+n+"' depends on axioms: [propext,\n Classical.choice, Quot.sound]" for n in names]
        self.assertEqual(len(m.parse_axioms('\n'.join(lines),names)),2)
        for log in [lines[0],'\n'.join(lines+[lines[0]]),'\n'.join(lines).replace('propext','sorryAx')]:
            with self.assertRaises(ValueError):m.parse_axioms(log,names)

    def test_unicode_positions_and_invalid_coordinates(self):
        raw='αβ\nz'.encode();self.assertEqual(m.byte_position(raw,{'line':1,'column':1}),2)
        self.assertEqual(m.byte_position(raw,{'line':2,'column':0}),5)
        for pos in [{'line':True,'column':0},{'line':0,'column':0},{'line':1,'column':3}]:
            with self.assertRaises(ValueError):m.byte_position(raw,pos)

if __name__=='__main__':unittest.main()
