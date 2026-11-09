#!/usr/bin/env python3
"""Negative controls against the actual revision-bound memory-call observations."""
import copy,importlib.util,json,pathlib,sys,unittest
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('memory_call_audit',ROOT/'scripts/roadmap-v16-memory-call-audit.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
DATA=None;LOG=None;REPORT=None
class AuditTests(unittest.TestCase):
    def setUp(self):self.r=copy.deepcopy(REPORT)
    def rejected(self):
        with self.assertRaises(m.core.Invalid):m.validate_report(self.r,DATA,LOG)
    def test_live(self):m.validate_report(self.r,DATA,LOG)
    def test_wrong_revision(self):self.r['producerRevision']='0'*40;self.rejected()
    def test_wrong_head(self):self.r['head']=m.PRODUCER;self.rejected()
    def test_wrong_producer_bytes(self):self.r['producerHashes'][m.FILES[0]]='0'*64;self.rejected()
    def test_constructor_absent(self):self.r['constructor']='absent';self.rejected()
    def test_constructor_closed(self):self.r['constructorStatus']='closed';self.rejected()
    def test_lane_closed(self):self.r['laneComplete']=True;self.rejected()
    def test_stage_closed(self):self.r['stageStatus']['G49.01']='closed';self.rejected()
    def test_erased_input(self):self.r['openPremises'].pop(0);self.rejected()
    def test_fabricated_events(self):self.r['eventBoundary']='full G01 events';self.rejected()
    def test_absent_actual_statement(self):self.r['controls']['theorems'].pop();self.rejected()
    def test_changed_actual_statement(self):self.r['controls']['theorems'][0]['type']='PublicCorrectness';self.rejected()
    def test_assumed_public_correctness(self):self.r['controls']['theorems'][0]['typeConstants'].append('Solidity.Roadmap.PublicCorrectness');self.rejected()
    def test_undesired_axiom(self):self.r['controls']['theorems'][0]['axioms'].append('sorryAx');self.rejected()
    def test_missing_emitter(self):self.r['controls']['definitions']=[];self.rejected()
    def test_changed_scope_boundary(self):self.r['boundary']='all compiler correctness proved';self.rejected()
    def theorem_map(self):
        return {r['name']:r for r in copy.deepcopy(REPORT['controls']['theorems'])}
    def extra_premise_rejected(self,name,is_prop=True):
        rows=self.theorem_map()
        rows[m.P+'memory_call_diamond']['premises'].append(
          {'name':name,'type':'unproved desired conclusion','isProp':is_prop,'constants':['Eq']})
        with self.assertRaises(m.core.Invalid):m.validate_diamond_premises(rows)
    def test_extra_source_success_premise(self):self.extra_premise_rejected('source')
    def test_extra_not_exhausted_premise(self):self.extra_premise_rejected('notExhausted')
    def test_extra_target_run_premise(self):self.extra_premise_rejected('desiredTarget')
    def test_hidden_oracle_parameter(self):self.extra_premise_rejected('oracle',False)
    def test_assumed_capacity(self):
        rows=self.theorem_map()
        rows[m.P+'memory_call_diamond_cursor']['premises'].append(
          {'name':'space','type':'cursor+cost<W','isProp':True,'constants':[]})
        with self.assertRaises(m.core.Invalid):m.validate_diamond_premises(rows)
    def test_input_replaced_by_desired_run(self):
        rows=self.theorem_map();row=rows[m.P+'memory_call_diamond']
        next(p for p in row['premises'] if p['name']=='input')['constants']=['Solidity.Prog.run','Eq']
        with self.assertRaises(m.core.Invalid):m.validate_diamond_premises(rows)
    def test_missing_actual_diamond_premise(self):
        rows=self.theorem_map();row=rows[m.P+'memory_call_diamond']
        row['premises']=[p for p in row['premises'] if p['name']!='diamond']
        with self.assertRaises(m.core.Invalid):m.validate_diamond_premises(rows)
    def test_public_correctness_on_reached_helper(self):
        controls=copy.deepcopy(REPORT['controls'])
        row=next(r for r in controls['theorems'] if r['name']==m.P+'memory_call_success')
        row['typeConstants'].append('Solidity.Roadmap.PublicCorrectness')
        with self.assertRaises(m.core.Invalid):m.validate_scoped_dependencies(controls)
    def test_imported_conditional_retained_outside_scope(self):
        rows=self.theorem_map();name=m.P+'decoded_invariant'
        self.assertIn(name,rows)
        self.assertTrue(any('PublicCorrectness' in c for c in rows[name]['typeConstants']))
        self.assertNotIn(name,m.validate_scoped_dependencies(REPORT['controls']))
        self.assertIn(name,REPORT['importedConditionalOutsideScope'])
    def test_same_input_binder_strengthened(self):
        rows=self.theorem_map();row=rows[m.P+'memory_call_diamond']
        premise=next(p for p in row['premises'] if p['name']=='input')
        premise['type']+=' ∧ desiredTargetRun'
        premise['closedExpr']='And ('+premise['closedExpr']+') desiredTargetRun'
        premise['constants'].append('And')
        with self.assertRaises(m.core.Invalid):m.validate_diamond_premises(rows)
    def test_same_diamond_binder_strengthened(self):
        rows=self.theorem_map();premise=next(p for p in rows[m.P+'memory_call_diamond']['premises'] if p['name']=='diamond')
        premise['type']+=' ∧ sourceSuccess'
        premise['closedExpr']='And ('+premise['closedExpr']+') sourceSuccess'
        with self.assertRaises(m.core.Invalid):m.validate_diamond_premises(rows)
    def test_same_constants_changed_argument_shape(self):
        rows=self.theorem_map();premise=next(p for p in rows[m.P+'memory_call_diamond']['premises'] if p['name']=='input')
        premise['closedExpr']+=' hidden application with unchanged constant set'
        with self.assertRaises(m.core.Invalid):m.validate_diamond_premises(rows)
    def test_same_path_binder_strengthened(self):
        rows=self.theorem_map();premise=next(p for p in rows[m.P+'memory_call_diamond']['premises'] if p['name']=='path')
        premise['type']+=' ∧ oracle'
        with self.assertRaises(m.core.Invalid):m.validate_diamond_premises(rows)
    def test_reached_core_helper_alias_with_public_correctness(self):
        controls=copy.deepcopy(REPORT['controls']);name=m.P+'hiddenInput'
        row=next(r for r in controls['theorems'] if r['name']==m.P+'memory_call_diamond')
        row['dependencies'].append(name)
        controls['definitions'].append({'name':name,'ownerName':name,'dependencies':['Solidity.Roadmap.PublicCorrectness']})
        with self.assertRaises(m.core.Invalid):m.validate_scoped_dependencies(controls)
    def test_missing_reached_core_helper(self):
        controls=copy.deepcopy(REPORT['controls'])
        row=next(r for r in controls['theorems'] if r['name']==m.P+'memory_call_diamond')
        row['dependencies'].append(m.P+'missingCoreAlias')
        with self.assertRaises(m.core.Invalid):m.validate_scoped_dependencies(controls)
    def test_private_reached_helper_with_public_correctness(self):
        controls=copy.deepcopy(REPORT['controls'])
        name='_private.Solidity.Examples.Roadmap.V16.MemoryCallConsumer.0.'+m.P+'secretAlias'
        row=next(r for r in controls['theorems'] if r['name']==m.P+'memory_call_diamond')
        row['dependencies'].append(name)
        controls['definitions'].append({'name':name,'ownerName':m.P+'secretAlias','dependencies':['Solidity.Roadmap.PublicCorrectness']})
        with self.assertRaises(m.core.Invalid):m.validate_scoped_dependencies(controls)
    def test_missing_private_reached_helper(self):
        controls=copy.deepcopy(REPORT['controls'])
        row=next(r for r in controls['theorems'] if r['name']==m.P+'memory_call_diamond')
        row['dependencies'].append('_private.Solidity.Examples.Roadmap.V16.MemoryCallConsumer.0.'+m.P+'missingAlias')
        with self.assertRaises(m.core.Invalid):m.validate_scoped_dependencies(controls)
    def test_same_box_binder_strengthened(self):
        rows=self.theorem_map();premise=next(p for p in rows[m.P+'memory_call_box']['premises'] if p['name']=='box')
        premise['type']+=' ∧ sourceSuccess'
        premise['closedExpr']='And ('+premise['closedExpr']+') sourceSuccess'
        with self.assertRaises(m.core.Invalid):m.validate_diamond_premises(rows)
    def test_extra_source_success_on_box(self):
        rows=self.theorem_map();rows[m.P+'memory_call_box']['premises'].append(
          {'name':'source','type':'desired source success','isProp':True,'closedExpr':'unproved','constants':['Eq']})
        with self.assertRaises(m.core.Invalid):m.validate_diamond_premises(rows)
    def test_box_input_replaced_by_total_success(self):
        rows=self.theorem_map();premise=next(p for p in rows[m.P+'memory_call_box']['premises'] if p['name']=='input')
        premise['constants']=['Solidity.Prog.run','Eq']
        with self.assertRaises(m.core.Invalid):m.validate_diamond_premises(rows)
    def test_box_does_not_assume_no_revert(self):
        rows=self.theorem_map();self.assertEqual(
          [p['name'] for p in rows[m.P+'memory_call_box']['premises'] if p['isProp']],['path','input','box'])
        m.validate_diamond_premises(rows)
    def test_negative_result_not_counted_as_extra_premise(self):
        rows=self.theorem_map();row=rows[m.P+'memory_call_not_exhausted']
        self.assertEqual([p['name'] for p in row['premises']],m.COMMON+['input'])
        m.validate_diamond_premises(rows)
    def test_stale_script(self):self.r['auditScriptSha256']='0'*64;self.rejected()
if __name__=='__main__':
    DATA=json.loads(pathlib.Path(sys.argv[1]).read_text());LOG=pathlib.Path(sys.argv[2]);REPORT=json.loads(pathlib.Path(sys.argv[3]).read_text())
    unittest.main(argv=[sys.argv[0]],verbosity=2)
