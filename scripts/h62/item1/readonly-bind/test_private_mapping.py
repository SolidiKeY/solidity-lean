"""Guard private mappings erasing inputs or conflating intrinsic signatures."""
import copy
import hashlib
import unittest
import private_mapping as mapping

SIGNATURE="""private theorem run_bind {α β : Type} (m : EM E Γ α) (k : α → EM E Γ β)
    (x : Locals E.layout Γ × St E) :
    (m >>= k).run x = match m.run x with
      | (.ok a, y) => (k a).run y
      | (.error e, y) => (.error e, y)"""


def sample():
    rows=[]
    for name in mapping.NAMES:
        rows.append({'file':'Solidity/Lowering/Readonly/'+name+'.lean','source_name':mapping.PREFIX+name+'.run_bind','visibility':'private','signature':SIGNATURE,'signature_sha256':hashlib.sha256(SIGNATURE.encode()).hexdigest(),'variable_context':['variable {E : Env}'] if name=='EnvironmentCredit' else ['variable {E : Env} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}']})
    rows += [{'file':'Other.lean','source_name':'Other.t'+str(i)} for i in range(789)]
    return {'base':mapping.export.census.BASE,'theorem_count':792,'declarations':rows}


class PrivateMappingControls(unittest.TestCase):
    def test_exact_three_selected_without_modifying_original(self):
        data=sample();original=copy.deepcopy(data);rows=mapping.select(data)
        self.assertEqual(len(rows),3);self.assertEqual(data,original)
        rows[0]['signature']='changed';self.assertEqual(data,original)

    def test_missing_duplicate_and_wrong_count_refused(self):
        for kind in ('missing','duplicate','count'):
            data=sample()
            if kind=='missing':data['declarations'][0]['source_name']='Other.missing'
            elif kind=='duplicate':data['declarations'][-1]=copy.deepcopy(data['declarations'][0])
            else:data['declarations'].pop()
            with self.subTest(kind=kind),self.assertRaises(ValueError):mapping.select(data)

    def test_intrinsic_context_change_refused_even_with_rehashed_statement(self):
        data=sample();row=data['declarations'][0]
        row['signature']=row['signature'].replace('EM E Γ α','EM E [] α')
        row['signature_sha256']=hashlib.sha256(row['signature'].encode()).hexdigest()
        with self.assertRaisesRegex(ValueError,'statement drift'):mapping.select(data)

    def test_variable_context_visibility_and_module_refused(self):
        for key,value in [('variable_context',['variable {E : OtherEnv}']),('visibility','public'),('file','Other.lean')]:
            data=sample();data['declarations'][0][key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):mapping.select(data)

    def test_generated_proofs_preserve_full_input_statement_and_shared_law(self):
        source=mapping.generate(mapping.select(sample()))
        self.assertEqual(source.count('theorem statement {α β : Type}'),3)
        self.assertEqual(source.count('exact Solidity.Source.Hoare.run_bind m k x'),3)
        self.assertNotIn('namespace Solidity.Lowering.Readonly.',source)
        self.assertIn('parameter-domain satisfiability only',source)

    def axiom_log(self):
        rows=mapping.select(sample())
        return rows,'\n'.join("'"+r['source_name']+"' depends on axioms: [propext,\n Classical.choice, Quot.sound]" for r in mapping.inventory(rows)['declarations'])

    def test_exact_axiom_inventory_checked(self):
        rows,log=self.axiom_log();self.assertEqual(len(mapping.check_axioms(log,rows)),5)

    def test_unknown_axiom_is_refused(self):
        rows,log=self.axiom_log()
        with self.assertRaisesRegex(ValueError,'unexpected theorem axiom'):mapping.check_axioms(log.replace('propext','injectedAxiom',1),rows)

    def test_missing_duplicate_or_foreign_axiom_record_refused(self):
        rows,log=self.axiom_log()
        for changed in [log[:log.rfind("'Solidity.H62.ReadonlyBind.Mappings.joint_parameters'")],log+"\n"+log,log.replace('Solidity.Source.Hoare.run_bind','Other.theorem')]:
            with self.assertRaises(ValueError):mapping.check_axioms(changed,rows)

    def test_cached_presence_is_observed_not_assumed_absent(self):
        query=mapping.query(mapping.select(sample()))
        self.assertEqual(query.count('PRIVATE_BIND_STATUS'),3)
        self.assertNotIn('PRIVATE_BIND_ABSENT',query)
        self.assertIn('env.contains oldName',query)


if __name__=='__main__':unittest.main()
