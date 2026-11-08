#!/usr/bin/env python3
"""Small parser regression fixtures; no compiler/server or external packages."""
import importlib.util,pathlib,unittest
p=pathlib.Path(__file__).with_name('audit.py')
spec=importlib.util.spec_from_file_location('audit',p);a=importlib.util.module_from_spec(spec);spec.loader.exec_module(a)
class Parser(unittest.TestCase):
    def test_nested_comments_and_strings(self):
        raw='/- outer /- theorem fake := by sorry -/ -/\n"theorem nope := by sorry"\ntheorem yes : True := by trivial\n'
        ds=a.lean_decls('x',raw)
        self.assertEqual([d['name'] for d in ds],['yes'])
        self.assertEqual(len(a.mask(raw)),len(raw))
        self.assertEqual(a.mask(raw).count('\n'),raw.count('\n'))
    def test_body_stops_before_commands(self):
        raw='@[simp]\ntheorem a : True := by\n  exact True.intro\nend X\n#print axioms a\nexample : True := by trivial\n'
        d=a.lean_decls('x',raw)[0]
        self.assertEqual(d['lines'],1);self.assertNotIn('end',d['proof']);self.assertNotIn('example',d['proof'])
    def test_binder_default_does_not_start_proof(self):
        d=a.lean_decls('x','theorem a (n : Nat := 2) : n = n := by rfl\n')[0]
        self.assertEqual(d['proof'],'rfl');self.assertEqual(d['lines'],1)
    def test_term_proof(self):
        d=a.lean_decls('x','lemma a : True := True.intro\n')[0]
        self.assertEqual(d['proof'],'True.intro')
    def test_simp_sets(self):
        self.assertEqual(a.simp_sizes('simp only [f (x, y), h]'),[2])
        self.assertEqual(a.simp_sizes('simp []'),[0])
    def test_foreign_proofs(self):
        coq='Lemma a: True. Proof. exact I. Qed.\nLemma b: True. Proof. (*nested (* hi *)*) exact I. Qed.'
        ds,h=a.foreign('x',coq,'coq');self.assertEqual((len(ds),h),(2,2));self.assertEqual(ds[0]['lines'],1)
        hol='Theorem a[simp]:\n T\nProof\n simp[]\nQED\n'
        ds,h=a.foreign('x',hol,'hol');self.assertEqual((len(ds),h),(1,1));self.assertEqual(ds[0]['lines'],1);self.assertEqual(ds[0]['line'],1)
    def test_generation_is_not_name_guess(self):
        self.assertEqual(a.gen('Solidity/Foo/Agreement.lean',''),'unresolved_chain_agreement')
        self.assertEqual(a.gen('Generated/VC.lean',''),'generated_vc')
    def test_numerals_not_erased_from_duplicate_proofs(self):
        self.assertNotEqual(a.alpha_proof('exact f 12'),a.alpha_proof('exact f 13'))
    def test_float_and_unbounded_histogram(self):
        for xs in ([.2,.5,1.2,3.3],[1000001,2000000]):
            x=a.dist(xs);self.assertEqual(sum(x['histogram'].values()),x['n'])
    def test_vendor_import_slice(self):
        tx={'Bridge/SolidityBridge/X.lean':'import V.Y\nlemma a : True := b\n','Bridge/vendor/V/Y.lean':'lemma b : True := True.intro\n'}
        a._SLICE_CACHE.clear()
        x=a.slice_count(tx,[('Bridge/SolidityBridge/X.lean','a')],'Bridge/SolidityBridge/')
        self.assertEqual(x['scope']['declarations'],1);self.assertEqual(x['vendored']['declarations'],1)
        self.assertEqual(x['all_tracked']['declarations'],2);self.assertEqual(x['external_imports'],[])
        a._SLICE_CACHE.clear()
    def test_distribution_denominator(self):
        x=a.dist([1,2,100]);self.assertEqual(x['total'],103);self.assertEqual(x['p50'],2)
        self.assertEqual(sum(x['histogram'].values()),x['n'])
if __name__=='__main__':unittest.main()
