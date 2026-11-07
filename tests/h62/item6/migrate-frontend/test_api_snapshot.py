"""Acceptance rejects substituted census/configuration/source snapshots."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location('api_snapshot',ROOT/'scripts/h62/item6/migrate-frontend/api_snapshot.py')
a=importlib.util.module_from_spec(spec)
spec.loader.exec_module(a)

class APIBindingControls(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        (self.root/'lakefile.toml').write_text('tracked configuration')
        self.private=self.root/'private.toml';self.private.write_text('private configuration')
        self.source=self.root/'Source.lean';self.source.write_text('def value := 1\n')
        self.census={'topological_closure':['Source'],'closure_sources':[{'path':'Source.lean','sha256':a.sha(self.source)}],'scope_files':[]}
        self.cp=self.root/'census.json';self.cp.write_text(json.dumps(self.census))
        self.meta={'status':'pass','targets':['Source'],'census_sha256':a.sha(self.cp),
                   'results':[{'command':['lake','--file',str(self.private)]}],
                   'private_config_sha256':a.sha(self.private),
                   'tracked_lakefile_sha256':a.sha(self.root/'lakefile.toml')}

    def validate(self): return a.validate_inputs(self.meta,self.census,self.cp,self.root)

    def test_exact_bindings_are_accepted(self):
        self.assertEqual(self.validate(),str(self.private))

    def test_substituted_census_is_rejected(self):
        self.cp.write_text('{}')
        with self.assertRaisesRegex(SystemExit,'Census provenance'): self.validate()

    def test_private_configuration_change_is_rejected(self):
        self.private.write_text('different flags')
        with self.assertRaisesRegex(SystemExit,'Private configuration'): self.validate()

    def test_tracked_configuration_change_is_rejected(self):
        (self.root/'lakefile.toml').write_text('different root flags')
        with self.assertRaisesRegex(SystemExit,'Tracked configuration'): self.validate()

    def test_source_change_is_rejected(self):
        self.source.write_text('def value := 2\n')
        with self.assertRaisesRegex(SystemExit,'Source drift'): self.validate()

    def test_incomplete_build_is_rejected(self):
        self.meta['status']='failed'
        with self.assertRaisesRegex(SystemExit,'Full passing'): self.validate()

if __name__=='__main__': unittest.main()
