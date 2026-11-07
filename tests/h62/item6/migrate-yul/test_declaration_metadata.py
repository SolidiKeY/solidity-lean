"""Protocol controls are synthetic; compiled fixture behavior is checked separately."""
import copy
import importlib.util
import json
import pathlib
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
scripts = pathlib.Path(__file__).resolve().parents[4] / 'scripts/h62/item6/migrate-yul'
sys.path.insert(0, str(scripts))
spec = importlib.util.spec_from_file_location('declaration_metadata', scripts / 'declaration-metadata.py')
metadata = importlib.util.module_from_spec(spec)
spec.loader.exec_module(metadata)

class DeclarationMetadata(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.raw = pathlib.Path(self.tmp.name) / 'raw.jsonl'
        self.module = metadata.interfaces.module_name('Example')
        self.header = dict(record='header', schema=1, module=self.module,
            loaded_extensions=True, import_all=True, import_level='private',
            expected_declarations=0, expected_classes=0, expected_instances=0, expected_defaults=0)
        self.footer = dict(record='complete', module=self.module,
            declarations=0, classes=0, instances=0, defaults=0, migration_acceptance=False)

    def inspect(self, rows):
        self.raw.write_text(''.join(json.dumps(row)+'\n' for row in rows))
        return metadata.inspect(self.raw, 'Example')

    def declaration(self, suffix):
        return dict(record='declaration', module=self.module,
            name=metadata.interfaces.module_name('Example.'+suffix), display_name=suffix,
            private_name_marker=False, protected=False, **{'class': False},
            active_instance_priority=None)

    def fixture_report(self):
        # Actual declaration-name inventory of the old compiled fixture; no dummy padding.
        suffixes = ['Marker.mk.noConfusion', 'Marker.value', 'privateValue', 'global17',
            'Marker.casesOn', 'private11', 'protectedValue', 'global63', 'Marker',
            'local97', 'Marker.recOn', 'Marker.noConfusion', 'Marker.rec', 'Marker.mk',
            'Marker.mk._flat_ctor', 'Scoped.scoped41', 'Marker.noConfusionType', 'Marker.ctorIdx']
        prefix = 'H62.MigrateYul.MetadataFixture.'
        declarations = []
        for suffix in suffixes:
            row = self.declaration(suffix)
            row.update(name=metadata.interfaces.module_name(prefix+suffix), display_name=prefix+suffix)
            declarations.append(row)
        ds = {d['display_name']: d for d in declarations}
        ds[prefix+'Marker']['class'] = True
        ds[prefix+'protectedValue']['protected'] = True
        ds[prefix+'privateValue']['private_name_marker'] = True
        instances = []
        for suffix, priority, kind, private in [('global17',17,'global',False),
                ('global63',63,'global',False), ('private11',11,'global',True),
                ('Scoped.scoped41',41,'scoped',False)]:
            entry = dict(display_name=prefix+suffix, priority=priority,
                attribute_kind=kind, private_name_marker=private,
                scope_namespace=metadata.interfaces.module_name(prefix+'Scoped') if kind=='scoped' else None)
            instances.append(dict(entry=entry))
            ds[prefix+suffix]['active_instance_priority'] = priority if kind=='global' else None
        classes = [dict(name=ds[prefix+'Marker']['name'], out_parameters=[])]
        defaults = [dict(priority=7, instance_name=ds[prefix+'global17']['name'], class_name=classes[0]['name'])]
        return dict(header=dict(loaded_extensions=True), records=dict(
            declaration=declarations, instance=instances, **{'class': classes}, default_instance=defaults))

    def test_protocol_controls(self):
        self.assertFalse(self.inspect([self.header,self.footer])['migration_acceptance'])
        with self.assertRaisesRegex(ValueError,'incomplete'):
            self.inspect([self.header])
        self.header['loaded_extensions'] = False
        with self.assertRaisesRegex(ValueError,'self-reported extension flag'):
            self.inspect([self.header,self.footer])
        self.header['loaded_extensions'] = True
        self.header['expected_instances'] = 1
        with self.assertRaisesRegex(ValueError,'coverage/count'):
            self.inspect([self.header,self.footer])
        self.header['expected_instances'] = 0
        self.footer['migration_acceptance'] = True
        with self.assertRaisesRegex(ValueError,'acceptance claim'):
            self.inspect([self.header,self.footer])

    def test_duplicate_declaration_rejected(self):
        self.header['expected_declarations'] = self.footer['declarations'] = 2
        row = self.declaration('value')
        with self.assertRaisesRegex(ValueError,'duplicate declaration'):
            self.inspect([self.header,row,copy.deepcopy(row),self.footer])

    def test_index_mismatch_rejected(self):
        self.header['expected_classes'] = self.footer['classes'] = 1
        row = dict(record='class', module=self.module, index=1,
            name=metadata.interfaces.module_name('Example.Marker'), out_parameters=[])
        with self.assertRaisesRegex(ValueError,'order/index'):
            self.inspect([self.header,row,self.footer])

    def test_fixture_positive_and_wrong_priority(self):
        report = self.fixture_report()
        self.assertEqual(len(metadata.check_fixture_records(report)), 6)
        report['records']['instance'][0]['entry']['priority'] = 18  # valid Nat, wrong fixture value
        with self.assertRaisesRegex(ValueError,'priority/kind/private'):
            metadata.check_fixture_records(report)

    def test_fixture_asserts_eighteen_declarations(self):
        report = self.fixture_report()
        report['records']['declaration'].pop()
        with self.assertRaisesRegex(ValueError,'must be 18'):
            metadata.check_fixture_records(report)

    def test_self_reported_true_does_not_establish_initialization(self):
        report = self.fixture_report()
        marker = next(d for d in report['records']['declaration'] if d['display_name'].endswith('.Marker'))
        marker['class'] = False
        self.assertTrue(report['header']['loaded_extensions'])
        with self.assertRaisesRegex(ValueError,'declaration flags'):
            metadata.check_fixture_records(report)

    def test_missing_fields_have_value_error(self):
        del self.header['expected_classes']
        with self.assertRaisesRegex(ValueError,'malformed validation input') as caught:
            self.inspect([self.header,self.footer])
        self.assertIsInstance(caught.exception.__cause__, KeyError)
        with patch.object(metadata.interfaces, 'validate_probe', return_value={}):
            for function, args in [(metadata.seal, (self.raw,'unused','Example')),
                    (metadata.check_fixture, ({},'unused'))]:
                with self.assertRaisesRegex(ValueError,'malformed validation input'):
                    function(*args)
        empty = pathlib.Path(self.tmp.name)/'summary.json'
        empty.write_text('{}')
        with self.assertRaisesRegex(ValueError,'malformed validation input'):
            metadata.check_original_coverage({}, empty)

    def test_nonobject_record_has_value_error(self):
        with self.assertRaisesRegex(ValueError,'malformed validation input'):
            self.inspect([self.header,[],self.footer])

if __name__ == '__main__':
    unittest.main()
