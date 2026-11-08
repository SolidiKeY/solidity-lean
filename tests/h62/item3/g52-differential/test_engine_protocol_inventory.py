"""Guarded regression: a mixed or malformed Engine profile never gains execution credit."""
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch
import tempfile

SOURCE = Path(__file__).resolve().parents[4]/'scripts/h62/item3/g52-differential/engine_protocol_inventory.py'
spec = importlib.util.spec_from_file_location('engine_protocol_inventory', SOURCE)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


def record(index=0, requests=None):
    return dict(index=index, path='p', case='c', fixture=dict(network='Osaka',
                _info={'fixture-format': 'blockchain_test_engine_x'},
                engineNewPayloads=requests if requests is not None else [
                    dict(newPayloadVersion=4, forkchoiceUpdatedVersion=3, params=[{}, [], '0x' + '00'*32, []])]))


class Profiles(unittest.TestCase):
    def test_mixed_positive_and_expected_error_remain_one_unexecuted_case(self):
        row = record()
        row['fixture']['engineNewPayloads'].append(dict(newPayloadVersion=4, forkchoiceUpdatedVersion=3,
                                                      params=[{}, [], '0x' + '00'*32, []], validationError='INVALID'))
        result = m.inventory([row], 1)
        self.assertEqual(result['case_profile_counts'], {'extra-request-fields': 1})
        self.assertEqual(result['rows'][0]['requests'][1]['extra_keys'], ['validationError'])
        self.assertEqual((result['executed_cases'], result['source_matches'], result['differential_complete']), (0, 0, False))

    def test_shape_candidates_are_not_execution(self):
        result = m.inventory([record()], 1)
        self.assertEqual(result['case_profile_counts'], {'outer-envelope-candidate': 1})
        self.assertEqual(result['executed_cases'], 0)

    def test_empty_request_list_stays_visible(self):
        result = m.inventory([record(requests=[])], 1)
        self.assertEqual(result['case_profile_counts'], {'empty-payload-sequence': 1})

    def test_version_and_parameter_gaps_are_all_retained(self):
        row = record(requests=[dict(newPayloadVersion=3, forkchoiceUpdatedVersion=2, params=None)])
        result = m.inventory([row], 1)
        self.assertEqual(result['rows'][0]['issues'], ['forkchoice-version', 'new-payload-version', 'parameter-shape'])

    def test_noncanonical_versions_and_inner_shapes_stay_visible(self):
        profile = m.request_profile(dict(newPayloadVersion=4.0, forkchoiceUpdatedVersion=3.0, params=[None, None, 'bad', {}]))
        self.assertEqual(set(profile['issues']), {'new-payload-version', 'forkchoice-version', 'payload-object-shape', 'blob-hashes-shape', 'beacon-root-shape', 'execution-requests-shape'})
        self.assertEqual(profile['parameter_types'], ['NoneType', 'NoneType', 'str', 'dict'])

    def test_cli_refuses_overwriting_input_before_archive_work(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root/'engine-x-inputs.jsonl.gz'
            target.write_bytes(b'pinned input')
            with patch('sys.argv', ['inventory', '--bulk', str(root), '--output', str(target)]), patch.object(m, 'build') as build, self.assertRaises(SystemExit) as stop:
                m.main()
            self.assertEqual(stop.exception.code, 2)
            build.assert_not_called()
            self.assertEqual(target.read_bytes(), b'pinned input')

    def test_identity_count_and_malformed_requests_refuse(self):
        for rows, count in [([record(index=True)], 1), ([record(), record()], 2),
                            ([record()], 2), ([record(requests=[None])], 1)]:
            with self.subTest(rows=rows, count=count), self.assertRaises(ValueError):
                m.inventory(rows, count)


if __name__ == '__main__':
    unittest.main()
