import unittest
from correspondence import compare

class CorrespondenceControls(unittest.TestCase):
    original = "theorem byte_component : True := True.intro\ntheorem byte_component_decode : True := True.intro\n"
    candidate = "theorem original_byte_component : True := True.intro\ntheorem original_byte_component_decode : True := True.intro\n"
    def test_exact_instances(self):
        self.assertEqual(len(compare(self.original,self.candidate)),2)
    def test_changed_observation_refused(self):
        with self.assertRaises(ValueError): compare(self.original,self.candidate.replace(': True', ': False',1))
    def test_dropped_instance_refused(self):
        with self.assertRaises(ValueError): compare(self.original,self.candidate.splitlines()[0])

if __name__ == "__main__": unittest.main()
