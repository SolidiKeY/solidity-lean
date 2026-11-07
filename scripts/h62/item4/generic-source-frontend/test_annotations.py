"""Guard regression: annotations must not mask proof, path, mode or inventory changes."""
import unittest
from acceptance import ANNOTATION, allowed_source_delta, check_changed_paths


class AnnotationTests(unittest.TestCase):
    path = 'Solidity/Frontend/NumericLiteralProofs/WordTable/Part00.lean'
    frozen = b'import Base\n\ntheorem stable : True := by trivial\n'

    def annotated(self):
        first, _, tail = self.frozen.partition(b'\n')
        return first+b'\n'+ANNOTATION+tail

    def test_unchanged(self):
        self.assertFalse(allowed_source_delta(self.path,self.frozen,self.frozen))

    def test_exact_annotation(self):
        self.assertTrue(allowed_source_delta(self.path,self.frozen,self.annotated()))

    def test_all_thirty_paths(self):
        for i in range(30):
            self.assertTrue(allowed_source_delta(self.path.replace('Part00',f'Part{i:02}'),self.frozen,self.annotated()))

    def test_no_source_weakening(self):
        for changed in [self.annotated().replace(b'True',b'False'),self.annotated().replace(b'trivial',b'sorry'),self.annotated().replace(b'Base',b'Other'),self.annotated().replace(ANNOTATION,ANNOTATION+ANNOTATION),self.frozen+ANNOTATION]:
            with self.assertRaises(SystemExit):
                allowed_source_delta(self.path,self.frozen,changed)

    def test_no_foreign_family(self):
        for path in ['Solidity/Frontend/Checked/Token.lean',self.path.replace('Part00','Part30'),self.path.replace('Part00.lean','../Part00.lean')]:
            with self.assertRaises(SystemExit):
                allowed_source_delta(path,self.frozen,self.annotated())

    def test_changed_path_and_mode_boundary(self):
        row = b':100644 100644 a b M\0' + self.path.encode() + b'\0'
        check_changed_paths(row, b'')
        check_changed_paths(b'', b'')
        for changed in [row.replace(b'100644 100644', b'100644 100755'),
                        row.replace(b' M\0', b' A\0'),
                        row.replace(b'Part00.lean', b'notes.json'),
                        row.replace(b'Part00', b'Part30'), row[:-2]]:
            with self.assertRaises(SystemExit):
                check_changed_paths(changed, b'')
        with self.assertRaises(SystemExit):
            check_changed_paths(b'', b'Solidity/Frontend/new.txt\0')
