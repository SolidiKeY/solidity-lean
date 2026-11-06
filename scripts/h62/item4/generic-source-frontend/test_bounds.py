#!/usr/bin/env python3
"""Host availability must never conceal exhausted VM cgroup headroom."""
import tempfile
import unittest
from pathlib import Path
from bounded import effective_available, GIB

class BoundTests(unittest.TestCase):
    def test_cgroup_headroom_is_effective(self):
        with tempfile.TemporaryDirectory() as root:
            p = Path(root)
            (p/'memory.max').write_text(str(16*GIB))
            (p/'memory.current').write_text(str(13*GIB))
            effective,host,group = effective_available({'MemAvailable':str(20*1024*1024)+' kB'},p)
            self.assertEqual(effective,3*GIB)
            self.assertGreater(host,group)
    def test_host_headroom_still_applies(self):
        with tempfile.TemporaryDirectory() as root:
            p = Path(root)
            (p/'memory.max').write_text(str(16*GIB))
            (p/'memory.current').write_text(str(GIB))
            self.assertEqual(effective_available({'MemAvailable':'1048576 kB'},p)[0],GIB)

if __name__ == '__main__':
    unittest.main()
