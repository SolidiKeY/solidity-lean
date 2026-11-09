#!/usr/bin/env python3
"""Generate an off-git, bounded serial Lake config; tracked pins stay untouched."""
import json
from pathlib import Path
import sys
root = Path(__file__).resolve().parents[1]
text = (root / "lakefile.toml").read_text()
# Weak compiler flags do not change statements or package source configuration.
prefix = ("srcDir = " + json.dumps(str(root)) + "\n"
          + "buildDir = " + json.dumps(str(root / ".lake/build")) + "\n"
          + 'weakLeanArgs = ["-j1", "-M8192"]\n')
text = text.replace("[[lean_lib]]", prefix + "\n[[lean_lib]]", 1)
Path(sys.argv[1]).write_text(text)
