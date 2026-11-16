#!/usr/bin/env python3
"""Export fresh numeric observations, independently of cached import side effects."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    # Importing Fixtures alone does not rerun its export run_cmd on a cached build.
    # This new command computes the observation definitions, not fixtureExpected.
    query = """import Solidity.Frontend.NumericLiteralProofs.Fixtures
open Solidity.Frontend.NumericLiteralProofs in
#eval IO.FS.writeFile (System.FilePath.mk OUTPUT)
  (Lean.Json.pretty (Lean.Json.arr ((fixtureObservations.map observationJson).toArray)))
""".replace("OUTPUT", json.dumps(str(output)))
    with tempfile.TemporaryDirectory(prefix="feature-citations-observations-") as tmp:
        source = Path(tmp) / "Export.lean"
        source.write_text(query)
        env = dict(os.environ, LEAN_NUM_THREADS="1")
        subprocess.run(["lake", "env", "lean", "-j1", "-M8192", "--tstack=131072",
                        str(source)], cwd=ROOT, env=env, check=True)
    observations = json.loads(output.read_text())
    print(f"fresh numeric observations: {len(observations)} rows")


if __name__ == "__main__":
    main()
