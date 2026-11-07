#!/usr/bin/env python3
"""Private configuration for repeatable clean serial run-lean.sh measurements."""
import argparse, json, shlex
from pathlib import Path
p=argparse.ArgumentParser(); p.add_argument("--toolchain",type=Path,required=True); p.add_argument("--output",type=Path,required=True); a=p.parse_args()
a.output.mkdir(parents=True,exist_ok=True)
config=Path("lakefile.toml").read_text().replace("enableArtifactCache = true","enableArtifactCache = false")
for table in ("[[lean_lib]]","[[lean_exe]]"):
    config=config.replace(table,table+'\nmoreLeanArgs = ["-j1", "-M11000"]')
config_path=a.output.resolve()/"lakefile.toml"; config_path.write_text(config)
wrapper=a.output.resolve()/"bin"; wrapper.mkdir(exist_ok=True)
(wrapper/"lake").write_text("#!/bin/sh\nexec "+shlex.quote(str(a.toolchain.resolve()/"bin/lake"))+" --no-cache -f "+shlex.quote(str(config_path))+ ' "$@"\n')
(wrapper/"lake").chmod(0o755)
print(json.dumps({"config":str(config_path),"wrapper":str(wrapper),"moreLeanArgs":["-j1","-M11000"],"artifact_cache":False}))
