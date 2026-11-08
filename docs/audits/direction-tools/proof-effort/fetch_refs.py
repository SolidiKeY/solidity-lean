#!/usr/bin/env python3
"""Fetch the three clean pinned public references outside the code checkout.
Usage: python3 -B docs/audits/direction-tools/proof-effort/fetch_refs.py CACHE
"""
import importlib.util,pathlib,subprocess,sys,json
spec=importlib.util.spec_from_file_location("audit",pathlib.Path(__file__).with_name("audit.py"));a=importlib.util.module_from_spec(spec);spec.loader.exec_module(a)
cache=pathlib.Path(sys.argv[1]).resolve()
if cache.is_relative_to(a.ROOT):raise SystemExit("Reference cache must be outside the code checkout")
cache.mkdir(parents=True,exist_ok=True)
pins=json.loads(a.blob("docs/audits/direction-tools/references/pins.json"));sources=json.loads(a.blob("docs/audits/direction-tools/references/sources.json"))
for n in ("CompCert","CakeML","Clear"):
    p=cache/n;url="https://github.com/"+sources[n]+".git"
    if not p.exists():subprocess.run(["git","clone","--depth","1",url,str(p)],check=True)
    if a.git(p,"status","--porcelain"):raise SystemExit("Refuse dirty reference "+n)
    if a.git(p,"remote","get-url","origin")!=url:raise SystemExit("Unexpected reference origin "+n)
    subprocess.run(["git","-C",str(p),"fetch","--depth","1","origin",pins[n]],check=True)
    subprocess.run(["git","-C",str(p),"checkout","--detach",pins[n]],check=True)
    assert a.git(p,"rev-parse","HEAD")==pins[n]
    print(n,pins[n])
