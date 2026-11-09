#!/usr/bin/env python3
"""Source/output-bound validation for additive old compiler-signature batches.
IR signatures remain observations, never public API or semantic acceptance.
"""
import importlib.util, json, pathlib, sys
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('compiler_signatures',pathlib.Path(__file__).with_name('compiler-signatures.py'))
collector = importlib.util.module_from_spec(spec)
spec.loader.exec_module(collector)
interfaces = collector.interfaces

def jobs(path):
    data = json.loads(pathlib.Path(path).read_text())
    if not isinstance(data,list) or not data:
        raise ValueError('expected nonempty jobs array')
    names, outputs = set(), set()
    for row in data:
        if not isinstance(row,dict) or set(row) != {'module','output'}:
            raise ValueError('unknown job shape')
        if not isinstance(row['module'],str) or not isinstance(row['output'],str):
            raise ValueError('invalid job value')
        interfaces.module_name(row['module'])
        output = pathlib.Path(row['output'])
        if not output.is_absolute() or str(output.resolve()) != str(output):
            raise ValueError('output must be canonical absolute path')
        if row['module'] in names or str(output) in outputs:
            raise ValueError('duplicate module/output job')
        names.add(row['module']);outputs.add(str(output))
    return data

def seal(probe_path,jobs_path):
    probe_path=pathlib.Path(probe_path).resolve();jobs_path=pathlib.Path(jobs_path).resolve()
    probe=interfaces.validate_probe(probe_path)
    if len(probe['modules'])!=1:
        raise ValueError('expected one supervised batch process')
    cmd=probe['modules'][0]['command']
    if '--run' not in cmd:
        raise ValueError('not a Lean batch exporter')
    pos=cmd.index('--run');repo=pathlib.Path(probe['repository'])
    if len(cmd)!=pos+3:
        raise ValueError('batch argument count mismatch')
    helper=(repo/cmd[pos+1]).resolve();requested=(repo/cmd[pos+2]).resolve()
    if helper!=(repo/'tests/h62/item6/migrate-yul/ExportCompilerSignaturesBatch.lean').resolve() or requested!=jobs_path:
        raise ValueError('batch helper/jobs argument mismatch')
    if str(helper) not in probe['probe_sources_before'] or str(jobs_path) not in probe['probe_sources_before']:
        raise ValueError('unbound helper/jobs input')
    planned=jobs(jobs_path);bound=probe['probe_outputs_after']
    if probe.get('probe_output_freshness_required') is not True or set(bound)!={job['output'] for job in planned}:
        raise ValueError('batch output coverage mismatch')
    reports=[]
    for job in planned:
        raw=pathlib.Path(job['output'])
        if interfaces.digest(raw)!=bound[str(raw)]['sha256'] or raw.stat().st_size!=bound[str(raw)]['bytes']:
            raise ValueError('batch output hash/size mismatch')
        report=collector.inspect(raw,job['module'])
        report.update(raw=str(raw),raw_sha256=interfaces.digest(raw),probe=str(probe_path),probe_sha256=interfaces.digest(probe_path),jobs=str(jobs_path),jobs_sha256=interfaces.digest(jobs_path),lean=probe['lean'],lake=probe['lake'],collector_sha256=interfaces.digest(__file__),single_parser_sha256=interfaces.digest(collector.__file__),limitation='IR/compiler observations only; compiler visibility is not independently verified public API classification. Missing IR remains unresolved.')
        reports.append(report)
    return reports
