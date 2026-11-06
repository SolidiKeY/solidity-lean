#!/usr/bin/env python3
"""Reproduce the off-git v4.24 launch tree; do not download or alter binaries."""
import argparse
import os
from pathlib import Path
import shlex
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--toolchain-root', required=True, type=Path)
    parser.add_argument('--artifacts', required=True, type=Path)
    parser.add_argument('--report-name', default='mcp-session')
    parser.add_argument('--project', type=Path, help='owned Lean project; defaults to repository root')
    args = parser.parse_args()
    if args.artifacts.is_symlink(): parser.error('preserve unexpected artifact-root symlink')
    repo = Path(__file__).resolve().parents[4]
    project = (args.project or repo).resolve()
    if not project.is_relative_to(repo) or not (project/'lean-toolchain').is_file() or not any((project/name).is_file() for name in ['lakefile.toml', 'lakefile.lean']):
        parser.error('project must be an existing Lean package within the assigned repository')
    real, artifacts = args.toolchain_root.resolve(), args.artifacts.resolve()
    if artifacts.is_relative_to(repo): parser.error('runtime output must be outside repository')
    if artifacts.is_relative_to(real): parser.error('runtime output must not be inside official toolchain')
    if not args.report_name.replace('-', '').isalnum(): parser.error('invalid report name')
    version = subprocess.check_output([str(real/'bin/lean'), '--version'], text=True).strip()
    githash = subprocess.check_output([str(real/'bin/lean'), '--githash'], text=True).strip()
    if not version.startswith('Lean (version 4.24.0,') or githash != '797c613eb9b6d4ec95db23e3e00af9ac6657f24b':
        parser.error('only the official assigned v4.24.0 compiler is accepted')
    surrogate = artifacts/'v424-serial-sysroot'
    for directory in [artifacts, surrogate, surrogate/'bin', artifacts/'evidence']:
        if directory.is_symlink() or (directory.exists() and not directory.is_dir()):
            raise ValueError(f'preserve unexpected directory: {directory}')
        directory.mkdir(exist_ok=True)
    launch = repo/'scripts/h62/item4/generic-p10/lean-launch.py'
    def link(path, target):
        if path.is_symlink():
            if path.resolve() != target.resolve(): raise ValueError(f'preserve unexpected symlink: {path}')
        elif path.exists(): raise ValueError(f'preserve unexpected file: {path}')
        else: path.symlink_to(target, target_is_directory=target.is_dir())
    for child in real.iterdir():
        if child.name != 'bin': link(surrogate/child.name, child)
    for child in (real/'bin').iterdir():
        link(surrogate/'bin'/child.name, launch if child.name == 'lean' else child)
    values = dict(GENERIC_P10_LEAN_EXE=str(real/'bin/lean'), LEAN_SYSROOT=str(surrogate),
        LAKE_OVERRIDE_LEAN='true', LEAN_NUM_THREADS='1', LEAN_LSP_MAX_OPEN_FILES='1',
        LEAN_MCP_SCRATCH_SLOTS='1', LEAN_REPL='0',
        LEAN_MCP_START_WAIT='60', PYTHONDONTWRITEBYTECODE='1',
        PATH=str(Path.home()/'.elan/bin')+os.pathsep+os.environ.get('PATH', ''),
        LEAN_PROJECT_PATH=str(project),
        LEAN_MCP_DISABLED_TOOLS='lean_leansearch,lean_loogle,lean_leanfinder,lean_state_search,lean_hammer_premise,lean_get_widgets,lean_get_widget_source',
        LEAN_MCP_SERVER_CMD=shlex.join(['python3', str(repo/'scripts/h62/item4/generic-p10/bounded.py'),
            '--report', str(artifacts/'evidence'/f'{args.report_name}-resources.json'),
            '--', str(repo/'.venv/bin/python'), '-m', 'lean_lsp_mcp', '--lean-project-path', str(project)]))
    output = artifacts/f'runtime-env-{args.report_name}.sh'
    content = ''.join(f'export {k}={shlex.quote(v)}\n' for k,v in values.items())
    if output.is_symlink() or (output.exists() and not output.is_file()):
        raise ValueError(f'preserve unexpected environment path: {output}')
    if output.exists():
        if output.read_text() != content: raise ValueError(f'preserve conflicting environment: {output}')
    else:
        with output.open('x') as stream: stream.write(content)
    print(version)
    print(f'unchanged official binary; launch flags only; environment saved: {output}')


if __name__ == '__main__': main()
