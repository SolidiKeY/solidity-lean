#!/usr/bin/env python3
"""Deliberate Python validation support for check-tests-used.py (stdlib only).

This helper is never invoked by inventory/write/check. The caller supplies an
exact command, an isolated scratch checkout, a committed-byte manifest and an
external evidence output stem. No fixture in the original checkout is changed.

  python3 -B scripts/check-tests-used-trace.py --scratch SCRATCH \
    --manifest EXTERNAL_MANIFEST --output EXTERNAL_STEM -- python3 -B tests/test.py

The manifest has measured_revision and files[path] = {blob, sha256}. An audit
hook captures read-only Python open stacks; strace confirms actual reads and
excludes every file mutated during validation. The scratch inputs must match
the committed manifest before execution. It records the actual Python call stack and tracks inherited Python
children that honor sitecustomize. Native/Node reads and isolated Python
children are NOT observed. Missing observations never establish non-use.
Instrumentation must pass as well as the ordinary command before any route is
promoted. Raw stdout, event traces and receipts are external lane evidence.
"""
import argparse
import hashlib
import functools
import itertools
import posixpath
import stat
import types
import ast
import re
import shutil
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import threading
import time

sys.dont_write_bytecode = True


def code_fingerprint(code, _hash=hashlib.sha256, _dumps=json.dumps):
    """Structural code identity independent of filename and marshal interning."""
    def constant(value):
        if isinstance(value, types.CodeType): return ['code', structure(value)]
        if isinstance(value, bytes): return ['bytes', value.hex()]
        if isinstance(value, tuple): return ['tuple', [constant(v) for v in value]]
        if isinstance(value, frozenset): return ['frozenset', sorted((constant(v) for v in value), key=repr)]
        if isinstance(value, float): return ['float', value.hex()]
        if isinstance(value, complex): return ['complex', value.real.hex(), value.imag.hex()]
        if value is Ellipsis: return ['ellipsis']
        if value is None or type(value) in (str, bool, int): return [type(value).__name__, value]
        raise ValueError('unsupported code constant type')
    def structure(item):
        attributes = ('co_argcount', 'co_posonlyargcount', 'co_kwonlyargcount', 'co_nlocals',
                      'co_stacksize', 'co_flags', 'co_name', 'co_qualname', 'co_firstlineno',
                      'co_names', 'co_varnames', 'co_freevars', 'co_cellvars')
        result = {name: getattr(item, name) for name in attributes}
        for name in ('co_code', 'co_linetable', 'co_exceptiontable'): result[name] = getattr(item, name).hex()
        result['co_consts'] = [constant(c) for c in item.co_consts]
        return result
    return _hash(_dumps(structure(code), sort_keys=True, ensure_ascii=True, separators=(',', ':')).encode()).hexdigest()


@functools.lru_cache(maxsize=8192)
def source_code_hashes(data, filename):
    hashes = set(); modules = set()
    for optimize in (0, 1, 2):
        try: code = compile(data, filename, 'exec', dont_inherit=True, optimize=optimize)
        except (SyntaxError, ValueError): continue
        modules.add(code_fingerprint(code))
        pending = [code]
        while pending:
            current = pending.pop(); hashes.add(code_fingerprint(current))
            pending.extend(c for c in current.co_consts if isinstance(c, types.CodeType))
    return {'code_hashes': sorted(hashes), 'module_code_hashes': sorted(modules)}


def verify_inputs(scratch, manifest):
    """Verify Git object bindings and actual bytes, independently of index flags."""
    root = Path(scratch).resolve()
    raw = subprocess.check_output(['git', '-C', str(root), 'ls-tree', '-r', '-z', manifest['measured_revision']])
    expected = {}; links = {}; directories = set()
    for item in raw.split(b'\0'):
        if not item: continue
        meta, path = item.split(b'\t', 1)
        mode, kind, blob = meta.split()
        name = path.decode('utf-8', 'surrogateescape')
        directories.update(Path(name).parents)
        if kind == b'blob':
            if mode == b'120000': links[name] = blob.decode()
            else: expected[name] = blob.decode()
    for directory in directories:
        if not stat.S_ISDIR((root / directory).lstat().st_mode):
            raise ValueError('scratch tree ancestor is not a real directory')
    for path, blob in links.items():
        target = root / path
        if not stat.S_ISLNK(target.lstat().st_mode): raise ValueError('tracked symlink changed type')
        actual = os.fsencode(os.readlink(target))
        wanted = subprocess.check_output(['git', '-C', str(root), 'cat-file', 'blob', blob])
        if actual != wanted: raise ValueError('tracked symlink bytes differ from measured object')
    if set(expected) != set(manifest['files']): raise ValueError('manifest set differs from committed regular-file set')
    object_format = subprocess.check_output(['git', '-C', str(root), 'rev-parse', '--show-object-format'], text=True).strip()
    files = {}
    for path, blob in expected.items():
        entry = manifest['files'][path]
        if set(entry) != {'blob', 'sha256'} or entry['blob'] != blob: raise ValueError('manifest Git object binding mismatch: ' + path)
        target = root / path
        if not stat.S_ISREG(target.lstat().st_mode) or target.lstat().st_nlink != 1 or not target.resolve().is_relative_to(root):
            raise ValueError('scratch input is not an owned regular file: ' + path)
        data = target.read_bytes()
        object_hash = hashlib.new(object_format, b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if object_hash != blob or hashlib.sha256(data).hexdigest() != entry['sha256']:
            raise ValueError('scratch bytes differ from measured object: ' + path)
        files[path] = dict(entry)
        if path.endswith('.py'): files[path].update(source_code_hashes(data, '<measured>'))
    # Untracked data, bytecode or source can alter selection/import behavior.
    for options in (['--exclude-standard'], ['--ignored', '--exclude-standard']):
        unknown = subprocess.check_output(['git', '-C', str(root), 'ls-files', '--others', '-z', *options]).split(b'\0')
        if any(unknown):
            raise ValueError('untracked/ignored input in scratch checkout')
    return {'measured_revision': manifest['measured_revision'], 'files': files}


def install_hook():
    root = os.path.realpath(os.environ['X1_TRACE_ROOT'])
    with open(os.environ['X1_TRACE_MANIFEST'], encoding='utf-8') as stream:
        manifest = json.load(stream)['files']
    log = os.open(os.environ['X1_TRACE_LOG'], os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    state = threading.local()
    sequence = itertools.count(1)
    fingerprints = {}
    untrusted_sources = set()
    original_hash = hashlib.sha256

    def relative(path):
        try:
            full = os.path.realpath(os.path.abspath(path))
            if os.path.commonpath((root, full)) != root: return None
            return os.path.relpath(full, root).replace(os.sep, '/')
        except (OSError, TypeError, ValueError): return None

    def audit(event, args):
        if getattr(state, 'busy', False): return
        if event == 'compile':
            source, filename = args
            target = relative(filename) if isinstance(filename, (str, bytes)) else None
            if target in manifest:
                data = source.encode('utf-8') if isinstance(source, str) else source
                if source is not None and (not isinstance(data, bytes) or original_hash(data).hexdigest() != manifest[target]['sha256']):
                    untrusted_sources.add(target)
            return
        if event == 'exec':
            code = args[0]; target = relative(code.co_filename)
            if target in manifest and code_fingerprint(code) not in manifest[target].get('module_code_hashes', ()):
                untrusted_sources.add(target)
            return
        if event != 'open': return
        path, mode, flags = args
        if not isinstance(path, (str, bytes, os.PathLike)): return
        if flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND): return
        state.busy = True
        try:
            target = relative(os.fsdecode(path))
            if target not in manifest: return
            frames = []
            frame = sys._getframe(1)
            while frame:
                source = relative(frame.f_code.co_filename)
                if source in manifest:
                    code = frame.f_code
                    cached = fingerprints.get(id(code))
                    if cached is None:
                        cached = (code, code_fingerprint(code)); fingerprints[id(code)] = cached
                    if source in untrusted_sources or cached[1] not in manifest[source].get('code_hashes', ()):
                        return
                    frames.append({'path': source, 'line': frame.f_lineno, 'code_qualname': code.co_qualname, 'code_firstlineno': code.co_firstlineno})
                elif frame.f_code.co_filename in ('<string>', '<stdin>'):
                    return
                elif frame.f_code.co_filename.startswith(root + os.sep):
                    return
                elif os.path.isabs(frame.f_code.co_filename) and not any(
                    frame.f_code.co_filename.startswith(prefix + os.sep) for prefix in (sys.prefix, sys.base_prefix)):
                    return
                frame = frame.f_back
            if not frames: return
            event = {'event_id': f'X1AUDIT:{threading.get_native_id()}:{next(sequence)}',
                     'argument': os.fsdecode(path), 'target': target, 'frames': frames}
            encoded = json.dumps(event, separators=(',', ':')).encode() + b'\n'
            os.write(log, encoded)
        except (OSError, ValueError, TypeError):
            # A denied/missing/mutated object gets no consumption credit.
            pass
        finally:
            state.busy = False

    sys.addaudithook(audit)


def run(command, scratch, manifest, output, timeout=30):
    scratch = Path(scratch).resolve()
    output = Path(output).resolve()
    manifest = Path(manifest).resolve()
    tool_checkout = Path(__file__).resolve().parent.parent
    if scratch == tool_checkout: raise ValueError('use a disposable scratch checkout, not the tool checkout')
    if output.is_relative_to(scratch) or manifest.is_relative_to(scratch) or output.is_relative_to(tool_checkout):
        raise ValueError('manifest and validation receipts must be outside the scratch checkout')
    expected = json.loads(manifest.read_bytes())
    revision = subprocess.check_output(['git', '-C', str(scratch), 'rev-parse', 'HEAD'], text=True).strip()
    if revision != expected['measured_revision']: raise ValueError('scratch revision differs from manifest')
    verified = verify_inputs(scratch, expected)
    output.parent.mkdir(parents=True, exist_ok=True)
    events = str(output) + '.events.jsonl'
    Path(events).write_bytes(b'')
    with tempfile.TemporaryDirectory(prefix='x1-audit-', dir=output.parent) as directory:
        checked_manifest = Path(directory) / 'verified-manifest.json'
        checked_manifest.write_text(json.dumps(verified, sort_keys=True))
        hook = Path(directory) / 'sitecustomize.py'
        hook.write_text('import runpy\nrunpy.run_path(' + repr(str(Path(__file__).resolve())) +
                        ', run_name="x1_audit_hook")["install_hook"]()\n')
        env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', LEAN_NUM_THREADS='1',
                   X1_TRACE_ROOT=str(scratch), X1_TRACE_MANIFEST=str(checked_manifest), X1_TRACE_LOG=events,
                   PYTHONPATH=directory + (os.pathsep + os.environ['PYTHONPATH'] if os.environ.get('PYTHONPATH') else ''))
        instrumentation_sha = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        start = time.monotonic()
        with open(str(output) + '.stdout', 'wb') as stream:
            if not shutil.which('strace'): raise ValueError('strace is required for actual read validation')
            traced = ['strace', '-f', '-qq', '-yy', '-s', '256', '-e',
                      'trace=%file,read,pread64,write,pwrite64,mmap,sendfile,copy_file_range,close',
                      '-o', str(output) + '.syscalls', '--', *command]
            process = subprocess.Popen(traced, cwd=scratch, env=env, stdout=stream,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            timed_out = False
            try: status = process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                status = process.wait()
        receipt = {'command': command, 'input_revision': revision, 'exit': status,
                   'timeout': timed_out, 'seconds': round(time.monotonic() - start, 3),
                   'events': events, 'stdout': str(output) + '.stdout',
                   'instrumentation_source_sha256': instrumentation_sha,
                   'instrumentation': 'Python open stacks intersected with strace actual reads; mutation-excluded committed inputs'}
        Path(str(output) + '.receipt.json').write_text(json.dumps(receipt, sort_keys=True, indent=2) + '\n')
        return receipt


def _observed_routes(receipt, scratch, manifest, runner, nonpassing=False):
    """Match each actual read to its audited open by native thread and fd.

    Every mutated path and directory descendant is excluded, even if restored.
    Unknown descriptor inheritance and incomplete syscall records get no credit.
    """
    if receipt['timeout'] or (receipt['exit'] and not nonpassing): return []
    if receipt['input_revision'] != manifest['measured_revision'] or receipt['command'] != ['python3', '-B', runner]:
        raise ValueError('trace invocation differs from validated runner')
    scratch_path = Path(scratch).resolve(); scratch = str(scratch_path)
    files = manifest['files']
    def relative(value):
        return value[len(scratch) + 1:] if value.startswith(scratch + '/') else None
    events = {e['event_id']: e for line in Path(receipt['events']).read_text().splitlines() if (e := json.loads(line))}
    pending = {}; descriptors = {}; reads = set(); all_read_paths = set(); dirty = set(); unfinished = {}
    directories = set()
    for name in files:
        parent = posixpath.dirname(name)
        while parent and parent not in directories:
            directories.add(parent); parent = posixpath.dirname(parent)
    def taint(value):
        value = posixpath.normpath(value)
        rel = relative(value)
        if value == scratch: dirty.update(files); return
        if rel is not None:
            if rel in files: dirty.add(rel)
            elif rel in directories: dirty.update(p for p in files if p.startswith(rel.rstrip('/') + '/'))
        elif not value.startswith('/'):
            suffix = posixpath.normpath(value)
            while suffix.startswith('../'): suffix = suffix[3:]
            if suffix in ('.', '..'): dirty.update(files); return
            dirty.update(p for p in files if p == suffix or p.endswith('/' + suffix) or
                         ('/' + suffix + '/') in ('/' + p))
    def arguments(line):
        # Split strace arguments, preserving quoted strings and annotated fds.
        start = line.find('(')
        if start < 0: return []
        result = []; at = start + 1; depth = 1; quoted = False; escaped = False; annotated = False
        for index in range(start + 1, len(line)):
            char = line[index]
            if quoted:
                if escaped: escaped = False
                elif char == '\\': escaped = True
                elif char == '"': quoted = False
                continue
            if annotated:
                if char == '>': annotated = False
                continue
            if char == '"': quoted = True
            elif char == '<': annotated = True
            elif char in '([{': depth += 1
            elif char in ')]}':
                depth -= 1
                if depth == 0:
                    result.append(line[at:index].strip()); return result
            elif char == ',' and depth == 1:
                result.append(line[at:index].strip()); at = index + 1
        return []
    def path_argument(value, directory=None):
        try: path = ast.literal_eval(value)
        except (SyntaxError, ValueError): dirty.update(files); return
        if not isinstance(path, str): dirty.update(files); return
        if not path.startswith('/') and directory is not None:
            match = re.search(r'<([^>]+)>', directory)
            if match: path = posixpath.normpath(posixpath.join(match[1], path))
        taint(path)
    syscall_path = str(receipt['events']).removesuffix('.events.jsonl') + '.syscalls'
    for original in Path(syscall_path).read_text(errors='replace').splitlines():
        match = re.match(r'^(\d+)\s+(.*)', original)
        if not match: continue
        tid, line = int(match[1]), match[2]
        if '<unfinished ...>' in line:
            unfinished[tid] = line.split('<unfinished ...>', 1)[0]; continue
        resumed = re.match(r'<[.][.][.] \w+ resumed>(.*)', line)
        if resumed:
            if tid not in unfinished: continue
            line = unfinished.pop(tid) + resumed[1]
        marker = re.search(r'X1AUDIT:[0-9]+:[0-9]+', line)
        if marker and marker[0] in events:
            pending.setdefault(tid, []).append(marker[0])
        # Every successful open resets descriptor attribution, including native opens.
        if re.match(r'(?:open|openat|openat2)\(', line):
            literals = re.findall(r'"(?:[^"\\]|\\.)*"', line)
            argument = None
            if literals:
                try: argument = ast.literal_eval(literals[0])
                except (ValueError, SyntaxError): pass
            choices = pending.get(tid, [])
            selected = next((e for e in reversed(choices) if events[e]['argument'] == argument), None)
            if selected: choices.remove(selected)
            opened = re.search(r'= (\d+)<([^>]+)>\s*$', line)
            if opened:
                fd, path = int(opened[1]), relative(opened[2])
                descriptors.pop((tid, fd), None)
                if selected and path == events[selected]['target']:
                    descriptors[(tid, fd)] = selected
        if re.search(r'= -1\b', line): continue
        match = re.match(r'(?:read|pread64)\((\d+)<([^>]+)>.*\)\s+=\s+([0-9]+)\s*$', line)
        if match:
            actual = relative(match[2]); args = arguments(line)
            attempted = len(args) >= 3 and bool(re.fullmatch(r'[1-9][0-9]*', args[2]))
            # A real EOF read observes an empty fixture. Opening it, a native
            # child's read, or a zero-length no-op read does not qualify.
            consumed = (int(match[3]) > 0 or (attempted and actual in files and
                        files[actual]['sha256'] == hashlib.sha256(b'').hexdigest()))
            if consumed:
                if actual in files: all_read_paths.add(actual)
                event_id = descriptors.get((tid, int(match[1])))
                if event_id and actual == events[event_id]['target']: reads.add(event_id)
        closed = re.match(r'close\((\d+).*\)\s+=\s+0\s*$', line)
        if closed: descriptors.pop((tid, int(closed[1])), None)
        path_change = bool(re.match(r'(?:creat|truncate|ftruncate|unlink|unlinkat|rmdir|rename|renameat|renameat2|link|linkat|symlink|symlinkat)\(', line))
        modifies = path_change or bool(re.match(r'(?:write|pwrite64|sendfile|copy_file_range)\(', line))
        modifies |= any(flag in line for flag in ('O_WRONLY', 'O_RDWR', 'O_TRUNC', 'O_CREAT'))
        modifies |= ('mmap(' in line and 'PROT_WRITE' in line and 'MAP_SHARED' in line)
        if not modifies: continue
        if re.match(r'(?:open|openat|openat2)\(', line):
            target_fd = re.search(r'= \d+<([^>]+)>\s*$', line)
            if target_fd: taint(target_fd[1])
            else: dirty.update(files)
        elif not path_change or line.startswith('ftruncate('):
            for value in re.findall(r'\b\d+<([^>]+)>', line): taint(value)
        if path_change:
            name = line.split('(', 1)[0]; args = arguments(line)
            if not args: dirty.update(files); continue
            if name in ('renameat', 'renameat2', 'linkat') and len(args) >= 4:
                path_argument(args[1], args[0]); path_argument(args[3], args[2])
            elif name == 'unlinkat' and len(args) >= 2:
                path_argument(args[1], args[0])
            elif name == 'symlinkat' and len(args) >= 3:
                path_argument(args[2], args[1])
            elif name in ('rename', 'link', 'symlink') and len(args) >= 2:
                path_argument(args[0]); path_argument(args[1])
            elif name != 'ftruncate':
                path_argument(args[0])
    routes = {}
    for event_id in sorted(reads):
        event = events[event_id]; target = event['target']
        if target not in files or target in dirty: continue
        if any(frame['path'] in dirty or frame['path'] not in all_read_paths for frame in event['frames']): continue
        frames = list(reversed(event['frames']))
        if not frames or frames[0]['path'] != runner: continue
        # Recheck credited objects after execution too; temporary writes were
        # already excluded by the syscall analysis even when later restored.
        relevant = {target} | {f['path'] for f in frames}
        try:
            if any(hashlib.sha256((scratch_path / p).read_bytes()).hexdigest() != files[p]['sha256'] for p in relevant): continue
        except OSError:
            continue
        route = {'runner': ('nonpassing:' if nonpassing else 'validated:') + runner, 'input_revision': manifest['measured_revision'],
                 'frames': [{'path': f['path'], 'blob': files[f['path']]['blob'], 'line': f['line'],
                             **({'code_qualname': f.get('code_qualname'), 'code_firstlineno': f.get('code_firstlineno')} if nonpassing else {})} for f in frames],
                 'target': target, 'target_blob': files[target]['blob'],
                 'operation': ('Observed fixture read during nonpassing unittest' if nonpassing else 'validated Python read of measured bytes')}
        routes[json.dumps(route, sort_keys=True, separators=(',', ':'))] = route
    return [routes[k] for k in sorted(routes)]



def observed_routes(receipt, scratch, manifest, runner):
    """Passing traces only; failures never receive passing-runner credit."""
    return _observed_routes(receipt, scratch, manifest, runner)


def observed_test_failure_routes(receipt, normal, scratch, manifest, runner, instrumentation_source=None):
    """Separate observations from an ordinary failed unittest, never a pass.

    The normal run and trace must exhibit the same unittest failure diagnostics.
    Bootstrap-only failures and unentered methods do not establish fixture use.
    Callers must separately review fixture roles; this only establishes reads.
    Raw receipts and immutable instrumentation source stay in private evidence.
    """
    if (receipt.get('timeout') is not False or normal.get('timeout') is not False
            or type(receipt.get('exit')) is not int or receipt['exit'] not in range(1, 124)
            or type(normal.get('exit')) is not int or normal.get('exit') != receipt['exit'] or normal.get('revision') != manifest['measured_revision']
            or normal.get('command') != receipt.get('command')):
        return []
    import ast
    import importlib.util
    import types
    source = Path(instrumentation_source) if instrumentation_source else Path(__file__)
    raw = source.read_bytes()
    if hashlib.sha256(raw).hexdigest() != receipt.get('instrumentation_source_sha256'):
        raise ValueError('nonpassing trace instrumentation source mismatch')
    if raw != Path(__file__).read_bytes():
        raise ValueError('nonpassing trace requires the complete reviewed instrumentation source')
    spec = importlib.util.spec_from_file_location('tests_used_failure_roles', Path(__file__).with_name('check-tests-used.py'))
    rules = importlib.util.module_from_spec(spec); spec.loader.exec_module(rules)
    source_bytes = (Path(scratch) / runner).read_bytes()
    if hashlib.sha256(source_bytes).hexdigest() != manifest['files'][runner]['sha256']: return []
    repo = types.SimpleNamespace(texts={runner: source_bytes.decode()},
        tree={runner: ('100644', 'blob', manifest['files'][runner]['blob'])}, ref=manifest['measured_revision'])
    declaration = rules.declared_unittest(repo, runner)
    if declaration is None: return []
    def diagnostic(path):
        text = Path(path).read_text(errors='replace')
        if not re.search(r'^Ran [0-9]+ tests? in [0-9.]+s$', text, re.M): return None
        start = re.search(r'^(?:FAIL|ERROR): [^\n]+$', text, re.M)
        if start is None or not re.search(r'^FAILED \([^\n]+\)$', text, re.M): return None
        # Preserve test IDs, source/line traceback locations and full assertions.
        # Only framework elapsed time and freshly allocated temporary names vary.
        section = text[start.start():]
        section = re.sub(r'^(Ran [0-9]+ tests? in )[0-9.]+s$', r'\1<elapsed>s', section, flags=re.M)
        return re.sub(r'/tmp/(?:tmp|x1-audit-)[^/\s\']+', '<temporary>', section)
    ordinary = diagnostic(normal['log']); traced = diagnostic(receipt['stdout'])
    if ordinary is None or ordinary != traced: return []
    routes = _observed_routes(receipt, scratch, manifest, runner, nonpassing=True)
    return [r for r in routes if any(frame['path'] == runner and any(
        context['first'] <= frame['line'] <= context['last'] and context['qualname'] == frame.get('code_qualname')
        and context['code_firstlineno'] == frame.get('code_firstlineno') for context in declaration['test_contexts']) for frame in r['frames'])]


def self_test():
    with tempfile.TemporaryDirectory(prefix='tests-used-trace-controls-') as directory:
        base = Path(directory); root = base / 'repo'; root.mkdir()
        sources = {
            'tests/input/data.txt': 'measured\n',
            'tests/helper.py': 'def open_without_read():\n stream = open("tests/input/data.txt")\n stream.close()\n',
            'tests/direct.py': 'from pathlib import Path\nassert Path("tests/input/data.txt").read_text() == "measured\\n"\n',
            'tests/fake.py': 'from pathlib import Path\nname = str(Path(__file__).resolve().with_name("helper.py"))\nexec(compile("from pathlib import Path\\nPath(\'tests/input/data.txt\').read_text()\\n", name, "exec"))\n',
            'tests/native.py': 'import helper, subprocess\nhelper.open_without_read()\nsubprocess.run(["cat", "tests/input/data.txt"], check=True)\n',
            'tests/replace.py': 'import os, shutil\nfrom pathlib import Path\nos.rename("tests/input", "tests/saved")\nPath("tests/input").mkdir()\nPath("tests/input/data.txt").write_text("changed\\n")\nPath("tests/input/data.txt").read_text()\nshutil.rmtree("tests/input")\nos.rename("tests/saved", "tests/input")\n',
        }
        sources['tests/failed_unit.py'] = 'import unittest\nfrom pathlib import Path\nclass T(unittest.TestCase):\n def test_input(self):\n  self.assertEqual(Path("tests/input/data.txt").read_text(), "expected")\nif __name__ == "__main__": unittest.main()\n'
        sources['tests/bootstrap_unit.py'] = 'import unittest\nfrom pathlib import Path\nPath("tests/input/data.txt").read_text()\nassert False, "bootstrap"\nclass T(unittest.TestCase):\n def test_input(self): pass\nif __name__ == "__main__": unittest.main()\n'
        sources['tests/failed_plain.py'] = 'from pathlib import Path\nPath("tests/input/data.txt").read_text()\nassert False\n'
        sources['tests/failed_mutation.py'] = 'import unittest\nfrom pathlib import Path\nclass T(unittest.TestCase):\n def test_input(self):\n  p=Path("tests/input/data.txt"); value=p.read_bytes(); p.write_bytes(b"changed"); p.write_bytes(value)\n  self.assertFalse(True)\nif __name__ == "__main__": unittest.main()\n'
        sources['tests/escaped_unit.py'] = 'import unittest\nfrom pathlib import Path\nclass T(unittest.TestCase):\n def test_factory(self):\n  def escaped():\n   return Path("tests/input/data.txt").read_text()\n  return escaped\n def test_failure(self): self.assertFalse(True)\nT("test_factory").test_factory()()\nif __name__ == "__main__": unittest.main()\n'
        sources['tests/failure_helper.py'] = 'from pathlib import Path\ndef read(): return Path("tests/input/data.txt").read_text()\n'
        sources['tests/mutated_helper_unit.py'] = 'import unittest\nfrom pathlib import Path\nclass T(unittest.TestCase):\n def test_input(self):\n  p=Path(__file__).with_name("failure_helper.py"); original=p.read_text(); p.write_text(original + "# changed\\n")\n  import failure_helper\n  value=failure_helper.read(); p.write_text(original)\n  self.assertFalse(True)\nif __name__ == "__main__": unittest.main()\n'
        sources['tests/input/twin.txt'] = 'measured\n'
        sources['tests/input/empty.txt'] = ''
        sources['tests/input/empty-unread.txt'] = ''
        sources['tests/empty.py'] = 'from pathlib import Path\nassert Path("tests/input/empty.txt").read_text() == ""\n'
        sources['tests/empty_zero.py'] = 'import os\nwith open("tests/input/empty.txt") as stream: assert os.read(stream.fileno(), 0) == b""\n'
        sources['tests/empty_native.py'] = 'import subprocess\nwith open("tests/input/empty-unread.txt"): pass\nsubprocess.run(["cat", "tests/input/empty-unread.txt"], check=True)\n'
        helper = 'VERSION="current"\ndef read_data():\n with open("tests/input/data.txt") as stream: return stream.read()\ndef open_without_read():\n stream = open("tests/input/data.txt")\n stream.close()\n'
        sources['tests/helper.py'] = helper
        historical = helper.replace('VERSION="current"', 'VERSION="historical"')
        for scenario, read_first in (('historical', False), ('historical_read', True)):
            sources['tests/' + scenario + '.py'] = ('from pathlib import Path\nname=Path(__file__).resolve().with_name("helper.py")\n' +
                ('name.read_text()\n' if read_first else '') + 'namespace={}\nexec(compile(' + repr(historical) + ', str(name), "exec"), namespace)\nnamespace["read_data"]()\n')
        sources['tests/hard.py'] = 'from pathlib import Path\na=Path("tests/input/data.txt"); b=Path("tests/input/twin.txt")\noriginal=a.read_bytes()\nb.write_bytes(b"changed\\n")\nassert a.read_bytes()==b"changed\\n"\nb.write_bytes(original)\n'
        sources['tests/link.py'] = 'from pathlib import Path\nassert Path("tests/alias").read_text()=="measured\\n"\n'
        for path, content in sources.items():
            target = root / path; target.parent.mkdir(parents=True, exist_ok=True); target.write_text(content)
        def git(*args):
            return subprocess.check_output(['git', '-C', str(root), '-c', 'core.hooksPath=/dev/null', *args])
        os.symlink('input/data.txt', root / 'tests/alias')
        git('init', '-q'); git('add', '.')
        git('-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit', '-qm', 'control')
        revision = git('rev-parse', 'HEAD').decode().strip()
        manifest = {'measured_revision': revision, 'files': {p: {
            'blob': git('rev-parse', revision + ':' + p).decode().strip(),
            'sha256': hashlib.sha256((root / p).read_bytes()).hexdigest()} for p in sources}}
        manifest_path = base / 'manifest.json'; manifest_path.write_text(json.dumps(manifest))
        for scenario in ('failed_unit', 'bootstrap_unit', 'failed_plain', 'failed_mutation', 'escaped_unit', 'mutated_helper_unit'):
            runner = 'tests/' + scenario + '.py'; command = ['python3', '-B', runner]
            normal_path = base / (scenario + '.normal.log')
            with normal_path.open('wb') as stream:
                process = subprocess.run(command, cwd=root, stdout=stream, stderr=subprocess.STDOUT, timeout=15,
                                         env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
            normal = {'command': command, 'revision': revision, 'exit': process.returncode, 'timeout': False, 'log': str(normal_path)}
            assert normal['exit'] == 1
            receipt = run(command, root, manifest_path, base / (scenario + '-trace'), 15)
            assert receipt['exit'] == 1 and not receipt['timeout']
            assert not observed_routes(receipt, root, manifest, runner)
            routes = observed_test_failure_routes(receipt, normal, root, manifest, runner)
            targets = {r['target'] for r in routes}
            assert ('tests/input/data.txt' in targets) == (scenario == 'failed_unit'), (scenario, targets)
            if scenario == 'mutated_helper_unit': assert not routes
            if scenario == 'failed_unit':
                assert all(r['operation'] == 'Observed fixture read during nonpassing unittest' and r['runner'] == 'nonpassing:' + runner for r in routes)
                for invalid in (dict(receipt, timeout=True), dict(receipt, exit=143), dict(receipt, exit=0)):
                    assert not observed_test_failure_routes(invalid, normal, root, manifest, runner)
                assert not observed_test_failure_routes(receipt, dict(normal, exit=True), root, manifest, runner)
                changed_log = base / 'instrumentation-only.log'
                changed_log.write_text(normal_path.read_text().replace('AssertionError:', 'RuntimeError: instrumentation-only '))
                assert not observed_test_failure_routes(dict(receipt, stdout=str(changed_log)), normal, root, manifest, runner)
                try: observed_test_failure_routes(dict(receipt, instrumentation_source_sha256='0'*64), normal, root, manifest, runner)
                except ValueError: pass
                else: raise AssertionError('fabricated instrumentation binding accepted')
                altered = base / 'altered-instrumentation.py'; altered.write_bytes(Path(__file__).read_bytes() + b'\nsubprocess = None\n')
                forged = dict(receipt, instrumentation_source_sha256=hashlib.sha256(altered.read_bytes()).hexdigest())
                try: observed_test_failure_routes(forged, normal, root, manifest, runner, altered)
                except ValueError: pass
                else: raise AssertionError('self-consistent altered instrumentation accepted')
                for old, replacement in [('test_input (__main__.T.test_input)', 'test_other (__main__.T.test_other)'), ('line 5, in test_input', 'line 4, in test_input')]:
                    changed_log.write_text(normal_path.read_text().replace(old, replacement))
                    assert changed_log.read_text() != normal_path.read_text()
                    assert not observed_test_failure_routes(dict(receipt, stdout=str(changed_log)), normal, root, manifest, runner)

        for scenario in ('direct', 'link', 'fake', 'native', 'replace', 'historical', 'historical_read', 'empty', 'empty_zero', 'empty_native'):
            runner = 'tests/' + scenario + '.py'
            receipt = run(['python3', '-B', runner], root, manifest_path, base / scenario, 15)
            assert receipt['exit'] == 0, (scenario, Path(receipt['stdout']).read_text())
            routes = observed_routes(receipt, root, manifest, runner)
            targets = {e['target'] for e in routes}
            assert ('tests/input/data.txt' in targets) == (scenario in ('direct', 'link')), (scenario, targets)
            assert ('tests/input/empty.txt' in targets) == (scenario == 'empty'), (scenario, targets)
            assert 'tests/input/empty-unread.txt' not in targets
            bad = dict(receipt, command=['python3', '-c', 'pass'])
            try: observed_routes(bad, root, manifest, runner)
            except ValueError: pass
            else: raise AssertionError('mismatched command accepted')
        data = root / 'tests/input/data.txt'; twin = root / 'tests/input/twin.txt'
        twin.unlink(); os.link(data, twin)
        # The unsafe write/read/restore leaves Git and hashes apparently clean.
        subprocess.run(['python3', '-B', 'tests/hard.py'], cwd=root, check=True)
        git('diff', '--exit-code', 'HEAD')
        try: verify_inputs(root, manifest)
        except ValueError: pass
        else: raise AssertionError('initial inode alias accepted')
        twin.unlink(); twin.write_bytes(data.read_bytes())
        external = base / 'external-link'; os.link(data, external)
        try: verify_inputs(root, manifest)
        except ValueError: pass
        else: raise AssertionError('external inode alias accepted')
        external.unlink()
        alias = root / 'tests/alias'
        git('update-index', '--assume-unchanged', 'tests/alias')
        alias.unlink(); os.symlink('input/twin.txt', alias)
        git('diff', '--exit-code', 'HEAD')
        try: verify_inputs(root, manifest)
        except ValueError: pass
        else: raise AssertionError('changed tracked symlink accepted')
        alias.unlink(); os.symlink('input/data.txt', alias)
        git('update-index', '--no-assume-unchanged', 'tests/alias')
        alternate = root / 'tests/alternate'; shutil.copytree(root / 'tests/input', alternate)
        saved = base / 'saved-input'; os.rename(root / 'tests/input', saved)
        os.symlink('alternate', root / 'tests/input')
        try: verify_inputs(root, manifest)
        except ValueError: pass
        else: raise AssertionError('symlinked tree ancestor accepted')
        (root / 'tests/input').unlink(); os.rename(saved, root / 'tests/input'); shutil.rmtree(alternate)
        # Existing normalizer controls exercise real temporary-tree cleanup;
        # exact dirfd resolution additionally excludes unrelated relative names.
        forged = json.loads(json.dumps(manifest)); forged['files']['tests/input/data.txt']['sha256'] = '0' * 64
        try: verify_inputs(root, forged)
        except ValueError: pass
        else: raise AssertionError('forged manifest accepted')
        original = (root / 'tests/input/data.txt').read_bytes()
        git('update-index', '--assume-unchanged', 'tests/input/data.txt')
        (root / 'tests/input/data.txt').write_text('unmeasured\n')
        git('diff', '--exit-code', 'HEAD')
        try: verify_inputs(root, manifest)
        except ValueError: pass
        else: raise AssertionError('assume-unchanged mutation accepted')
        (root / 'tests/input/data.txt').write_bytes(original)
        git('update-index', '--no-assume-unchanged', 'tests/input/data.txt')
        cache = root / 'tests/__pycache__/stale.pyc'; cache.parent.mkdir(); cache.write_bytes(b'stale')
        try: verify_inputs(root, manifest)
        except ValueError: pass
        else: raise AssertionError('untracked bytecode accepted')
    print('trace self-test: measured inputs, forged manifest, index flags, bytecode, actual read/fd correlation, historical/synthetic code, link aliases, directory replacement and command binding PASS')


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--scratch')
    parser.add_argument('--manifest')
    parser.add_argument('--output')
    parser.add_argument('--timeout', type=float, default=30)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.self_test:
        self_test(); return 0
    if not all((args.scratch, args.manifest, args.output)): parser.error('--scratch, --manifest and --output are required')
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command: parser.error('supply an explicit command after --')
    try:
        receipt = run(command, args.scratch, args.manifest, args.output, args.timeout)
        print(json.dumps(receipt, sort_keys=True))
        return 0 if receipt['exit'] == 0 else 1
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        parser.exit(1, str(error) + '\n')


if __name__ == '__main__':
    sys.exit(main())
