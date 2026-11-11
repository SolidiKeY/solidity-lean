#!/usr/bin/env python3
"""Deliberate Python validation support for check-tests-used.py (stdlib only).

This helper is never invoked by inventory/write/check. The caller supplies an
exact command, an isolated scratch checkout, a committed-byte manifest and an
external evidence output stem. No fixture in the original checkout is changed.

  python3 -B scripts/check-tests-used-trace.py --scratch SCRATCH \
    --manifest EXTERNAL_MANIFEST --output EXTERNAL_STEM -- python3 -B tests/test.py

The manifest has measured_revision and files[path] = {blob, sha256}. An audit
hook captures read-only Python open stacks; strace confirms actual reads or
supported kernel copies. Observed mutations and ambiguous writes exclude inputs. The scratch inputs must match
the committed manifest before execution. It records the actual Python call stack and tracks inherited Python
children that honor sitecustomize. Native/Node reads and isolated Python
children are NOT observed. Missing observations never establish non-use.
Passing routes require successful ordinary and instrumented commands. Separate
nonpassing unittest observations retain failure status and require an entered
test/setup method identity. Reinterpreting older traces requires an exact
reviewed full collector SHA. Raw traces and receipts stay outside the code branch.

--observe-module-entry is an explicit, off-by-default positive observation. A
profile call event observes an entered measured module frame, rather than an
audit exec attempt or source-loader read. It adds overhead within the same
timeout. Missing events, removed profiling and unsupported interpreters provide
no non-use evidence. This telemetry is not proof or adversarial attestation.
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
    compiled_sources = set()
    observe_entries = os.environ.get('X1_TRACE_MODULE_ENTRY') == '1'

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
            if observe_entries and target in manifest and isinstance(data, bytes) and original_hash(data).hexdigest() == manifest[target]['sha256']:
                compiled_sources.add(target)
            return
        if observe_entries and event == 'code.__new__':
            target = relative(args[1])
            if target in manifest: untrusted_sources.add(target)
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
    if observe_entries:
        if sys.implementation.name != 'cpython' or sys.getprofile() is not None or threading.getprofile() is not None:
            raise ValueError('module entry observation requires unprofiled CPython')
        def entered(frame, event, argument):
            if event != 'call' or frame.f_code.co_name != '<module>' or getattr(state, 'busy', False): return
            state.busy = True
            try:
                # Direct callback invocation is not an interpreter profile call.
                if sys._getframe(1) is not frame: return
                target = relative(frame.f_code.co_filename)
                if target not in compiled_sources or target in untrusted_sources: return
                fingerprint = code_fingerprint(frame.f_code)
                if fingerprint not in manifest[target].get('module_code_hashes', ()): return
                frames = []; caller = frame.f_back
                while caller:
                    source = relative(caller.f_code.co_filename)
                    if source in manifest:
                        if source in untrusted_sources or code_fingerprint(caller.f_code) not in manifest[source].get('code_hashes', ()): return
                        frames.append({'path': source, 'line': caller.f_lineno})
                    elif caller.f_code.co_filename in ('<string>', '<stdin>') or caller.f_code.co_filename.startswith(root + os.sep): return
                    elif os.path.isabs(caller.f_code.co_filename) and not any(caller.f_code.co_filename.startswith(prefix + os.sep) for prefix in (sys.prefix, sys.base_prefix)): return
                    caller = caller.f_back
                if not frames: return
                record = {'event_id': f'X1EXEC:{threading.get_native_id()}:{next(sequence)}',
                          'target': target, 'frames': frames, 'module_code_sha256': fingerprint,
                          'module_frame_line': frame.f_lineno,
                          'python': list(sys.version_info[:3])}
                os.write(log, json.dumps(record, separators=(',', ':')).encode() + b'\n')
            except (OSError, ValueError, TypeError):
                pass
            finally:
                state.busy = False
        sys.setprofile(entered)
        threading.setprofile(entered)


def run(command, scratch, manifest, output, timeout=30, observe_module_entry=False):
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
        env['X1_TRACE_MODULE_ENTRY'] = '1' if observe_module_entry else '0'
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
                   'observe_module_entry': observe_module_entry,
                   'timeout': timed_out, 'seconds': round(time.monotonic() - start, 3),
                   'events': events, 'stdout': str(output) + '.stdout',
                   'instrumentation_source_sha256': instrumentation_sha,
                   'instrumentation': 'Python open stacks intersected with strace actual reads; mutation-excluded committed inputs'}
        Path(str(output) + '.receipt.json').write_text(json.dumps(receipt, sort_keys=True, indent=2) + '\n')
        return receipt


def _observed_routes(receipt, scratch, manifest, runner, nonpassing=False, module_entries=False):
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
    entries = set(); thread_reads = {}
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
        entry_marker = re.search(r'X1EXEC:[0-9]+:[0-9]+', line)
        if entry_marker and entry_marker[0] in events:
            entry = events[entry_marker[0]]
            # Source and all measured callers must have been read BEFORE entry.
            needed = {entry['target']} | {f['path'] for f in entry['frames']}
            expected_prefix = f'X1EXEC:{tid}:'
            if (entry_marker[0].startswith(expected_prefix) and line.startswith('write(')
                    and str(Path(receipt['events'])) in line and re.search(r'= [1-9][0-9]*\s*$', line)
                    and not resumed and needed <= thread_reads.get(tid, set())): entries.add(entry_marker[0])
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
                if actual in files:
                    all_read_paths.add(actual); thread_reads.setdefault(tid, set()).add(actual)
                event_id = descriptors.get((tid, int(match[1])))
                if event_id and actual == events[event_id]['target']: reads.add(event_id)
        kernel_copy = re.match(r'(sendfile|copy_file_range)\(', line)
        if kernel_copy:
            args = arguments(line)
            name = kernel_copy[1]
            source_index, destination_index, count_index, arity = ((1, 0, 3, 4) if name == 'sendfile' else (0, 2, 4, 6))
            def descriptor(argument):
                return re.fullmatch(r'([0-9]+)<([^>]+)>', argument)
            destination = descriptor(args[destination_index]) if len(args) > destination_index else None
            # A malformed/unknown output descriptor cannot establish immutability.
            if destination is None: dirty.update(files)
            else:
                taint(destination[2])
            source = descriptor(args[source_index]) if len(args) > source_index else None
            result = re.search(r'\)\s+=\s+([0-9]+)\s*$', line)
            supported = (len(args) == arity and source is not None and destination is not None
                         and re.fullmatch(r'[0-9]+', args[count_index])
                         and (name == 'sendfile' or args[5] == '0'))
            if supported and result:
                requested, transferred = int(args[count_index]), int(result[1])
                actual = relative(source[2])
                consumed = (requested > 0 and transferred <= requested and
                            (transferred > 0 or actual in files and files[actual]['sha256'] == hashlib.sha256(b'').hexdigest()))
                if consumed:
                    if actual in files:
                        all_read_paths.add(actual); thread_reads.setdefault(tid, set()).add(actual)
                    event_id = descriptors.get((tid, int(source[1])))
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
        elif kernel_copy:
            # The input fd is read-only evidence, not a mutation. Destination
            # taint was handled above, including conservative unknown forms.
            pass
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
    for event_id in sorted(entries if module_entries else reads):
        event = events[event_id]; target = event['target']
        if target not in files or target in dirty: continue
        if module_entries:
            if event.get('python') != list(sys.version_info[:3]): continue
            hashes = source_code_hashes((scratch_path / target).read_bytes(), '<measured>')
            if event.get('module_code_sha256') not in hashes['module_code_hashes']: continue
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
        if module_entries:
            route.update(operation='entered measured Python module; no fixture consumption credit',
                         module_code_sha256=event['module_code_sha256'], python=event['python'],
                         module_frame_line=event['module_frame_line'])
        routes[json.dumps(route, sort_keys=True, separators=(',', ':'))] = route
    return [routes[k] for k in sorted(routes)]



def observed_routes(receipt, scratch, manifest, runner):
    """Passing traces only; failures never receive passing-runner credit."""
    return _observed_routes(receipt, scratch, manifest, runner)


def observed_module_entries(receipt, normal, scratch, manifest, runner):
    """Candidate observations only, requiring independently successful runs.

    This deliberately does not change the public inventory or grant child/data
    use. Review a separate root chain before adopting any candidate into it.
    """
    if (receipt.get('observe_module_entry') is not True or receipt.get('timeout') is not False
            or normal.get('timeout') is not False or type(receipt.get('exit')) is not int
            or receipt['exit'] != 0 or type(normal.get('exit')) is not int or normal['exit'] != 0
            or normal.get('revision') != manifest['measured_revision']
            or normal.get('command') != receipt.get('command')): return []
    if receipt.get('instrumentation_source_sha256') != hashlib.sha256(Path(__file__).read_bytes()).hexdigest():
        raise ValueError('entered-module observation requires exact collector source')
    return _observed_routes(receipt, scratch, manifest, runner, module_entries=True)


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
    reviewed_collectors = {
        # scripts/check-tests-used-trace.py at 1e3896861de530ec76897f73de3c97efff7b2069.
        # Includes measured-code fingerprints and actual test-method identities.
        '70c5a9e41492bc3f21b4350e4e26f5656e89be41dae8549984cb6e5680ecf316',
        # Reviewed kernel-copy collector frozen with current-master census receipts.
        'bbc4200a194d2ac636f66db5ff5b32fc62efd3fb1af951849072dfd822834c64',
    }
    if raw != Path(__file__).read_bytes() and hashlib.sha256(raw).hexdigest() not in reviewed_collectors:
        raise ValueError('nonpassing trace requires a complete reviewed instrumentation source')
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



def kernel_copy_boundary_controls():
    with tempfile.TemporaryDirectory(prefix='tests-used-copy-controls-') as directory:
        base=Path(directory);root=base/'repo';root.mkdir()
        sources={'tests/input/data.txt':'measured\n','tests/input/twin.txt':'measured\n','tests/input/empty.txt':''}
        def program(operation, mode):
            call=("os.sendfile(dst.fileno(),src.fileno(),None,COUNT)" if operation=='sendfile'
                  else "os.copy_file_range(src.fileno(),dst.fileno(),COUNT)")
            count='0' if mode=='zero' else '1024'
            body='import os,tempfile,threading,ctypes\nfrom pathlib import Path\n'
            name='tests/input/empty.txt' if mode=='empty' else 'tests/input/data.txt'
            if mode=='mutated':body+='p=Path("tests/input/data.txt");original=p.read_bytes();p.write_bytes(b"changed!\\n")\n'
            if mode=='alias':body+='alias=Path("tests/input/alias.txt");os.link("tests/input/data.txt",alias)\n'
            if mode=='reuse':
                body+='libc=ctypes.CDLL(None);src=open("tests/input/data.txt","rb");old=src.fileno();src.close();fd=libc.open(b"tests/input/data.txt",0);assert fd==old\n'
                body+='with tempfile.NamedTemporaryFile() as dst: '+call.replace('src.fileno()','fd').replace('COUNT',count)+'\nos.close(fd)\n'
                return body
            body+='with open('+repr(name)+',"rb") as src:\n'
            if mode=='eof':body+=' src.seek(9999)\n'
            if mode=='thread':
                body+=' def copy():\n  with tempfile.NamedTemporaryFile() as dst: '+call.replace('COUNT',count)+'\n worker=threading.Thread(target=copy);worker.start();worker.join()\n'
            else:
                destination='open("tests/input/twin.txt","wb")' if mode=='destination' else 'tempfile.NamedTemporaryFile()'
                body+=' with '+destination+' as dst:\n'
                if mode=='error':
                    native = ('ctypes.CDLL(None).sendfile(-1,src.fileno(),None,1024)' if operation=='sendfile' else 'ctypes.CDLL(None).copy_file_range(src.fileno(),None,-1,None,1024,0)')
                    body+='  assert '+native+'==-1\n'
                else:body+='  result='+call.replace('COUNT',count)+'\n  assert result=='+('0' if mode in ('zero','eof','empty') else '9')+'\n'
            if mode=='destination':body+='assert Path("tests/input/twin.txt").read_text()=="measured\\n"\n'
            if mode=='mutated':body+='p.write_bytes(original)\n'
            if mode=='alias':body+='alias.unlink()\n'
            return body
        scenarios=[]
        for operation in ('sendfile','copy_file_range'):
            for mode in ('out','destination','mutated','alias','reuse','thread','zero','eof','empty','error'):
                path='tests/'+operation+'_'+mode+'.py';sources[path]=program(operation,mode);scenarios.append((operation,mode,path))
        for path,text in sources.items():
            target=root/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_text(text)
        def git(*args):return subprocess.check_output(['git','-C',str(root),'-c','core.hooksPath=/dev/null',*args])
        git('init','-q');git('add','.');git('-c','user.name=Control','-c','user.email=control@example.invalid','commit','-qm','copy controls')
        revision=git('rev-parse','HEAD').decode().strip()
        manifest={'measured_revision':revision,'files':{path:{'blob':git('rev-parse',revision+':'+path).decode().strip(),'sha256':hashlib.sha256((root/path).read_bytes()).hexdigest()} for path in sources}}
        mp=base/'manifest.json';mp.write_text(json.dumps(manifest))
        for operation,mode,runner in scenarios:
            receipt=run(['python3','-B',runner],root,mp,base/(operation+'-'+mode),15)
            assert receipt['exit']==0,(operation,mode,Path(receipt['stdout']).read_text())
            routes=observed_routes(receipt,root,manifest,runner);targets={r['target'] for r in routes}
            expected='tests/input/empty.txt' if mode=='empty' else 'tests/input/data.txt'
            assert (expected in targets)==(mode in ('out','destination','empty')),(operation,mode,targets)
            assert 'tests/input/twin.txt' not in targets,(operation,mode,'destination received source credit')
            if mode=='out':
                path=Path(receipt['events']).with_name(Path(receipt['events']).name.replace('.events.jsonl','.syscalls'));original=path.read_text()
                lines=original.splitlines(True);index=next(i for i,line in enumerate(lines) if re.match(r'\d+ '+operation+r'\(',line) and re.search(r'= 9\s*$',line))
                line=lines[index].rstrip('\n');tid,body=line.split(' ',1);split=body.rfind(') =')
                assert split>0
                altered=lines[:index]+[tid+' '+body[:split]+' <unfinished ...>\n',tid+' <... '+operation+' resumed>'+body[split:]+'\n']+lines[index+1:]
                path.write_text(''.join(altered));assert expected in {r['target'] for r in observed_routes(receipt,root,manifest,runner)}
                path.write_text(''.join(lines[:index]+[tid+' '+body[:split]+' <unfinished ...>\n']+lines[index+1:]));assert expected not in {r['target'] for r in observed_routes(receipt,root,manifest,runner)}
                if operation=='copy_file_range':
                    malformed=re.sub(r', 0\) = 9$',', 1) = 9',line);assert malformed!=line
                    path.write_text(''.join(lines[:index]+[malformed+'\n']+lines[index+1:]));assert expected not in {r['target'] for r in observed_routes(receipt,root,manifest,runner)}
                path.write_text(original)
        print('kernel-copy self-test: '+str(len(scenarios))+' actual syscall scenarios plus resumed/unfinished/flag controls PASS')


def module_entry_boundary_controls():
    """Finite positive/negative controls; sources are committed in this helper."""
    with tempfile.TemporaryDirectory(prefix='tests-used-entry-controls-') as directory:
        base = Path(directory); root = base / 'repo'; root.mkdir()
        helper = 'VALUE = 3\ndef function(): return VALUE\n'
        setup = 'from pathlib import Path\np=Path(__file__).with_name("helper.py")\n'
        sources = {'tests/helper.py': helper,
            'tests/imported.py': 'import helper\nassert helper.function() == 3\n',
            'tests/read_only.py': setup + 'p.read_bytes()\n',
            'tests/compiled.py': setup + 'compile(p.read_bytes(), str(p), "exec")\n',
            'tests/dead.py': 'if False: import helper\n',
            'tests/blocked.py': setup + 'import sys\ncode=compile(p.read_bytes(),str(p),"exec")\ndef block(event,args):\n if event=="exec" and args[0].co_filename==str(p): raise RuntimeError("blocked")\nsys.addaudithook(block)\ntry: exec(code,{})\nexcept RuntimeError: pass\n',
            'tests/literal.py': setup + 'exec(compile(' + repr(helper) + ',str(p),"exec"),{})\n',
            'tests/read_after.py': setup + 'exec(compile(' + repr(helper) + ',str(p),"exec"),{})\np.read_bytes()\n',
            'tests/wrong_bytes.py': setup + 'data=p.read_bytes()+b"# changed\\n"\nexec(compile(data,str(p),"exec"),{})\n',
            'tests/replaced.py': setup + 'p.read_bytes()\ncode=compile(' + repr(helper) + ',"other.py","exec").replace(co_filename=str(p))\nexec(code,{})\n',
            'tests/restored.py': setup + 'data=p.read_bytes()\np.write_bytes(data+b"# temporary\\n")\np.write_bytes(data)\nexec(compile(data,str(p),"exec"),{})\n',
            'tests/failed.py': 'import helper\nraise RuntimeError("failed")\n',
            'tests/profiler_removed.py': 'import sys\nsys.setprofile(None)\nimport helper\n'}
        for path, content in sources.items():
            target=root/path; target.parent.mkdir(parents=True,exist_ok=True); target.write_text(content)
        def git(*args): return subprocess.check_output(['git','-C',str(root),'-c','core.hooksPath=/dev/null',*args])
        git('init','-q');git('add','.')
        git('-c','user.name=Control','-c','user.email=control@example.invalid','commit','-qm','entry controls')
        revision=git('rev-parse','HEAD').decode().strip()
        manifest={'measured_revision':revision,'files':{p:{'blob':git('rev-parse',revision+':'+p).decode().strip(),
                  'sha256':hashlib.sha256((root/p).read_bytes()).hexdigest()} for p in sources}}
        manifest_path=base/'manifest.json';manifest_path.write_text(json.dumps(manifest))
        for scenario in ('imported','read_only','compiled','dead','blocked','literal','read_after','wrong_bytes','replaced','restored','failed','profiler_removed'):
            runner='tests/'+scenario+'.py';command=['python3','-B',runner]
            normal_process=subprocess.run(command,cwd=root,capture_output=True,timeout=15,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
            normal={'command':command,'revision':revision,'timeout':False,'exit':normal_process.returncode}
            receipt=run(command,root,manifest_path,base/scenario,15,observe_module_entry=True)
            entries=observed_module_entries(receipt,normal,root,manifest,runner)
            targets={r['target'] for r in entries}
            assert ('tests/helper.py' in targets)==(scenario=='imported'), (scenario, targets,Path(receipt['stdout']).read_text())
            if scenario=='imported':
                for bad in (dict(receipt,timeout=True),dict(receipt,observe_module_entry=False),dict(receipt,exit=1)):
                    assert not observed_module_entries(bad,normal,root,manifest,runner)
                assert not observed_module_entries(receipt,dict(normal,exit=True),root,manifest,runner)
                try: observed_module_entries(dict(receipt,instrumentation_source_sha256='0'*64),normal,root,manifest,runner)
                except ValueError: pass
                else: raise AssertionError('fabricated entry collector accepted')
                syscall_path=Path(str(receipt['events']).removesuffix('.events.jsonl')+'.syscalls')
                original_trace=syscall_path.read_text()
                lines=original_trace.splitlines(); altered=[]
                for line in lines:
                    if '/tests/helper.py>' in line and re.search(r'\b(?:read|pread64)\(',line): continue
                    if 'X1EXEC:' in line:
                        tid, body=line.split(None,1)
                        if any(e['target']=='tests/helper.py' and e['event_id'] in line for e in map(json.loads,Path(receipt['events']).read_text().splitlines())):
                            start=body.rsplit(' = ',1)[0]
                            altered += [tid+' '+start+' <unfinished ...>', tid+' read(99<'+str(root/'tests/helper.py')+'>, "x", 1) = 1',tid+' <... write resumed>) = 1']
                            continue
                    altered.append(line)
                assert altered!=lines
                syscall_path.write_text('\n'.join(altered)+'\n')
                assert not observed_module_entries(receipt,normal,root,manifest,runner), 'resumed marker admitted late source read'
                syscall_path.write_text(original_trace)
                disabled=run(command,root,manifest_path,base/'disabled',15)
                assert not any('X1EXEC:' in line for line in Path(disabled['events']).read_text().splitlines())
                assert not observed_module_entries(disabled,normal,root,manifest,runner)
        print('module entry controls: positive import; loader-only/compile/dead/blocked/literal/read-after/wrong-bytes/code-replace/restored/failure/removed-profile/default-off PASS')


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
    kernel_copy_boundary_controls()
    module_entry_boundary_controls()
    print('trace self-test: measured inputs, forged manifest, index flags, bytecode, actual read/fd correlation, historical/synthetic code, link aliases, directory replacement and command binding PASS')


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--observe-module-entry', action='store_true', help='opt in to positive entered-module candidate observations; same timeout, no proof credit')
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
        receipt = run(command, args.scratch, args.manifest, args.output, args.timeout, args.observe_module_entry)
        print(json.dumps(receipt, sort_keys=True))
        return 0 if receipt['exit'] == 0 else 1
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        parser.exit(1, str(error) + '\n')


if __name__ == '__main__':
    sys.exit(main())
