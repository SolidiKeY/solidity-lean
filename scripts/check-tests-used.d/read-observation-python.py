"""Opt-in measured Python frame candidates paired with host byte observations.

H1390 P5. This is telemetry under reviewed host/CPython trust, not adversarial
attestation, an independently kept root, or registration of a consumer row.
"""
import itertools
import json
import os
from pathlib import Path
import runpy
import sys
import threading


def collector():
    path = Path(__file__).resolve().parents[1] / 'check-tests-used-trace.py'
    return runpy.run_path(str(path), run_name='observation_primitives')


def install_hook():
    primitives = collector()
    root = Path(os.environ['X1_READ_ROOT']).resolve()
    manifest = json.loads(Path(os.environ['X1_READ_MANIFEST']).read_bytes())['files']
    log = os.open(os.environ['X1_READ_LOG'], os.O_WRONLY | os.O_APPEND)
    serial, busy = itertools.count(1), threading.local()
    def relative(path):
        try:
            return str(Path(path).resolve().relative_to(root))
        except (ValueError, TypeError, OSError):
            return None
    def audit(event, args):
        if event != 'open' or getattr(busy, 'value', False):
            return
        path, _, flags = args
        if not isinstance(path, (str, bytes, os.PathLike)) or flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND):
            return
        busy.value = True
        try:
            target = relative(os.fsdecode(path))
            if target not in manifest:
                return
            frames, frame = [], sys._getframe(1)
            while frame is not None:
                source = relative(frame.f_code.co_filename)
                if source in manifest:
                    code_hash = primitives['code_fingerprint'](frame.f_code)
                    if code_hash not in manifest[source].get('code_hashes', ()):
                        return
                    frames.append(dict(path=source, blob=manifest[source]['blob'], line=frame.f_lineno,
                                       qualname=frame.f_code.co_qualname,
                                       code_firstlineno=frame.f_code.co_firstlineno, code_sha256=code_hash))
                elif (frame.f_code.co_filename.startswith('<') or source is not None
                      or not any(frame.f_code.co_filename.startswith(prefix + os.sep) for prefix in (sys.prefix, sys.base_prefix))):
                    return
                frame = frame.f_back
            if frames:
                record = dict(kind='open', event_id='READHOOK:%d:%d' % (threading.get_native_id(), next(serial)),
                              argument=os.fsdecode(path), target=target, frames=list(reversed(frames)))
                os.write(log, (json.dumps(record, separators=(',', ':')) + '\n').encode())
                busy.pending = record['event_id']
        except (OSError, ValueError, TypeError):
            return  # unavailable context, including a C-level open with no caller frame
        finally:
            busy.value = False
    def ended(frame, event, argument):
        if (getattr(busy, 'value', False) or frame.f_code.co_filename == __file__
                or event not in ('call', 'return', 'c_return', 'c_exception')):
            return
        marker = getattr(busy, 'pending', None)
        if marker is not None:
            busy.value = True
            try:
                busy.pending = None
                os.write(log, (json.dumps(dict(kind='end', event_id=marker)) + '\n').encode())
            finally:
                busy.value = False
    if sys.getprofile() is not None:
        raise ValueError('existing profiler makes open-attempt observation unavailable')
    sys.setprofile(ended)
    sys.addaudithook(audit)


def prepare(scratch, manifest, directory):
    """Owned external instrumentation; measured scratch policy stays unchanged."""
    root, directory = Path(scratch).resolve(), Path(directory).resolve()
    source_root = Path(__file__).resolve().parents[2]
    if directory.is_relative_to(root) or directory.is_relative_to(source_root):
        raise ValueError('instrumentation must be outside scratch and tool checkout')
    verified = collector()['verify_inputs'](root, manifest)
    directory.mkdir(mode=0o700, parents=True, exist_ok=False)
    (directory / 'manifest.json').write_text(json.dumps(verified, sort_keys=True))
    (directory / 'events.jsonl').touch(mode=0o600, exist_ok=False)
    hook = 'import runpy\nrunpy.run_path(' + repr(str(Path(__file__).resolve())) + ',run_name="observation_hook")["install_hook"]()\n'
    (directory / 'sitecustomize.py').write_text(hook)
    return dict(X1_READ_ROOT=str(root), X1_READ_MANIFEST=str(directory / 'manifest.json'),
                X1_READ_LOG=str(directory / 'events.jsonl'), PYTHONPATH=str(directory),
                PYTHONDONTWRITEBYTECODE='1')


class PythonEvents:
    def __init__(self, capture, root, log, *, max_hook_bytes):
        if type(max_hook_bytes) is not int or max_hook_bytes <= 0:
            raise ValueError('positive hook budget required')
        self.capture, self.root, self.log = capture, Path(root).resolve(), str(Path(log).resolve())
        self.limit, self.used, self.pending, self.observed = max_hook_bytes, 0, {}, []
        self.unbound, self.bindings = {}, {}

    def cstring(self, pid, address):
        # /proc memory reads are bounded, and stop at the first terminator.
        data = bytearray()
        while len(data) < 4096:
            chunk = self.capture.memory(pid, address + len(data), 1)
            if chunk == b'\0':
                return os.fsdecode(bytes(data))
            data.extend(chunk)
        raise ValueError('unbounded open pathname')

    def __call__(self, event, pid, tasks):
        self.capture(event, pid, tasks)
        if event['kind'] == 'enter' and event['number'] in (2, 257):
            address = event['args'][0 if event['number'] == 2 else 1]
            try:
                event['path_argument'] = self.cstring(pid, address)
                marker = self.unbound.pop(event['identity'], None)
                if marker is not None and marker['record']['argument'] == event['path_argument']:
                    self.bindings[event['sequence']] = marker
            except OSError:
                return  # kernel may reject an invalid pathname; no match inferred
        if event['kind'] == 'enter' and event['number'] == 1:
            fd, address, count = event['args'][:3]
            try:
                path = os.readlink('/proc/%d/fd/%d' % (pid, fd))
            except OSError:
                return
            if path == self.log:
                if len(tasks) != 1 or self.used + count > self.limit:
                    raise ValueError('unsupported hook context or output budget')
                data = self.capture.memory(pid, address, count)
                self.pending[event['sequence']] = data
                self.used += count
        if event['kind'] == 'leave' and event.get('number') == 1:
            data = self.pending.pop(event.get('enter_sequence'), None)
            if data is not None:
                if event['result'] != len(data):
                    raise ValueError('partial hook write')
                record = json.loads(data)
                if not record.get('event_id', '').startswith('READHOOK:%d:' % pid):
                    raise ValueError('hook task mismatch')
                if record.get('kind') == 'end':
                    marker = self.unbound.get(event['identity'])
                    if marker is not None and marker['record']['event_id'] == record['event_id']:
                        self.unbound.pop(event['identity'])
                elif record.get('kind') == 'open':
                    marker = dict(write_sequence=event['sequence'], task=event['identity'], record=record)
                    self.observed.append(marker)
                    self.unbound[event['identity']] = marker
                else:
                    raise ValueError('unsupported hook event')

    def candidates(self, trace_result):
        capture = self.capture.finish(trace_result)
        if capture['status'] != 'captured':
            return dict(status='unavailable', credit='none', candidates=[], capture=capture)
        candidates = []
        events = trace_result['events']
        for read in capture['records']:
            opened = events[read['open_sequence']]
            if opened.get('number') not in (2, 257):
                continue  # no inferred Python stack across a native fd duplication
            entry = events[opened['enter_sequence']]
            marker = self.bindings.get(entry['sequence'])
            if (marker is not None and marker['task'] == read['task']
                    and str(self.root / marker['record']['target']) == read['target']):
                candidates.append(dict(read_sequence=read['sequence'], hook=marker))
        return dict(status='candidates' if candidates else 'unavailable', credit='none',
                    candidates=candidates, capture=capture)
