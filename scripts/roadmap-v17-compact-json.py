#!/usr/bin/env python3
"""Hash-bound JSON whitespace compaction. Data accounting, NEVER proof validation."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import resource
import stat
import sys
import tarfile

MAX_INPUT = 512 * 1024 * 1024
MAX_COMPACT = 16 * 1024 * 1024
MAX_MEMBERS = 10000
CHUNK = 65536
FLAGS = dict(kernelValidated=False, selectorsAuthenticated=False, replayVerified=False,
             semanticPremisesDischarged=False, releaseClosed=False)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(stream):
    h = hashlib.sha256()
    while block := stream.read(CHUNK):
        h.update(block)
    return h.hexdigest()


def regular(path):
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        require(stat.S_ISREG(os.fstat(fd).st_mode), 'input is not a regular file')
        return os.fdopen(fd, 'rb')
    except BaseException:
        os.close(fd)
        raise


def identity(info):
    return (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns)


def pinned_hash(value):
    require(isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value), 'invalid SHA256 pin')
    return value


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def forbidden_constant(value):
    raise ValueError('non-JSON numeric constant: ' + value)


def compact(stream, output, expected, validation=None):
    """Compact bytes plus a bounded syntax copy retaining token separators.

    A syntax copy retains one space per outside-string whitespace run. Its
    size is at most twice the compact bytes plus one; strings/numbers retain
    exact original bytes. This validates original syntax, not repaired tokens.
    """
    pinned_hash(expected)
    source_hash = hashlib.sha256()
    output_hash = hashlib.sha256()
    validation_hash = hashlib.sha256()
    total = written = validation_size = 0
    quoted = escaped = last_space = False
    whitespace = re.compile(rb'[ \t\r\n]+')
    while block := stream.read(CHUNK):
        total += len(block)
        require(total <= MAX_INPUT, 'input byte limit exceeded')
        source_hash.update(block)
        buf = bytearray()
        syntax = bytearray()
        i = 0
        while i < len(block):
            if not quoted:
                end = block.find(b'"', i)
                end = len(block) if end < 0 else end
                outside = block[i:end]
                buf.extend(outside.translate(None, b' \t\r\n'))
                separated = whitespace.sub(b' ', outside)
                if last_space and separated.startswith(b' '):
                    separated = separated[1:]
                if separated:
                    syntax.extend(separated)
                    last_space = separated.endswith(b' ')
                i = end
                if i < len(block):
                    buf.append(34)
                    syntax.append(34)
                    last_space = False
                    quoted = True
                    i += 1
            else:
                if escaped:
                    buf.append(block[i])
                    syntax.append(block[i])
                    i += 1
                    escaped = False
                    continue
                quote = block.find(b'"', i)
                slash = block.find(b'\\', i)
                end = min(x for x in (quote, slash, len(block)) if x >= 0)
                buf.extend(block[i:end])
                syntax.extend(block[i:end])
                i = end
                if i < len(block):
                    char = block[i]
                    buf.append(char)
                    syntax.append(char)
                    i += 1
                    if char == 34:
                        quoted = False
                    elif i < len(block):
                        buf.append(block[i])
                        syntax.append(block[i])
                        i += 1
                    else:
                        escaped = True
        written += len(buf)
        validation_size += len(syntax)
        require(written <= MAX_COMPACT, 'compact byte limit exceeded')
        require(validation_size <= 2 * MAX_COMPACT + 1, 'syntax-copy byte limit exceeded')
        output.write(buf)
        if validation is not None:
            validation.write(syntax)
        output_hash.update(buf)
        validation_hash.update(syntax)
    require(not quoted and not escaped, 'truncated JSON string')
    require(source_hash.hexdigest() == expected, 'input SHA256 mismatch')
    return dict(inputBytes=total, compactBytes=written, inputSha256=expected,
                compactSha256=output_hash.hexdigest(), syntaxBytes=validation_size,
                syntaxSha256=validation_hash.hexdigest())


def safe_name(name):
    p = PurePosixPath(name)
    return bool(name) and not p.is_absolute() and '..' not in p.parts and str(p) == name


def execute(args):
    pinned_hash(args.sha256)
    require((args.member is None) == (args.archive_sha256 is None), 'archive member/pin must be paired')
    if args.member is not None:
        require(safe_name(args.member), 'unsafe member name')
        pinned_hash(args.archive_sha256)
    out = Path(args.out)
    out.mkdir(mode=0o700, parents=False, exist_ok=False)
    report = dict(schema=1, status='incomplete', accountingOnly=True, toolExecutionAuthenticated=False, **FLAGS)
    tool_before = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report['input'] = dict(path=str(Path(args.input).absolute()), expectedSha256=args.sha256,
                           member=args.member, expectedArchiveSha256=args.archive_sha256)
    partial = out / 'compact.unverified.json'
    final = out / 'compact.json'
    syntax_path = out / 'syntax.unverified.json'
    try:
        with regular(args.input) as source:
            before = identity(os.fstat(source.fileno()))
            if args.member is None:
                require(before[2] <= MAX_INPUT, 'input byte limit exceeded')
                with partial.open('xb') as target, syntax_path.open('xb') as syntax:
                    report['bytes'] = compact(source, target, args.sha256, syntax)
            else:
                require(digest(source) == args.archive_sha256, 'archive SHA256 mismatch')
                source.seek(0)
                seen = set()
                found = False
                with tarfile.open(fileobj=source, mode='r:*') as archive:
                    for member in archive:
                        require(len(seen) < MAX_MEMBERS, 'archive member limit exceeded')
                        require(safe_name(member.name) and member.name not in seen, 'unsafe/duplicate archive member')
                        seen.add(member.name)
                        require(member.type in (tarfile.REGTYPE, tarfile.AREGTYPE) and not member.issparse(), 'nonregular archive member')
                        require(0 <= member.size <= MAX_INPUT, 'archive member byte limit exceeded')
                        if member.name == args.member:
                            found = True
                            with archive.extractfile(member) as data, partial.open('xb') as target, syntax_path.open('xb') as syntax:
                                report['bytes'] = compact(data, target, args.sha256, syntax)
                require(found, 'missing archive member')
                report['archiveMembers'] = len(seen)
            require(identity(os.fstat(source.fileno())) == before, 'input changed during collection')
            require(identity(os.stat(args.input, follow_symlinks=False)) == before, 'input path changed')
            source.seek(0)
            expected = args.archive_sha256 if args.member is not None else args.sha256
            require(digest(source) == expected, 'input changed after collection')
        syntax = syntax_path.read_bytes()
        require(hashlib.sha256(syntax).hexdigest() == report['bytes']['syntaxSha256'], 'syntax copy changed')
        json.loads(syntax, object_pairs_hook=unique_object, parse_constant=forbidden_constant)
        del syntax
        raw = partial.read_bytes()
        require(hashlib.sha256(raw).hexdigest() == report['bytes']['compactSha256'], 'compact output changed')
        json.loads(raw, object_pairs_hook=unique_object, parse_constant=forbidden_constant)
        del raw
        tool_after = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        require(tool_before == tool_after, 'tool source changed during collection')
        report.update(status='data-only', jsonSyntaxValidated=True, compactPath=str(final.absolute()))
        report['reportedToolSourceSha256'] = tool_before
        report['reportedPythonFileSha256'] = hashlib.sha256(Path(sys.executable).read_bytes()).hexdigest()
        report['ceilings'] = dict(addressSpaceBytes=512 * 1024 * 1024, cpuSeconds=60,
                                  inputBytes=MAX_INPUT, compactBytes=MAX_COMPACT)
        report['observedProcessLimits'] = dict(addressSpace=list(resource.getrlimit(resource.RLIMIT_AS)),
                                               cpu=list(resource.getrlimit(resource.RLIMIT_CPU)))
        pending = out / 'receipt.pending.json'
        with pending.open('x') as receipt:
            receipt.write(json.dumps(report, indent=2) + '\n')
        partial.rename(final)
        pending.rename(out / 'receipt.json')
        return report
    except Exception as error:
        if final.exists():
            final.rename(partial)
        report.update(status='error', error=type(error).__name__ + ': ' + str(error))
        (out / 'receipt.json').write_text(json.dumps(report, indent=2) + '\n')
        raise


def main():
    for key, cap in [(resource.RLIMIT_AS, 512 * 1024 * 1024), (resource.RLIMIT_CPU, 60)]:
        soft, hard = resource.getrlimit(key)
        finite = [n for n in (soft, hard, cap) if n != resource.RLIM_INFINITY]
        limit = min(finite)
        resource.setrlimit(key, (limit, limit))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', required=True)
    parser.add_argument('--sha256', required=True)
    parser.add_argument('--member')
    parser.add_argument('--archive-sha256')
    parser.add_argument('--out', required=True)
    args = parser.parse_args()
    try:
        print(json.dumps(execute(args), sort_keys=True))
        return 0
    except Exception as error:
        print(json.dumps(dict(status='error', error=type(error).__name__ + ': ' + str(error), **FLAGS)), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
