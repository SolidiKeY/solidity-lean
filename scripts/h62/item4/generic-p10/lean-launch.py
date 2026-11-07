#!/usr/bin/env python3
"""Launch the unchanged official Lean with this lane's resource flags.

Used only in an off-git surrogate sysroot; never changes an original toolchain
binary or tracked Lake configuration. File compilation is serialized, while
the LSP watchdog itself must remain free to launch its single file worker.
"""
import fcntl
import os
import sys

args = sys.argv[1:]
real = os.environ['GENERIC_P10_LEAN_EXE']
for i, arg in enumerate(args):
    for short, long, maximum in [('-j', '--threads', 1), ('-M', '--memory', 11264), ('-s', '--tstack', 131072)]:
        value = None
        if arg in {short, long}:
            value = args[i+1] if i+1 < len(args) else ''
        elif arg.startswith(long+'='): value = arg.split('=', 1)[1]
        elif arg.startswith(short) and arg != short: value = arg[len(short):]
        if value is not None:
            if not value.isdigit() or not 0 < int(value) <= maximum:
                raise SystemExit(f'conflicting resource argument: {arg}')
if any(a.endswith('.lean') for a in args) and not any(a in {'--server', '--worker'} for a in args):
    lock = open('/tmp/generic-p10-compiler.lock', 'w')
    fcntl.flock(lock, fcntl.LOCK_EX)
    os.set_inheritable(lock.fileno(), True)
os.environ['LEAN_NUM_THREADS'] = '1'
os.execv(real, [real, '-j1', '-M11264', '--tstack=131072', *args])
