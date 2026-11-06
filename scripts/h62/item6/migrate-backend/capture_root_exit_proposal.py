#!/usr/bin/env python3
"""UNAPPROVED proposal: exit-event observation of the existing gate root only.
Do not execute without explicit approval after the recorded automatic rejection.
Never launches Lean, traces syscalls, changes sources or signals Lean modules.
"""
import argparse
import ctypes
import json
import os
from pathlib import Path
import time
from watch_existing_baseline import process


def main():
    raise RuntimeError('WITHDRAWN after independent safety review; prior approval question is withdrawn and this proposal must not execute')
    parser=argparse.ArgumentParser()
    parser.add_argument('--approved-exit-observation',action='store_true')
    parser.add_argument('--pid',type=int,required=True)
    parser.add_argument('--start-ticks',type=int,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if not args.approved_exit_observation: raise RuntimeError('proposal requires explicit approval')
    output=args.output.resolve()
    if not output.is_relative_to(Path('/workspace/migrate-backend-evidence')) or output.exists():
        raise RuntimeError('refusing output outside owned evidence or existing output')
    original=process(args.pid)
    if not original or original['start_ticks']!=args.start_ticks or original['cmdline'].strip()!='bash ./run-lean.sh':
        raise RuntimeError('original baseline root identity changed')
    libc=ctypes.CDLL(None,use_errno=True)
    def ptrace(request,data=0):
        if libc.ptrace(request,args.pid,0,data)==-1: raise OSError(ctypes.get_errno(),'ptrace')
    # PTRACE_SEIZE with only PTRACE_O_TRACEEXIT; no EXITKILL or syscall tracing.
    ptrace(0x4206,0x40)
    report={'status':'observing_exit_only','root':original,'start_wall':time.time()}
    output.write_text(json.dumps(report,indent=2)+'\n')
    while True:
        pid,status,usage=os.wait4(args.pid,0)
        if os.WIFSTOPPED(status):
            event=status>>16
            if event==6:
                word=ctypes.c_ulong();ptrace(0x4201,ctypes.byref(word))
                report['pending_exit_status_word']=word.value
            ptrace(7,0 if event else os.WSTOPSIG(status))
        else:
            report.update(status='exit_observed',exit_status_word=status,
                          exit_code=os.waitstatus_to_exitcode(status),
                          traced_root_maxrss_kib=usage.ru_maxrss,end_wall=time.time())
            output.write_text(json.dumps(report,indent=2)+'\n')
            return

if __name__=='__main__': main()
