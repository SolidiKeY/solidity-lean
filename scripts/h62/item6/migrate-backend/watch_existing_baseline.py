#!/usr/bin/env python3
"""Observe the existing baseline and enforce only H78's 8GiB module limit.
No ptrace, restart, new Lean invocation or OS-headroom-triggered signal.
"""
import argparse
import fcntl
import json
import os
from pathlib import Path
import signal
import time

CAP = 8*1024**3
EVIDENCE = Path('/workspace/migrate-backend-evidence')
LEAN = '/workspace/.setup/tools/lean-4.24.0-linux/bin/lean'


def process(pid):
    try:
        raw=Path(f'/proc/{pid}/stat').read_text();fields=raw[raw.rindex(')')+2:].split()
        rows=Path(f'/proc/{pid}/status').read_text().splitlines()
        sizes={row.split(':',1)[0]:int(row.split()[1])*1024 for row in rows if row.startswith(('VmRSS:','VmHWM:'))}
        return {'pid':pid,'ppid':int(fields[1]),'start_ticks':int(fields[19]),'state':fields[0],
                'exit_status_word':int(fields[49]) if len(fields)>49 and fields[0] in ('Z','X') else None,
                'cmdline':Path(f'/proc/{pid}/cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace'),
                'exe':str(Path(f'/proc/{pid}/exe').resolve()),
                'cwd':str(Path(f'/proc/{pid}/cwd').resolve()),**sizes}
    except (FileNotFoundError,ProcessLookupError,PermissionError): return None


def descendant(pid, root, records):
    seen=set()
    while pid in records and pid not in seen:
        if pid == root: return True
        seen.add(pid);pid=records[pid]['ppid']
    return False


def root_epoch_ok(records, pid, start_ticks):
    root=records.get(pid)
    return bool(root and root['start_ticks']==start_ticks and root.get('state') not in ('Z','X'))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--root-pid',type=int,required=True)
    parser.add_argument('--root-start-ticks',type=int,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();output=args.output.resolve()
    if not output.is_relative_to(EVIDENCE): raise RuntimeError('output outside owned evidence')
    lock=Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock').open('a')
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    root=process(args.root_pid)
    if not root or root.get('state') in ('Z','X') or root['start_ticks'] != args.root_start_ticks or root['cmdline'].strip() != 'bash ./run-lean.sh' or root['cwd'] != '/workspace/migrate-backend-baseline':
        raise RuntimeError('existing root identity changed')
    if Path('/proc/swaps').read_text().splitlines()[1:]: raise RuntimeError('swap enabled')
    output.mkdir(exist_ok=False)
    stopped=False
    def stop_observer(sig,frame):
        nonlocal stopped
        stopped=True
    for sig in (signal.SIGTERM,signal.SIGHUP,signal.SIGINT): signal.signal(sig,stop_observer)
    def event(row):
        with (output/'events.jsonl').open('a') as stream: stream.write(json.dumps(row,sort_keys=True)+'\n')
    report={'status':'observing','monitor_pid':os.getpid(),'root':root,'module_cap_bytes':CAP,
            'prior_interval':'Original supervisor lost; prior continuous monitoring/maxRSS/exit capture unavailable.',
            'boundary':'Exit is unknown unless an actual zombie exit word is observed; no matched clean timing acceptance. H78 resource epoch differs from original prefix.',
            'peak_cgroup_bytes':0,'peak_observed_module_rss_bytes':0}
    start=time.monotonic();known={};ended=set()
    (output/'monitor.pid').write_text(str(os.getpid())+'\n')
    try:
        while not stopped:
            current_root=process(args.root_pid)
            if not current_root or current_root['start_ticks'] != args.root_start_ticks:
                report['status']='root_ended_exit_unknown';break
            if current_root['state'] in ('Z','X'):
                report['status']='root_exit_observed_in_proc'
                report['root_exit_status_word']=current_root['exit_status_word']
                if current_root['exit_status_word'] is not None:
                    report['root_exit_code']=os.waitstatus_to_exitcode(current_root['exit_status_word'])
                break
            records={}
            for entry in os.listdir('/proc'):
                if entry.isdigit():
                    item=process(int(entry))
                    if item: records[item['pid']]=item
            if not root_epoch_ok(records,args.root_pid,args.root_start_ticks):
                report['status']='root_epoch_changed_or_ended';break
            current=int(Path('/sys/fs/cgroup/memory.current').read_text())
            available=int(next(row.split()[1] for row in Path('/proc/meminfo').read_text().splitlines() if row.startswith('MemAvailable:')))*1024
            report['peak_cgroup_bytes']=max(report['peak_cgroup_bytes'],current)
            report['headroom_alert']=current > 12*1024**3 or available < 4*1024**3
            live=set()
            for pid,item in records.items():
                if item.get('state') in ('Z','X') or item['exe'] != LEAN or not descendant(pid,args.root_pid,records): continue
                key=(pid,item['start_ticks']);live.add(key)
                row=known.setdefault(key,{'pid':pid,'start_ticks':key[1],'cmdline':item['cmdline'],'peak_rss_bytes':0,'resource_stopped':False})
                row['peak_rss_bytes']=max(row['peak_rss_bytes'],item.get('VmRSS',0),item.get('VmHWM',0))
                report['peak_observed_module_rss_bytes']=max(report['peak_observed_module_rss_bytes'],row['peak_rss_bytes'])
                if row['peak_rss_bytes'] > CAP and not row['resource_stopped']:
                    # pidfd prevents signaling a reused PID. This sole signal condition
                    # is the explicitly authorized per-module 8GiB excess, not headroom.
                    try:
                        fd=os.pidfd_open(pid)
                        try:
                            again=process(pid)
                            root_now=process(args.root_pid)
                            if root_epoch_ok({args.root_pid:root_now} if root_now else {},args.root_pid,args.root_start_ticks) and again and again['start_ticks']==key[1] and again['exe']==LEAN:
                                signal.pidfd_send_signal(fd,signal.SIGKILL)
                                row['resource_stopped']=True
                                event({'event':'module_exceeded_8GiB',**row})
                        finally: os.close(fd)
                    except ProcessLookupError: pass
            for key in set(known)-live-ended:
                ended.add(key);event({'event':'process_ended_exit_unknown',**known[key]})
            report.update(current_cgroup_bytes=current,available_bytes=available,observed_modules=len(known),monitor_wall_seconds=time.monotonic()-start)
            (output/'progress.json').write_text(json.dumps(report,indent=2)+'\n')
            time.sleep(0.25)
        if stopped: report['status']='observer_stopped_build_untouched'
    except BaseException as exc:
        report['status']='observer_failed_build_untouched'
        report['exception']=repr(exc)
        raise
    finally:
        report['monitor_wall_seconds']=time.monotonic()-start
        (output/'result.json').write_text(json.dumps(report,indent=2)+'\n')

if __name__ == '__main__': main()
