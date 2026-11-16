#!/usr/bin/env python3
"""Linux owned-PGID quiescence and fail-closed lease handoff.
Only Z/X states count as stopped. Unknown observations never count as empty.
This covers the owned group, not processes deliberately escaping its session.
"""
if not __debug__: raise SystemExit('OPTIMIZED_PYTHON_UNSUPPORTED')
import fcntl,json,os,pathlib,re,select,shutil,signal,subprocess,sys,time
HERE=pathlib.Path(__file__).resolve().parent

def group_members(pgid,proc_root='/proc'):
 result=[]
 for p in pathlib.Path(proc_root).iterdir():
  if not p.name.isdigit():continue
  try:fields=(p/'stat').read_text().rsplit(') ',1)[1].split()
  except (FileNotFoundError,ProcessLookupError):continue
  # Permission, IO and parse errors are UNKNOWN, never evidence of absence.
  if int(fields[2])==pgid and fields[0] not in ('Z','X','x'):result.append(int(p.name))
 return result

def await_quiescence(pgid,timeout,*,poll=.02,probe=None):
 end=None if timeout is None else time.monotonic()+timeout;empty=0
 while True:
  try:members=(probe or group_members)(pgid)
  except (OSError,ValueError,IndexError):empty=0
  else:empty=empty+1 if not members else 0
  if empty>=2:return True
  if end is not None and time.monotonic()>=end:return False
  time.sleep(poll)

def validate_spec(spec):
 if spec is None:return None
 assert set(spec)=={'view','logs','module','source_root'} and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*',spec['module'])
 out={n:str(pathlib.Path(spec[n]).resolve()) for n in ('view','logs','source_root')};out['module']=spec['module']
 view,logs,source=(pathlib.Path(out[n]) for n in ('view','logs','source_root'))
 for product in (view,logs):
  for protected in (source,HERE.parents[3]):assert not product.is_relative_to(protected) and not protected.is_relative_to(product),'Quarantine overlaps protected source/checkout'
 assert not logs.is_relative_to(view) and not view.is_relative_to(logs),'Quarantine trees overlap'
 return out

def quarantine(spec):
 spec=validate_spec(spec)
 if spec is None:return
 view=pathlib.Path(spec['view']);logs=pathlib.Path(spec['logs']);module=pathlib.Path(spec['module'].replace('.','/'))
 sources=[(view/module.with_suffix(s),module.with_suffix(s)) for s in ('.olean','.ilean','.olean.server','.olean.private')]
 sources += [(logs/'receipt.json',pathlib.Path('receipt.json')),(logs/'cleanup-pending.json',pathlib.Path('cleanup-pending.json'))]
 existing=[(a,b) for a,b in sources if a.exists() or a.is_symlink()]
 for a,b in existing:
  protected=view if a.is_relative_to(view) else logs
  assert a.parent.resolve().is_relative_to(protected),'Artifact/receipt alias escapes quarantine tree'
 if not existing:return
 out=logs/('quarantine-exception-'+str(time.time_ns()));out.mkdir(parents=True)
 for source,relative in existing:
  target=out/relative;target.parent.mkdir(parents=True,exist_ok=True);shutil.move(str(source),str(target))

def handoff(pgid,lease,spec,*,ready_timeout=5):
 """Return a confirmed guardian PID, or None; caller retains lease on failure."""
 spec=validate_spec(spec)
 try:read,write=os.pipe()
 except OSError:return None
 guard=None
 if spec is not None:
  try:
   marker=pathlib.Path(spec['logs'])/'cleanup-pending.json';temporary=marker.with_name(marker.name+'.tmp-'+str(time.time_ns()))
   with temporary.open('x') as stream:stream.write(json.dumps({'pgid':pgid,'state':'lease handoff pending'})+'\n')
   os.replace(temporary,marker)
  except OSError:pass
 try:
  guard=subprocess.Popen([sys.executable,'-I','-B',str(HERE/'lease_lifecycle.py'),'--guardian',str(pgid),str(lease.fileno()),str(write),json.dumps(spec)],pass_fds=(lease.fileno(),write),start_new_session=True,stdin=subprocess.DEVNULL,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
  os.close(write);write=None
  if select.select([read],[],[],ready_timeout)[0]:
   message=os.read(read,4096)
   expected=json.dumps({'pgid':pgid,'dev':os.fstat(lease.fileno()).st_dev,'ino':os.fstat(lease.fileno()).st_ino},sort_keys=True).encode()+b'\n'
   if message==expected:return guard.pid
 except BaseException:pass
 finally:
  try:os.close(read)
  except OSError:pass
  if write is not None:
   try:os.close(write)
   except OSError:pass
 # A non-confirmed guardian must not race the caller's eventual quarantine.
 if guard is not None:
  if guard.poll() is None:guard.kill()
  while guard.poll() is None:time.sleep(.02)
  guard.wait()
 return None

def guardian(pgid,fd,ready,spec):
 assert pgid>1 and fd>=3
 spec=validate_spec(spec)
 # Never drop the inherited lease because of ordinary cancellation/probe errors.
 for sig in (signal.SIGTERM,signal.SIGINT):signal.signal(sig,lambda *_:None)
 fcntl.flock(fd,fcntl.LOCK_EX|fcntl.LOCK_NB)
 st=os.fstat(fd);message=json.dumps({'pgid':pgid,'dev':st.st_dev,'ino':st.st_ino},sort_keys=True).encode()+b'\n'
 try:os.write(ready,message)
 except OSError:pass
 finally:os.close(ready)
 while True:
  try:
   if await_quiescence(pgid,1):
    quarantine(spec);os.close(fd);return
  except BaseException:pass
  # Retain lease on observation/quarantine failure; no new native work starts.
  time.sleep(.1)

if __name__=='__main__':
 assert len(sys.argv)==6 and sys.argv[1]=='--guardian'
 guardian(int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]),json.loads(sys.argv[5]))
