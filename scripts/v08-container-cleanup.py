"""Confirm cleanup of exactly the labelled container created by this run.
Unknown/foreign ownership fails closed. No container is removed.
"""
import json, subprocess
LABEL = 'org.solidity.v08.run'

def ensure_stopped(docker, name, token, log, run=subprocess.run, env=None):
 def command(arguments, timeout):
  log.write('$ ' + json.dumps(docker + arguments) + '\n'); log.flush()
  try:
   result = run(docker + arguments, text=True, stdout=subprocess.PIPE,
    stderr=subprocess.STDOUT, timeout=timeout, env=env)
   log.write('exit=' + str(result.returncode) + '\n' + result.stdout + '\n'); log.flush()
   return result
  except (subprocess.TimeoutExpired, OSError) as error:
   log.write(type(error).__name__ + ': ' + str(error) + '\n'); log.flush()
   return None
 def inspect():
  result = command(['inspect', '--format', '{{.State.Running}} {{index .Config.Labels "' + LABEL + '"}}', name], 5)
  if result is None: return 'unknown'
  if result.returncode != 0:
   if 'No such object' in result.stdout or 'No such container' in result.stdout: return 'absent'
   return 'unknown'
  fields = result.stdout.split()
  if len(fields) != 2 or fields[1] != token: return 'foreign'
  return {'true': 'running', 'false': 'stopped'}.get(fields[0], 'unknown')
 state = inspect()
 if state in ['stopped', 'absent']: return True, False
 if state != 'running': return False, False
 # The identity token was verified before either stop/kill operation.
 command(['stop', name], 15)
 state = inspect()
 if state in ['stopped', 'absent']: return True, True
 if state != 'running': return False, True
 command(['kill', name], 5)
 return inspect() in ['stopped', 'absent'], True
