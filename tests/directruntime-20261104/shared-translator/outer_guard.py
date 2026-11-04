"""Guard the VM's outer cgroup while the owned bounded container runs."""
import json, os, pathlib, signal, subprocess, sys, time
cg = pathlib.Path('/sys/fs/cgroup')
limit = int((cg/'memory.max').read_text())
reserve = 4 * 1024**3
minimum = limit
command = sys.argv[1:]
# This harness only runs a newly named task-owned container.
name = command[command.index('--name')+1]
docker_index = command.index('docker')
run_index = command.index('run', docker_index)
stop_command = command[:run_index] + ['stop', '--timeout', '5', name]
def headroom():
    vm = limit - int((cg/'memory.current').read_text())
    host = next(int(x.split()[1])*1024 for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))
    return min(vm, host)
assert headroom() >= reserve, 'H1 initial 4 GiB reserve'
start = time.monotonic()
child = subprocess.Popen(command, start_new_session=True)
violated = False
while child.poll() is None:
    available = headroom()
    minimum = min(minimum, available)
    if available < reserve:
        violated = True
        print('RESOURCE_STOP: outer VM reserve below 4 GiB', flush=True)
        stopped = subprocess.run(stop_command, check=False)
        if stopped.returncode != 0:
            # A startup race must not leave an unguarded task running.
            try:
                os.killpg(child.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                child.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
            cleanup = command[:run_index] + ['rm', '--force', name]
            for attempt in range(3):
                subprocess.run(cleanup, check=False)
                probe = subprocess.run(command[:run_index] + ['ps', '-aq', '--filter', 'name=^/'+name+'$'], capture_output=True, text=True)
                if probe.returncode == 0 and not probe.stdout.strip():
                    break
                time.sleep(.5)
            else:
                print('RESOURCE_STOP: owned container cleanup not established', flush=True)
                sys.exit(125)
        break
    time.sleep(.25)
exit_code = child.wait()
print(json.dumps({'outerExit': exit_code, 'resourceStop': violated,
                  'minimumOuterAvailableBytes': minimum,
                  'outerWallSeconds': time.monotonic()-start}), flush=True)
sys.exit(125 if violated else exit_code)
