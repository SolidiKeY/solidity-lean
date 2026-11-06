"""Guard regression: altered container config passes as the intended Lean execution."""
import copy
import importlib.util
import pathlib
import unittest

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/container_spec.py"
spec = importlib.util.spec_from_file_location("container_spec", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class ContainerSpec(unittest.TestCase):
    def setUp(self):
        self.plan = {"image": "sha256:" + "a" * 64, "argv": ["/tool/lean", "-j1", "--tstack=131072", "Solidity/A.lean"],
                     "user": "1000:1000", "cwd": "/repo", "cgroup_parent": "",
                     "cpu": {"NanoCpus": 0, "CpuQuota": 0, "CpuPeriod": 0, "CpuShares": 0, "CpusetCpus": "", "CpusetMems": ""}, "env": {"LEAN_NUM_THREADS": "1", "LEAN_PATH": "/cache"},
                     "mounts": [{"source": "/host/repo", "destination": "/repo"}, {"source": "/host/cache", "destination": "/cache"}]}
        self.inspect = {"Image": self.plan["image"],
                        "Config": {"Entrypoint": ["/tool/lean"], "Cmd": self.plan["argv"][1:], "User": "1000:1000", "WorkingDir": "/repo",
                                   "Env": ["LEAN_NUM_THREADS=1", "LEAN_PATH=/cache"], "Healthcheck": None},
                        "HostConfig": {"Memory": 12 * module.GIB, "MemorySwap": 12 * module.GIB, "PidsLimit": 16,
                                       "NetworkMode": "none", "Privileged": False, "ReadonlyRootfs": True,
                                       "PidMode": "", "IpcMode": "private", "UTSMode": "", "CgroupnsMode": "private", "CapAdd": None,
                                       "Devices": [], "SecurityOpt": ["no-new-privileges"],
                                       "RestartPolicy": {"Name": "no", "MaximumRetryCount": 0}, "CgroupParent": "",
                                       **self.plan["cpu"]},
                        "Mounts": [{"Type": "bind", "RW": False, "Source": "/host/repo", "Destination": "/repo"},
                                   {"Type": "bind", "RW": False, "Source": "/host/cache", "Destination": "/cache"}]}

    def test_matching_fixture(self):
        self.assertEqual([], module.validate(self.inspect, self.plan))

    def test_guarded_regressions(self):
        changes = [("Memory", 12 * module.GIB + 1), ("MemorySwap", 0), ("PidsLimit", 0),
                   ("NetworkMode", "host"), ("Privileged", True), ("ReadonlyRootfs", False),
                   ("PidMode", "host"), ("CgroupnsMode", None),
                   ("RestartPolicy", {"Name": "always", "MaximumRetryCount": 0}),
                   ("RestartPolicy", {"Name": "no", "MaximumRetryCount": False}),
                   ("NanoCpus", 100000000), ("CpusetCpus", "0"), ("CgroupParent", "/different-cpu-limited-parent"), ("DeviceRequests", ["device"]), ("CapAdd", ["SYS_ADMIN"]), ("SecurityOpt", [])]
        for key, value in changes:
            obj = copy.deepcopy(self.inspect)
            obj["HostConfig"][key] = value
            with self.subTest(key=key):
                self.assertNotEqual([], module.validate(obj, self.plan))
        missing_healthcheck = copy.deepcopy(self.inspect)
        del missing_healthcheck["Config"]["Healthcheck"]
        self.assertTrue(module.validate(missing_healthcheck, self.plan))
        missing_cpu = copy.deepcopy(self.plan)
        del missing_cpu["cpu"]["CpusetCpus"]
        self.assertTrue(module.validate(self.inspect, missing_cpu))
        for mutate in [lambda obj: obj.update(Image="sha256:" + "b" * 64),
                       lambda obj: obj["Config"].update(Cmd=["-j4", "A.lean"]),
                       lambda obj: obj["Config"].update(Env=["LEAN_NUM_THREADS=2", "LEAN_PATH=/cache"]),
                       lambda obj: obj["Config"].update(User="0:0"),
                       lambda obj: obj["Config"].update(WorkingDir="/other"),
                       lambda obj: obj["Config"].update(Healthcheck={"Test": ["CMD", "/tool/lean", "-j4", "Other.lean"]}),
                       lambda obj: obj["Mounts"][0].update(RW=True),
                       lambda obj: obj["Mounts"].append({"Type": "bind", "RW": False, "Source": "/var/run/docker.sock", "Destination": "/sock"})]:
            obj = copy.deepcopy(self.inspect)
            mutate(obj)
            self.assertTrue(module.validate(obj, self.plan))


if __name__ == "__main__":
    unittest.main()
