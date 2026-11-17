import contextlib,io,json,subprocess,sys,tarfile,tempfile,unittest
from types import SimpleNamespace
from unittest.mock import patch
import paired_evidence as paired
from pathlib import Path
from replay_current_helpers import helper_targets,require_complete_targets

class CurrentReplayTests(unittest.TestCase):
    def test_nested_helpers_discovered(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);base=root/"tests/h62/item2/audit-theories";(base/"nested").mkdir(parents=True)
            for name in ("A.lean","ElaboratedCensus.lean","nested/B.lean"):(base/name).write_text("")
            self.assertEqual(helper_targets(root),["tests/h62/item2/audit-theories/A.lean","tests/h62/item2/audit-theories/nested/B.lean"])
    def test_complete_unordered_census(self):
        require_complete_targets(["a","nested/b"],{"modules":[{"source":"nested/b"},{"source":"a"}]})
    def test_unreplayed_nested_certificate_refused(self):
        with self.assertRaisesRegex(AssertionError,"recursive replay targets"):
            require_complete_targets(["a"],{"modules":[{"source":"a"},{"source":"nested/b"}]})
    def test_duplicate_certificate_row_refused(self):
        with self.assertRaisesRegex(AssertionError,"recursive replay targets"):
            require_complete_targets(["a"],{"modules":[{"source":"a"},{"source":"a"}]})


class PrivateAttachmentReaderTests(unittest.TestCase):
    BASE = "c7f33cfc9e1b3c8d0e634f0b267971aa2671688d"

    def setUp(self):
        directory = Path(tempfile.gettempdir()).resolve()
        if directory.is_relative_to(paired.ROOT):
            directory = paired.ROOT.parent
        self.temp = tempfile.TemporaryDirectory(dir=directory)
        self.addCleanup(self.temp.cleanup)
        self.work = Path(self.temp.name)
        self.private = self.work / "private"
        self.raw = {}
        for name in paired.HISTORICAL_PINS:
            relative = paired.HISTORICAL_INPUT_PREFIX / name
            raw = subprocess.check_output(
                ["git", "--no-replace-objects", "show", self.BASE + ":" + relative.as_posix()],
                cwd=paired.ROOT,
            )
            path = self.private / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
            self.raw[name] = raw

    def arguments(self):
        return SimpleNamespace(
            historical_input_root=self.private,
            current_repository=self.work / "current",
            original_repository=self.work / "original",
            current_evidence=self.work / "current-evidence",
            original_evidence=self.work / "original-evidence",
            history_record=self.work / "history.json",
            historical_evidence=self.work / "historical-evidence",
            out=self.work / "output.tar.gz",
        )

    def command(self, *extra):
        a = self.arguments()
        command = ["paired_evidence.py", "export"]
        for name in ("current_repository", "current_evidence", "original_repository",
                     "original_evidence", "history_record", "historical_evidence", "out"):
            command.extend(["--" + name.replace("_", "-"), str(getattr(a, name))])
        return command + list(extra)

    def test_exact_private_bytes_and_closed_set(self):
        loaded = paired.load_historical_attachments(self.private)
        self.assertEqual(loaded, self.raw)
        self.assertTrue(all(type(data) is bytes for data in loaded.values()))
        for change in (lambda d: d.pop(next(iter(d))), lambda d: d.update(extra=b"x"),
                       lambda d: d.update({next(iter(d)): bytearray(next(iter(d.values())))})):
            damaged = dict(loaded)
            change(damaged)
            with self.assertRaisesRegex(ValueError, "set mismatch|checksum mismatch"):
                paired.validate_historical_attachments(damaged)

    def test_same_size_corruption_and_extra_byte_refused(self):
        for name, raw in self.raw.items():
            path = self.private / paired.HISTORICAL_INPUT_PREFIX / name
            for damaged in (bytes([raw[0] ^ 1]) + raw[1:], raw + b" "):
                with self.subTest(name=name, size=len(damaged)):
                    path.write_bytes(damaged)
                    with self.assertRaisesRegex(ValueError, "checksum mismatch"):
                        paired.load_historical_attachments(self.private)
            path.write_bytes(raw)

    def test_missing_input_has_no_repository_fallback(self):
        name = next(iter(self.raw))
        (self.private / paired.HISTORICAL_INPUT_PREFIX / name).unlink()
        old_open = Path.open
        def guarded_open(path, *args, **kwargs):
            if path == paired.ROOT / paired.HISTORICAL_INPUT_PREFIX / name:
                raise AssertionError("repository fallback forbidden")
            return old_open(path, *args, **kwargs)
        with patch.object(Path, "open", guarded_open), self.assertRaises(FileNotFoundError):
            paired.load_historical_attachments(self.private)

    def test_nonregular_input_refused(self):
        name = next(iter(self.raw))
        path = self.private / paired.HISTORICAL_INPUT_PREFIX / name
        path.unlink()
        path.mkdir()
        with self.assertRaisesRegex(ValueError, "regular file"):
            paired.load_historical_attachments(self.private)

    def test_repository_roots_refused_before_reads(self):
        with self.assertRaisesRegex(ValueError, "outside repositories"):
            paired.load_historical_attachments(paired.ROOT / ".lake/private-input-must-not-be-read")
        with self.assertRaisesRegex(ValueError, "outside repositories"):
            paired.load_historical_attachments(self.private, repositories=(self.work,))

    def test_symlink_and_parent_escape_refused(self):
        name = next(iter(self.raw))
        path = self.private / paired.HISTORICAL_INPUT_PREFIX / name
        path.unlink()
        outside = self.work / "outside.txt"
        outside.write_bytes(self.raw[name])
        path.symlink_to(outside)
        with self.assertRaisesRegex(ValueError, "escapes private root|symlink"):
            paired.load_historical_attachments(self.private)
        path.unlink()
        path.parent.rename(path.parent.with_name("saved-handoff"))
        path.parent.symlink_to(self.work, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "escapes private root|symlink"):
            paired.load_historical_attachments(self.private)

    def test_ancestor_root_cannot_redirect_into_repository(self):
        a = self.arguments()
        repository_inputs = a.current_repository / paired.HISTORICAL_INPUT_PREFIX
        repository_inputs.mkdir(parents=True)
        for name, raw in self.raw.items():
            (repository_inputs / name).write_bytes(raw)
        alias = self.work / paired.HISTORICAL_INPUT_PREFIX
        alias.parent.mkdir(parents=True)
        alias.symlink_to(repository_inputs, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlink|outside repositories"):
            paired.load_historical_attachments(self.work, repositories=(a.current_repository, a.original_repository))

    def test_each_file_must_be_outside_repository_even_without_symlinks(self):
        private_inputs = self.work / paired.HISTORICAL_INPUT_PREFIX
        private_inputs.mkdir(parents=True)
        for name, raw in self.raw.items():
            (private_inputs / name).write_bytes(raw)
        repository = self.work / "scripts"
        with self.assertRaisesRegex(ValueError, "outside repositories"):
            paired.load_historical_attachments(self.work, repositories=(repository,))

    def test_v2_delegates_authenticated_values_only(self):
        a = self.arguments()
        with patch.object(paired, "export") as exporter:
            paired.export_v2(a)
        exporter.assert_called_once_with(a, historical_attachments=self.raw)
        (self.private / paired.HISTORICAL_INPUT_PREFIX / next(iter(self.raw))).write_bytes(b"bad")
        with patch.object(paired, "export") as exporter:
            with self.assertRaisesRegex(ValueError, "checksum mismatch"):
                paired.export_v2(a)
            exporter.assert_not_called()
        self.assertFalse(a.out.exists())

    def test_v2_excludes_both_repository_inputs(self):
        for field in ("current_repository", "original_repository"):
            a = self.arguments()
            setattr(a, field, self.private)
            with self.subTest(field=field), patch.object(paired, "export") as exporter:
                with self.assertRaisesRegex(ValueError, "outside repositories"):
                    paired.export_v2(a)
                exporter.assert_not_called()

    def test_cli_v1_stays_default_and_v2_is_explicit(self):
        with patch.object(sys, "argv", self.command()), patch.object(paired, "export") as v1, patch.object(paired, "export_v2") as v2:
            paired.main()
            self.assertEqual(v1.call_count, 1)
            v2.assert_not_called()
        args = self.command("--interface-version", "2", "--historical-input-root", str(self.private))
        with patch.object(sys, "argv", args), patch.object(paired, "export") as exporter:
            paired.main()
            self.assertEqual(exporter.call_args.kwargs, {"historical_attachments": self.raw})

    def test_cli_missing_or_wrong_version_root_refused(self):
        for extra in (("--interface-version", "2"),
                      ("--historical-input-root", str(self.private))):
            with self.subTest(extra=extra), patch.object(sys, "argv", self.command(*extra)), contextlib.redirect_stderr(io.StringIO()), patch.object(paired, "export") as exporter:
                with self.assertRaises(SystemExit) as error:
                    paired.main()
                self.assertEqual(error.exception.code, 2)
                exporter.assert_not_called()

    def test_verify_dispatch_unchanged(self):
        a = self.work / "archive.tar.gz"
        with patch.object(sys, "argv", ["paired_evidence.py", "verify", "--archive", str(a)]), patch.object(paired, "verify") as verifier, patch.object(paired, "export") as exporter:
            paired.main()
            self.assertEqual(verifier.call_args.args[0].archive, a)
            exporter.assert_not_called()

    def test_original_output_guard_and_missing_reports_preserved(self):
        a = self.arguments()
        a.out = paired.ROOT / ".paired-output-must-not-be-created"
        with self.assertRaises(AssertionError):
            paired.export(a, historical_attachments=dict(self.raw))
        self.assertFalse(a.out.exists())
        a.out = self.work / "unavailable.tar.gz"
        with self.assertRaises(FileNotFoundError):
            paired.export_v2(a)
        self.assertFalse(a.out.exists())

    def test_export_bytes_identical_with_private_immutable_attachments(self):
        # Synthetic packing controls only: no Lean artifacts or verifier passes.
        a = self.arguments()
        for repo, evidence in ((a.original_repository, a.original_evidence),
                               (a.current_repository, a.current_evidence)):
            repo.mkdir()
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            subprocess.run(["git", "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                            "commit", "--allow-empty", "-qm", "synthetic packing fixture"], cwd=repo, check=True)
            (evidence / "serial").mkdir(parents=True)
            (evidence / "serial/baseline-results.json").write_text(json.dumps({"version": "synthetic-no-Lean-run"}))
            names = ("verified-helpers.json", "original-coverage-ledger.json", "remaining-original-records.json",
                     "all-reviewed-pure-input-roles.json", "acceptance-snapshot.json", "mapped-module-dispositions.json",
                     "verified-payable.json", "verified-totality.json")
            for name in names:
                (evidence / name).write_text(json.dumps({"modules": []} if name in ("verified-helpers.json", "mapped-module-dispositions.json") else {}))
        original_head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=a.original_repository, text=True).strip()
        a.history_record.write_text(json.dumps({"frozen_commit": original_head, "original_tracked_sources_unchanged": True}))
        a.historical_evidence.mkdir()
        (a.historical_evidence / "verified-census.json").write_text("{}")
        repository_inputs = a.current_repository / paired.HISTORICAL_INPUT_PREFIX
        repository_inputs.mkdir(parents=True)
        for name, raw in self.raw.items():
            (repository_inputs / name).write_bytes(raw)
        for name in ("scope-manifest.json", "COORDINATOR-ANSWERS-20261107.json"):
            (repository_inputs / name).write_text(json.dumps({"synthetic_repository_bound_input": name}))
        frozen_source = subprocess.check_output(
            ["git", "--no-replace-objects", "show", self.BASE + ":scripts/h62/item2/audit-theories/paired_evidence.py"],
            cwd=paired.ROOT,
        )
        frozen = {"__name__": "_frozen_paired_exporter", "__file__": paired.__file__}
        exec(compile(frozen_source, "<frozen-paired-exporter>", "exec"), frozen)
        with contextlib.redirect_stdout(io.StringIO()):
            frozen["export"](a)
        legacy = a.out.read_bytes()
        with contextlib.redirect_stdout(io.StringIO()):
            paired.export(a)
        self.assertEqual(a.out.read_bytes(), legacy)
        with contextlib.redirect_stdout(io.StringIO()):
            paired.export_v2(a)
        self.assertEqual(a.out.read_bytes(), legacy)
        for name in self.raw:
            (repository_inputs / name).unlink()
        a.out = self.work / "private-only.tar.gz"
        with self.assertRaises(FileNotFoundError):
            paired.export(a)
        old_open = Path.open
        def guarded_open(path, *args, **kwargs):
            if path.parent == repository_inputs and path.name in self.raw:
                raise AssertionError("legacy attachment fallback forbidden")
            return old_open(path, *args, **kwargs)
        with patch.object(Path, "open", guarded_open), contextlib.redirect_stdout(io.StringIO()):
            paired.export_v2(a)
        self.assertEqual(a.out.read_bytes(), legacy)
        loaded = paired.load_historical_attachments(self.private)
        for name in self.raw:
            (self.private / paired.HISTORICAL_INPUT_PREFIX / name).unlink()
        a.out = self.work / "immutable-buffer.tar.gz"
        with contextlib.redirect_stdout(io.StringIO()):
            paired.export(a, historical_attachments=loaded)
        self.assertEqual(a.out.read_bytes(), legacy)
        with tarfile.open(a.out, "r:gz") as archive:
            index = json.loads(archive.extractfile("index.json").read())
            self.assertIs(index["full_assignment_acceptance"], False)
            self.assertIn("no kernel rerun", index["boundary"])
            for name, raw in self.raw.items():
                self.assertEqual(archive.extractfile("blobs/" + index["attachments"][name]).read(), raw)
            for name in ("scope-manifest.json", "COORDINATOR-ANSWERS-20261107.json"):
                data = archive.extractfile("blobs/" + index["attachments"][name]).read()
                self.assertEqual(json.loads(data), {"synthetic_repository_bound_input": name})

if __name__=="__main__":unittest.main()
