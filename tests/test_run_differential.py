#!/usr/bin/env python3

import contextlib
import io
import json
from pathlib import Path
import shutil
import sys
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import run_differential as driver  # noqa: E402

SOURCE = "testdata/differential/a.sol"
ARTIFACT = "testdata/differential/expected/a.json"


def corpus(cases=None):
    return {
        "format": driver.CORPUS_FORMAT,
        "fuel": 1000,
        "suites": [{
            "name": "a",
            "source": SOURCE,
            "contract": "A",
            "artifact": ARTIFACT,
            "cases": cases if cases is not None else [
                {"name": "f_returns", "function": "f", "args": [1, True, "0x00ff"],
                 "expect": {"return": [2]}},
            ],
        }],
    }


class FakeRoot:
    """A repository root with one suite, its artifact and a fake holbuild."""

    def __init__(self, directory: Path, source: str = "contract A {}\n") -> None:
        self.root = directory
        shutil.copyfile(ROOT / "SOLIDITY_PIN", directory / "SOLIDITY_PIN")
        (directory / "profiles").mkdir()
        profile = driver.exporter.DEFAULT_PROFILE
        shutil.copyfile(profile, directory / "profiles" / profile.name)
        self.write(driver.CORPUS.as_posix(), json.dumps(corpus()))
        self.write(SOURCE, source)
        pin = (ROOT / "SOLIDITY_PIN").read_text(encoding="ascii").strip()
        self.write(ARTIFACT, json.dumps({
            "format": driver.ARTIFACT_FORMAT,
            "compiler": {"pin": pin, "reportedVersion": f"Version: 0.8.37+commit.{pin[:8]}"},
            "profile": json.loads(profile.read_text(encoding="utf-8")),
            "input": {
                "settings": {**json.loads(profile.read_text(encoding="utf-8"))["settings"],
                             "outputSelection": driver.exporter.OUTPUT_SELECTION},
                "sources": {SOURCE: {"content": "contract A {}\n"}},
            },
            "output": {"contracts": {SOURCE: {"A": {"evm": {"deployedBytecode": {"object": "00"}}}}}},
        }))
        self.write(driver.CORPUS_SCRIPT.as_posix(), textwrap.dedent(f"""\
            fun holbuild_extra_deps (_ : string list) = ()
            val () = holbuild_extra_deps [
              "../{driver.CORPUS.as_posix()}",
              "../{ARTIFACT}"
            ]
            """))

    def write(self, name: str, text: str) -> None:
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def holbuild(self, results: list[dict], status: int) -> Path:
        """A holbuild that writes the given result lines to its child log."""
        log = self.root / "build.log"
        lines = "".join(driver.RESULT_PREFIX + json.dumps(r) + "\n" for r in results)
        path = self.root / "holbuild"
        path.write_text(textwrap.dedent(f"""\
            #!{sys.executable}
            import sys
            open({str(log)!r}, "w").write({lines!r})
            print("child log: {log}")
            sys.exit({status})
            """), encoding="utf-8")
        path.chmod(0o755)
        return path

    def run(self, holbuild: Path) -> tuple[int, dict]:
        report_dir = self.root / "report"
        with contextlib.redirect_stdout(io.StringIO()):
            status = driver.main(["--holbuild", str(holbuild), "--report-dir", str(report_dir)],
                                 root=self.root)
        report = json.loads((report_dir / "report.json").read_text(encoding="utf-8"))
        return status, report


SUITE_OK = {"kind": "suite", "suite": "a", "status": "ok"}
RETURNED = {"returned": "0x" + "00" * 31 + "02"}


class CorpusTests(unittest.TestCase):
    def test_committed_corpus_is_consistent(self) -> None:
        loaded = driver.load_corpus(ROOT / driver.CORPUS)
        checks = driver.check_artifacts(ROOT, loaded)
        checks.append(driver.check_staging(ROOT, driver.CORPUS, loaded))
        self.assertEqual([c for c in checks if c["status"] != "pass"], [])

    def test_rejects_duplicate_cases(self) -> None:
        case = {"name": "f", "function": "f", "args": [], "expect": {"panic": 17}}
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "corpus.json"
            path.write_text(json.dumps(corpus([case, case])), encoding="utf-8")
            with self.assertRaisesRegex(driver.CorpusError, "duplicate case"):
                driver.load_corpus(path)

    def test_rejects_malformed_expectation(self) -> None:
        case = {"name": "f", "function": "f", "args": [], "expect": {"return": [1], "panic": 1}}
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "corpus.json"
            path.write_text(json.dumps(corpus([case])), encoding="utf-8")
            with self.assertRaisesRegex(driver.CorpusError, "exactly one"):
                driver.load_corpus(path)

    def test_detects_stale_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary), source="contract A { }\n")
            checks = driver.check_artifacts(fake.root, corpus())
            failed = [c["check"] for c in checks if c["status"] != "pass"]
            self.assertEqual(failed, ["source-fresh"])

    def test_detects_unstaged_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            fake.write(driver.CORPUS_SCRIPT.as_posix(), "val () = ()\n")
            self.assertEqual(driver.check_staging(fake.root, driver.CORPUS, corpus())["status"],
                             "fail")

    def test_detects_compiler_identity_inconsistent_with_pin_and_profile(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            path = fake.root / ARTIFACT
            artifact = json.loads(path.read_text(encoding="utf-8"))
            commit = artifact["compiler"]["pin"][:8]
            for version in (f"Version: 0.8.20+commit.{commit}",
                            "Version: 0.8.37+commit.00000000",
                            f"Version: 0.8.37+commit.{commit[:4]}",
                            "Version: 0.8.37", None):
                with self.subTest(version=version):
                    artifact["compiler"]["reportedVersion"] = version
                    fake.write(ARTIFACT, json.dumps(artifact))
                    checks = driver.check_artifacts(fake.root, corpus())
                    self.assertEqual([c["check"] for c in checks if c["status"] != "pass"],
                                     ["artifact-compiler-version"])

    def test_detects_input_settings_inconsistent_with_profile(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            original = json.loads((fake.root / ARTIFACT).read_text(encoding="utf-8"))
            for key, value in (("viaIR", False), ("evmVersion", "paris"),
                               ("outputSelection", {})):
                with self.subTest(setting=key):
                    artifact = json.loads(json.dumps(original))
                    artifact["input"]["settings"][key] = value
                    fake.write(ARTIFACT, json.dumps(artifact))
                    checks = driver.check_artifacts(fake.root, corpus())
                    self.assertEqual([c["check"] for c in checks if c["status"] != "pass"],
                                     ["artifact-settings"])


class DriverTests(unittest.TestCase):
    def test_agreement_passes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            status, report = fake.run(fake.holbuild([
                SUITE_OK,
                {"kind": "case", "suite": "a", "case": "f_returns", "status": "agree",
                 "theorem": "a_f_returns", "outcome": RETURNED},
            ], 0))
            self.assertEqual(status, 0)
            self.assertEqual(report["failures"], [])
            self.assertIn({"theorem": "a_f_returns", "suite": "a", "case": "f_returns",
                           "status": "proved", "outcome": RETURNED}, report["kernel_checked"])

    def test_altered_expectation_fails_with_reproduction(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            unexpected = {"kind": "case", "suite": "a", "case": "f_returns",
                          "status": "unexpected", "bytecode": RETURNED, "source": RETURNED,
                          "expected": {"returned": "0x" + "00" * 31 + "03"}}
            status, report = fake.run(fake.holbuild([SUITE_OK, unexpected], 1))
            self.assertEqual(status, 1)
            self.assertEqual([f["status"] for f in report["failures"]], ["unexpected"])
            directory = fake.root / "report" / "failures" / "a" / "f_returns"
            for name in ("inputs.json", "outcomes.json", "compiler.json", "artifact.json",
                         "sources/" + SOURCE):
                self.assertTrue((directory / name).is_file(), name)
            outcomes = json.loads((directory / "outcomes.json").read_text(encoding="utf-8"))
            self.assertEqual(outcomes["bytecode"], RETURNED)

    def test_suite_rejection_fails(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            rejected = {"kind": "suite", "suite": "a", "status": "import-rejected",
                        "message": "unsupported nodeType"}
            status, report = fake.run(fake.holbuild([rejected], 1))
            self.assertEqual(status, 1)
            self.assertEqual([f["status"] for f in report["failures"]], ["import-rejected"])
            self.assertEqual(report["kernel_checked"], [])

    def test_missing_result_fails(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            status, report = fake.run(fake.holbuild([SUITE_OK], 0))
            self.assertEqual(status, 1)
            self.assertEqual([f["status"] for f in report["failures"]], ["missing"])

    def test_missing_suite_result_fails_without_claiming_witnesses(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            status, report = fake.run(fake.holbuild([], 0))
            self.assertEqual(status, 1)
            self.assertEqual([f["status"] for f in report["failures"]], ["missing"])
            self.assertEqual(report["kernel_checked"], [])
            self.assertTrue((fake.root / "report/failures/a/inputs.json").is_file())

    def test_missing_suite_result_does_not_discard_other_suites(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            data = corpus()
            second = {**data["suites"][0], "name": "b"}
            data["suites"].append(second)
            fake.write(driver.CORPUS.as_posix(), json.dumps(data))
            status, report = fake.run(fake.holbuild([
                SUITE_OK,
                {"kind": "case", "suite": "a", "case": "f_returns", "status": "agree",
                 "theorem": "a_f_returns", "outcome": RETURNED},
            ], 0))
            self.assertEqual(status, 1)
            self.assertEqual([(f["suite"], f["status"]) for f in report["failures"]],
                             [("b", "missing")])
            self.assertEqual(len(report["kernel_checked"]), 3)
            self.assertTrue(all(w["suite"] == "a" for w in report["kernel_checked"]))

    def test_cached_build_keeps_witnesses_without_result_log(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            fake.write("holbuild", f"#!{sys.executable}\n"
                       f"print('{driver.CORPUS_THEORY} restored from cache')\n")
            holbuild = fake.root / "holbuild"
            holbuild.chmod(0o755)
            status, report = fake.run(holbuild)
            self.assertEqual(status, 0)
            self.assertEqual(len(report["kernel_checked"]), 3)
            self.assertTrue(all(w["status"] == "proved (cached)"
                                for w in report["kernel_checked"]))

    def test_build_failure_without_results_fails(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            status, report = fake.run(fake.holbuild([], 1))
            self.assertEqual(status, 1)
            self.assertEqual([f["kind"] for f in report["failures"]], ["hol-build"])


if __name__ == "__main__":
    unittest.main()
