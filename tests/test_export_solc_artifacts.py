#!/usr/bin/env python3

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
EXPORTER = ROOT / "tools" / "export_solc_artifacts.py"
SOURCE = ROOT / "testdata" / "frontend" / "types.sol"


class ExporterTests(unittest.TestCase):
    def fake_solc(self, directory: Path, version: str, output: dict) -> Path:
        path = directory / "solc"
        path.write_text(
            textwrap.dedent(
                f"""\
                #!{sys.executable}
                import json
                import sys
                if "--version" in sys.argv:
                    print({version!r})
                else:
                    json.load(sys.stdin)
                    json.dump({output!r}, sys.stdout)
                """
            ),
            encoding="utf-8",
        )
        path.chmod(0o755)
        return path

    def run_exporter(self, solc: Path, output: Path) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [
                sys.executable,
                str(EXPORTER),
                "--solc",
                str(solc),
                "--output",
                str(output),
                str(SOURCE),
            ],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )

    def test_rejects_wrong_compiler_commit(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            solc = self.fake_solc(
                directory,
                "Version: 0.8.37+commit.00000000.Linux.g++",
                {},
            )
            result = self.run_exporter(solc, directory / "artifact.json")
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("compiler commit mismatch", result.stderr)

    def test_rejects_compiler_errors(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            solc = self.fake_solc(
                directory,
                "Version: 0.8.37+commit.f401782d.Linux.g++",
                {
                    "errors": [
                        {
                            "severity": "error",
                            "formattedMessage": "synthetic compiler error",
                        }
                    ]
                },
            )
            result = self.run_exporter(solc, directory / "artifact.json")
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("synthetic compiler error", result.stderr)

    def test_output_is_deterministic(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            solc = self.fake_solc(
                directory,
                "Version: 0.8.37+commit.f401782d.Linux.g++",
                {"contracts": {}, "sources": {}},
            )
            first = directory / "first.json"
            second = directory / "second.json"
            self.assertEqual(self.run_exporter(solc, first).returncode, 0)
            self.assertEqual(self.run_exporter(solc, second).returncode, 0)
            self.assertEqual(first.read_bytes(), second.read_bytes())


if __name__ == "__main__":
    unittest.main()
