#!/usr/bin/env python3

from pathlib import Path
import sys
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import semantic_tests_coverage as coverage  # noqa: E402

PROFILE = {"settings": {"evmVersion": "osaka", "debug": {"revertStrings": "default"}}}


def variable(node_id, *, state=False, type_identifier="t_uint256"):
    return {
        "nodeType": "VariableDeclaration", "id": node_id, "stateVariable": state,
        "constant": False, "mutability": "mutable", "storageLocation": "default",
        "typeDescriptions": {"typeIdentifier": type_identifier},
        "typeName": {"nodeType": "ElementaryTypeName", "id": node_id + 100, "name": "uint256"},
    }


def function(node_id, statements):
    return {
        "nodeType": "FunctionDefinition", "id": node_id, "kind": "function",
        "implemented": True, "virtual": False, "stateMutability": "pure", "modifiers": [],
        "parameters": {"nodeType": "ParameterList", "id": node_id + 100, "parameters": []},
        "body": {"nodeType": "Block", "id": node_id + 200, "statements": statements},
    }


def unit(members):
    return {"nodeType": "SourceUnit", "id": 1, "nodes": [{
        "nodeType": "ContractDefinition", "id": 2, "contractKind": "contract",
        "abstract": False, "baseContracts": [], "linearizedBaseContracts": [2],
        "nodes": members,
    }]}


ASSEMBLY = {"nodeType": "InlineAssembly", "id": 20,
            "AST": {"nodeType": "YulBlock", "statements": []}}


class ReadTestTests(unittest.TestCase):
    def read(self, text: str) -> coverage.SemanticTest:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / "dir" / "t.sol"
            path.parent.mkdir()
            path.write_text(textwrap.dedent(text), encoding="utf-8")
            return coverage.read_test(root, path)

    def test_splits_sources_and_reads_settings(self) -> None:
        test = self.read("""\
            ==== Source: a.sol ====
            contract A {}
            ==== Source: b.sol ====
            import "a.sol";
            // ====
            // EVMVersion: >=cancun
            // compileViaYul: true
            // ----
            // f() -> 1
            """)
        self.assertEqual(test.name, "dir/t.sol")
        self.assertEqual(list(test.sources), ["a.sol", "b.sol"])
        self.assertEqual(test.sources["a.sol"], "contract A {}\n")
        self.assertEqual(test.settings, {"EVMVersion": ">=cancun", "compileViaYul": "true"})
        self.assertIsNone(coverage.skip_reason(test, PROFILE))

    def test_skips_by_own_settings(self) -> None:
        def reason(settings: str) -> str | None:
            return coverage.skip_reason(
                self.read(f"contract C {{}}\n// ====\n{settings}// ----\n"), PROFILE)

        self.assertIn("legacy", reason("// compileViaYul: false\n"))
        self.assertIn("EVMVersion: <osaka", reason("// EVMVersion: <osaka\n"))
        self.assertIsNone(reason("// EVMVersion: >=osaka\n"))
        self.assertIn("revertStrings: debug", reason("// revertStrings: debug\n"))


class ClassifyTests(unittest.TestCase):
    def test_import_rejection_records_first_and_all_blockers(self) -> None:
        ast = unit([variable(3, state=True), function(4, [ASSEMBLY])])
        result = coverage.classify(
            "t.sol", coverage.scan({"t.sol": ast}),
            {"status": "import-rejected",
             "message": "VariableDeclaration 3: state variables are not supported"})
        self.assertEqual(result.category, coverage.IMPORT_REJECTED)
        self.assertEqual(result.first, coverage.Blocker(
            "VariableDeclaration", "state variables", "import"))
        self.assertEqual({b.feature for b in result.blockers},
                         {"state variables", "inline assembly"})
        self.assertTrue(result.scan_agrees)

    def test_scan_must_explain_the_importer(self) -> None:
        ast = unit([function(4, [])])
        result = coverage.classify(
            "t.sol", coverage.scan({"t.sol": ast}),
            {"status": "import-rejected", "message": "Block 204: unsupported statement X"})
        self.assertEqual(result.first.feature, "unclassified")
        self.assertFalse(result.scan_agrees)

    def test_elaboration_rejection_and_admission(self) -> None:
        strings = unit([function(4, [{
            "nodeType": "VariableDeclarationStatement", "id": 5,
            "declarations": [variable(6, type_identifier="t_string_memory_ptr")],
        }])])
        rejected = coverage.classify(
            "s.sol", coverage.scan({"s.sol": strings}),
            {"status": "elaboration-rejected", "message": "elaborate_unit returned NONE"})
        self.assertEqual([b.feature for b in rejected.blockers], ["bytes and string"])
        self.assertTrue(rejected.scan_agrees)
        admitted = coverage.classify(
            "a.sol", coverage.scan({"a.sol": unit([function(4, [])])}), {"status": "admitted"})
        self.assertEqual(admitted.blockers, [])
        self.assertTrue(admitted.scan_agrees)

    def test_ranking_counts_only_blockers(self) -> None:
        def rejected(name: str, members: list) -> coverage.Classification:
            return coverage.classify(
                name, coverage.scan({name: unit(members)}),
                {"status": "import-rejected",
                 "message": "VariableDeclaration 3: state variables are not supported"})

        report = coverage.Report("pin", "profile", [
            rejected("a.sol", [variable(3, state=True), function(4, [])]),
            rejected("b.sol", [variable(3, state=True), function(4, [ASSEMBLY])]),
        ])
        ranking = {f["feature"]: f for f in report.feature_ranking()}
        self.assertEqual(ranking["state variables"]["tests"], 2)
        self.assertEqual(ranking["state variables"]["only_blocker"], 1)
        self.assertEqual(ranking["state variables"]["first_rejection"], 2)
        self.assertEqual(ranking["inline assembly"]["only_blocker"], 0)
        self.assertEqual(report.greedy_order(5), [("state variables", 1), ("inline assembly", 2)])


if __name__ == "__main__":
    unittest.main()
