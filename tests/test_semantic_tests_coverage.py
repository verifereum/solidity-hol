#!/usr/bin/env python3

from pathlib import Path
import json
import sys
import tempfile
import textwrap
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import semantic_tests_coverage as coverage  # noqa: E402

PROFILE = {"settings": {"evmVersion": "osaka", "debug": {"revertStrings": "default"}}}


def variable(node_id: int, *, state: bool = False, type_identifier: str = "t_uint256",
             visibility: str = "private") -> dict:
    return {
        "nodeType": "VariableDeclaration", "id": node_id, "stateVariable": state,
        "constant": False, "mutability": "mutable", "storageLocation": "default",
        "visibility": visibility,
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


class BuiltinCoverageTests(unittest.TestCase):
    def test_literal_messages_are_admitted_only_in_builtin_calls(self) -> None:
        artifact = json.loads((ROOT / "testdata/differential/expected/builtins.json").read_text())
        ast = artifact["output"]["sources"]["testdata/differential/builtins.sol"]["ast"]
        self.assertEqual(coverage.scan({"builtins.sol": ast}), {})
        literal = next(n for n in coverage.nodes(ast)
                       if n["nodeType"] == "Literal" and n["kind"] == "string")
        self.assertEqual(coverage.elaboration_blockers(literal), [
            coverage.Blocker("Literal", "bytes and string", "elaboration")])

    def test_shadowed_names_are_ordinary_calls(self) -> None:
        artifact = json.loads((ROOT / "testdata/differential/expected/shadowed_builtins.json").read_text())
        ast = artifact["output"]["sources"]["testdata/differential/shadowed_builtins.sol"]["ast"]
        self.assertEqual(coverage.scan({"shadowed_builtins.sol": ast}), {})
        for node in coverage.nodes(ast):
            if node["nodeType"] == "FunctionCall":
                self.assertGreaterEqual(node["expression"]["referencedDeclaration"], 0)


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
        self.assertEqual(test.sources["b.sol"], 'import "a.sol";\n')
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
        ast = unit([variable(3, state=True, visibility="public"), function(4, [ASSEMBLY])])
        result = coverage.classify(
            "t.sol", coverage.scan({"t.sol": ast}),
            {"status": "import-rejected",
             "message": "VariableDeclaration 3: public state variables are not supported"})
        self.assertEqual(result.category, coverage.IMPORT_REJECTED)
        self.assertEqual(result.first, coverage.Blocker(
            "VariableDeclaration", "public state variables", "import"))
        self.assertEqual({b.feature for b in result.blockers},
                         {"public state variables", "inline assembly"})
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

    def test_scan_records_every_property_of_a_variable(self) -> None:
        constant = dict(variable(3, state=True), constant=True, mutability="constant",
                        value={"nodeType": "Literal", "id": 4, "kind": "number",
                               "typeDescriptions": {"typeIdentifier": "t_rational_1_by_1"}})
        self.assertEqual({b.feature for b in coverage.scan({"t.sol": unit([constant])})[3]},
                         {"constants", "declaration values"})

    def test_scan_finds_literals_of_non_integer_types(self) -> None:
        def literal(node_id, type_identifier):
            return {"nodeType": "Literal", "id": node_id, "kind": "number", "value": "1",
                    "typeDescriptions": {"typeIdentifier": type_identifier}}

        address = literal(5, "t_address")
        declaration = {
            "nodeType": "VariableDeclarationStatement", "id": 6,
            "declarations": [variable(7, type_identifier="t_bytes4")],
            "initialValue": literal(8, "t_rational_305419896_by_1"),
        }
        boolean = {"nodeType": "Literal", "id": 9, "kind": "bool", "value": "false",
                   "typeDescriptions": {"typeIdentifier": "t_bool"}}
        found = coverage.scan({"t.sol": unit([function(4, [address, declaration, boolean])])})
        self.assertEqual(found[5], [coverage.Blocker(
            "Literal", "literals of non-integer types", "elaboration")])
        self.assertEqual(found[6], [coverage.Blocker(
            "VariableDeclarationStatement", "literals of non-integer types", "elaboration")])
        self.assertNotIn(8, found)
        self.assertNotIn(9, found)

    def test_tuples_are_classified_by_a_component(self) -> None:
        self.assertTrue(coverage.decodes("t_tuple$_t_bool_$_t_bytes4_$"))
        self.assertFalse(coverage.decodes("t_tuple$_t_bool_$_t_bytes_memory_ptr_$"))
        self.assertEqual(coverage.type_feature("t_tuple$_t_bool_$_t_bytes_memory_ptr_$"),
                         "bytes and string")
        self.assertEqual(coverage.type_feature("t_bytes32"),
                         "fixed-size bytes members and indexing")

    def test_storage_and_nonpayable_functions_are_admitted(self) -> None:
        f = dict(function(4, []), stateMutability="nonpayable")
        ast = unit([variable(3, state=True), f])
        self.assertEqual(coverage.scan({"t.sol": ast}), {})
        f["stateMutability"] = "view"
        self.assertEqual(coverage.scan({"t.sol": ast}), {})
        f["stateMutability"] = "payable"
        self.assertEqual(coverage.scan({"t.sol": ast})[4], [
            coverage.Blocker("FunctionDefinition", "payable functions", "elaboration")])

    def test_nested_mappings_are_storage_types(self) -> None:
        tid = "t_mapping$_t_int8_$_t_mapping$_t_address_$_t_bytes4_$_$"
        self.assertTrue(coverage.storage_type_supported(tid))
        self.assertTrue(coverage.storage_type_supported("t_mapping$_t_uint160_$_t_bytes32_$"))
        self.assertTrue(coverage.storage_type_supported("t_mapping$_t_int80_$_t_bytes16_$"))
        self.assertTrue(coverage.storage_type_supported("t_mapping$_t_address_payable_$_t_bool_$"))
        self.assertFalse(coverage.storage_type_supported("t_mapping$_t_bytes_memory_ptr_$_t_uint8_$"))
        self.assertFalse(coverage.storage_type_supported("t_mapping$_t_uint8_$_t_uint8_$junk"))
        self.assertFalse(coverage.storage_type_supported("t_mapping$_t_mapping$_t_uint8_$_t_uint8_$_$_t_uint8_$"))
        v = variable(3, state=True, type_identifier=tid)
        self.assertEqual(coverage.elaboration_blockers(v), [])
        v["stateVariable"] = False
        v["storageLocation"] = "storage"
        self.assertIn("local reference bindings", {b.feature for b in coverage.elaboration_blockers(v)})

    def test_mapping_and_fixed_storage_array_indexing_are_admitted(self) -> None:
        base = {"nodeType": "Identifier", "id": 5, "name": "m", "referencedDeclaration": 3,
                "typeDescriptions": {"typeIdentifier": "t_mapping$_t_uint256_$_t_uint8_$"}}
        index = {"nodeType": "IndexAccess", "id": 6, "baseExpression": base,
                 "indexExpression": {"nodeType": "Literal", "id": 7, "kind": "number", "value": "1",
                                     "typeDescriptions": {"typeIdentifier": "t_rational_1_by_1"}},
                 "typeDescriptions": {"typeIdentifier": "t_uint8"}}
        self.assertEqual(coverage.scan({"t.sol": unit([function(4, [index])])}), {})
        base["typeDescriptions"]["typeIdentifier"] = "t_array$_t_uint8_$2_storage"
        self.assertEqual(coverage.node_blockers(index), [])
        self.assertEqual(coverage.scan({"t.sol": unit([function(4, [index])])}), {})
        base["typeDescriptions"]["typeIdentifier"] = "t_array$_t_uint8_$dyn_storage"
        self.assertEqual(coverage.elaboration_blockers(index), [
            coverage.Blocker("IndexAccess", "arrays", "elaboration")])

    def test_nested_array_types_and_fixed_length_prefix(self) -> None:
        tid = "t_array$_t_array$_t_uint24_$11_storage_$2_storage"
        self.assertTrue(coverage.storage_type_supported(tid))
        self.assertFalse(coverage.storage_type_supported(tid + "_ptr"))
        self.assertFalse(coverage.storage_type_supported("t_array$_t_uint8_$2_memory_ptr"))
        self.assertFalse(coverage.storage_type_supported("t_array$_t_mapping$_t_uint8_$_t_uint8_$_$2_storage"))
        root = {"nodeType": "Identifier", "id": 5, "name": "rows", "referencedDeclaration": 3,
                "typeDescriptions": {"typeIdentifier": tid}}
        length = {"nodeType": "MemberAccess", "id": 6, "memberName": "length", "expression": root,
                  "typeDescriptions": {"typeIdentifier": "t_uint256"}}
        self.assertEqual(coverage.scan({"t.sol": unit([function(4, [length])])}), {})

    def test_compilation_retains_storage_layout_for_import(self) -> None:
        metadata = {"storageLayout": {"storage": [{"astId": 3, "slot": "0"}]},
                    "evm": {"deployedBytecode": {"object": "00"}}}
        output = {"sources": {"t.sol": {"ast": unit([])}},
                  "contracts": {"t.sol": {"C": metadata}}}
        with patch.object(coverage.exporter, "build_artifact_from_sources",
                          return_value={"output": output}):
            result = coverage.compile_test(Path("solc"), coverage.SemanticTest("t.sol", {}, {}),
                                           Path("profile"))
        self.assertEqual(result, {"t.sol": {"ast": unit([]), "contracts": {
            "C": {"storageLayout": metadata["storageLayout"]}}}})

    def test_ranking_counts_only_blockers(self) -> None:
        def rejected(name: str, members: list) -> coverage.Classification:
            return coverage.classify(
                name, coverage.scan({name: unit(members)}),
                {"status": "import-rejected",
                 "message": "VariableDeclaration 3: public state variables are not supported"})

        report = coverage.Report("pin", "profile", [
            rejected("a.sol", [variable(3, state=True, visibility="public"), function(4, [])]),
            rejected("b.sol", [variable(3, state=True, visibility="public"), function(4, [ASSEMBLY])]),
        ])
        ranking = {f["feature"]: f for f in report.feature_ranking()}
        self.assertEqual(ranking["public state variables"]["tests"], 2)
        self.assertEqual(ranking["public state variables"]["only_blocker"], 1)
        self.assertEqual(ranking["public state variables"]["first_rejection"], 2)
        self.assertEqual(ranking["inline assembly"]["only_blocker"], 0)
        self.assertEqual(report.greedy_order(5), [("public state variables", 1), ("inline assembly", 2)])


if __name__ == "__main__":
    unittest.main()
