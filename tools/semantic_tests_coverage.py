#!/usr/bin/env python3
"""Report how much of solc's semantic test corpus the semantics admits.

Every test under test/libsolidity/semanticTests of a solidity checkout at
SOLIDITY_PIN is compiled with the pinned compiler and profile, then imported
(syntax/solidityImportLib.sml) and elaborated (elaborate_unit) in HOL by
tools/semantic_tests_coverage.sml. Each test is classified as skipped by its
own settings, a compile failure, an importer rejection, an elaborator
rejection, or admitted. The tests' call expectations are not run.

The importer stops at its first rejection. To rank features by how many tests
they block, and by how many they alone block, this tool also scans each AST
for every construct outside the importer's vocabulary. The scan restates the
importer's checks; the report counts every test where the scan disagrees with
the importer, so drift between the two shows up rather than skewing the
ranking.
"""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Any, Iterator

import export_solc_artifacts as exporter

ROOT = Path(__file__).resolve().parents[1]
TESTS_DIR = Path("test/libsolidity/semanticTests")
HOL_SCRIPT = ROOT / "tools" / "semantic_tests_coverage.sml"
REPORT_FORMAT = "solidity-hol-semantic-tests-coverage-v1"
RESULT_PREFIX = "coverage-result: "

SOURCE_MARKER = re.compile(r"^==== (Source|ExternalSource): (.*) ====\s*$")
SETTING = re.compile(r"^//\s*([A-Za-z][A-Za-z0-9]*)\s*:\s*(.*?)\s*$")
EVM_VERSIONS = [
    "homestead", "tangerineWhistle", "spuriousDragon", "byzantium", "constantinople",
    "petersburg", "istanbul", "berlin", "london", "paris", "shanghai", "cancun",
    "prague", "osaka", "amsterdam", "@future",
]
IMPORT_ERROR_NODE = re.compile(r"^([A-Za-z]+) ([0-9]+): (.*)$", re.S)

SKIPPED = "skipped"
COMPILE_FAILURE = "compile-failure"
IMPORT_REJECTED = "import-rejected"
ELABORATION_REJECTED = "elaboration-rejected"
ADMITTED = "admitted"
GREEDY_STEPS = 20
CATEGORIES = [ADMITTED, ELABORATION_REJECTED, IMPORT_REJECTED, COMPILE_FAILURE, SKIPPED]


class TestFormatError(Exception):
    pass


# Test files


@dataclass
class SemanticTest:
    """A test file: its sources, by Standard JSON name, and its settings."""

    name: str
    sources: dict[str, str]
    settings: dict[str, str]


def read_test(tests_root: Path, path: Path) -> SemanticTest:
    """Parse a test as solc's TestCaseReader does: `==== Source: name ====` and
    `==== ExternalSource: [name=]path ====` markers split the sources, and the
    `// key: value` lines between `// ====` and `// ----` are its settings."""
    name = path.relative_to(tests_root).as_posix()
    sources: dict[str, list[str]] = {}
    current = name
    settings: dict[str, str] = {}
    in_settings = False
    for line in path.read_text(encoding="utf-8").splitlines(keepends=True):
        stripped = line.rstrip("\r\n")
        marker = SOURCE_MARKER.match(stripped)
        if marker is not None:
            kind, spec = marker.groups()
            if kind == "Source":
                current = spec
                sources[current] = []
            else:
                source_name, _, external = (part.strip() for part in spec.partition("="))
                external = external or source_name
                external_path = Path(os.path.normpath(path.parent / external))
                sources[source_name] = [external_path.read_text(encoding="utf-8")]
            continue
        if stripped.startswith("// ----"):
            break
        if stripped.startswith("// ===="):
            in_settings = True
        elif in_settings:
            setting = SETTING.match(stripped)
            if setting is None:
                raise TestFormatError(f"{name}: malformed setting {stripped!r}")
            settings[setting.group(1)] = setting.group(2)
        else:
            sources.setdefault(current, []).append(line)
    return SemanticTest(name, {k: "".join(v) for k, v in sources.items()}, settings)


def find_tests(tests_root: Path) -> list[Path]:
    """Test files, without the directories starting with `_` that hold
    external sources, which isoltest does not run either."""
    return sorted(
        path for path in tests_root.rglob("*.sol")
        if not any(part.startswith("_") for part in path.relative_to(tests_root).parts)
    )


def evm_version_admits(requirement: str, version: str) -> bool:
    """Whether `version` meets an `EVMVersion` setting such as `>=cancun`."""
    if requirement == "any":
        return True
    match = re.fullmatch(r"([<>=!]*)(.*)", requirement)
    assert match is not None
    comparator, required = match.groups()
    if required not in EVM_VERSIONS:
        raise TestFormatError(f"unknown EVM version {required!r}")
    a, b = EVM_VERSIONS.index(version), EVM_VERSIONS.index(required)
    comparisons = {">": a > b, ">=": a >= b, "<": a < b, "<=": a <= b, "=": a == b, "!": a != b}
    if comparator not in comparisons:
        raise TestFormatError(f"unknown EVM version comparator {comparator!r}")
    return comparisons[comparator]


def skip_reason(test: SemanticTest, profile: dict[str, Any]) -> str | None:
    """Why the test's own settings exclude it from the via-IR profile, if
    they do."""
    settings = test.settings
    if settings.get("compileViaYul", "also") == "false":
        return "legacy pipeline only (compileViaYul: false)"
    evm = settings.get("EVMVersion", "any")
    if not evm_version_admits(evm, profile["settings"]["evmVersion"]):
        return f"EVM version (EVMVersion: {evm})"
    revert_strings = settings.get("revertStrings", "default")
    if revert_strings != profile["settings"]["debug"]["revertStrings"]:
        return f"revert strings (revertStrings: {revert_strings})"
    return None


# Compilation


def compile_test(solc: Path, test: SemanticTest, profile_path: Path) -> dict[str, Any]:
    """ASTs and storage layouts by source; compiler diagnostics raise SystemExit."""
    output = exporter.build_artifact_from_sources(solc, test.sources, profile_path)["output"]
    return {
        name: {
            "ast": source["ast"],
            "contracts": {
                contract: {"storageLayout": metadata["storageLayout"]}
                for contract, metadata in output.get("contracts", {}).get(name, {}).items()
            },
        }
        for name, source in output["sources"].items()
    }


# The scan


@dataclass(frozen=True)
class Blocker:
    """A construct the semantics does not support: the AST node's type, the
    feature it belongs to, and the stage that rejects it, the importer
    ("import") or the elaborator ("elaboration")."""

    node_type: str
    feature: str
    stage: str


EXPRESSIONS = {
    "Identifier", "Literal", "UnaryOperation", "BinaryOperation", "Assignment",
    "TupleExpression", "FunctionCall", "IndexAccess",
}
STATEMENTS = {
    "Block", "UncheckedBlock", "ExpressionStatement", "VariableDeclarationStatement",
    "IfStatement", "WhileStatement", "DoWhileStatement", "ForStatement", "Break",
    "Continue", "Return",
}
# Nodes the importer reads only in a fixed position, checked there, and nodes
# it never reaches because it rejects their parents (IdentifierPath) or never
# reads the field holding them (StructuredDocumentation).
STRUCTURAL = {
    "SourceUnit", "PragmaDirective", "ContractDefinition", "FunctionDefinition",
    "ParameterList", "VariableDeclaration", "ElementaryTypeName",
    "ElementaryTypeNameExpression", "IdentifierPath", "StructuredDocumentation", "Mapping",
}
FEATURES = {
    "ArrayTypeName": "arrays",
    "Conditional": "conditional expressions",
    "EmitStatement": "events",
    "EnumDefinition": "enums",
    "EnumValue": "enums",
    "ErrorDefinition": "custom errors",
    "EventDefinition": "events",
    "FunctionCallOptions": "call options ({value: …, gas: …})",
    "FunctionTypeName": "function types",
    "ImportDirective": "imports",
    "IndexRangeAccess": "array slices",
    "InheritanceSpecifier": "inheritance",
    "InlineAssembly": "inline assembly",
    "ModifierDefinition": "modifiers",
    "ModifierInvocation": "modifiers",
    "OverrideSpecifier": "overrides",
    "PlaceholderStatement": "modifiers",
    "RevertStatement": "custom errors",
    "StructDefinition": "structs",
    "TryCatchClause": "try/catch",
    "TryStatement": "try/catch",
    "UserDefinedValueTypeDefinition": "user-defined value types",
    "UsingForDirective": "using for",
}
FUNCTION_KINDS = {
    "constructor": "constructors", "fallback": "fallback functions",
    "receive": "receive functions", "freeFunction": "free functions",
}
# By the leading part of a type identifier.
TYPE_FEATURES = [
    ("t_magic_message", "msg/block/tx globals"),
    ("t_magic_block", "msg/block/tx globals"),
    ("t_magic_transaction", "msg/block/tx globals"),
    ("t_magic_abi", "abi.* functions"),
    ("t_magic_meta_type", "type(…)"),
    ("t_type$_t_enum", "enums"),
    ("t_type$_t_struct", "structs"),
    ("t_type$_t_userDefinedValueType", "user-defined value types"),
    ("t_type$_t_contract", "library calls and contract-name members"),
    ("t_type$_t_super", "inheritance"),
    ("t_type$_t_bytes_", "bytes and string"),
    ("t_type$_t_string", "bytes and string"),
    ("t_type$_t_array", "arrays"),
    ("t_type", "members of elementary type names"),
    ("t_struct", "structs"),
    ("t_enum", "enums"),
    ("t_userDefinedValueType", "user-defined value types"),
    ("t_mapping", "mappings"),
    ("t_array", "arrays"),
    ("t_bytes_", "bytes and string"),
    ("t_bytes", "fixed-size bytes members and indexing"),
    ("t_string", "bytes and string"),
    ("t_contract", "external calls and contract members"),
    ("t_super", "inheritance"),
    ("t_address", "address members (balance, call, transfer, …)"),
    ("t_function_event", "events"),
    ("t_function_error", "custom errors"),
    ("t_error", "custom errors"),
    ("t_function", "function members (selector, address, …)"),
    ("t_module", "imports"),
    ("t_uint", "using for"),
    ("t_int", "using for"),
    ("t_bool", "using for"),
    ("t_rational", "using for"),
]
BUILTINS = {
    "msg": "msg/block/tx globals", "block": "msg/block/tx globals",
    "tx": "msg/block/tx globals", "abi": "abi.* functions", "type": "type(…)",
    "require": "require/assert/revert", "assert": "require/assert/revert",
    "revert": "require/assert/revert", "this": "this", "super": "inheritance",
    "keccak256": "hash and signature built-ins", "sha256": "hash and signature built-ins",
    "ripemd160": "hash and signature built-ins", "ecrecover": "hash and signature built-ins",
}


def type_feature(type_identifier: str | None) -> str:
    """The feature a type needs, classifying a tuple by its first component
    outside the elementary types."""
    if (type_identifier or "").startswith("t_tuple$_"):
        if "$__$" in type_identifier:
            return "tuples with empty components"
        for component in type_identifier[len("t_tuple$_"):].split("_$_"):
            component = component.removesuffix("_$")
            if component.startswith("t_tuple"):
                return "nested tuples"
            if not (VALUE_TYPE.fullmatch(component) or RATIONAL.fullmatch(component)):
                return type_feature(component)
    for prefix, feature in TYPE_FEATURES:
        if (type_identifier or "").startswith(prefix):
            return feature
    return f"values of type {type_identifier}"


def nodes(value: Any) -> Iterator[dict[str, Any]]:
    """Every Solidity AST node under `value`, in document order. The Yul nodes
    of inline assembly, which have no id, are left out, and so are storage
    layout specifiers, which the importer does not read."""
    if isinstance(value, dict):
        if value.get("nodeType") == "StorageLayoutSpecifier":
            return
        if "nodeType" in value and "id" in value:
            yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


def node_blockers(node: dict[str, Any]) -> list[Blocker]:
    """What the importer rejects at this node itself; children are checked as
    nodes of their own. Member and index accesses are classified by the type
    of the value accessed."""
    kind = node["nodeType"]
    found: list[str] = []
    if kind in FEATURES:
        found.append(FEATURES[kind])
    elif kind == "MemberAccess":
        found.append(type_feature(node["expression"]["typeDescriptions"].get("typeIdentifier")))
    elif kind == "NewExpression":
        created = node["typeName"]
        found.append("contract creation (new C)" if created["nodeType"] == "UserDefinedTypeName"
                     else "memory arrays (new T[](n))" if created["nodeType"] == "ArrayTypeName"
                     else type_feature(created["typeDescriptions"].get("typeIdentifier")))
    elif kind == "UserDefinedTypeName":
        found.append(type_feature(node["typeDescriptions"].get("typeIdentifier")))
    elif kind == "Literal":
        if "value" not in node:
            # solc omits the value of a hex string that is not valid UTF-8.
            found.append("bytes and string")
        if node.get("subdenomination") is not None:
            found.append("literal subdenominations (ether, days, …)")
    elif kind == "Identifier":
        if node.get("referencedDeclaration", 0) < 0:
            found.append(BUILTINS.get(node["name"], f"built-in {node['name']}"))
    elif kind == "TupleExpression":
        if node["isInlineArray"]:
            found.append("inline arrays")
    elif kind == "FunctionCall":
        if node["names"]:
            found.append("named arguments")
        if node["tryCall"]:
            found.append("try/catch")
        if node["kind"] == "structConstructorCall":
            found.append("structs")
    elif kind == "VariableDeclaration":
        if node["stateVariable"] and node.get("visibility") == "public":
            found.append("public state variables")
        if node["constant"]:
            found.append("constants")
        if node["mutability"] == "immutable":
            found.append("immutables")
        if node.get("value") is not None:
            found.append("declaration values")
    elif kind == "FunctionDefinition":
        if node["kind"] != "function":
            found.append(FUNCTION_KINDS.get(node["kind"], f"{node['kind']} functions"))
        if not node["implemented"]:
            found.append("unimplemented functions")
        if node["modifiers"]:
            found.append("modifiers")
        if node["virtual"]:
            found.append("virtual functions")
        if node.get("overrides") is not None:
            found.append("overrides")
    elif kind == "ContractDefinition":
        if node["contractKind"] != "contract":
            found.append({"library": "libraries", "interface": "interfaces"}[node["contractKind"]])
        if node["abstract"]:
            found.append("abstract contracts")
        if node["baseContracts"] or node["linearizedBaseContracts"] != [node["id"]]:
            found.append("inheritance")
    elif kind not in EXPRESSIONS | STATEMENTS | STRUCTURAL:
        found.append(f"{kind} nodes")
    return [Blocker(kind, feature, "import") for feature in found]


VALUE_TYPE = re.compile(
    r"t_(bool|address_payable|address|u?int(8|16|24|32|40|48|56|64|72|80|88|96|104|112|120"
    r"|128|136|144|152|160|168|176|184|192|200|208|216|224|232|240|248|256)"
    r"|bytes([1-9]|[12][0-9]|3[0-2]))"
)
RATIONAL = re.compile(r"t_rational_(minus_)?[0-9]+_by_[0-9]+")


def decodes(type_identifier: str) -> bool:
    """Whether decode_type_identifier admits a type identifier: an elementary
    value type, a rational literal type, or a tuple of elementary types."""
    if VALUE_TYPE.fullmatch(type_identifier) or RATIONAL.fullmatch(type_identifier):
        return True
    if type_identifier == "t_tuple$__$":
        return True
    if not type_identifier.startswith("t_tuple$"):
        return False
    *components, last = type_identifier[len("t_tuple$"):].split("$")
    return last == "" and all(
        len(c) >= 2 and c[0] == c[-1] == "_" and VALUE_TYPE.fullmatch(c[1:-1]) is not None
        for c in components
    )


def storage_type_supported(type_identifier: str) -> bool:
    """Elementary scalar storage, or scalar-key mappings ending in a scalar."""
    def parse_at(start: int) -> int | None:
        prefix = "t_mapping$_"
        if not type_identifier.startswith(prefix, start):
            scalar = VALUE_TYPE.match(type_identifier, start)
            return scalar.end() if scalar is not None else None
        key = VALUE_TYPE.match(type_identifier, start + len(prefix))
        if key is None or not type_identifier.startswith("_$_", key.end()):
            return None
        value_end = parse_at(key.end() + 3)
        if value_end is None or not type_identifier.startswith("_$", value_end):
            return None
        return value_end + 2

    return parse_at(0) == len(type_identifier)


UNARY_OPERATORS = {"++", "--", "-", "!", "~"}


def elaboration_blockers(node: dict[str, Any]) -> list[Blocker]:
    """What valid_src_unit or elaborate_unit rejects at a node the importer
    admits: unsupported storage/reference types and indexing, conversions
    outside the elementary types, string literals, payable functions, `delete`,
    and units that are not one
    contract with functions. Other expressions get their types from these, or
    are rejected by the importer."""
    kind = node["nodeType"]
    found: list[str] = []
    if (kind == "VariableDeclaration"
            or (kind == "FunctionCall" and node["kind"] == "typeConversion")
            or (kind == "Literal" and node["kind"] not in ("number", "bool"))):
        type_identifier = node["typeDescriptions"].get("typeIdentifier") or ""
        admitted_storage = (kind == "VariableDeclaration" and node["stateVariable"]
                            and storage_type_supported(type_identifier))
        if not decodes(type_identifier) and not admitted_storage:
            found.append(type_feature(type_identifier))
        if (kind == "VariableDeclaration"
                and node["storageLocation"] not in ("default", "memory")):
            found.append("transient storage" if node["storageLocation"] == "transient"
                         else "local reference bindings")
    elif (kind == "TupleExpression" and not node["isInlineArray"]
          and not decodes(node["typeDescriptions"]["typeIdentifier"])):
        type_identifier = node["typeDescriptions"]["typeIdentifier"]
        found.append("tuples of literals" if "t_rational" in type_identifier
                     else type_feature(type_identifier))
    elif kind == "UnaryOperation" and node["operator"] not in UNARY_OPERATORS:
        found.append(f"operator {node['operator']}")
    elif ((kind == "UnaryOperation" and RATIONAL.fullmatch(node["typeDescriptions"]["typeIdentifier"]))
          or (kind == "BinaryOperation"
              and RATIONAL.fullmatch(node["commonType"]["typeIdentifier"]))):
        found.append("constant expressions over literals")
    elif kind == "Literal" and node["kind"] == "number" and not RATIONAL.fullmatch(
            node["typeDescriptions"].get("typeIdentifier") or ""):
        found.append("literals of non-integer types")
    elif kind == "FunctionDefinition" and node["stateMutability"] == "payable":
        found.append("payable functions")
    elif kind == "IndexAccess":
        base_type = node["baseExpression"]["typeDescriptions"].get("typeIdentifier") or ""
        if not base_type.startswith("t_mapping$_") or not storage_type_supported(base_type):
            found.append(type_feature(base_type))
    elif kind == "SourceUnit":
        contracts = [m for m in node["nodes"] if m["nodeType"] == "ContractDefinition"]
        if len(contracts) != 1:
            found.append("source units without exactly one contract")
    elif kind == "ContractDefinition":
        if not any(m["nodeType"] == "FunctionDefinition" for m in node["nodes"]):
            found.append("contracts without functions")
    return [Blocker(kind, feature, "elaboration") for feature in found]


def callee_blockers(node: dict[str, Any], callees: set[int],
                    conversions: set[int]) -> list[Blocker]:
    """Type names and function names, which the semantics admits only as the
    callee of a conversion or a call; and the callees of conversions to
    non-elementary types, where the importer rejects those."""
    if node["id"] in conversions and node["nodeType"] != "ElementaryTypeNameExpression":
        return [Blocker(node["nodeType"], "conversions to non-elementary types", "import")]
    if node["id"] in callees:
        return []
    if node["nodeType"] == "ElementaryTypeNameExpression":
        return [Blocker(node["nodeType"], "type names as values", "import")]
    if (node["nodeType"] == "Identifier"
            and node["typeDescriptions"].get("typeIdentifier", "").startswith("t_function_internal")):
        return [Blocker(node["nodeType"], "functions as values", "elaboration")]
    return []


INTEGER_TYPE = re.compile(r"t_u?int[0-9]+")


def coerced_literals(node: dict[str, Any], by_id: dict[int, dict[str, Any]]) -> list[Blocker]:
    """Integer literals used where a value of another type is expected, which
    elaborate_unit converts only to integer types: initial values, returned
    values, assigned values, operands and arguments."""
    kind = node["nodeType"]
    expected: list[tuple[dict[str, Any] | None, dict[str, Any]]] = []
    if kind == "VariableDeclarationStatement" and len(node["declarations"]) == 1:
        expected.append((node.get("initialValue"), node["declarations"][0]))
    elif kind == "Return" and node.get("expression") is not None:
        returns = by_id.get(node.get("functionReturnParameters"), {}).get("parameters", [])
        if len(returns) == 1:
            expected.append((node["expression"], returns[0]))
    elif kind == "Assignment" and node["operator"] not in ("<<=", ">>="):
        expected.append((node["rightHandSide"], node))
    elif kind == "BinaryOperation":
        common = {"typeDescriptions": node["commonType"]}
        expected.append((node["leftExpression"], common))
        if node["operator"] not in ("<<", ">>", "**"):
            expected.append((node["rightExpression"], common))
    elif kind == "FunctionCall" and node["kind"] == "functionCall":
        callee = by_id.get(node["expression"].get("referencedDeclaration"), {})
        if callee.get("nodeType") == "FunctionDefinition":
            expected.extend(zip(node["arguments"], callee["parameters"]["parameters"]))
    for value, target in expected:
        target_type = target["typeDescriptions"].get("typeIdentifier") or ""
        if (value is not None and value["nodeType"] == "Literal"
                and RATIONAL.fullmatch(value["typeDescriptions"].get("typeIdentifier") or "")
                and VALUE_TYPE.fullmatch(target_type) and not INTEGER_TYPE.fullmatch(target_type)):
            return [Blocker(kind, "literals of non-integer types", "elaboration")]
    return []


def scan(asts: dict[str, Any]) -> dict[int, list[Blocker]]:
    """Every node the semantics rejects, by node id, the importer's reasons
    first."""
    found: dict[int, list[Blocker]] = {}
    for ast in asts.values():
        by_id = {n["id"]: n for n in nodes(ast)}
        calls = [n for n in by_id.values() if n["nodeType"] == "FunctionCall"]
        callees = {n["expression"]["id"] for n in calls}
        conversions = {n["expression"]["id"] for n in calls if n["kind"] == "typeConversion"}
        storage_bases = {n["baseExpression"]["id"] for n in by_id.values()
                         if n["nodeType"] == "IndexAccess"}
        for node in nodes(ast):
            blockers = (node_blockers(node) + callee_blockers(node, callees, conversions)
                        + elaboration_blockers(node) + coerced_literals(node, by_id))
            if (node["nodeType"] in {"Identifier", "IndexAccess"}
                    and node.get("typeDescriptions", {}).get("typeIdentifier", "").startswith("t_mapping$_")
                    and node["id"] not in storage_bases):
                blockers.append(Blocker(node["nodeType"], "mapping values", "elaboration"))
            if blockers:
                found.setdefault(node["id"], []).extend(blockers)
    return found


# The HOL run


def run_hol(holbuild: str, work: Path, units: list[tuple[str, Path]]) -> dict[str, dict[str, Any]]:
    """Import and elaborate every unit, in one HOL session; the result of each
    test by name."""
    manifest = work / "manifest.txt"
    manifest.write_text("".join(f"{name}\t{path}\n" for name, path in units), encoding="utf-8")
    log = work / "hol.log"
    # `holbuild run` loads built theories but does not build them.
    build = [holbuild, "-j8", "build", "--skip-checkpoints", "--skip-proof-steps", "solidityImportLib",
             "solidityElaborateTheory"]
    print("+", " ".join(build), file=sys.stderr, flush=True)
    subprocess.run(build, cwd=ROOT, check=True)
    command = [holbuild, "-j1", "run", str(HOL_SCRIPT)]
    print("+", " ".join(command), file=sys.stderr, flush=True)
    with log.open("w", encoding="utf-8") as stream:
        status = subprocess.run(
            command, cwd=ROOT, stdin=subprocess.DEVNULL, stdout=stream,
            stderr=subprocess.STDOUT,
            env={**os.environ, "SEMANTIC_TESTS_MANIFEST": str(manifest)},
        ).returncode
    results = {}
    for line in log.read_text(encoding="utf-8", errors="replace").splitlines():
        if line.startswith(RESULT_PREFIX):
            result = json.loads(line[len(RESULT_PREFIX):])
            results[result["test"]] = result
    missing = [name for name, _ in units if name not in results]
    if status != 0 or missing:
        tail = "".join(log.read_text(encoding="utf-8", errors="replace").splitlines(True)[-30:])
        raise SystemExit(f"the HOL run failed (status {status}, {len(missing)} tests "
                         f"without a result):\n{tail}")
    return results


# Classification


@dataclass
class Classification:
    """A test's category, the first construct the importer rejected, and every
    construct the scan found that the semantics does not support."""

    test: str
    category: str
    reason: str | None = None
    first: Blocker | None = None
    blockers: list[Blocker] = field(default_factory=list)
    scan_agrees: bool = True


def classify(test: str, scanned: dict[int, list[Blocker]], hol: dict[str, Any]) -> Classification:
    """Combine the importer's and elaborator's verdict with the scan. The scan
    agrees if it finds nothing in an admitted test, only elaboration-stage
    blockers in a test the elaborator rejects, and an import-stage blocker at
    the node the importer rejected."""
    blockers = sorted({b for bs in scanned.values() for b in bs},
                      key=lambda b: (b.feature, b.node_type, b.stage))
    stages = {b.stage for b in blockers}
    status = hol["status"]
    message = hol.get("message")
    if status == ADMITTED:
        return Classification(test, ADMITTED, blockers=blockers, scan_agrees=not blockers)
    if status == ELABORATION_REJECTED:
        return Classification(test, ELABORATION_REJECTED, message, blockers=blockers,
                              scan_agrees=stages == {"elaboration"})
    if status != IMPORT_REJECTED:
        raise ValueError(f"{test}: unknown HOL status {status!r}")
    match = IMPORT_ERROR_NODE.match(message or "")
    at_node = [b for b in scanned.get(int(match.group(2)), []) if b.stage == "import"] if match else []
    first = at_node[0] if at_node else Blocker(match.group(1) if match else "?", "unclassified", "import")
    return Classification(test, IMPORT_REJECTED, message, first, blockers,
                          scan_agrees=bool(at_node))


# The report


@dataclass
class Report:
    pin: str
    profile: str
    results: list[Classification]

    def counts(self) -> Counter[str]:
        return Counter(r.category for r in self.results)

    def rejected(self) -> list[Classification]:
        return [r for r in self.results if r.category in (IMPORT_REJECTED, ELABORATION_REJECTED)]

    def feature_ranking(self) -> list[dict[str, Any]]:
        """Features by how many rejected tests they occur in, with how many
        they are the only blocker of and how many the importer stopped at."""
        rejected = self.rejected()
        blocking: Counter[str] = Counter()
        only: Counter[str] = Counter()
        first: Counter[str] = Counter()
        node_types: dict[str, set[str]] = {}
        for r in rejected:
            features = {b.feature for b in r.blockers}
            for b in r.blockers:
                node_types.setdefault(b.feature, set()).add(b.node_type)
            blocking.update(features)
            if len(features) == 1:
                only.update(features)
            if r.first is not None:
                first[r.first.feature] += 1
        return [
            {"feature": f, "node_types": sorted(node_types.get(f, ())), "tests": n,
             "only_blocker": only[f], "first_rejection": first[f]}
            for f, n in sorted(blocking.items(), key=lambda kv: (-kv[1], -only[kv[0]], kv[0]))
        ]

    def greedy_order(self, limit: int) -> list[tuple[str, int]]:
        """Features in the order that admits the most rejected tests at each
        step, by the scan, with the number admitted once all up to it are
        supported. Ties go to the feature occurring in more tests."""
        tests = [{b.feature for b in r.blockers} for r in self.rejected()]
        occurrences = Counter(f for features in tests for f in features)
        chosen: set[str] = set()
        order = []
        for _ in range(min(limit, len(occurrences))):
            def admitted(f: str) -> int:
                return sum(1 for features in tests if features <= chosen | {f})
            best = max(sorted(set(occurrences) - chosen),
                       key=lambda f: (admitted(f), occurrences[f]))
            order.append((best, admitted(best)))
            chosen.add(best)
        return order

    def json(self) -> dict[str, Any]:
        return {
            "format": REPORT_FORMAT,
            "solidity_pin": self.pin,
            "profile": self.profile,
            "counts": {c: self.counts()[c] for c in CATEGORIES},
            "features": self.feature_ranking(),
            "greedy_order": [{"feature": f, "admitted": n} for f, n in self.greedy_order(GREEDY_STEPS)],
            "tests": [
                {"test": r.test, "category": r.category, "reason": r.reason,
                 "first": r.first.feature if r.first else None,
                 "features": sorted({b.feature for b in r.blockers}),
                 "scan_agrees": r.scan_agrees}
                for r in self.results
            ],
        }

    def markdown(self) -> str:
        counts = self.counts()
        total = len(self.results)
        disagreements = [r for r in self.results if not r.scan_agrees]
        lines = [
            "# Coverage of solc's semantic tests",
            "",
            "Generated by `tools/semantic_tests_coverage.py`; do not edit by hand.",
            "",
            f"Every test under `{TESTS_DIR.as_posix()}` of argotorg/solidity at "
            f"`{self.pin}` was compiled with profile `{self.profile}`, imported by "
            "`solidityImportLib` and elaborated by `elaborate_unit`. Call expectations "
            "(the `// ----` sections) are not run, so an admitted test is one the "
            "semantics accepts, not one it is known to agree on.",
            "",
            "To regenerate it from the repository root, with the pinned solc and the "
            "tests checked out outside the repository:",
            "",
            "```sh",
            "git init ../solidity-tests && cd ../solidity-tests",
            "git remote add origin https://github.com/argotorg/solidity.git",
            f"git sparse-checkout set --no-cone {TESTS_DIR.as_posix()}",
            f"git fetch --depth 1 --filter=blob:none origin {self.pin}",
            "git checkout FETCH_HEAD && cd -",
            "tools/semantic_tests_coverage.py ../solidity-tests --solc /path/to/solc",
            "```",
            "",
            "| outcome | tests |",
            "| --- | ---: |",
        ]
        lines += [f"| {c} | {counts[c]} |" for c in CATEGORIES]
        lines += [f"| total | {total} |", ""]
        lines += [
            "## Features blocking rejected tests",
            "",
            "Each rejected test is scanned for every construct the importer or the "
            "elaborator rejects. *tests* counts the rejected tests a feature occurs in; "
            "*only blocker* the tests in which it is the only feature found, which "
            "supporting it would admit as far as the scan can tell; *first* the tests "
            "the importer stopped at it.",
            "",
            f"The scan disagrees with the HOL run on {len(disagreements)} tests"
            + (", listed at the end." if disagreements else "."),
            "",
            "| feature | AST nodes | tests | only blocker | first |",
            "| --- | --- | ---: | ---: | ---: |",
        ]
        for f in self.feature_ranking():
            node_types = ", ".join(f"`{t}`" for t in f["node_types"])
            lines.append(f"| {f['feature']} | {node_types} | {f['tests']} | "
                         f"{f['only_blocker']} | {f['first_rejection']} |")
        lines += [
            "",
            "## Features in order of tests admitted",
            "",
            "Supporting the features in this order admits the most rejected tests at "
            "each step, by the scan; *admitted* counts the tests admitted once every "
            "feature up to that row is supported. It ignores how hard a feature is.",
            "",
            "| step | feature | admitted |",
            "| ---: | --- | ---: |",
        ]
        lines += [f"| {i} | {f} | {n} |" for i, (f, n) in enumerate(self.greedy_order(GREEDY_STEPS), 1)]
        lines += ["", "## Skipped and compile failures", "", "| reason | tests |", "| --- | ---: |"]
        reasons = Counter(r.reason if r.category == SKIPPED else "compile failure"
                          for r in self.results if r.category in (SKIPPED, COMPILE_FAILURE))
        lines += [f"| {reason} | {n} |" for reason, n in sorted(reasons.items(), key=lambda kv: -kv[1])]
        for title, category in (("Admitted", ADMITTED), ("Elaborator rejections", ELABORATION_REJECTED)):
            lines += ["", f"## {title}", ""]
            tests = [r for r in self.results if r.category == category]
            lines += [f"- `{r.test}`" + (f": {r.reason}" if r.reason else "") for r in tests] or ["None."]
        if disagreements:
            lines += ["", "## Scan disagreements", ""]
            lines += [f"- `{r.test}` ({r.category}): {r.reason}" for r in disagreements]
        return "\n".join(lines) + "\n"


def parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("solidity", type=Path,
                        help="a checkout of argotorg/solidity at SOLIDITY_PIN")
    parser.add_argument("--solc", required=True, type=Path)
    parser.add_argument("--profile", type=Path, default=exporter.DEFAULT_PROFILE)
    parser.add_argument("--holbuild", default="holbuild")
    parser.add_argument("-j", "--jobs", type=int, default=os.cpu_count())
    parser.add_argument("--output", type=Path, default=ROOT / "docs" / "semantic-tests-coverage",
                        help="report path without extension; .md and .json are written")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    pin = exporter.PIN_FILE.read_text(encoding="ascii").strip()
    profile = exporter.read_json(args.profile)
    # Checked once here, so that every failure below is the test's own.
    exporter.compiler_identity(args.solc, profile["compilerVersion"], pin)
    tests_root = args.solidity / TESTS_DIR
    tests = [read_test(tests_root, path) for path in find_tests(tests_root)]

    results: dict[str, Classification] = {}
    to_compile = []
    for test in tests:
        reason = skip_reason(test, profile)
        if reason is not None:
            results[test.name] = Classification(test.name, SKIPPED, reason)
        else:
            to_compile.append(test)

    def compile_one(test: SemanticTest) -> tuple[SemanticTest, dict[str, Any] | str]:
        try:
            return test, compile_test(args.solc, test, args.profile)
        except SystemExit as error:
            return test, str(error)

    with tempfile.TemporaryDirectory(prefix="semantic-tests-") as temporary:
        work = Path(temporary)
        compiled: dict[str, dict[str, Any]] = {}
        units = []
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            for index, (test, outcome) in enumerate(pool.map(compile_one, to_compile)):
                if isinstance(outcome, str):
                    results[test.name] = Classification(test.name, COMPILE_FAILURE, outcome)
                    continue
                compiled[test.name] = outcome
                path = work / f"{index}.json"
                path.write_text(json.dumps(outcome), encoding="utf-8")
                units.append((test.name, path))
        print(f"{len(tests)} tests, {len(units)} compiled", file=sys.stderr, flush=True)
        hol = run_hol(args.holbuild, work, units)
    for name, sources in compiled.items():
        results[name] = classify(name, scan({source: data["ast"] for source, data in sources.items()}),
                                 hol[name])

    report = Report(pin, args.profile.stem, [results[t.name] for t in tests])
    exporter.write_json_atomic(args.output.with_suffix(".json"), report.json())
    args.output.with_suffix(".md").write_text(report.markdown(), encoding="utf-8")
    counts = report.counts()
    print(", ".join(f"{counts[c]} {c}" for c in CATEGORIES), file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
