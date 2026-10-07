#!/usr/bin/env python3
"""Reproduce the static connector review; never run Lean, Lake, or Git.

This parses the actual generated library/data/proof trees, exhaustively checks
their finite index routing, and checks interface source text. It is not a Lean
elaborator, a kernel check, an axiom audit, or an all-word exclusion proof.
"""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
ALL = "Jsp000404/N4R2AllLeavesChecked.lean"
TERMINAL = "Jsp000404/N4R2BetweenTerminal.lean"
MANIFEST = "research/JSP404_N4_R2_SHARED_REPLAY_SOURCE_MANIFEST_20261007.json"
OUTPUT = "research/JSP404_N4_R2_ALL_CONNECTOR_STATIC_AUDIT_20261007.json"
CATALOG_SIZE = 24698
CHUNK_SIZE = 128
BLOCK_COUNT = 193
SOURCE_HASHES = {}


def require(condition, description):
    if not condition:
        raise AssertionError(description)


def read_source(relative):
    raw = (ROOT / relative).read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    old = SOURCE_HASHES.setdefault(relative, digest)
    require(old == digest, f"Source changed during audit: {relative}")
    return raw.decode("utf-8")


def normalize(text):
    return " ".join(text.split())


def theorem_header(text, name):
    match = re.search(rf"\btheorem {name}\b.*?(?=\s*:=)", text, re.S)
    require(match is not None, f"Missing theorem header: {name}")
    return normalize(match.group())


def require_header(text, name, expected):
    actual = theorem_header(text, name)
    require(actual == normalize(expected), f"Static API text mismatch: {name}")
    return actual


def definition_body(text, start, end):
    return text.split(start, 1)[1].split(end, 1)[0].split(":=", 1)[1]


def parse_dispatch(text):
    pattern = re.compile(
        r"LeafShard\d+\.(?:library|lookup)|id\.val|\bif\b|\bthen\b|\belse\b|\d+|[()<-]"
    )
    tokens = []
    previous = 0
    for match in pattern.finditer(text):
        require(not text[previous:match.start()].strip(), "Unsupported dispatch syntax")
        tokens.append(match.group())
        previous = match.end()
    require(not text[previous:].strip(), "Unsupported dispatch suffix")
    position = 0

    def eat(expected):
        nonlocal position
        require(position < len(tokens) and tokens[position] == expected,
                f"Dispatch token {position}: expected {expected}")
        position += 1

    def expression():
        nonlocal position
        require(position < len(tokens), "Unexpected end of dispatch")
        if tokens[position] == "(":
            eat("(")
            result = expression()
            eat(")")
            return result
        if tokens[position] == "if":
            eat("if")
            eat("id.val")
            eat("<")
            boundary = int(tokens[position])
            position += 1
            eat("then")
            left = expression()
            eat("else")
            right = expression()
            return ("if", boundary, left, right)
        token = tokens[position]
        position += 1
        match = re.fullmatch(r"LeafShard(\d+)\.(library|lookup)", token)
        require(match is not None, f"Unexpected dispatch leaf: {token}")
        block = int(match[1])
        offset = None
        if match[2] == "lookup":
            eat("(")
            eat("id.val")
            eat("-")
            offset = int(tokens[position])
            position += 1
            eat(")")
        return ("leaf", block, offset)

    tree = expression()
    require(position == len(tokens), "Trailing dispatch tokens")
    return tree


def shape(tree):
    if tree[0] == "if":
        return ("if", tree[1], shape(tree[2]), shape(tree[3]))
    return ("leaf", tree[1])


def route(tree, index):
    while tree[0] == "if":
        tree = tree[2] if index < tree[1] else tree[3]
    return tree


def parse_proof(text):
    body = text.split("theorem all_leaves_checked", 1)[1].split(":= by", 1)[1]
    body = body.split("#print", 1)[0]
    lines = [line for line in body.splitlines() if line.strip()]
    position = 0
    split_pattern = re.compile(r"(\s*)by_cases h(\d+) : id.val < (\d+)$")
    leaf_pattern = re.compile(
        r"(\s*)exact LeafShard(\d+)\.correct id \(by omega\) \(by omega\)$"
    )

    def subtree(depth):
        nonlocal position
        require(position < len(lines), "Unexpected end of proof tree")
        line = lines[position]
        leaf = leaf_pattern.fullmatch(line)
        if leaf:
            require(len(leaf[1]) == depth, "Unexpected proof leaf indentation")
            position += 1
            return ("leaf", int(leaf[2]), None)
        split = split_pattern.fullmatch(line)
        require(split is not None, f"Unsupported proof line: {line}")
        require(len(split[1]) == depth and split[2] == split[3],
                "Proof split indentation or named boundary mismatch")
        boundary = int(split[2])
        position += 1

        def branch():
            nonlocal position
            expected = " " * depth + (
                f"· simp only [leafData, libraryFor, h{boundary}, ↓reduceIte]"
            )
            require(position < len(lines) and lines[position] == expected,
                    f"Proof branch does not simplify its own boundary {boundary}")
            position += 1
            return subtree(depth + 2)

        return ("if", boundary, branch(), branch())

    tree = subtree(2)
    require(position == len(lines), "Trailing proof lines")
    return tree


def check_intervals(tree, lower, upper, intervals):
    if tree[0] == "leaf":
        block = tree[1]
        expected = (CHUNK_SIZE * block,
                    min(CHUNK_SIZE * (block + 1), CATALOG_SIZE))
        require((lower, upper) == expected, f"Incorrect interval for block {block}")
        intervals.append((block, lower, upper))
        return
    boundary = tree[1]
    require(lower < boundary < upper, "Empty or reversed dispatch interval")
    check_intervals(tree[2], lower, boundary, intervals)
    check_intervals(tree[3], boundary, upper, intervals)


def main():
    all_source = read_source(ALL)
    terminal_source = read_source(TERMINAL)
    manifest = json.loads(read_source(MANIFEST))
    library_tree = parse_dispatch(definition_body(all_source, "def libraryFor", "def leafData"))
    data_tree = parse_dispatch(definition_body(all_source, "def leafData", "theorem all_leaves_checked"))
    proof_tree = parse_proof(all_source)
    require(shape(library_tree) == shape(data_tree) == shape(proof_tree),
            "Library, data, and proof dispatch trees differ")
    imports = [int(number) for number in re.findall(
        r"(?m)^import Jsp000404\.N4R2LeafCheckedShard(\d+)$", all_source
    )]
    require(imports == list(range(BLOCK_COUNT)), "Missing, duplicate, or unordered leaf imports")
    for index in range(CATALOG_SIZE):
        library = route(library_tree, index)
        data = route(data_tree, index)
        proof = route(proof_tree, index)
        block = index // CHUNK_SIZE
        require(library[1] == data[1] == proof[1] == block,
                f"Catalog index {index} selects inconsistent blocks")
        require(data[2] == CHUNK_SIZE * block, f"Wrong lookup subtraction at {index}")

    intervals = []
    check_intervals(proof_tree, 0, CATALOG_SIZE, intervals)
    require([item[0] for item in intervals] == list(range(BLOCK_COUNT)),
            "Proof does not contain exactly every block once")
    leaf_records = []
    for block, lower, upper in intervals:
        module = f"Jsp000404.N4R2LeafCheckedShard{block:03d}"
        path = f"Jsp000404/N4R2LeafCheckedShard{block:03d}.lean"
        text = read_source(path)
        count = upper - lower
        require_header(text, "point_checked", f"""
          theorem point_checked (j : Fin {count}) :
          leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 ({lower} + j.val)))
            (lookup j.val) = true
        """)
        require_header(text, "correct", f"""
          theorem correct (id : Fin 24698) (hlow : {lower} ≤ id.val)
            (hhigh : id.val < {upper}) :
          leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - {lower})) = true
        """)
        require(f"if offset < {count} then" in text, f"Wrong lookup guard: block {block}")
        named = [tuple(map(int, match)) for match in re.findall(
            r"theorem namedLeaf(\d+)_checked :\s*leafCheck library "
            r"\(N4R2WordTree.catalog \(Fin.ofNat 24698 (\d+)\)\) namedLeaf(\d+) = true",
            text,
        )]
        require(named == [(offset, lower + offset, offset) for offset in range(count)],
                f"Named word/leaf indices differ: block {block}")
        require(re.search(rf"namespace Jsp404.N4R2ReplayData.LeafShard{block:03d}\b", text),
                f"Wrong local namespace: block {block}")
        require("def library : Library := fun id =>" in text,
                f"Missing same-namespace library: block {block}")
        require("import Jsp000404.N4R2CycleLibrary" not in text,
                f"Unexpected global library import: block {block}")
        local_map = manifest["leaf_local_cycle_maps"][module]
        require(local_map["start"] == lower and local_map["count"] == count,
                f"Manifest local-map range differs: block {block}")
        require(SOURCE_HASHES[path] == manifest["source_hashes"][path],
                f"Manifest source hash differs: block {block}")
        leaf_records.append({"block": block, "start": lower, "end_exclusive": upper,
                             "count": count, "source": path,
                             "source_sha256": SOURCE_HASHES[path]})

    aggregate_header = require_header(all_source, "all_leaves_checked", """
      theorem all_leaves_checked (id : Fin 24698) :
      leafCheck (libraryFor id) (N4R2WordTree.catalog id) (leafData id) = true
    """)
    terminal_header = require_header(terminal_source, "between_pure_tail_impossible", """
      theorem between_pure_tail_impossible (M : GenericModel 7 4)
      (hdef0 : SatScalarModel.rowDefect M 0 = 2)
      (hdef6 : SatScalarModel.rowDefect M 6 = 2)
      (htails : ∀ i : Fin 7, 0 < i.val → i.val < 6 → SatScalarModel.rowDefect M i = 4) : False
    """)
    expected_terminal_body = normalize("""
      obtain ⟨id, hword⟩ := N4R2ModelCatalog.exists_catalog_model_word M
      exact N4R2RowDataReplaySoundness.leafCheck_sound (N4R2ReplayData.libraryFor id) M
        (N4R2WordTree.catalog id) hword hdef0 hdef6 htails
        (N4R2ReplayData.leafData id) (N4R2ReplayData.all_leaves_checked id)
    """)
    terminal_body = terminal_source.split("theorem between_pure_tail_impossible", 1)[1]
    terminal_body = terminal_body.split(":= by", 1)[1].split("#print", 1)[0]
    require(normalize(terminal_body) == expected_terminal_body, "Terminal application differs")
    soundness = read_source("Jsp000404/N4R2RowDataReplaySoundness.lean")
    soundness_header = require_header(soundness, "leafCheck_sound", """
      theorem leafCheck_sound (lib : N4R2ThinReplay.Library) (M : GenericModel 7 4)
      (w : N4R2ThinReplay.Word) (hword : WordSound M w)
      (hdef0 : SatScalarModel.rowDefect M 0 = 2)
      (hdef6 : SatScalarModel.rowDefect M 6 = 2)
      (htails : ∀ i : Fin 7, 0 < i.val → i.val < 6 → SatScalarModel.rowDefect M i = 4)
      (data : N4R2RowDataReplay.LeafData)
      (hcheck : N4R2RowDataReplay.leafCheck lib w data = true) : False
    """)
    producer = read_source("Jsp000404/N4R2ModelCatalog.lean")
    producer_header = require_header(producer, "exists_catalog_model_word", """
      theorem exists_catalog_model_word (M : GenericModel 7 4) :
      ∃ id : Fin 24698, WordSound M (N4R2WordTree.catalog id)
    """)
    aliases = {
        "Jsp000404/N4R2WordDefinitions.lean": ["abbrev Word := Fin 35 → Bool"],
        "Jsp000404/N4R2ThinReplay.lean": ["abbrev Word := N4R2WordDefinitions.Word"],
        "Jsp000404/N4R2RowDataReplay.lean": ["abbrev Word := N4R2ThinReplay.Word",
                                                   "abbrev Library := N4R2ThinReplay.Library"],
        "Jsp000404/N4R2ModelWordSoundness.lean": ["abbrev Word := N4R2WordDefinitions.Word"],
    }
    for path, expected_aliases in aliases.items():
        text = read_source(path)
        for alias in expected_aliases:
            require(alias in text, f"Static alias mismatch in {path}: {alias}")
    catalog = read_source("Jsp000404/N4R2WordCatalog.lean")
    require("def catalog (id : Fin 24698) : N4R2WordDefinitions.Word :=" in catalog,
            "Catalog parameter or result alias differs")

    read_source("tools/audit_n4_r2_all_connector_20261007.py")
    for path, digest in SOURCE_HASHES.items():
        require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest,
                f"Source changed before report publication: {path}")
    report = {
        "status": "STATIC_ONLY_NOT_KERNEL",
        "Lean_compiled": False,
        "kernel_checked": False,
        "normal_built": False,
        "all_word_exclusion_completed_by_this_audit": False,
        "all_word_exclusion_status": "Not completed by this audit; parent strict and genuine normal validation remains required",
        "compiler_commands_run": [],
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "auditor": "tools/audit_n4_r2_all_connector_20261007.py",
        "aggregate_source": ALL,
        "terminal_source": TERMINAL,
        "manifest": MANIFEST,
        "source_hashes": SOURCE_HASHES,
        "tree_checks": {"same_library_data_proof_shape": True,
                        "split_nodes": BLOCK_COUNT - 1, "leaf_nodes": BLOCK_COUNT,
                        "imports_exactly_000_through_192": True,
                        "each_block_occurs_once": True,
                        "each_branch_simplifies_its_own_boundary": True},
        "index_checks": {"domain": "Fin 24698", "indices_enumerated": CATALOG_SIZE,
                         "all_three_routes_equal_floor_id_div_128": True,
                         "lookup_subtraction_equals_128_times_block": True,
                         "correct_call_intervals_match_every_path": True,
                         "tail_block": 192, "tail_start": 24576,
                         "tail_end_exclusive": 24698, "tail_count": 122,
                         "all_named_catalog_and_leaf_indices_align": True,
                         "manifest_localmap_ranges_and_source_hashes_align": True},
        "static_api_checks": {"method": "Exact normalized declaration/application text and alias inspection; not Lean elaboration",
                              "aggregate_header": aggregate_header,
                              "terminal_header": terminal_header,
                              "soundness_header": soundness_header,
                              "producer_header": producer_header,
                              "terminal_application_matches_argument_order": True,
                              "word_and_library_aliases_align": True,
                              "no_caller_word_or_catalog_id_in_terminal_premises": True},
        "omega_boundary_assessment": "Every proof path gives the required integer interval. The upper endpoint of the last block is the Fin 24698 bound; Lean 4.34 OmegaM.analyzeAtom adds Fin.isLt for a Fin.val atom. This is source inspection, not an executed tactic check.",
        "leaf_sources": leaf_records,
        "ordinary_logic_or_api_findings": [],
        "not_claimed": ["Lean elaboration success", "Kernel verification", "Normal build success",
                        "Verified axiom sets", "All-word exclusion completion",
                        "Cycle or row soundness internal re-audit", "Original eight-point theorem"],
    }
    (ROOT / OUTPUT).write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": report["status"], "report": OUTPUT,
                      "bound_sources": len(SOURCE_HASHES), "catalog_indices": CATALOG_SIZE,
                      "split_nodes": BLOCK_COUNT - 1, "leaf_nodes": BLOCK_COUNT,
                      "tail_count": 122, "ordinary_logic_or_api_findings": []}, indent=2))


if __name__ == "__main__":
    main()
