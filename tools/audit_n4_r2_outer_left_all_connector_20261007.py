#!/usr/bin/env python3
"""Inspect exact outer-left connector routing; never run a proof compiler.

The frozen between auditor supplies only syntax parsers for the same balanced
tree grammar. All outer-left interfaces and files are checked independently
below. This report is diagnostic, never a substitute for kernel receipts.
"""
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
BASE = "tools/audit_n4_r2_all_connector_20261007.py"
ALL = "Jsp000404/N4R2OuterLeftAllChecked.lean"
TERMINAL = "Jsp000404/N4R2OuterLeftTerminal.lean"
SOUNDNESS = "Jsp000404/N4R2OuterLeftReplaySoundness.lean"
MANIFEST = "research/JSP404_N4_R2_OUTER_LEFT_SOURCE_MANIFEST_20261007.json"
OUTPUT = "research/JSP404_N4_R2_OUTER_LEFT_ALL_CONNECTOR_STATIC_AUDIT_20261007.json"


def main():
    spec = importlib.util.spec_from_file_location("frozen_connector_syntax", ROOT / BASE)
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    require, read = parser.require, parser.read_source
    all_source, terminal = read(ALL), read(TERMINAL)
    manifest = json.loads(read(MANIFEST))
    trees = [parser.parse_dispatch(parser.definition_body(all_source, a, b))
             for a, b in [("def libraryFor", "def leafData"),
                          ("def leafData", "theorem all_leaves_checked")]]
    trees.append(parser.parse_proof(all_source))
    require(parser.shape(trees[0]) == parser.shape(trees[1]) == parser.shape(trees[2]),
            "Library, leaf and proof tree shapes differ")
    imports = list(map(int, re.findall(
        r"(?m)^import Jsp000404\.N4R2OuterLeftLeafCheckedShard(\d+)$", all_source)))
    require(imports == list(range(193)), "Imports are not exactly ordered shards 000..192")
    intervals = []
    parser.check_intervals(trees[2], 0, 24698, intervals)
    require([b for b, _, _ in intervals] == list(range(193)), "Repeated or missing shard")
    for index in range(24698):
        lib, data, proof = [parser.route(tree, index) for tree in trees]
        block = index // 128
        require(lib[1] == data[1] == proof[1] == block, f"Inconsistent route at {index}")
        require(data[2] == 128 * block, f"Wrong local offset at {index}")
    for block, lower, upper in intervals:
        module = f"Jsp000404.N4R2OuterLeftLeafCheckedShard{block:03d}"
        source = f"Jsp000404/N4R2OuterLeftLeafCheckedShard{block:03d}.lean"
        text, count = read(source), upper - lower
        record = manifest["blocks"][module]
        require(record["start"] == lower and record["count"] == count, "Manifest range differs")
        require(parser.SOURCE_HASHES[source] == record["source_sha256"] ==
                manifest["source_hashes"][source], "Manifest source digest differs")
        parser.require_header(text, "correct", f"""
          theorem correct (id : Fin 24698) (hlow : {lower} ≤ id.val)
            (hhigh : id.val < {upper}) :
          leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - {lower})) = true
        """)
        require(f"namespace Jsp404.N4R2OuterLeftData.LeafShard{block:03d}" in text,
                "Unexpected shard namespace")
    aggregate_header = parser.require_header(all_source, "all_leaves_checked", """
      theorem all_leaves_checked (id : Fin 24698) :
      leafCheck (libraryFor id) (N4R2WordTree.catalog id) (leafData id) = true
    """)
    terminal_header = parser.require_header(terminal, "outer_left_low1_pure_tail_impossible", """
      theorem outer_left_low1_pure_tail_impossible (M : GenericModel 7 4)
      (hdef1 : SatScalarModel.rowDefect M 1 = 2)
      (htails : ∀ i : Fin 7, 1 < i.val → SatScalarModel.rowDefect M i = 4) : False
    """)
    expected_body = parser.normalize("""
      obtain ⟨id, hword⟩ := N4R2ModelCatalog.exists_catalog_model_word M
      exact N4R2OuterLeftReplaySoundness.leafCheck_sound
        (N4R2OuterLeftData.libraryFor id) M (N4R2WordTree.catalog id) hword hdef1 htails
        (N4R2OuterLeftData.leafData id) (N4R2OuterLeftData.all_leaves_checked id)
    """)
    body = terminal.split("theorem outer_left_low1_pure_tail_impossible", 1)[1]
    body = body.split(":= by", 1)[1].split("#print", 1)[0]
    require(parser.normalize(body) == expected_body, "Terminal arguments or producer differ")
    soundness_header = parser.require_header(read(SOUNDNESS), "leafCheck_sound", """
      theorem leafCheck_sound (library : N4R2OuterLeftReplay.Library) (M : GenericModel 7 4)
      (w : N4R2OuterLeftReplay.Word) (hword : WordSound M w)
      (hdef1 : SatScalarModel.rowDefect M 1 = 2)
      (htails : ∀ i : Fin 7, 1 < i.val → SatScalarModel.rowDefect M i = 4)
      (data : N4R2OuterLeftReplay.LeafData)
      (hcheck : N4R2OuterLeftReplay.leafCheck library w data = true) : False
    """)
    read(BASE)
    read(str(Path(__file__).relative_to(ROOT)))
    for path, digest in parser.SOURCE_HASHES.items():
        require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest,
                f"Source changed during audit: {path}")
    report = {
        "status": "STATIC_ONLY_NOT_KERNEL", "Lean_compiled": False,
        "kernel_all_words": False, "compiler_commands_run": [],
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "aggregate_source": ALL, "terminal_source": TERMINAL,
        "source_hashes": parser.SOURCE_HASHES,
        "tree_checks": {"three_routes_identical": True, "leaf_nodes": 193,
                        "split_nodes": 192, "exact_indices": 24698,
                        "same_shard_and_local_offset_for_every_index": True,
                        "intervals": intervals},
        "static_api_checks": {"aggregate_header": aggregate_header,
                              "terminal_header": terminal_header,
                              "soundness_header": soundness_header,
                              "terminal_obtains_word_and_id_internally": True},
        "not_claimed": ["Lean elaboration", "Kernel all-word proof",
                        "Normal compilation", "Original all-n theorem"]}
    (ROOT / OUTPUT).write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": report["status"], "indices": 24698,
                      "shards": 193, "bound_sources": len(parser.SOURCE_HASHES),
                      "report": OUTPUT}))


if __name__ == "__main__":
    main()
