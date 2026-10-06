#!/usr/bin/env python3
"""Read-only, independent static audit of the unbounded-n between terminal.

Uses only the Python standard library. Does not import or run the generator,
Lean, Lake, Git, or any subprocess, and does not write an audit receipt.
The JSON result includes the source lines for every split, leaf, and signature.
This is a static audit, not a fresh Lean kernel check.
"""

from collections import Counter, defaultdict, deque
import hashlib
from itertools import combinations
import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = "research/JSP404_SIX_SYMBOLIC_BETWEEN_TERMINAL_SOURCE_MANIFEST_20261006.json"
TERMINAL = "Jsp000404/SixExactFloorKernelSymbolicBetweenTerminal.lean"
MODEL = "Jsp000404/SixModelCompression.lean"
PUBLIC = "Jsp404.SixExactFloorKernel.symbolic_between_impossible"
TRIPLES = tuple(combinations(range(5), 3))
FORBIDDEN = re.compile(r"\b(?:sorry|admit|native_decide|axiom|newaxiom)\b")
BASE_SIGNATURE = (
    "{n:ℕ}(M:SixModelCompression.ModelSixn)"
    "(hn4:4≤n)(hhigh:(1/2:ℝ)≤M.delta)"
    + "".join(
        f"(hdef{i}:SixModelCompression.rowDefectM{i}={value})"
        for i, value in ((0, 2), (1, 3), (3, 3), (4, 2))
    )
)
LEAF_ARGS = ["M", "hn4", "hhigh", "hdef0", "hdef1", "hdef3", "hdef4"] + [
    f"htri{i}{j}{k}" for i, j, k in TRIPLES
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def local_path(relative):
    path = ROOT / relative
    require(path.resolve().is_relative_to(ROOT), f"Path escapes repository: {relative}")
    require(path.is_file(), f"Missing input: {relative}")
    return path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def compact(text):
    return re.sub(r"\s+", "", text)


def line_number(text, position):
    return 1 + text[:position].count("\n")


def declaration(text, short, source):
    pattern = re.compile(
        r"^theorem\s+" + re.escape(short) + r"\b(?P<signature>.*?)\s*:=\s*by\b",
        re.MULTILINE | re.DOTALL,
    )
    matches = list(pattern.finditer(text))
    require(len(matches) == 1, f"Expected one theorem {short} in {source}")
    return matches[0]


def source_namespace(text, position):
    """Read namespace/section nesting before a declaration, masking comments."""
    prefix = text[:position]
    masked = list(prefix)
    index, block, quoted = 0, 0, False
    while index < len(prefix):
        pair = prefix[index:index + 2]
        if block:
            size = 2 if pair in ("/-", "-/") else 1
            block += 1 if pair == "/-" else -1 if pair == "-/" else 0
        elif quoted:
            size = min(2, len(prefix) - index) if prefix[index] == "\\" else 1
            if prefix[index] == '"':
                quoted = False
        elif pair == "/-":
            block, size = 1, 2
        elif pair == "--":
            newline = prefix.find("\n", index)
            size = (len(prefix) if newline < 0 else newline) - index
        elif prefix[index] == '"':
            quoted, size = True, 1
        else:
            index += 1
            continue
        for offset in range(size):
            if prefix[index + offset] != "\n":
                masked[index + offset] = " "
        index += size
    require(not block and not quoted, "Declaration lies inside an unfinished comment/string")
    frames = []
    commands = re.finditer(r"^[ \t]*(namespace|section|end)(?:[ \t]+(\S+))?[ \t]*$",
                           "".join(masked), re.MULTILINE)
    for command in commands:
        kind, name = command.groups()
        if kind != "end":
            require(kind != "namespace" or name is not None, "Unnamed namespace command")
            require(not (name or "").startswith("_root_."), "Unsupported absolute namespace command")
            frames.append((kind, name))
        else:
            require(frames and (name is None or name == frames[-1][1]),
                    "Unmatched namespace/section end command")
            frames.pop()
    return ".".join(name for kind, name in frames if kind == "namespace")


def no_forbidden_tokens(text, source):
    hits = [
        {"source": source, "line": line_number(text, match.start()), "token": match.group()}
        for match in FORBIDDEN.finditer(text)
    ]
    require(not hits, f"Forbidden source tokens: {hits}")


def triangle_facts(triple, arm):
    i, j, k = triple
    first, middle, last = (i, j), (i, k), (j, k)
    low, high = (first, last) if arm == 0 else (last, first)
    return {
        f"htr{i}{j}{k}a": (low, high, "positive_unit_gap"),
        f"htr{i}{j}{k}b": (low, middle, "strict"),
        f"htr{i}{j}{k}c": (middle, high, "strict"),
    }


def cyclic(edges):
    """Kahn's algorithm, independently of the generator's recursive DFS."""
    adjacency = defaultdict(list)
    indegree = Counter()
    for low, high, kind in edges:
        require(kind in ("strict", "positive_unit_gap"), "Unknown edge semantics")
        indegree.setdefault(low, 0)
        indegree[high] += 1
        adjacency[low].append(high)
    ready = deque(vertex for vertex, degree in indegree.items() if degree == 0)
    visited = 0
    while ready:
        vertex = ready.popleft()
        visited += 1
        for other in adjacency[vertex]:
            indegree[other] -= 1
            if indegree[other] == 0:
                ready.append(other)
    return visited != len(indegree)


def cycle_witness(edges):
    adjacency = defaultdict(list)
    for low, high, _ in edges:
        adjacency[low].append(high)
    done, active, route = set(), set(), []

    def visit(vertex):
        if vertex in active:
            return route[route.index(vertex):] + [vertex]
        if vertex in done:
            return None
        active.add(vertex)
        route.append(vertex)
        for other in adjacency[vertex]:
            found = visit(other)
            if found:
                return found
        route.pop()
        active.remove(vertex)
        done.add(vertex)
        return None

    for vertex in list(adjacency):
        found = visit(vertex)
        if found:
            return [f"d{i}{j}" for i, j in found]
    raise ValueError("Kahn detected a cycle but no witness was recovered")


def expected_leaf_signature(mask):
    signature = BASE_SIGNATURE
    for bit, (i, j, k) in enumerate(TRIPLES):
        low, high = ((j, k), (i, j)) if mask & (1 << bit) else ((i, j), (j, k))
        a, b, c = f"M.d{low[0]}{low[1]}", f"M.d{high[0]}{high[1]}", f"M.d{i}{k}"
        signature += f"(htri{i}{j}{k}:{a}+1≤{b}∧{a}<{c}∧{c}<{b})"
    return signature + ":False"


def parse_lean_body(lines, start_index, registry):
    """Parse the actual rcases/bullet tree, preserving every source line."""
    position = start_index
    split_evidence, leaf_evidence = [], []

    def take(expected=None):
        nonlocal position
        require(position < len(lines), "Unexpected end of terminal source")
        value, number = lines[position], position + 1
        if expected is not None:
            require(value == expected, f"Unexpected source at line {number}: {value!r}")
        position += 1
        return value, number

    def parse(depth, mask, bits, indent):
        prefix = " " * indent
        value, number = take()
        require(value.startswith(prefix) and not value.startswith(prefix + " "),
                f"Incorrect proof indentation at line {number}")
        statement = value[indent:]
        core_match = re.fullmatch(r"linarith only \[(.*)\]", statement)
        if core_match:
            names = [part.strip() for part in core_match.group(1).split(",")]
            require(names and all(re.fullmatch(r"htr[0-4]{3}[abc]", name) for name in names),
                    f"Malformed linarith core at line {number}")
            leaf_evidence.append({"line": number, "kind": "badprefix", "depth": depth,
                                  "prefix_mask": mask, "bits": bits, "core": names})
            return {"core": names, "covered_full_arms": 1 << (10 - depth)}
        if statement.startswith("exact "):
            tokens = statement.split()
            require(depth == 10 and mask in registry,
                    f"Nonterminal or unregistered exact leaf at line {number}")
            require(tokens == ["exact", registry[mask]["theorem"], *LEAF_ARGS],
                    f"Wrong leaf theorem or arguments at line {number}")
            leaf_evidence.append({"line": number, "kind": "orientation", "depth": depth,
                                  "mask": mask, "bits": bits,
                                  "theorem": tokens[1], "arguments": tokens[2:]})
            return {"mask": mask, "covered_full_arms": 1}
        require(depth < 10, f"Unexpected split beyond ten triangles at line {number}")
        i, j, k = TRIPLES[depth]
        name = f"htri{i}{j}{k}"
        expected = f"rcases M.triangle {i} {j} {k} (by decide) (by decide) with {name} | {name}"
        require(statement == expected, f"Wrong triangle split at line {number}")
        split_evidence.append({"line": number, "depth": depth, "prefix_mask": mask,
                               "triple": [i, j, k]})
        children = []
        for arm in (0, 1):
            take(prefix + "·")
            for suffix, projection in (("a", ".1"), ("b", ".2.1"), ("c", ".2.2")):
                take(prefix + f"  have htr{i}{j}{k}{suffix} := {name}{projection}")
            children.append(parse(depth + 1, mask | (arm << depth), bits + [arm], indent + 2))
        return {"triple": [i, j, k], "children": children}

    parsed = parse(0, 0, [], 2)
    return parsed, position, split_evidence, leaf_evidence


def audit_tree(tree, leaf_evidence):
    coverage = Counter()
    stats = Counter()
    depths = Counter()
    masks = set()
    records = iter(leaf_evidence)

    def visit(node, depth, mask, bits, facts):
        has_cycle = cyclic(facts.values())
        if "core" in node:
            require(set(node) == {"core", "covered_full_arms"}, "Unexpected core node fields")
            require(has_cycle, f"Badprefix has no cycle: {bits}")
            names = node["core"]
            require(names and len(set(names)) == len(names), f"Repeated or empty core: {bits}")
            require(set(names) <= set(facts), f"Core references facts outside its branch: {bits}")
            edges = [facts[name] for name in names]
            require(cyclic(edges), f"Core itself contains no cycle: {bits}")
            count = 1 << (10 - depth)
            require(node["covered_full_arms"] == count, f"Incorrect badprefix coverage: {bits}")
            coverage.update(mask | (suffix << depth) for suffix in range(count))
            record = next(records)
            require(record["bits"] == bits and record["core"] == names,
                    "Core evidence does not match tree traversal")
            record.update({"covered_arms": count, "expansion_step": 1 << depth,
                           "cycle_witness": cycle_witness(edges),
                           "core_edges": [
                               {"name": name, "low": f"d{low[0]}{low[1]}",
                                "high": f"d{high[0]}{high[1]}", "relation": kind}
                               for name, (low, high, kind) in zip(names, edges)
                           ]})
            stats["cycle_leaves"] += 1
            depths[depth] += 1
            return
        require(not has_cycle, f"Tree fails to prune the first cyclic prefix: {bits}")
        if "mask" in node:
            require(set(node) == {"mask", "covered_full_arms"}, "Unexpected mask node fields")
            require(depth == 10 and node["mask"] == mask and node["covered_full_arms"] == 1,
                    f"Incorrect complete orientation leaf: {bits}")
            require(mask not in masks, f"Duplicate orientation leaf: {mask}")
            masks.add(mask)
            coverage[mask] += 1
            record = next(records)
            require(record["bits"] == bits and record["mask"] == mask,
                    "Orientation evidence does not match tree traversal")
            record["covered_arms"] = 1
            stats["orientation_leaves"] += 1
            return
        require(set(node) == {"triple", "children"}, "Unexpected split node fields")
        require(depth < 10 and tuple(node["triple"]) == TRIPLES[depth],
                f"Wrong triangle order at depth {depth}")
        require(len(node["children"]) == 2, "Triangle split is not binary")
        stats["splits"] += 1
        for arm, child in enumerate(node["children"]):
            visit(child, depth + 1, mask | (arm << depth), bits + [arm],
                  {**facts, **triangle_facts(TRIPLES[depth], arm)})

    visit(tree, 0, 0, [], {})
    require(next(records, None) is None, "Unused leaf evidence")
    require(coverage == Counter({mask: 1 for mask in range(1024)}),
            "The 1024 arms are not covered exactly once")
    require(dict(stats) == {"splits": 197, "cycle_leaves": 136, "orientation_leaves": 62},
            f"Unexpected tree statistics: {dict(stats)}")
    acyclic_masks = set()
    for mask in range(1024):
        facts = {}
        for bit, triple in enumerate(TRIPLES):
            facts.update(triangle_facts(triple, (mask >> bit) & 1))
        if not cyclic(facts.values()):
            acyclic_masks.add(mask)
    require(masks == acyclic_masks and len(acyclic_masks) == 62,
            "Orientation leaves differ from the independently enumerated acyclic masks")
    return dict(stats), masks, depths, coverage


def audit():
    manifest_path = local_path(MANIFEST)
    manifest = json.loads(manifest_path.read_text())
    require(manifest["source"] == TERMINAL and manifest["public_theorem"] == PUBLIC,
            "Unexpected public source or theorem in manifest")
    hashes = {}
    for field in ("source", "generator", "coverage_tree"):
        digest = sha(local_path(manifest[field]))
        require(digest == manifest[field + "_sha256"], f"Manifest hash mismatch: {field}")
        hashes[field] = {"path": manifest[field], "sha256": digest}
    source = local_path(TERMINAL).read_text()
    no_forbidden_tokens(source, TERMINAL)
    public_short = PUBLIC.rsplit(".", 1)[1]
    public_decl = declaration(source, public_short, TERMINAL)
    require(source_namespace(source, public_decl.start()) == "Jsp404.SixExactFloorKernel",
            "Public theorem is declared in the wrong source namespace")
    require(compact(public_decl.group("signature")) == BASE_SIGNATURE + ":False",
            "Public theorem has additional, missing, or different assumptions")

    model = local_path(MODEL).read_text()
    triangle = re.search(r"^  triangle\s*:.*?(?=^  rowxs\s*:)", model,
                         re.MULTILINE | re.DOTALL)
    require(triangle is not None, "ModelSix triangle field was not found")
    expected_triangle = (
        "triangle:∀ijk,i<j→j<k→"
        "(dij+1≤djk∧dij<dik∧dik<djk)∨"
        "(djk+1≤dij∧djk<dik∧dik<dij)"
    )
    require(compact(triangle.group()) == expected_triangle,
            "ModelSix triangle inequalities differ from the audited edge semantics")

    registry = {}
    signature_evidence = []
    scanned_sources, freeze_paths = set(), set()
    for key, entry in manifest["typed_leaf_registry"].items():
        require(re.fullmatch(r"0|[1-9][0-9]*", key) is not None, f"Noncanonical mask: {key}")
        mask = int(key)
        require(0 <= mask < 1024, f"Out-of-range registry mask: {mask}")
        require(entry["source"] == entry["module"].replace(".", "/") + ".lean",
                f"Module/source mismatch for mask {mask}")
        for field in ("source", "freeze"):
            require(sha(local_path(entry[field])) == entry[field + "_sha256"],
                    f"Registry hash mismatch for mask {mask}: {field}")
        text = local_path(entry["source"]).read_text()
        if entry["source"] not in scanned_sources:
            no_forbidden_tokens(text, entry["source"])
            scanned_sources.add(entry["source"])
        freeze_paths.add(entry["freeze"])
        short = entry["theorem"].rsplit(".", 1)[1]
        require(re.fullmatch(r"symbolic_(?:v2_)?mask" + str(mask)
                             + r"_(?:probe|legacy_reuse)", short) is not None,
                f"Theorem name disagrees with mask {mask}")
        require(entry["theorem"].startswith("Jsp404.SixExactFloorKernel."),
                f"Unexpected theorem namespace for mask {mask}")
        decl = declaration(text, short, entry["source"])
        require(source_namespace(text, decl.start()) == "Jsp404.SixExactFloorKernel",
                f"Leaf theorem is declared in the wrong source namespace: mask {mask}")
        require(compact(decl.group("signature")) == expected_leaf_signature(mask),
                f"Leaf signature mismatch for mask {mask}")
        signature_evidence.append({
            "mask": mask, "source": entry["source"], "theorem": entry["theorem"],
            "line_start": line_number(text, decl.start()),
            "line_end": line_number(text, decl.end()),
            "source_sha256": entry["source_sha256"], "freeze": entry["freeze"],
            "freeze_sha256": entry["freeze_sha256"], "exact_signature_match": True,
            "source_namespace_match": True,
        })
        registry[mask] = entry
    require(len(registry) == 62, "Registry does not contain 62 typed leaves")
    imports = re.findall(r"^import\s+(\S+)\s*$", source, re.MULTILINE)
    require(len(imports) == len(set(imports)) and set(imports) ==
            {entry["module"] for entry in registry.values()}, "Terminal imports differ from registry")

    lines = source.splitlines()
    body_start_index = source[:public_decl.end()].count("\n") + 1
    parsed, body_end_index, split_evidence, leaf_evidence = parse_lean_body(
        lines, body_start_index, registry
    )
    require(compact("\n".join(lines[body_end_index:])) ==
            "#printaxioms" + public_short + "endJsp404.SixExactFloorKernel",
            "Unexpected source following the public proof")
    data = json.loads(local_path(manifest["coverage_tree"]).read_text())
    require(parsed == data["tree"], "Actual Lean proof tree differs from saved JSON tree")
    stats, masks, depths, coverage = audit_tree(parsed, leaf_evidence)
    require(masks == set(registry), "Registered masks differ from actual orientation leaves")
    require(data["coverage"] == {**stats, "full_arms_covered": 1024},
            "Saved coverage statistics differ from independently computed statistics")
    require(manifest["coverage"] == {**stats, "all_1024_arms": True},
            "Manifest coverage statistics differ from independently computed statistics")

    return {
        "audit": "independent_six_symbolic_between_static_20261006b",
        "status": "PASS", "scope": "Static source/coverage/signature audit; no Lean execution",
        "audit_script_sha256": sha(Path(__file__)),
        "manifest": {"path": MANIFEST, "sha256": sha(manifest_path)}, "hashes": hashes,
        "public_contract": {
            "theorem": PUBLIC, "source": TERMINAL,
            "line_start": line_number(source, public_decl.start()),
            "line_end": line_number(source, public_decl.end()),
            "statement": "forall n >= 4, ModelSix n, HIGH, defects(2,3,*,3,2) => False",
            "exact_signature_match": True, "row2_unrestricted": True,
            "source_namespace_match": True,
            "caller_orientation_assumptions": 0,
        },
        "model_triangle_evidence": {
            "source": MODEL, "sha256": sha(local_path(MODEL)),
            "line_start": line_number(model, triangle.start()),
            "line_end": line_number(model, triangle.end() - 1),
            "exact_inequality_semantics_match": True,
        },
        "coverage": {
            **stats, "full_arms_covered": len(coverage), "each_arm_covered_once": True,
            "badprefix_covered_arms": sum(item["covered_arms"] for item in leaf_evidence
                                           if item["kind"] == "badprefix"),
            "badprefix_depth_counts": dict(sorted(depths.items())),
            "independently_enumerated_acyclic_masks": sorted(masks),
            "all_cores_scoped_and_cyclic": True, "first_cycle_pruning_matches": True,
            "actual_lean_tree_equals_saved_json": True,
            "triangle_bit_order": [list(triple) for triple in TRIPLES],
        },
        "registry": {"signatures_checked": len(registry),
                     "independent_sources": len(scanned_sources),
                     "independent_freezes": len(freeze_paths),
                     "all_source_and_freeze_hashes_match": True,
                     "all_exact_leaf_arguments_match": True},
        "forbidden_token_scan": {
            "scope": "Terminal and the 56 distinct registered leaf source files",
            "files_scanned": 1 + len(scanned_sources),
            "tokens": ["sorry", "admit", "native_decide", "axiom", "newaxiom"], "hits": [],
            "entire_transitive_import_tree_scanned": False,
        },
        "source_line_evidence": {
            "proof_line_start": body_start_index + 1, "proof_line_end": body_end_index,
            "total_source_lines": len(lines), "splits": split_evidence,
            "leaves": leaf_evidence, "leaf_signatures": sorted(signature_evidence,
                                                               key=lambda item: item["mask"]),
        },
    }


def main():
    try:
        result = audit()
        code = 0
    except Exception as error:
        result = {"audit": "independent_six_symbolic_between_static_20261006b",
                  "status": "FAIL", "error_type": type(error).__name__, "error": str(error),
                  "scope": "Static source/coverage/signature audit; no Lean execution"}
        code = 1
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return code


if __name__ == "__main__":
    sys.exit(main())
