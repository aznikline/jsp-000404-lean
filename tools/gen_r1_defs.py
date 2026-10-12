#!/usr/bin/env python3
"""Generate sharded Jsp000404/R1DefsN{P}*.lean — N9/N10/N11 models, row
signatures, canonical multiset signatures and converters for the R1
terminal profiles (9, 10, 11 centres).  Reuses gen_s7_defs.emit_family.

Per family P the emit_family chunk list is sharded into:

  R1DefsN{P}Base.lean     header + chunks[:12]
                          (model structure, mem helpers, RowSig{1,2},
                           CMSig{1,2}_{P}_{cls} abbreviations)
  R1DefsN{P}Conv{kk}.lean header + `import ...Base` + the independent
                          `msig..._of_pos` converter lemmas, 3 per file
                          (2-digit index covering all of them)
  R1DefsN{P}Canon.lean    header + one `import ...Conv{kk}` per conv file
                          + chunks[-2:] (msig{1,2}_{P}_canon_of_pos)
  R1Defs.lean             aggregator: `import ...N{P}Canon` for each P,
                          so `import Jsp000404.R1Defs` sees everything
                          transitively (replaces the old 31k-line monolith
                          that needed `import Mathlib` and blew the 4GiB
                          RSS job cap).
"""
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen_s7_defs import emit_family

# Narrow Mathlib imports — `import Mathlib` maps ~4.3GB of oleans and
# blows the 4GiB RSS job cap.  Every tactic/name used by the emitted
# chunks is covered by these (rcases/obtain live in core Init.RCases,
# List.Perm and the Fin order lemmas are core, simpa/simp/classical are
# core, linarith is Mathlib.Tactic.Linarith, ℝ is
# Mathlib.Basic.Real.Basic, and StrictMono is
# Mathlib.Order.Monotone.Defs.  NOTE: Mathlib.Tactic.RCases does not
# exist in pinned mathlib (rcases was upstreamed to core Init.RCases);
# importing it fails with "unknown module".
MATHLIB_IMPORTS = """import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Fin.Basic"""

HEADER_TAIL = """
set_option maxHeartbeats 1600000

namespace R2N4

open List

"""

# (N, P) pairs: N = P - 2, P = centre count.
FAMILIES = [(7, 9), (8, 10), (9, 11)]

# Number of independent converter lemmas per Conv shard.
CONVS_PER_FILE = 3


def header(extra_imports=()):
    lines = MATHLIB_IMPORTS.splitlines()
    lines += [f"import {m}" for m in extra_imports]
    return "\n".join(lines) + HEADER_TAIL


def write_shard(out_dir, name, extra_imports, chunks):
    txt = header(extra_imports) + "\n\n".join(chunks) + "\n\nend R2N4\n"
    path = os.path.join(out_dir, name + ".lean")
    with open(path, 'w') as f:
        f.write(txt)
    print('wrote', path, len(txt.splitlines()), 'lines')


def main():
    out_dir = os.path.join(HERE, '..', 'Jsp000404')
    canon_mods = []
    for _N, P in FAMILIES:
        chunks = emit_family(_N, P)
        base_chunks = chunks[:12]
        conv_chunks = chunks[12:-2]
        canon_chunks = chunks[-2:]

        write_shard(out_dir, f'R1DefsN{P}Base', [], base_chunks)

        conv_mods = []
        for k, i in enumerate(range(0, len(conv_chunks), CONVS_PER_FILE), 1):
            mod = f'R1DefsN{P}Conv{k:02d}'
            write_shard(out_dir, mod,
                        [f'Jsp000404.R1DefsN{P}Base'],
                        conv_chunks[i:i + CONVS_PER_FILE])
            conv_mods.append(mod)

        write_shard(out_dir, f'R1DefsN{P}Canon',
                    [f'Jsp000404.{m}' for m in conv_mods],
                    canon_chunks)
        canon_mods.append(f'Jsp000404.R1DefsN{P}Canon')

    # Aggregator: three import lines only.
    agg = ''.join(f'import {m}\n' for m in canon_mods)
    path = os.path.join(out_dir, 'R1Defs.lean')
    with open(path, 'w') as f:
        f.write(agg)
    print('wrote', path, len(agg.splitlines()), 'lines')


if __name__ == '__main__':
    main()
