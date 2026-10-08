#!/usr/bin/env python3
"""Emit a small test file: header + helpers + needed MSig decls + one leaf."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_n4_leaves as G

def main(cert, keystr, out):
    spec, hasem = G.CERTS[cert]
    key = tuple(int(v) for v in keystr.split(','))
    kinds = set()
    for i, (r, kind) in enumerate(spec):
        kinds.add((kind, key[i]))
    chunks = [G.emit_header(), G.HELPERS]
    for kind, c in sorted(kinds):
        kind2, kk = G.case_of(kind, c)
        if kind2 == 'med':
            chunks.append(G.sig_decl('sig1', kk))
        elif kind2 == 'hi':
            chunks.append(G.sig_decl('sig2', kk))
        else:
            chunks.append(G.sig_decl('sig2', kk))
    core = G.CORES[cert][keystr]
    chunks.append(G.leaf_theorem(cert, keystr, core))
    txt = "\n\n".join(chunks) + "\n\nend R2N4\n"
    open(out, 'w').write(txt)
    print('wrote', out, len(txt.splitlines()), 'lines')

if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2], sys.argv[3])
