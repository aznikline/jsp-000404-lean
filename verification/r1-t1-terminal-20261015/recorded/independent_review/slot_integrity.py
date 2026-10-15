import pathlib, re, json, itertools

pkg = pathlib.Path('/Users/wizout/op/learn/sunyuchen/.coordination/t1-input/package/Jsp000404')

# canon alternative orders from S7N7Defs
SIG2_ALTS = ['H_L', 'H_I', 'H_R', 'M_LI', 'M_LR', 'M_IR']   # msig2_7_canon_of_pos
SIG1_ALTS = ['L_0', 'L_I', 'L_R']                            # msig1_7_canon_of_pos

# spec table: cert file -> (s2 rank, s1 ranks) in rank order rows
SPECS = {
    'R1CertT1_20_12_14.lean': {'rows': [(2, 0), (1, 2), (1, 4)]},   # (sig, rank) in rank order
    'R1CertT1_11_23.lean':    {'rows': [(1, 1), (2, 3)]},
    'R1CertT1_13_24.lean':    {'rows': [(1, 3), (2, 4)]},
    'R1CertT1_22_14.lean':    {'rows': [(2, 2), (1, 4)]},
    'R1CertT1_21_15.lean':    {'rows': [(2, 1), (1, 5)]},
    'R1CertT1_11_13_25.lean': {'rows': [(1, 1), (1, 3), (2, 5)]},
}

def key_token(sig, rank):
    return str(sig) + str(rank)

report = {}
all_ok = True
for cert, spec in SPECS.items():
    txt = (pkg / cert).read_text()
    # ordered list of exact leaf calls
    calls = re.findall(r'exact (r1l7_[A-Za-z0-9_]+)', txt)
    rows = spec['rows']
    # expected canon product in order
    alts = [SIG2_ALTS if s == 2 else SIG1_ALTS for s, r in rows]
    expected = list(itertools.product(*alts))  # major = first row
    n_slots = len(expected)
    ok_count = 0
    problems = []
    if len(calls) != n_slots:
        problems.append('slot count %d != expected %d' % (len(calls), n_slots))
    for i, (call, exp) in enumerate(zip(calls, expected)):
        name = call[len('r1l7_'):]
        toks = name.split('_')
        # key = leading numeric tokens; canon = the rest
        j = 0
        while j < len(toks) and toks[j].isdigit():
            j += 1
        key_toks = toks[:j]
        canon_toks = toks[j:]
        # decode key: each key token must be str(sig)+str(rank) for a row of the spec, in rank order
        rows_by_rank = {r: s for s, r in rows}
        try:
            decoded = []
            for kt in key_toks:
                s, r = int(kt[0]), int(kt[1:])
                decoded.append((s, r))
            # decoded rows must be a subsequence of spec rows in rank order, with correct sig
            it = iter(rows)
            for dr in decoded:
                if dr not in rows:
                    problems.append('slot %d: key row %s not in spec %s' % (i, dr, rows))
                    break
        except Exception as ex:
            problems.append('slot %d: key decode error %s' % (i, ex))
            continue
        # canon tokens: for each decoded row (in order) take its canon (2 tokens each)
        exp_for_key = []
        for dr in decoded:
            idx = [r for s, r in rows].index(dr[1])
            exp_for_key.extend(exp[idx].split('_'))
        if canon_toks != exp_for_key:
            problems.append('slot %d: canon %s != expected %s (key %s)' % (i, '_'.join(canon_toks), '_'.join(exp_for_key), '_'.join(key_toks)))
        else:
            ok_count += 1
    status = 'OK' if not problems and len(calls) == n_slots and ok_count == n_slots else 'PROBLEM'
    if status != 'OK':
        all_ok = False
    report[cert] = dict(slots=len(calls), expected_slots=n_slots,
                        canon_ok=ok_count, status=status, problems=problems[:6])
    print(cert, 'slots', len(calls), 'expected', n_slots, 'canon_ok', ok_count, '->', status)
    for p in problems[:6]:
        print('    !', p)

print()
print('ALL CERTS SLOT/CANON/KEY INTEGRITY:', 'PASS' if all_ok else 'FAIL')

# also: key value decode table for evidence
keys_seen = set()
for cert in SPECS:
    txt = (pkg / cert).read_text()
    for call in set(re.findall(r'exact (r1l7_[A-Za-z0-9_]+)', txt)):
        toks = call[len('r1l7_'):].split('_')
        j = 0
        while j < len(toks) and toks[j].isdigit():
            j += 1
        keys_seen.add(tuple(toks[:j]))
print('distinct keys used across certs:', len(keys_seen))
print(sorted('_'.join(k) for k in keys_seen))
