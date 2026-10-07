# AIR CHALLENGE — same-side two-in (F/F, L/L) + indegree ≤ 1

STATUS = PENDING (no real delegation channel; owner self-notes only)

## Scope under challenge

- `tools/same_side_two_in_branch.py` (research-only exact LP checker)
- planned `same_side_two_in_F_impossible`,
  `same_side_two_in_L_impossible`, `same_side_two_in_excluded`,
  `five_point_R3_high_receiver_short_indegree_le_one`

## Specific challenge points

1. Up total-order reduction: does `up_or_up + up_not_both + up_trans`
   really leave exactly 8 leaves for F/F (2 under Up(R,H), 6 under
   Up(H,R))? Any wrap/positional case dropped?
2. `not ShortWitness(R,H)` produces only the two aggregate arc bounds
   `z - theta_R >= lam` and `theta_R + pi - z >= lam`. These must NOT be
   converted into primitive first/last row gaps unless the actual row
   order proves `z` extremal in row R. Audit every use.
3. `row4_eq` adjacency: `five_point_no_adjacent_big` calls must use the
   real row order of the row being scored, not the Up order.
4. Type-I defect-2 rows: the checker enumerates big-gap sets
   {0},{1},{2},{3},{0,2},{0,3},{1,3} — verify nothing silently assumes
   Type II only.
5. Floor boundary arithmetic: `gapScore = floor(x/lam) - 1` truncated;
   `x < 2 lam -> score 0`, `x < lam -> floor 0`. Boundary `=` cases.
6. F/F -> L/L: no unproved reflection transport; L/L needs its own
   `two_in_L_below`-based analysis.
7. dirRep_ne usage: equal `dirRep` at a shared vertex is only known for
   *distinct* endpoint pairs (legal_dirRep_ne); the strictness
   hypothesis `u < v` from sorting the two received directions must be
   justified by `u != v` (legal_dirRep_ne at H) before sorting.
8. Consumer coverage: indegree ≤ 1 must split two witnesses into F/F,
   L/L, F+L — the side classification must come from
   `star_chord_window` + theta ordering, not from consumer hypotheses.
9. Checker trust: LP feasibility is EMPIRICAL/EXACT-DISCOVERY; every
   branch claimed dead in Lean must be re-derived from proved
   inequalities; no SAT branch may be silently dropped.
