# Same-side two-in — AIR discovery analysis (2026-09-28)

Tool: `tools/same_side_two_in_branch.py` (z3 branch synthesis).
Outputs: `research/SAME_SIDE_FF_LEAVES_n{3,4}.txt`.

## Setup (five-point R=3 SatChart)

h defect ≥3, a b t defect 2.  F/F = ShortWitness a→h, b→h both landing
in h's F window `[θ_h+λ, β+λ)`.  Sender short-last is impossible
(needs φ > θ+π−λ ≥ π−λ but F window < β+λ < π−λ), so senders are
forced short-first → `Up(h,a)`, `Up(h,b)` forced.

`two_in_F_above` gives `φ_ha < φ_hb < φ_ht` and defect(h) = 2+μ.

## Enumeration result (n = 3,4,5,6 uniform)

16 orientation patterns for the four free chords
{h,t},{a,b},{a,t},{b,t}:

- 12 die to up_trans transitivity/up_not_both.
- 4 survive orientation layer.

Adding per-row defect equations (gapScore floors over the lifted row
interval, defect 2/2/2 on a/b/t, defect 3 = μ=1 on h, anchor defect 1):

- **LEAF 2,3,4: UNSAT — dead by pure direction+score arithmetic.**
  No new geometry needed for these in Lean; each dies once its forced
  row orders are fed into `row4_defect` + floor counting.
- **LEAF 1: SAT — the unique residual.**

## LEAF 1 (the only survivor)

Edges: `a→b, h→a, h→b, t→a, t→b, t→h` (t is an Up-source to all).
Forced row orders (all raw, no lifts, no ambiguity):

```
h: θ_h < φ_ha < φ_hb < φ_ht
a: θ_a < φ_ha < φ_at < φ_ab
b: θ_b < φ_hb < φ_bt < φ_ab
t: θ_t < φ_at < φ_bt < φ_ht
```

Betweenness (resolved): `φ_hb<φ_bt<φ_ht`, `φ_ha<φ_at<φ_ht`,
`φ_at<φ_bt<φ_ab`, `φ_ha<φ_hb<φ_ab`.
Caps (λ-separation): `φ_ht−φ_hb`, `φ_ht−φ_ha`, `φ_ab−φ_at`, `φ_ab−φ_ha`.
Theta: `θ_h<θ_t<θ_b` forced; `θ_a` free.

## LEAF 1 — why direction+score is not enough

z3 finds concrete real-valued certificates (directions + all five
defect equations).  The missing constraint is **distance closure**:
each chord fixes `r_x/r_y = sin(φ−θ_y)/sin(φ−θ_x)`; the six ratios must
be consistent with four actual distances — i.e. for every triple
{x,y,z} the cycle product
`sin(φ_xy−θ_y)/sin(φ_xy−θ_x) · sin(φ_yz−θ_z)/sin(φ_yz−θ_y) ·
 sin(φ_zx−θ_x)/sin(φ_zx−θ_z) = 1`.

Numerics: 16/64 big-gap assignments admit direction+closure+defect
solutions, but every concrete point realization lands on degenerate
boundaries (equal thetas, coincident directions, angle-cap violations).
Verdict: leaf 1 is likely killable by closure+legality interplay, but
needs the sine-rule mechanism formalized — NEW infrastructure, not in
the codebase.

## Lean plan

1. `SameSideTwoIn.lean`: F/F theorem mirroring
   `two_in_mixed_central_exclusion` — derive sender-first +
   `Up(h,a),Up(h,b)`, `two_in_F_above`, orientation case split.
2. 12 transitive kills + 3 score kills → reduces F/F to leaf-1 pattern.
3. Leaf 1: residual — needs distance-closure lemma
   (`sin`-ratio product) or a five-point-specific argument.
   OPEN — the real mathematical frontier.

## L/L

Mirror: `two_in_L_below` exists; symmetric enumeration pending
(run tool with mirrored constraints — sender must be short-last).
