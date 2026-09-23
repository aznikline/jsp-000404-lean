# Remote matrix

| ref | SHA | role |
|---|---|---|
| `origin/lane/integration` | 9945ee8bd25ed3520aa89a063493cf3398e6f884 | semantic base (INTEGRATION_BASE_SHA) |
| `origin/agent/jsp404-angle-cert-goal-01-owner` | 9ae823086d0a13d8f0d98545c9346a73c4e7938b | certB source (CERT_SOURCE_SHA) |
| `origin/lane/l1-lowp` | 2e19fd3f57ab1b7e9acf00e92e763f16f54db060 | partial scan only (~17k/85536), no Lean selection |
| `origin/lane/v1-vacuum` | 2c1c0d4ad478d6e141fdf7f24a6346e06af2fb13 | claimed counterexample actually equality W=5/2 — not a refutation |
| `origin/agent/jsp404-maxgap-emission-02-spec-audit` | (new, audit lane) | maxgap spec audit; original statement FALSIFIED |
| `origin/goal/jsp404-completion` | 0ceac4d (moved during session) | shared goal branch — not ours |

Working: `agent/jsp404-proof-convergence-02-owner` in
`D:/op/sunyuchen/jsp-000404-pc02` (worktree), merge-base with cert
source `ccc95c09a406d71a8871b971758a622d9c7dbc46`.

## L1 / V1 / MAXGAP assessment

- L1: mid-campaign scan, no Lean selection theorem — reuse
  FANLINK/FANLINK2/LINK evidence only; do not resume the big scan.
- V1: the listed `k=[3,3,1,1], d=[0,0,2,2], W=5/2` is equality at the
  cap, not a violation — do not formalize it as a counterexample.
  Negative q cells are normalized away by `ProperGaps.ModeA.normalize`
  / `exists_nonnegative_model`; they are not geometric-capacity
  counterexamples per se.
- MAXGAP: audit closed; `maxGap_boundary_emission` FALSIFIED
  (s=2 unconditional, s=3 conditional, s=4 square).  On the forbidden-
  dependency list; the parameter-aligned candidate remains
  FROZEN/UNPROVED.
