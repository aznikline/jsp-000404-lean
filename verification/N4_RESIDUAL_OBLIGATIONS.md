# N4 residual obligations — 2026-10-10

Classification of the remaining `CertExists o e 4 big lam` workload.
`S` = number of saturated centres (defect `1`); `R` = number of
defect-`2` rows. `F` = `potential`. Cap: LOW `16`, HIGH `20`.

The classification itself is bookkeeping, **not** a capacity proof.
Each open cell admits any of three exits: direct capacity bound,
a real `EmissionDichotomy` witness, or a real deletion gain /
`Removable` feeding the induction — no exit is prescribed.

| cell | status | evidence |
|---|---|---|
| LOW, `S ≥ 1` | CLOSED | `potential_le_two_pow_of_saturated` (`δ < 1/2`, any `s`): `F ≤ 16`, over-cap domain empty. |
| **LOW, `S = 0`** | **OPEN — LOW0** | `F > 16` ⇒ no saturated centre. The `17 ≤ F ≤ 20` sub-interval lives here, not in R2-emission scope. |
| HIGH, `S ≥ 2` | CLOSED | `potential_le_high_of_two_saturated`: `F ≤ 20`, any size. |
| HIGH, `S = 1`, `R = 2` | **CLOSED — this batch** | `r2_n4_overcap_impossible`: `F > 20` impossible for `t ≥ 6`; `s ≤ 5` joins the existing small HIGH bounds (`potential_le_high_cap_of_le_five`, `potential_le_high_of_saturated_{small,five}`). |
| HIGH, `S = 1`, `R ≥ 3` | REDUCIBLE | Three defect-`2` rows cannot co-occupy the two extremal θ-slots; general low-defect counting bounds + small-size results expected to close. Not yet proved end-to-end. |
| **HIGH, `S = 1`, `R = 0`** | **OPEN — HIGH-R0** | Unique saturated anchor, no defect-`2` row, `F > 20`. |
| **HIGH, `S = 1`, `R = 1`** | **OPEN — HIGH-R1** | Unique saturated anchor, unique defect-`2` row, tail defect `≥ 3`, `F > 20`. Next target — see below. |
| **HIGH, `S = 0`** | **OPEN — HIGH0** | No saturated centre, `F > 20`. |

Non-obligations recorded so nothing is re-proved:

- `δ = 1/2` belongs to HIGH (`big = true`); no boundary case lost.
- `potential_le_two_pow_of_saturated` already removes **all**
  saturated-centre configurations from the LOW over-cap domain, not
  just R2 profiles — so `17 ≤ F ≤ 20` with a saturated centre is
  vacuous, and no emission construction is owed for it.
- `r2_residual_tail_emission` carries an R2 premise and does **not**
  transfer to non-R2 cells; `tail_weight_ledger` is arithmetic, not a
  geometric emitter; a short chord does not by itself give
  `rowGain ≥ 1`.
- Completing `CertExists o e 4 big lam` closes **only** the `n = 4`
  strip of `GeometricCertificates` (quantified `n ≥ 3`); the
  `sendov_lower` `sorry` at N ≥ 9 requires the remaining strips.

## Next action: HIGH-R1 deletion transfer

Unique saturated anchor, unique defect-`2` row `a`, every other row
defect `≥ 3`, `F > 20`, `t ≥ 7` (for `t = 6` the potential bound is
`8+4+2·5 = 22` — near-critical; small sizes may need dedicated bounds).
Two candidate discharges, both to be verified before being claimed:

1. Delete a tail vertex `Q`. If a surviving row's defect *drops* to `2`
   (gain), the reduced `t−1` profile is R2 or one step from it; if the
   defect-`2` row's defect *drops* to `1`, the reduced configuration
   has two saturated centres — either way the `F > 20` budget collides
   with the `t−1` capacity bounds.
2. If no tail deletion gains, the profile is deletion-stable — the
   tail weight ledger + θ-cluster machinery may exclude it directly.

Failure handling: save the exact countermodel/failed branch rather
than widening the claim.
