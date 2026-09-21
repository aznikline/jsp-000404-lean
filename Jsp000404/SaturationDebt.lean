import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Saturation-debt certificates — pure arithmetic lemmas

These lemmas are exact rational certificates extracted by
`tools/remainder_check.py` + `tools/exact_verify.py` from the
cell/remainder decomposition of the s = 4, n = 4 Sendov model.
Each is one Farkas combination proving that its integer skeleton
forces `δ ≥ 1/2` — the low-regime phase boundary.

## Model recap (λ-normalised units, so π = n + δ)

* Each fan gap decomposes as `g = q + r` with integer cell `q` and
  remainder `0 ≤ r < 1`.  The `rᵢⱼ` variables below are those
  remainders (`('r', i, j)` in the Python model).
* `fan*` hypotheses are the exact fan equalities: the three gaps at a
  vertex sum to `n + δ`.
* `tri*` hypotheses are the exact triangle equalities: the three
  triangle angles sum to `n + δ`.
* `ang*` hypotheses are triangle-angle upper bounds
  `∠ ≤ n + δ − 1` — the provable `Section4Legality.triAngle`
  contract (mode A).  No angle *lower* bounds appear anywhere:
  those belong to mode B and are not derivable from GA.
* `nn*` hypotheses are remainder nonnegativity `0 ≤ r`.

Hypothesis names record the certificate provenance — `fan` /
`tri` / `ang` / `nn` — matching the `kind` field of
`exact_verify.py --json` output (`fan_sum`, `triangle_sum`,
`tri_angle`, `nonneg`; `mode_b_leak` must be false).
-/

namespace Jsp404

/-- **Certificate A** — skeleton `idxs = [12, 84, 1, 12]` of profile
`(3,2,2,1)` (`tools/exact_verify.py A 12 84 1 12`).

Template: 2 fan equalities − 1 triangle equality + 1 angle upper
bound + remainder nonnegativity, all weighted `1/2`.

Mechanism (the predicted saturation-debt shape): `ang102` is the
bound `∠₁₀₂ ≤ π − λ` unfolded to `r₁₀ + r₁₁ ≥ 1` — the saturated
angle forces remainder debt `≥ 1`; `fan0 + fan2 − tri012` is the
exact identity `r₁₀ + r₁₁ = 2δ − (r₀₂ + r₂₁ + r₂₂) ≤ 2δ`; hence
`1 ≤ 2δ`.  Combined form: `½ − δ + (r₂₁ + r₂₂)/2 ≤ 0`. -/
theorem saturation_debt_A
    (r00 r01 r02 r10 r11 r20 r21 r22 delta : Real)
    (fan0 : r00 + r01 + r02 - delta = 0)
    (fan2 : r20 + r21 + r22 - delta = 0)
    (tri012 : r00 + r01 - r10 - r11 + r20 = 0)
    (ang102 : 1 - r10 - r11 ≤ 0)
    (nn02 : 0 ≤ r02)
    (nn21 : 0 ≤ r21)
    (nn22 : 0 ≤ r22) :
    (1 : Real) / 2 ≤ delta := by
  linarith

/-- **Certificate B** — skeleton `idxs = [0, 36, 15, 2]` of profile
`(3,2,2,1)` (`tools/exact_verify.py A 0 36 15 2`).

Template: 1 fan equality − 2 triangle equalities + 2 angle upper
bounds + remainder nonnegativity, all weighted `1/2`.
Combined form: `½ − δ + r₂₁/2 ≤ 0`. -/
theorem saturation_debt_B
    (r00 r01 r02 r10 r20 r21 r30 r31 delta : Real)
    (fan0 : r00 + r01 + r02 - delta = 0)
    (tri012 : r00 - r10 + r20 = 0)
    (tri023 : r01 - r20 - r21 + r30 + r31 - 1 = 0)
    (ang102 : 1 - r10 ≤ 0)
    (ang302 : r30 + r31 - delta - 1 ≤ 0)
    (nn02 : 0 ≤ r02)
    (nn21 : 0 ≤ r21) :
    (1 : Real) / 2 ≤ delta := by
  linarith

end Jsp404
