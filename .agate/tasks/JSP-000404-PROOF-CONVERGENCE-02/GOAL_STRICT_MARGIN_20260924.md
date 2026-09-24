# GOAL — 修正余量目标、严格边际与 R-HIGH1 闭合 (2026-09-24)

Owner branch: agent/jsp404-proof-convergence-02-owner @ fd67929
Integration: lane/integration @ 204f26a (absorbed via 349d3ef)
G3: 83d3dcf ; READY published: 7566549 (batch b2a7c32)

## Lead corrections to previous report (verified against source)

1. `defect_two_rows_le_three` / `exists_two_rows_defect_ge_three` use
   `c : Fin (s+1)` with `hs5 : 5 ≤ s` — domain is m ≥ 5 non-anchor rows,
   i.e. s_total ≥ 6.  Total-5-point residual (m = 4) is NOT covered and
   must be handled separately.  `four_defect_two_tiling` profile is
   (1,2,2,2,2), not (1,2,2,2,3).
2. Correct cap identity (non-anchor rows only, one valid n-bin cover):
   Q = 2^{n-2}, D = Σ2^{2-c_i}, H = 2^n − ΣC_i, S_i = C_i − w_i.
   H + ΣS = (4−D)Q;  HIGH cap ⟺ D ≤ 3 ⟺ H + ΣS ≥ Q.
   Retracted: "ΣS_i ≥ (D−3)Q" as residual target — wrong.
   Exact negative-control check (n=3, c=(2,2,2,3), a=(2,2,2,2)):
   Q=2, Σw=7, ΣC=8, H=0, ΣS=1, D=7/2 — wrong target holds, cap fails.
   Abstract bookkeeping countermodel, NOT a geometric counterexample.
3. Strict-prefix origin is θ_i (the row's own anchor ray), NOT λ:
   rowScore(full row i) = linearGapScore lam (θ_i) (θ_i + π) (row i).
   Local counterexample killing the first−λ variant:
   λ=4π/15, n=3, δ=3/4, θ=0, w=9λ/10, row=[2λ,3λ]:
   bins=[1,2], gapScore(first−λ)=0 but real first gapScore=1,
   score+occ=3=n — no deficit.

## Plan
docs fix → correct strict-prefix lemma (origin θ_i) → geometric supply
→ weighted closure.  m=4 and m≥5 handled separately.
