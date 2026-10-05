# Uniform finite fan score stability receipt

Owned source: `Jsp000404/UniformFanScoreStability.lean`. Previously frozen
helper sources were not edited. This lane performs no root import, commit,
or full Lake build. The new uniform source is outside the integration lane's
current frozen-helper publication batch.

The source proves the following complete analytic interface for any finite
row type `R` and one fixed nonempty fan label count `n`:

```lean
exists_uniform_sorted_score_stability
  (hn : 0 < n) (A : ℝ → R → Fin n → ℝ)
  (hcont : ∀ r i, ContinuousAt (fun eps => A eps r i) 0)
  (hrange : ∀ r i, A 0 r i ∈ Set.Ioo 0 Real.pi)
  (hlam : 0 < lam) (htau0 : 0 < tau) (htau : tau < lam) :
  ∃ lam', tau < lam' ∧ lam' < lam ∧
    ∀ᶠ eps in 𝓝 (0 : ℝ), ∀ r,
      rowScore lam' (sortedFan (A eps r)) =
        rowScore lam (sortedFan (A 0 r))
```

Its stronger `exists_uniform_sorted_gap_floor_stability` gives equality
for every actual internally sorted gap floor, with that same `λ'` for every
row. The proof never combines per-row existential scales or assumes score
invariance under changing the scale.

The common parameter is chosen **once**. The source enumerates `R × Fin n`
with `Fintype.equivFin`, flattens all rows' canonical limiting sorted gaps
into a single multiplicity-preserving list, and applies the frozen strict
floor-margin theorem to it. It then derives continuous gap floor events at
that already selected parameter, intersects over finite rows, finite label
permutations, and finite gap indices, and uses each actual `Tuple.sort`.
Every actual sorting permutation sorts the limit on the common event;
permutations may still vary inside repeated limiting classes.

Singleton fans and partially or wholly repeated direction values are
included; the genuine wrap remains `π`. The row type `R` may also be empty,
in which case the flattened list is empty and the resulting universal row
condition is vacuous. No nonempty row-type hypothesis is introduced.

This completes the common-scale analytic bridge only. Actual ray-family
identification, interior seam-safe references, the end-split score identity,
and finite recursive inflation are still separate remaining steps. It makes
no higher-strip or all-`n` capacity claim.

After the integration lane's sequential normal/AX heavy processes ended,
the first single-file `lean --trust=0 -o ...` check passed with **exit zero
in 4.100 s**, no warnings, and a real
`.lake/build/lib/lean/Jsp000404/UniformFanScoreStability.olean`.
Both audited exports printed only `propext`, `Classical.choice`, and
`Quot.sound`. No source-error repair or repeat verification was needed.

Frozen source SHA-256:
`3390aefe8051564a02b36ee15c21232fd29ca57afbf7b84007a279431570f6cb`.
The command, actual captured stdout, source hash, and resource data are in
`.lake/uniform-fan-score-stability-strict-20261005.log`.
`/usr/bin/time -l` maximum resident set size was **3,136,126,976 bytes**;
sampled actual Lean peak **3,058,499,584 bytes**; sampled process-group peak
**3,759,079,424 bytes**. Actual Lean remained below the authorized 3.5 GiB
admission cap; the group sum was recorded only. All compiler processes exited,
and root, integration, and the representative-leaf lane were notified of
resource release. No reset, redemption, or account-quota mutation occurred.

This is a strict PASS for the complete common-scale analytic theorem.
The source is now frozen. Actual fan-family identification, safe references,
end-split scoring, and recursive inflation remain open assembly steps.
