# n = 4 actual six-centre between / pure-tail scope

Source: `Jsp000404/N4StrongFourRowGeometry.lean`.

## Exact proved result

For a genuine `SatChart` on six points in strip `n = 4`, assume the anchor
has row defect 1, two non-anchor rows have defect 2, their theta values
surround all three remaining rows, and all three remaining rows have
defect 3. Then `False`.

The public exclusion is
`Jsp404.N4StrongFourRowGeometry.between_pure_tail_impossible`. The caller
supplies actual geometry and actual geometric row defects. It supplies no
scalar model, row permutation, successful solver run, or capacity axiom.

## Provenance of each step

1. `sigma_zero_four_of_between` uses the extracted angle-order bijection
   and strict monotonicity to prove `sigma C 0 = lo` and `sigma C 4 = hi`.
   This ordering lemma is valid for arbitrary `n`.
2. `model_defects_of_between_pure_tail` uses `model_rowDefect` and the
   injectivity of `sigma` to derive the sorted profile `(2,3,3,3,2)`.
   In particular ranks 1 and 3 are proved to be actual tail rows.
3. `between_pure_tail_high_impossible` constructs `SixModelExtraction.model C`
   internally and invokes the ordinary Lean terminal
   `N4StrongFourRowTerminal.four_rows_impossible`. The model's `hdelta`
   comes from `SixModelExtraction.delta_bounds`; the HIGH premise is the
   actual parameter inequality `1/2 ≤ Real.pi / lam - 4`.
4. `potential_eq_twenty_two_of_between_pure_tail` transports the actual
   row scores through the same derived permutation and proves
   `potential lam (directionRows o e c) = 22`.
5. `between_pure_tail_impossible` splits LOW/HIGH internally. LOW consumes
   the existing geometric theorem `potential_le_two_pow_of_saturated`,
   obtaining `22 ≤ 2^4 = 16`, a contradiction. HIGH consumes step 3.
6. `six_centre_n4_pure_tail_outer_class` consumes the existing genuine
   `defect_two_pair_theta_cluster`, transports row defects to its reference
   vector using `rowDefect_directionRow_reference_eq`, and removes the
   between alternative. It retains the all-below and all-above classes.

## Deliberate boundaries

- This closes only the `n = 4`, R2, **between**, **pure defect-3 tail**
  branch. It does not prove all-`n` R2, the full `n = 4` six-centre
  exclusion, the outer theta classes, or the main theorem.
- Merely having any two of the three tail rows of defect 3 is not enough
  to invoke this interface: the terminal needs the specifically derived
  ranks 1 and 3. This implementation requires all three tail rows to be
  defect 3, so those rank premises are genuine conclusions.
- No new `sorry`, `admit`, custom axiom, `native_decide`, or diagnostic
  success hypothesis is introduced.
- No root import, producer source, global audit, or existing research
  document is changed by this scoped work.

## Verification status

The producer reported `N4StrongFourRowTerminal.four_rows_impossible`
strict-0 PASS and provided its real `.olean` dependency. This geometry
file was then compiled in isolation:

```text
lake env lean --trust=0 Jsp000404/N4StrongFourRowGeometry.lean \
  -o .lake/build/lib/lean/Jsp000404/N4StrongFourRowGeometry.olean
exit code: 0
```

All six printed theorem axiom sets are exactly the three standard Lean
axioms `propext`, `Classical.choice`, and `Quot.sound`:

- `sigma_zero_four_of_between`
- `model_defects_of_between_pure_tail`
- `between_pure_tail_high_impossible`
- `potential_eq_twenty_two_of_between_pure_tail`
- `between_pure_tail_impossible`
- `six_centre_n4_pure_tail_outer_class`

The real geometry `.olean` has been generated. No full or heavy Lake
build was launched; root-import and global integration verification are
outside this scoped change and remain the integration owner's work.
