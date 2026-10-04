# JSP-000404: uniform four-row core, 2026-10-04

## Exact new result and its limit

The bounded scalar diagnostic can discard **all constraints on the deep row**
for the rank profile `(2,3,*,3,2)`. Splitting the ten triangle orientations first,
and fixing each row's order from those orientations, produced 62 UNSAT cases
with **one symbolic integer `n`, `3 ≤ n ≤ 24`**, rather than a separate run for
every strip and deep defect. There were no UNKNOWN cases; original wall time
was 16.488 seconds. The formerly timed-out case `n=9`, deep rank 2, deep defect 5
is included in this stronger necessary-model exclusion.

This is a diagnostic, **not a Lean proof**. Its source is
`tools/check_uniform_four_rows_20261004.py`; exact coverage is recorded in
`research/JSP404_UNIFORM_FOUR_ROW_DIAGNOSTIC_20261004.json`. Only rank profile
`(2,3,*,3,2)` has this complete 62-orientation run. Other unconstrained ranks and
low-pair placements have not thereby been certified or exhaustively checked.
The input is the necessary shared-chord model, with no planar-realization claim.

## A genuine arithmetic layer now available

`Jsp000404/SixModelBudget.lean` proves the following from the existing
`SixModelCompression.ModelSix`, including its actual sorted row and permutation:

- `cells_le`: the sum of gap floors is at most `n`.
- `support_add_loss`: `B + L = c`, where `B` is active-gap count and
  `L = n - cells`.
- `defect_two_budget`: `c=2` permits exactly `(B,L)=(1,1)` or `(2,0)`.
- `defect_three_budget`: with `n≥4`, `c=3` permits exactly
  `(B,L)=(1,2)`, `(2,1)`, or `(3,0)`.
- `row_budget`: also gives the exact, untruncated `score+c=n` identity.

Its source passed `lean --trust=0`; its target build completed with 3264 jobs.
The five printed key declarations use only
`[propext, Classical.choice, Quot.sound]`. Logs are
`/tmp/jsp404_six_model_budget_trust0_20261004.log` and
`/tmp/jsp404_six_model_budget_build_20261004.log`.
This does not prove the four-row exclusion itself.

## Why the orientation split helps

For each ordered triple `i<j<k`, the existing model gives one of

```
dij+1 ≤ djk, dij < dik < djk
```

or the reverse ordering. Of the 1024 sign assignments, 62 have no directed
cycle in the induced strict orders on the ten shared chords. Each surviving
assignment fixes all five four-chord row orders: no independent 24-way sorting
split is needed. Equivalently, each ordered quadruple's packet
`(abc,abd,acd,bcd)` has at most one sign change. These enumeration statements
are independently checked combinatorics at present; they need ordinary Lean
proofs when used in the final aggregate.

The committed diagnostic convention is **bit 0 = increasing**, bit 1 = decreasing,
with triples in lexicographic order. A separate color-research diagnostic used
the opposite convention; its masks must be complemented before copying them.

Color sorted neighbors of row `i` by `L` for index below `i`, `R` above `i`.
Every color change in the augmented word

```
L | four sorted neighbor colors | R
```

forces a different unit-sized gap. Internal changes use the triangle's unit
separation; the first R uses the lower corridor and the last L uses the upper
corridor. The number of such changes is odd. A defect-two row has support at
most two, so its colors must be `L*R*`: its mandatory gap is exactly sorted gap
index `i`. Consequently a decreasing triangle forces its middle row's defect
at least three. This geometric color lemma is a proposed formal next step,
not a theorem already present in the new arithmetic file.

This gives concrete finite support reduction:

- A defect-two row has five possible supports: its mandatory gap alone or
  with one of the other four gaps.
- A defect-three row with three forced gaps has exactly those three active
  gaps and `cells=n`.
- A defect-three row with one forced gap has eleven possible supports of
  sizes one, two, or three containing that gap.

Interior low rank 1 or 3 leaves 20 of the 62 orientation masks; interior low
rank 2 leaves 15. The endpoint pair `(0,4)` does not prune any mask by this rule.
Thus it is the appropriate hardest first core.

## A small first leaf, with no integer-cut machinery

In diagnostic mask 1, only triangle `012` is decreasing. The induced row 1
order is

```
d12 < d01 < d13 < d14.
```

The lower corridor and two triangle separations force the first three row 1
gaps to reach one. Because row 1 has defect three, `support=3`, `loss=0`, hence
`cells=n`; the remaining two floors vanish. The first three floor lower bounds
telescope to

```
n ≤ d13 - theta1.
```

Other increasing triangles and the upper corridor give

```
d13 < d23,  d23+1 ≤ d34 ≤ n+delta-1+theta4,
theta4-theta1 ≤ delta < 1,
```

so `d13-theta1<n`, a contradiction. In fact `theta4-theta1<1` suffices in the
last step. This excludes this orientation using **only the defect-three row 1**;
its proof can use the new budget file, actual natural floors, and ordinary
`linarith`/`omega`. The proof worker owns the certificate implementation.

## Required certification route

1. Split the ten actual `ModelSix.triangle` disjunctions. Eliminate cyclic
   branches with their ordinary strict inequalities. Either emit the 1024
   finite leaves directly or prove the five packet checks and emit 62 leaves.
2. For each remaining orientation, prove the explicit sorted chord list equals
   the model's row list using its `row_perm`, `row_sorted`, and uniqueness of a
   sorted permutation. Do not add a free floor-vector assumption as the final
   theorem's input.
3. Obtain the actual five floors in each constrained row. Use `row_budget` to
   state `sum floors = n-c+B`. Enumerate the small active support patterns,
   rather than every floor value from zero through 24.
4. Replay each leaf with ordinary inequalities. For a leaf that genuinely needs
   integer cuts, derive the cut using `Nat.floor`/cast arithmetic and `omega`,
   then use `linarith`. A solver's own UNSAT status is never the proof term.
5. Aggregate only after every surviving orientation has a kernel proof. The
   desired first theorem is

```
∀ n, 3 ≤ n → n ≤ 24 → ∀ M : ModelSix n,
  1/2 ≤ M.delta →
  rowDefect M 0 = 2 → rowDefect M 1 = 3 →
  rowDefect M 3 = 3 → rowDefect M 4 = 2 → False.
```

   There is intentionally no hypothesis on row 2. Use the existing actual
   chart extraction and defect-preserving compression only after proving this
   bounded necessary-model theorem. Other low-rank and tail-rank placements
   need their own aggregate theorem or a proved rank symmetry.

## Two routes already ruled out

- Keeping only two defect-two rows is too weak above the bottom strip. At
  `n=9` every tested low-pair placement has an exact necessary-model SAT witness.
  This does not give actual planar counterexamples and does not contradict
  the completed `n=3` geometric terminal.
- Replacing the gap-floor variables by arbitrary reals, even with the support
  condition `q=0 or q≥1`, gives SAT for this four-row core. Therefore the whole
  aggregate cannot be obtained by replaying the continuous relaxation with
  `linarith` alone. The original integer floor semantics must remain in the
  certification interface. Several individual leaves, including mask 1, are
  nevertheless excluded directly by the continuous inequalities.

No original theorem, definition, live AIR checkout, or root import was changed
by this research subtask. No full original proof or prize submission is claimed.
