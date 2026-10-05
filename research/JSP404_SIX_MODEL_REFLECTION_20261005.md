# Necessary six-centre model reflection

Source: `Jsp000404/SixModelReflection.lean`.

For every existing necessary scalar `SixModelCompression.ModelSix n`, set
`K = (n : ℝ) + 2 * M.delta` and construct:

```text
reflectedModel M : ModelSix n
theta' i = M.delta - M.theta i.rev
d' i j = K - M.d i.rev j.rev
rowxs' i = (M.rowxs i.rev).reverse.map (fun x => K - x)
```

The proved public preservation interface is:

```text
reflectedModel_rowDefect (M : ModelSix n) (i : Fin 5) :
  rowDefect (reflectedModel M) i = rowDefect M i.rev
```

## Mathematical dependencies

- `linearGaps_reflect_reverse` proves an exact list equality: the actual
  consecutive gaps of the reflected row are the reverse of the original
  gap list. This includes both endpoint gaps and requires neither sorted
  rows nor distinct chord values.
- `linearGapScore_reflect_reverse` applies the actual `gapScore lam` to
  this whole list for arbitrary `lam`. Reversing the list leaves the sum
  unchanged. The proof retains multiplicities and zero gaps.
- `erase_finRange_rev_perm` proves that the four actual row indices after
  removing `i.rev` are a permutation of the reverse images of the four
  indices after removing `i`. The index list is distinct; chord values
  need not be distinct.
- The construction preserves `delta`, its actual bounds, `n`, and `hn`.
  `Fin.rev` reverses theta order and subtraction reverses it back.
- The old corridor for `j.rev < i.rev` supplies the new lower bound from
  its upper bound, and the new upper bound from its lower bound.
- The old triangle on `k.rev < j.rev < i.rev` exchanges the outer chords
  relative to the new triple. Complementing all three chord values by
  `K` reverses those inequalities again. Each old arm therefore supplies
  the same new arm.
- For the old row interval `L = theta(i.rev)` and
  `R = L + ((n : ℝ) + delta)`, the reflected interval is
  `[K-R, K-L] = [theta' i, theta' i + ((n : ℝ) + delta)]`.
  Equality of full scores is proved before taking `n - score`, so natural
  subtraction introduces no weaker preservation claim.
- `reflectedModel_twice_rowDefect` applies this equality twice and uses
  `Fin.rev_rev`, recovering every original row defect.

## Scope

This is a mathematical symmetry tool for the existing necessary scalar
model. It does not construct reflected planar point coordinates, prove
that an arbitrary scalar model is geometrically realizable, or close any
all-`n` geometric exclusion. The equality concerns all five non-anchor
rows carried by `ModelSix`; it does not add a sixth anchor row to that
structure. Any exceptional row changes rank under `Fin.rev`.

No external solver, successful numeric diagnostic, custom axiom,
`sorry`, `admit`, or `native_decide` is used. Existing geometry bridge
sources, root imports, global audit files, and producer sources remain
outside this change.

## Verification

Static independent review found no algebraic, endpoint-gap, or
multiplicity defect. The final source passed its isolated strict-0
scope check and generated the real `.olean`:

```text
/usr/bin/time -l lake env lean --trust=0 Jsp000404/SixModelReflection.lean \
  -o .lake/build/lib/lean/Jsp000404/SixModelReflection.olean
exit code: 0
real: 4.43 seconds
maximum resident set size: 3104407552 bytes (approximately 2.89 GiB)
peak memory footprint: 138355416 bytes (approximately 132 MiB)
swaps: 0
```

The maximum RSS exceeded the requested 2.5 GiB ceiling; the short process
had already finished before the next poll, so there was no remaining
compile process to stop. This observation was reported to the root agent.
No full Lake build or concurrent scope process was launched by this owner.

The printed axiom sets for all six principal interfaces are exactly the
standard `propext`, `Classical.choice`, and `Quot.sound`:

- `linearGaps_reflect_reverse`
- `linearGapScore_reflect_reverse`
- `erase_finRange_rev_perm`
- `reflectedModel`
- `reflectedModel_rowDefect`
- `reflectedModel_twice_rowDefect`

The two local list helpers are consumed by these checked interfaces.
There is no custom or recovery axiom in the successful final output.
