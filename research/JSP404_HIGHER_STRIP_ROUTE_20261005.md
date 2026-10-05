# Genuine finite weighted inflation and the remaining higher-strip gap

## Status and scope

The new files `research/JSP404_HIGHER_STRIP_ROUTE_20261005.md`,
`Jsp000404/GapSplitFloorStability.lean`, and the subsequently authorized WIP
`Jsp000404/ActualScorePreservingExpansion.lean` are owned by this lane. Existing shared
sources were read, not edited. No LP, SMT, numerical search, or combinatorial
search was run. The arithmetic file has scoped single-file strict checks;
their results are recorded below. No root import, commit, or full
Lake build is performed by this lane.

**PROVED below means a complete paper derivation, not a claim that the full
geometric inflation theorem has already been kernel checked.** The arithmetic
source is distinguished separately from the still-unformalized geometric
sorting/cluster step. All higher-strip sharp cardinal bounds remain unproved
here. In particular, the same-strip score-zero cardinal bound is not an input
that may silently be assumed.

## The single recommended new geometric lemma

Let `c : Fin s → Plane₂`, `3 ≤ s`, `e ≠ 0`, and
`hleg : Section4Legality c λ`. Put

\[
 k_i=\operatorname{rowScore}_\lambda(i),\qquad
 F=\sum_i2^{k_i}=\operatorname{potential}_\lambda(c).
\]

For every `0 < τ < λ`, there exist

\[
 τ<\lambda_*<\lambda,
 \quad c_*:\operatorname{Fin}F\longrightarrow\mathbb R^2,
\]

such that `Section4Legality c_* λ_*` and **every actual final row has score
zero at `λ_*`**. Thus the final configuration consists of exactly `F` actual
distinct points. It is also legal at `τ` by weakening the angle cap, but score
zero is asserted at `λ_*`, not at an arbitrary much smaller `τ`.

Suggested interface, not yet a Lean theorem:

```lean
theorem exists_exact_score_zero_inflation
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {s : ℕ} (hs : 3 ≤ s) {c : Fin s → Plane₂}
    {lam tau : ℝ} (hleg : Section4Legality c lam)
    (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ lamFinal : ℝ, tau < lamFinal ∧ lamFinal < lam ∧
      ∃ cFinal : Fin (potential lam (directionRows o e c)) → Plane₂,
        Section4Legality cFinal lamFinal ∧
        ∀ j, rowScore lamFinal (directionRow o e cFinal j) = 0
```

This interface uses no saturation, no floor-strip assumption, no defect budget,
and no capacity premise. It is stronger than the `s + #positive` pair expansion
used in the current third strip.

## PROVED: exact one-step split arithmetic

Take a genuine positive-score projective gap `G ≥ 2λ`. Cut immediately after
that gap so its successor is angle zero. The occupied fan lies in
`[0, π-G]`. The explicit axis at projective angle `π-λ` splits the selected
gap into `G-λ` and `λ` and leaves every other nonzero cyclic gap unchanged.

Write `q = floor(G/λ) ≥ 2`. Then

\[
 \left\lfloor\frac{G-\lambda}{\lambda}\right\rfloor=q-1,
 \quad \operatorname{gapScore}_\lambda(\lambda)=0,
 \quad \operatorname{gapScore}_\lambda(G-\lambda)=q-2.
\]

Hence

\[
 \operatorname{gapScore}_\lambda(\lambda)
 +\operatorname{gapScore}_\lambda(G-\lambda)+1
 =\operatorname{gapScore}_\lambda(G).
\]

The gap axis stays at least `λ` from either lift of every old ray. This is
exactly the geometry behind `PositiveSplitAxis.axis` and
`positive_row_exists_both_split_caps`. For score accounting, retain the actual
selected gap and its immediately following cut; the weakened conclusion
“some occupied window has width at most `π-2λ`” alone does not identify the
exact decrement.

Multiplicities cause no exception. Duplicating an occupied direction merely
adds zero gaps, and `rowScore_dedup` removes them. If the whole old multiset
consists of one projective class, its gap list is zeros plus the genuine wrap
`π`; splitting that wrap gives `λ, π-λ`, with the same calculation. Legal
`s ≥ 3` configurations in fact cannot have three collinear centers, but the
arithmetic need not discard the one-class case.

For the later Lean assembly, a general insertion theorem is unnecessary.
After the post-gap cut, the axis `π-λ` is strictly after every occupied ray.
Append it as the last entry. `Deletion.rowScore_eraseIdx'` and
`rowGain_eq_mergeGain` identify removal of this last axis with the old fan
and merge exactly the adjacent gaps `G-λ` and `λ`. The proved end-split floor
identity makes that merge gain exactly one. Deduplication handles external
copies before this argument; the one-class old fan produces a two-entry
child list and satisfies the same deletion interface.

## PROVED: choosing the smaller parameter before actual perturbation

Choose axes at the old parameter `λ`. For each potential child, form its
limiting projective ray multiset:

* a singleton has the old ray to each other parent, repeated according to
  that parent's number of children;
* a paired child has those rays plus its sibling axis. The two signs of that
  axis define the same projective direction.

The singleton limiting score is exactly its old score `k`. Each paired-child
limiting score is exactly `k-1` by the end-split identity. Collect **all** gaps
of **all** these finite limiting multisets, including zero gaps. For each gap
`g ≥ 0`, set `q_g = floor(g/λ)`. We have

\[
 \frac{g}{q_g+1}<\lambda.
\]

Choose one parameter

\[
 \max\left(\tau,\max_g\frac{g}{q_g+1}\right)<\lambda'<\lambda.
\]

Then `g < (q_g+1)λ'`. If `q_g ≥ 1`, the old lower floor bound and the strict
parameter decrease give

\[
 q_g\lambda'<q_g\lambda\le g.
\]

Thus all positive floors have strict margins on both sides. A zero floor
only needs its strict upper margin `g < λ'`; zero gaps also have that margin.
Every old floor is therefore preserved exactly at `λ'`, simultaneously.

Now perturb by the actual points from `ActualPairExpansion.point`. This order
of choices is important: axes depend only on `λ`; next choose `λ'`; last choose
a positive actual `ε`. It is not a circular simultaneous limit.

## PROVED: the correct geometric stability argument

The raw representatives in `[0,π)` are not globally continuous. In particular,
a ray crossing the `0/π` cut makes its representative jump. Therefore one
cannot simply assert that the original `directionRow` or `cycGaps` coordinates
are continuous.

Instead choose a reference cut avoiding the finite union of all limiting
projective classes, for each row if desired. Reference invariance of score is
available in `ChartInvariance.rowScore_directionRow_reference_eq`. In this
chart every external nonzero ray is represented by a continuous real angle
near `ε=0`; the sibling's projective axis is constant. Sort the finite angle
multiset by clusters around its distinct limiting classes. The order inside a
cluster need not stabilize. Its internal gaps tend to zero, while the gap from
the last member of one cluster to the first member of the next tends to their
true projective gap. The wrap gap tends to the true wrap. If there is only one
cluster, all internal gaps tend to zero and the unique wrap tends to `π`.

For each limiting gap with positive floor, the strict margins above ensure
the corresponding actual gap retains that floor for all sufficiently small
positive `ε`. Each zero-floor or internal-cluster gap remains below `λ'`.
Finite intersection gives exact scores in every row. Sorting order statistics
in a fixed chart is another way to formalize this finite-cluster argument;
no fixed ordering of collided ray labels should be assumed.

Intersect this score-stability event with
`ActualPairExpansion.expansion_eventually_legality` at `λ'`, and with
`ε > 0`. The intersection is an actual positive-scale witness. Both paired
children have score `k-1`; all singleton scores are exactly `k`. The existing
`exists_pair_expansion_of_axes` alone is insufficient here because it hides
the perturbation parameter and proves only legality.

The still-unformalized part is precisely this finite projective-multiset
stability statement, followed by the finite simultaneous intersection. The
ordinary coordinate continuity assertion is not substituted for it.

A concrete finite-permutation formalization is now prepared in the new WIP.
For the continuous chart coordinates `a_i(ε)`, finite intersection first
preserves every strict inequality `a_i(0)<a_j(0)`. Therefore every permutation
sorting `a(ε)` for small `ε` also sorts `a(0)`: an inversion of different
limiting classes would persist and contradict sortedness. Equal classes need
not keep their label order. For each fixed permutation the `gapAfter` formula
is continuous, including `a_first+π-a_last` for the wrap; in the one-class case
that limit is exactly `π`. There are finitely many permutations, and all
permutations sorting the limit produce the same sorted value list. One can
therefore intersect the derived floor events for all admissible permutations
and apply the event to whichever permutation sorts the actual rays. This
requires no general claim that the raw changing `cycGaps` coordinates are
continuous and no unproved order-statistics API.

## PROVED: mass preservation and finite termination

Expand every positive-score row, or any nonempty set of them. Reindex with
`ActualPairExpansion.Reindex.indexEquivFin`. If `r` parents were paired, the
new number of points is `N+r`, and

\[
 2^k=2\,2^{k-1}\quad(k\ge1)
\]

makes the total potential **exactly** `F` after the step. Let `D=F-N`. Every
row contributes at least one, so `D ≥ 0`; a nonempty step decreases `D` by `r`.
Consequently there are at most `F-s` steps. When `D=0`, every summand is one,
so all row scores are zero and the actual number of points is `F`.

If all positive rows are expanded simultaneously, the largest row score also
drops by one each nonterminal round, giving the stronger round bound
`max_i k_i`. Every intermediate parameter is chosen above the fixed `τ`, so
the finite recursive construction retains a positive angle margin. It is
exact score preservation, not merely nondecreasing potential, that justifies
both termination arguments.

If the initial configuration is already score zero, no point split is needed.
Apply the finite floor-stable parameter choice to its old gaps and retain the
same points; this supplies a strict `τ<λ_*<λ` and preserves score zero. This
also covers the otherwise exceptional zero-step termination case.

## Actual limitations and concrete failure checks

**Axes must be re-chosen on the actual current configuration every round.**
After one split, a child already sees its sibling along the previous axis.
Reusing that same projective axis in the next round violates the two-sign
cap against that sibling: one angle is `π`. Three or more copies placed on
one original line would in any case violate triangle legality. The recursive
construction instead extracts a fresh positive gap in each actual child's
current row, including all previous siblings. Its new admissible axis is
therefore separated from those rays. This is a geometric requirement of the
proved one-step construction, not an assumption that arbitrarily many points
can be placed on the original axis.

**A generic admissible axis can lose two score units.** Take an isosceles
triangle with vertex angle `2λ`, where `λ=π/5`. Its vertex gaps are `2λ,3λ`,
and score is `1+2=3`. The midpoint of the `3λ` gap is admissible but splits it
into `1.5λ,1.5λ`; the new limiting score is `1+0+0=1`. The end-`λ` splitter
instead gives score two. The existing `Axes` hypothesis, without the chosen
end-split gap data, does not imply the required decrement.

**Current axes do not guarantee legality at the unchanged parameter.** Let
`0 < λ < π/3`, `A=(0,0)`, `B=(1,0)`, and
`C=(1+t cos λ,t sin λ)` for `t>0`. The angle at `B` is exactly `π-λ`.
At `A` the axis `u=(cos λ,-sin λ)` satisfies both current angular caps.
For small `ε>0`, the triangle `B, A+εu, C` has angle at `B` equal to
`π-λ+η`, with `η>0`, and is illegal at `λ`. This refutes unchanged-parameter
legality from arbitrary supplied axes; it does not assert that every possible
sign choice or every same-parameter construction fails. Strict parameter
decrease is sufficient and is supported by the actual expansion theorem.

## What inflation does and does not close

For LOW at strip `n`, choose `τ=π/(n+1/2)`. For HIGH choose
`τ=π/(n+1)`. Both are strictly below the caller's legal `λ`; the constructed
`λ_*` stays in the same original strip because it is below `λ ≤ π/n` and
above the chosen lower boundary. A HIGH caller with `δ≥1/2` also remains HIGH
because lowering `λ` increases `δ`.

Therefore a **separately proved, uniform same-strip** ordinary-point count
bound, even restricted to actual score-zero rows, would yield the full weighted
capacity via `F` distinct points. Conversely the weighted capacity immediately
bounds a score-zero configuration because its potential equals its cardinality.
These uniform assertions are equivalent after inflation. Assuming the count
bound here would thus be circular, not a new proof of all `n`.

The bare Nine/Eleven models use no score-zero premise. Their independent
finite cardinal bounds are valid consumers when already kernel proved.
The first genuinely new strip targets remain the independent 17-point LOW
exclusion at `λ>2π/9` and 21-point HIGH exclusion at `λ>π/5`.

`GlobalFiveLowCapacity` and the original `c₂/c₃` budgets cannot supply those
count bounds just by being renamed. In the final score-zero configuration
all defects equal `n`; positive-score `StrongGapBudget` requires `c<n`, so
the relevant structure has been discharged into the larger actual point set.
`KraftResidual` is exact arithmetic, but it does not independently exclude
the resulting overfull all-defect-`n` profile. `Induction.CertExists` remains
a geometric over-capacity obligation unless an independent count theorem is
available.

## PROVED: what the ordered model's simple binary rank gives

Let `p=π`, and use the complete `htr` alternatives from
`NoSatNineDBMModel` / `NoSatElevenDBMModel`. Put `h=ceil(p/λ)`. Partition
`[0,p)` into `h` half-open intervals of width at most `λ` (or strictly below
`λ` in a noninteger strip).

For a fixed interval, an ordered vertex cannot have both an incoming and an
outgoing edge in that interval: the middle separation in their triangle is
at least `λ`, whereas two labels in the same half-open interval differ by
strictly less than `λ`. Mark a vertex 1 if it has an incoming edge in that
interval, and 0 otherwise. An edge `i<j` in that interval then has bits 0 at
`i` and 1 at `j`. Every pair belongs to some interval, so all vertex binary
words are distinct. Consequently

\[
 s\le2^h.
\]

This is the concrete `EvenCover` / binary-word argument, using only middle
separation. For noninteger strip `n`, it gives `2^(n+1)`, hence **16** in the
third strip, not LOW 8 or HIGH 10. At `δ=0`, `h=n` and it does give `2^n`.

The missing half/integer improvement is not automatic merging of direction
bins. In an interval of width greater than `λ`, labels `0,λ/2,λ` form a legal
three-edge triangle: middle separation is `λ`, strict betweenness holds, and
endpoint differences are `λ/2`. The merged interval graph is `K₃`, not
bipartite. This is realizable by the two consecutive unit segments of
directions 0 and `λ`; for `λ≤2π/3` all three actual angles satisfy legality.

## PROVED: classic cups/caps length recurrence is weaker

An `m`-point cup or cap has `m-2` consecutive changes of size at least `λ`.
Since its first and last edge labels lie in `[0,p)`,

\[
 (m-2)\lambda<p,\qquad m\le h+1.
\]

The standard recurrence forbidding an `(h+2)`-cup and an `(h+2)`-cap therefore
gives `s≤binom(2h,h)`. In the noninteger third strip this is **70**; at `δ=0`
it is **20**. The simple binary interval argument is already stronger.

The complete endpoint caps do not improve that one-chain cutoff. For
`0≤i<j≤h`, the labels

\[
 d_{ij}=\frac{i+j-1}{2}\lambda
\]

form an `(h+1)`-point pure cup. Middle separation is
`(k-i)λ/2≥λ`; chord labels lie strictly between adjacent labels; maximum
label is `(h-1)λ<p`. Endpoint differences are at most `(h-1)λ/2`, which is
at most `p-λ` when `p≥2λ`. Thus LOW and HIGH have the same permitted longest
cup/cap length in the usual noninteger strip. Merely truncating those lengths
cannot discover the `δ=1/2` change.

Also, the pair “longest cup ending at the vertex, longest cap ending there”
is not an injective vertex rank. The five actual points
`(0,0),(1,3),(2,0),(3,2),(4,3)`, in x order, have both final vertices labelled
`(3,3)` under the ordinary increasing/decreasing-slope chain definition.
All triples are noncollinear, so sufficiently small positive `λ` makes this
a genuine legal complete model. The classical recurrence uses finer
edge/chain information, not this false two-dimensional vertex injection.

## CONJECTURAL: the sharp ordered-model improvement

No general triangle-order potential proving the sharp constants was obtained
in this lane. A new invariant would have to use the endpoint numerical caps
together with cross-boundary chord betweenness, rather than middle separation
or longest-chain lengths alone. The explicit arithmetic target is to exclude
half of the `h=n+1` binary words in LOW and all but
`5*2^(h-3)` words in HIGH. Nine/Eleven certify those consequences for `h=4`;
they do not constitute a recurrence for arbitrary `h`.

In particular, simply restricting label diameter from `p` to `p-λ` does not
produce a complete capped model with the smaller period. At `λ=1,p=13/4`,
the legal three-point labels `d01=0,d02=2,d12=21/10` already lie in
`[0,p-λ)`, but their endpoint difference 2 exceeds the smaller required cap
`p-2λ=5/4`. Original endpoint caps `p-λ=9/4` are satisfied. Therefore a
period-decrement binary recurrence must prove a new closure property; it
cannot inherit it from interval restriction.

The recommended next formal work is the finite inflation lemma above,
starting with the genuinely exact arithmetic already isolated in
`GapSplitFloorStability`. Its usefulness is a clean actual-point reduction and
independent finite count consumers; it is not a proof of the missing sharp
ordered-model recurrence or all `n`.

## Source dependencies

* `ActualPairExpansion.lean`: actual distinct perturbation points,
  `expansion_eventually_legality`, finite positive scale, and `s+#P` reindexing.
* `PositiveRowFan.lean`: actual positive gap and its post-gap cut, including
  repeated classes and full-circle wrap.
* `PositiveSplitAxis.lean`: explicit rotated axis and both original-ray caps.
* `ChartInvariance.lean`: reference changes preserve actual row scores.
* `Deletion.lean`: `gapScore`, `rowScore_dedup`, and potential arithmetic.
* `NoSatFiveGeometry.lean`: all five ordered-triangle constraints, independently
  derived from actual points.
* `NoSatNineDBMModel.lean`, `NoSatElevenDBMModel.lean`: complete necessary
  ordered models; no row-score capacity is a premise.
* `EvenPartition.lean`, `BinGraphs.lean`: proved binary covering infrastructure.

## Arithmetic validation receipt

The first scoped `lean --trust=0` invocation used `import Jsp000404.Deletion`.
It was terminated by the requested 1 GiB admission threshold after 3.009 s;
peak sampled process-group RSS was 1,104,461,824 bytes. It emitted no proof
result and is **not PASS**. After the heavy N4 check ended, the coordinator
authorized one more scoped check with a 2.5 GiB threshold. The file was reduced
to real-floor/order/tactic imports; `floor_score_end_split` is the exact
gap-score identity written in its definitional natural-floor form, so no
geometric import is needed.
The second check completed with exit 1 after 2.621 s. `/usr/bin/time -l`
reported maximum RSS 1,520,058,368 bytes; the sampled process-group peak was
2,214,035,456 bytes, below the authorized 2.5 GiB threshold. The end-split
floor identity was successfully elaborated and printed only the three
standard axioms. The finite-list statement had a real-cast inference error
and a local name removed by `rcases ... with rfl`; both source errors were
repaired. Multiplication monotonicity is now explicit instead of relying on
nonlinear arithmetic. The repaired finite-list source subsequently passed
the authorized scoped check with exit 0 in 2.669 s, `/usr/bin/time -l`
maximum RSS 1,514,930,176 bytes and sampled process-group peak 2,212,020,224
bytes. All three exports printed only `propext`, `Classical.choice`, and
`Quot.sound`.

The frozen source SHA-256 is
`9b9ac6dc1fa5a55ca4c6e45a4af914f0592b994798b7663005f63737354b1097`.
For the new WIP module's dependency, a scoped strict invocation then produced
the real `.lake/build/lib/lean/Jsp000404/GapSplitFloorStability.olean`, also
exit 0. Its receipt is `.lake/gap-split-floor-stability-strict-20261005.log`:
elapsed 3.416 s, maximum RSS 1,529,085,952 bytes, sampled process-group peak
2,174,697,472 bytes. No source changes followed this freeze.

The full finite geometric inflation theorem is a paper proof only and is not
kernel validated by checking its arithmetic helpers.

## Subsequent geometric WIP scope

`ActualScorePreservingExpansion.lean` currently contains explicit source for:
the projective chart's continuity off imaginary-zero directions; continuity
of actual external perturbation rays in that chart; exact normalization of
same-parent sibling rays at positive scales; preservation of intercluster
orders; the sorting-permutation limit condition; fixed-permutation `gapAfter`
continuity; finite continuous floor stability derived from the proved strict
margins; and intersection of that derived event with the actual legality event
at one positive `ε`.

These statements do not directly assume row-score stability. The finite
permutation collection, identification of the actual direction multiset with
the normalized ray family, generic seam-avoiding reference choice, and the
end-split score assembly remain to be completed before asserting the full
score-preserving or recursive inflation theorem.

The first conservative group-RSS check of this WIP was stopped at 4.061 s
and group RSS 2,714,091,520 bytes; it reached no source verdict. With the
coordinator's corrected per-Lean-process admission threshold, the next check
reached genuine source errors, exit 1 after 5.18 s, `/usr/bin/time -l` max
RSS 2,610,937,856 bytes, sampled Lean peak 2,590,326,784 bytes and group peak
3,291,070,464 bytes. It identified missing dimension-scoped instances, an
unfixed constant parameter, a nonzero-to-positive argument, over-aggressive
`ofFn` simplification, and an under-specified filter. The source has been
repaired accordingly. At that stage the WIP was not PASS, and compilation
paused while the coordinator's import-heavy third-strip adapter finished.
The frozen arithmetic module remained strictly PASS independently of this WIP.

After the adapter passed and exited, two further real source checks reduced
the remaining errors to the wrap branch's `Fin` zero literal versus explicit
zero constructor. The final pre-repair check exited 1 in 3.143 s, maximum RSS
2,614,722,560 bytes, sampled Lean peak 2,614,329,344 bytes and group peak
3,315,793,920 bytes. Eight other declarations printed only the standard three
axioms. The wrap branch was repaired to use an explicit zero index, and
verification waited for the integration lane's N4 normal heavy check to
release its slot. That failing check was not a PASS.

Once the N4 heavy processes finished, the repaired auxiliary module passed
its final real single-file `lean --trust=0 -o ...` check, exit 0 in **3.904 s**,
with **all nine declarations using only the standard three axioms**, no
warnings, and a real `.olean`. Source SHA-256:
`64748afb3537594f93f1ff6f05e751b0a1dbde1c7afcf51cef795f2e5320e48b`.
The actual captured stdout and hash/resource receipt are at
`.lake/actual-score-preserving-expansion-strict-20261005.log`.
`/usr/bin/time -l` maximum RSS was **2,657,337,344 bytes**; sampled Lean RSS
peak **2,575,450,112 bytes**; process-group peak **3,276,292,096 bytes**.
The actual Lean process stayed below its authorized 3.5 GiB admission cap.
All compiler processes exited and the integration lane was notified of
resource release. The auxiliary source is now strictly PASS and frozen;
the full inflation theorem and its missing assembly remain paper-only/WIP.
