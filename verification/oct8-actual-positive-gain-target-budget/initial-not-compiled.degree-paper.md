# Actual outgoing emission degree: bounded PAPER

This note records mathematical proofs and a precise actual implementation
route. No new result is called compiled here. The separately owned
`RowGainCyclicIncident.lean` and `ActualPositiveGainTargetBudget.lean`
are SOURCE_ONLY candidates; old PASS sources and the verified Apex module
were not changed. No Lean, solver, Git or quota operation was run.

Fix an actual observer z. Actual legality excludes three collinear
centers, so its m=N-1 actual projective directions occur at distinct
positions of a full sorted cyclic row. Write its gaps as g_i, indexed
modulo m, including the last-to-first wrap. They are positive and sum
to pi. Equal numerical gap lengths are still different indexed gaps.
Deleting the target at position i merges exactly g_(i-1) and g_i.
Set a_i=g_(i-1)+g_i.

## The degree-four bound

At a zero-score observer all old gap scores vanish, and its deletion
gain is exactly `gapScore(lambda,a_i)`. Thus positive gain is equivalent
to `a_i>=2*lambda`, including equality. No strict boundary replacement
is made. More generally, positive merge gain at any observer already
implies positive score of the merged gap, so the same lower bound holds
without assuming a zero old row or a gain-at-most-one bound.

Every indexed gap has precisely two possible endpoint incidences in
the full cyclic row. Consequently

`sum_i a_i = 2*pi`.

For d distinct emitting targets,

`2*lambda*d <= sum_emitting a_i <= 2*pi`,

so `lambda*d<=pi`. At `lambda>2*pi/9`, this gives d<9/2 and hence d<=4.
Targets do not acquire extra incidences through equal numerical gap
values. The actual direction-to-position map is injective because
actual directions are unique; counting abstract gap values as a set
would lose multiplicity and would not prove this actual target claim.

The full wrap is treated as one gap with two endpoint incidences. For
m=2 its predecessor and successor centers coincide, but the two cyclic
gap positions remain separate. The implementation may directly bound
the target count for N<=5 and use the indexed bridge for larger N.

The scalar bound can have four emitters below pi/4: at lambda=42 degrees,
take a five-entry cyclic row with gaps `(78,6,78,12,6)` degrees. Every old
gap has score zero, and the adjacent-arc sums are `(84,84,84,90,18)`.
There are four positive gains. This is a local scalar row control, not
a certified complete actual legal cloud or an F17 Model counterexample.

## Two stronger PAPER subcases

If lambda=pi/4 and m>=5, the degree is at most three. Four emitters would
need adjacent-arc total at least `8*lambda=2*pi`. Some row position is
not selected, and its two incident positive gaps lose at least one
incidence from the selected sum. The selected sum is strictly below
2*pi, a contradiction. The row-length hypothesis matters.

There is also a stronger interior bound above 2*pi/9, for m>=5. At an
actual original interior observer the twisted flip count is odd and at
least three. Every actual flip gap is at least lambda by actual legality.
At most four fit into total pi, so the odd count is exactly three.

Suppose four targets emit. If any flip gap has an unselected endpoint,
it is counted at most once in their adjacent-arc sum. That sum is then
at most `2*pi-lambda`, while four emissions require at least `8*lambda`.
This would give `9*lambda<=2*pi`, contrary to the strict LOW lower bound.
Thus all endpoints of the three distinct flip edges must be selected.

Deleting the three flip edges from the row cycle leaves three runs.
The number of distinct flip endpoints is six minus the number of
singleton runs. Since m>=5, at most two runs are singletons. Four
selected endpoints therefore force exactly two singleton runs and a
third run of length at least three. Both endpoints of that third run
emit. Their two adjacent-arc inequalities together include its two
boundary flip gaps and two distinct internal endpoint gaps and give
total at least `4*lambda`. The remaining third flip gap is distinct
and at least lambda. These five distinct original gaps force
`pi>=5*lambda`, again impossible above 2*pi/9.

Hence an actual original interior observer has degree at most three
under these hypotheses. This argument in fact never used score zero;
it used only positive-gain arc lower bounds and actual flip incidence.
It remains PAPER: the public odd/ge-three flip producers are checked,
but the exact indexed flip incidence/count packaging is not a new typed
result of this task. The degree-four actual consumer is the current
implementation target.

## Concrete F17 unique-zero consumption and the remaining gap

In an original F17 unique-zero Model, deleting a light target has zero
gain at every positive original observer by the checked positive-observer
leaf. If an original light hull target has actual cone width at most
`pi-2*lambda`, the checked hull-cone emitter producer supplies an actual
emitting observer. That observer must be the unique zero z. Such target
indices are therefore a subset of z's actual positive-gain target set.
The degree-four bound bounds the number of these targets, and the
interior PAPER refinement would lower this to three when z is interior.

The statement is about a fixed observer emitting toward several distinct
deleted targets. It does not bound, or identify, the emitter set after
deleting two targets at once. It also does not assert that every light
hull point has the narrow LB cone. The degree-four numerical LB count
may already follow from a hull-turn budget; the useful additional
information here is the common actual emitting observer and its indexed
target incidence constraint. No Z=1 exclusion or all-zero N=17 selector
is produced merely by this count.

## Public API route and exact bridge

The old file names are `Deletion.lean`, `GeometricDeletion.lean`,
`Induction.lean` and `CircleBound.lean`; there are no existing same-named
`ActualRowDeletion.lean` or `KappaChange.lean` modules in this tree.
The checked APIs reused are `rowGain_eq_mergeGain`,
`incident_gaps_mem_cycGaps`, `deleteIndex_lt`, `eraseIdx_directionRow`,
`cycGaps_eq_ofFn_gapAfter`, `gapAfter_nonneg`, `gapAfter_sum` and
`cycGaps_sum_eq_pi`. Mere membership of the incident gaps in cycGaps is
insufficient to count multiplicity.

The new indexed bridge proves, for the actual full sorted distinct row,

`rowGain(lambda,l,k) = mergeGain(lambda,gapAfter(pred k),gapAfter(k))`.

Its pure assumptions are exactly SortedLE, Nodup, membership in [0,pi),
positive lambda and row length at least two. The predecessor is the
genuine permutation `(finRotate m).symm`. Public List take/drop/head/
getLast identities, already used in the checked merge proof, connect
the rotated-erasure neighbors to these exact indices. A rotated list
is not assumed SortedLE. `Equiv.sum_comp` then supplies the incidence
sum without deduplicating equal gaps. Actual direction uniqueness and
`List.idxOf_inj` connect the target count to the position count internally.
No caller is asked to supply this merge identity or an ordinal bijection.
