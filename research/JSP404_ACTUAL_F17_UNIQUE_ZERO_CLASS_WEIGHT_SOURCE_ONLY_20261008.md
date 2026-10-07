# Actual F17 unique-zero class weights — SOURCE_ONLY

The new owned source is `Jsp000404/ActualF17UniqueZeroClassWeight.lean`,
209 lines, SHA
`1f04f2f7ab7f1e5047ac73cf3ea243f9e5e88d5fdad577b16d00ffab8dab4801`.
This candidate has not been compiled. No PASS, kernel verification or
complete F17 exclusion is claimed.

The sole public producer is
`Jsp404.ActualF17UniqueZeroClassWeight.exists_actual_unique_zero_interior_class_weight`.
Its arguments, in order, are `o e he H z hz hpositive p hp hnot`:

* H is the original actual n4 LOW whole-band minimum-counter Model to cap16.
* z has original row score zero, and every other original index has
  positive score. These are the actual unique-zero subcase premises.
* p has original score one and is not a full-original-hull vertex.

No actual partition, class sets, cardinality, potential, weight budget,
gain array, hull window or deletion capacity is a caller input. No model
is inherited by a deleted configuration. The construction does not
assume that the unique zero is on the original hull.

The returned `Data o e c lam z p` structure is generic in `c : Fin t → Plane₂`.
Its actual partition comes from the checked general
`ActualInteriorOnePartition.actualPartition`. The plain original-index
class sets and their membership/disjointness bridges use the checked
generic helpers in `ActualF18ClassWeight`; its F18 producer and its
four-per-class conclusion are not invoked.

The public Data fields are:

* `partition`, `score_one`, `classMembers`, `mem_iff`, `ne_center`, `disjoint`;
* `weight_sum`: the three original class weights sum to fifteen;
* `weight_ge_three`: every class has original weight at least three;
* `weight_ge_four_of_zero_not_mem`: a class not containing z has weight
  at least four;
* `pair_weight_ge_seven`: any two distinct classes have total weight at
  least seven;
* `weight_le_eight`: every class has weight at most eight.

Here all weights are `ActualF18ClassWeight.originalWeight`, the generic
sum of `2^original_score` on an original-index Finset. The namespace does
not imply an F18 premise or an F18 mass value.

The proof separates singleton and nonsingleton classes. A singleton
actually emits at the original observer p by the partition's actual
different-class angle bound. If its target score is zero, the original
critical form internally makes that incoming gain zero. If its target
score is one, the newly checked `ActualF17PositiveObserverZeroGain`
producer makes the gain zero because p is an original positive observer.
Consequently a singleton must have score at least two and weight at least
four. A heavy singleton is deliberately retained as a legal case.

For a class S with at least two indices, the unique-zero pointwise bound
gives

`2*S.card ≤ originalWeight(S) + indicator(z∈S)`.

Thus its mass is at least three if it contains z and at least four
otherwise. This permits a class `{z, light}` of mass three and does not
silently replace it by the F18 lower bound four. Disjoint classes cannot
both contain z, so any pair has mass at least seven. The checked critical
reduction derives original potential seventeen; removing center p of
weight two leaves original class mass fifteen. Subtracting the other two
classes' at-least-seven mass bounds each individual class by eight.

The separately discussed consequences — mutual nonapex for distinct
original score-one interior points, disjoint apexes and original-hull
membership except for z — are not declarations in this file. A later
consumer may use this Data after actual strict and genuine normal checks.
The four Z=1 profiles and all-zero N=17 remain unexcluded here.

Only this new source and this new note were written. Existing PASS
sources, actual definitions, receipts, Root files and Seven's pilot files
were not changed. No Lean, Git, solver, quota or installation operation
was run for this SOURCE_ONLY preparation.
