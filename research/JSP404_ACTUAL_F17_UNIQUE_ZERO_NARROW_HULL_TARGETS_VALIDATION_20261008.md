# F17 unique-zero narrow hull targets: scoped verification

The final actual source is
`Jsp000404/ActualF17UniqueZeroNarrowHullTargets.lean`, 81 lines, SHA
`354d8a5911424c80aaf70a9a298852173b3e6e7f376dcc9389b638216628f959`.
Strict attempt two and genuine normal attempt one both passed. The sole
selected theorem depends only on `propext`, `Classical.choice` and
`Quot.sound`; both checks have zero own warnings.

The theorem internally defines B as the original score-one full-hull
indices whose actual full pairwise ray angles are at most pi-2*lambda.
Its only mathematical case inputs are the original n4 LOW Model, an
original zero z, and positivity of every original index other than z.
The nonzero direction reference is explicit. No caller supplies B,
its cardinality, a hull type, window, bisector, cone, emitter or gain.

For every q in B, the checked actual hull-cone theorem produces an actual
emitting observer. Every positive original observer has zero gain when
deleting this light target, so the emitting observer must be z. The
conclusion retains both `q!=z` and positive actual gain at observer z
for each actual target q. B is a subset of the already checked actual
positive-gain target set at z, and therefore has cardinality at most four.

The original 59b9 candidate genuinely failed strict attempt one because
the noncomputable finite filter lacked its classical decidability
instance, causing a downstream membership-elaboration error. Its exact
source and complete raw log are retained as NOT_PROVED, including the
diagnostic sorryAx output. Adding explicit classical selection and
unfolding actual membership fixed the API; the predicate, mathematical
premises and conclusion were unchanged. No true parent source was edited.

Passing strict and normal checks took 82.32 and 82.42 real seconds
(guard elapsed 82.537 and 82.607 seconds). The normal run genuinely built
the own target and completed 9071 jobs. Its 469 warning headers are all
inherited. Every attempt preserved source bytes and complete raw output;
the published normal log is a lossless gzip copy. Each guard enforced
8 GiB, 180 seconds and global zero Lean/Lake before launch.

All dispatched processes exited, global zero Lean/Lake was confirmed,
and the sole slot was formally returned to Root before receipt work.
The three true direct parent source hashes still matched their initial
preflight records. The historical SOURCE_ONLY note remains unchanged.

No assertion is made that B is nonempty or contains every light hull
point. The zero z may be original interior, and other original interiors
are not counted or excluded. This one necessary-structure theorem is
not an F17 contradiction, a mandatory deletion selector or completion
of the original problem. Default full build/audit and the 2677 gate
were not modified or rerun by this task.
