# Actual third-strip six-point exclusion

`NoSatSixGeometry.six_centres_five_positive_impossible` proves that an
actual legal six-point configuration with `floor(pi/lambda)=3` cannot
have five positive rows. This is a statement on the original points;
the caller supplies no scalar model, ordered-coordinate, saturation,
zero-score, deletion, or minimality premise. It holds on the entire
third strip, including LOW and HIGH.

The proof reuses the actual occupied-cut and complete three-angle-cap
extraction from `NoSatFiveGeometry`. `ActualProjectionOrder` constructs
a bijective point order whose forward chords lie in `[0,pi)`. All
triangle caps, strict chord betweenness, and positive-row occupied cuts
instantiate `NoSatSixTerminal.SixModel`. The terminal's arithmetic
branches are ordinary Lean proofs; diagnostic results are not axioms
or certificates.

The terminal was split into independent profile lemmas to keep proof
checking manageable. The final public theorem retains the exact whole
strip `3*lambda<=pi<4*lambda` contract and permits zero projective
representatives. It was checked under `--trust=0`, with no warnings,
and uses only `[propext, Classical.choice, Quot.sound]`.

The actual extractor also passed `--trust=0` without warnings or errors.
Both printed declarations, `six_centres_five_positive_impossible` and
`six_positive_card_le_four`, have the same three standard axioms. The
geometry source is 139 lines, with SHA-256
`c56985ff7c77676bb81a1613e25a3190433fbff2b5ccb076897f439f22114dcc`.
The exact log is `/tmp/jsp404_nosat_six_geometry_trust0_20261004.log`.
The actual extractor's target build also completed successfully, with
8,969 jobs. The build log is
`/tmp/jsp404_nosat_six_geometry_build_20261004.log`.

Consequently the first HIGH minimal no-saturation profile `(s,r)=(6,5)`
is excluded. The proof can also be applied to an actual six-point
restriction of a larger configuration: retained positive rows remain
positive, so configurations with at least six points have at most four
positive rows. The latter restriction consumer is implemented separately
in `N3PositiveBounds`; it is not an assumed premise of the six-point
theorem. The original all-N proof still requires the remaining profiles
and higher-strip reductions.
