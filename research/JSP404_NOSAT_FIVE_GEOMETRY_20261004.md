# Actual LOW five-point exclusion

The first LOW no-saturation minimal profile `(s,r)=(5,4)` is excluded by
actual point geometry. The exported statement is stronger: at floor
`pi/lambda = 3` and `lambda > 2*pi/7`, an actual legal five-point
configuration cannot have four positive rows, regardless of the fifth
row's score. No minimality, saturation, zero-score, or deletion condition
is required by the exported theorem.

## Proof route

1. Every positive projective row has a cyclic gap of size at least
   `2*lambda`. Cutting immediately after that gap gives an occupied
   reference ray and a complementary projective window of width at most
   `pi-2*lambda`. The cut and all retained rays are actual list entries;
   multiplicities and a full-circle wrap are retained.
2. `ActualProjectionOrder.exists_ordered_config` constructs a bijection
   of the actual centers so every chord from a smaller index to a larger
   index has its actual oriented direction equal to its projective
   representative in `[0,pi)`. The order uses actual vector addition and
   the legal triangle cap. Zero representatives are permitted.
3. For `i<j<k`, write `x=phi(i,j)`, `y=phi(i,k)`, and `z=phi(j,k)`.
   Actual vector addition puts `y` strictly between `x` and `z`; the cap
   at `j` gives `abs(z-x)>=lambda`. The caps at `i` and `k` additionally
   give `abs(y-x)<=pi-lambda` and `abs(z-y)<=pi-lambda`.
4. These complete three-cap constraints and the four occupied-cut
   windows instantiate `NoSatFiveTerminal.FiveModel`. The generated
   finite terminal contains ordinary case splits and `linarith` proofs.
   The diagnostic selected branches; no solver result is a Lean axiom
   or proof certificate.
5. Positive scores remain positive when the actual points are
   bijectively reindexed, by the existing injective-restriction theorem.
   The terminal is therefore consumed on the original actual points.

Omitting the two endpoint caps in step 3 admits angular diagnostic
models. Such models do not refute the actual five-point statement; they
fail constraints that follow from the original legality contract.
For example, the LOW control has `p=83/24`, `phi(0,2)=27/8`, and
`phi(1,2)=1/24`. At vertex 2 of triangle `(0,1,2)`, the model therefore
gives angle `27/8-1/24=10/3`, whereas legality requires at most
`p-1=59/24`. This single endpoint already rules out that angular witness
as an actual legal configuration. The exact control is recorded in
`research/JSP404_N3_NOSAT_ENDPOINT_CAP_CONTROL_20261004.json`.

## Kernel verification

`Jsp000404/NoSatFiveGeometry.lean` passed `--trust=0`, without warnings or
errors. Five printed declarations, including
`five_centres_four_positive_impossible` and
`five_positive_card_le_three`, use only
`[propext, Classical.choice, Quot.sound]`. The actual source exports no
new axiom and contains no `sorry` or `native_decide`.

The check log is `/tmp/jsp404_nosat_five_geometry_trust0_20261004.log`.
The target build also completed successfully, with 8,967 jobs and no
warnings. The checked geometry source has SHA-256
`0aaac4c71b95c3676bf2a16804e56a5d1e06935be4c086fbdd22f9add73c39f6`.
The separate finite terminal was also checked under `--trust=0` with
the same three axioms. This proves the LOW five-point exclusion; it does
not close the remaining LOW profiles or the original all-N theorem.
