# JSP-000404 — consolidated status

Updated 2026-10-07 UTC after actual F18 hull/clump/rigidity producers and eight-point rank regions. **PARTIAL COVERAGE.**
The full arbitrary-N theorem and the prize submission are not complete.

The 2026-10-07 hull/deletion publication adds seven verified modules and
27 selected declarations. The 10429-job default build passes once, and the
trust-zero composed audit accepts 756 declarations (749 through the default
root plus seven existing explicit helper imports). Every new source has zero
own warnings; replayed dependency warnings remain in the unmodified raw
output. The original lower/upper gate still fails only for lower `sorryAx`.
Exact frozen sources and lossless stdout archives are recorded in
`research/JSP404_HULL_DELETION_RECEIPT_20261007.json`.

The next actual-producer publication adds eight verified modules and
27 selected declarations, bringing the standard-axiom gate to 783
(776 through the default root plus the same seven explicit helpers).
The default build passes once with 10437 jobs. Four new source warnings
are retained (one in Frame, three in Types); the other six module sources
have zero own warnings. Exact provenance and the unchanged lower-root
negative control are in `research/JSP404_F18_PRODUCERS_RECEIPT_20261007.json`.

Three subsequent standalone modules add ten exact-source strict/genuine-normal
checked declarations: interior-zero three-class geometry, nonacute-heavy
nearest exclusion, and actual window score lower bounds. They are not yet
imported by the default root, so the last composed audit remains 783 and
the last default build remains 10437 jobs. See
`research/JSP404_ZERO_NEAREST_SCOPED_RECEIPT_20261007.json`. No extra full
build is claimed for this standalone publication.

## Current proof boundary

| Obligation | Status | Evidence |
|---|---|---|
| Every N >= 3: sharp upper construction, both bands | PROVED | `UpperBound.sendov_upper`; every epsilon > 0, exactly N distinct points |
| Genuine extremal quantity <= formula | PROVED | `UpperBound.alpha_le_alphaN` |
| Every N from 3 through 16: lower bounds | PROVED | `sendov_lower_le_sixteen`, original `PtCfg` and `alphaN` |
| Every N from 3 through 16: genuine extremal equality | PROVED | `sendov_alpha_eq_le_sixteen`, original `JSP404.alpha` |
| First-strip low/high capacities (n = 1) | PROVED | `SmallStrip.first_strip_capacity_low/high` |
| Second-strip LOW capacity (n = 2), every profile | PROVED | `SecondStrip.potential_le_four_of_second_strip_low` |
| Second-strip HIGH capacity (n = 2), every profile | PROVED | `SecondStripHigh.potential_le_five_of_second_strip` |
| Third-strip LOW/HIGH capacity (n = 3), every actual size/profile | PROVED | `N3HighPairClosure.strip_capacity`, LOW cap 8 and HIGH cap 10 |
| Both original third-strip certificate obligations | PROVED | `N3HighPairClosure.strip_certificates`; actual over-capacity domains are empty |
| Every n >= 3, LOW, three through five actual centers | PROVED | `GlobalFiveLowCapacity.potential_le_two_pow_of_le_five_low` |
| Every n >= 3 LOW actual configuration with an anchor cone below lambda/2 | PROVED LOCAL CAPACITY | `SmallConeLowCapacity`; sharp full original potential bound, no saturated anchor required |
| LOW counterexample has no saturation at rho=pi/(n+1/2) | PROVED NECESSARY CONDITION | Original physical rays are reused at the original parameter; general NoSAT impossibility remains open |
| n = 4 six-center R2 between class, pure defect-3 tail | PROVED | `N4StrongFourRowGeometry.between_pure_tail_impossible`; actual saturated anchor and two defect-2 rows |
| n = 4 pure-tail profile reduces to the two outer theta classes | PROVED | `N4StrongFourRowGeometry.six_centre_n4_pure_tail_outer_class`; no model or solver-success premise |
| Full n = 4 capacity and remaining outer/mixed-tail cases | OPEN | The local between exclusion does not supply these cases |
| n = 5 HIGH necessary four-row scalar domain | PROVED | `SixExactFloorKernel.n5_between_impossible`; all 1024 triangle arms, no mask/acyclic premise |
| n = 5 actual six-center pure-tail between branch | PROVED | `N5StrongFourRowGeometry.between_pure_tail_impossible`; LOW actual potential 44 exceeds cap 32 |
| n = 5 actual pure-tail profile reduces to two outer theta classes | PROVED | `N5StrongFourRowGeometry.six_centre_n5_pure_tail_outer_class`; outer classes remain open |
| Uniform parameter across a finite family of continuous fans | PROVED | `UniformFanScoreStability`; explicit continuous safe-chart coordinate families |
| Two common Boolean coordinates, finite weighted packing | PROVED | `TwoCoordinatePacking`; remaining-bit separation is an explicit input, not yet an actual geometric construction |
| n = 4 minimal tail weight profiles and at-most-five overfull subset | PROVED | `R2CriticalWeightClassification`; finite arithmetic, no geometric capacity assumed |
| Arbitrary-size n = 4 R2 reduced to actual capacity through eight centers | CONDITIONAL | `R2N4FiniteReduction`; finite `hcap8`/`hfinite` premises remain unproved |
| Finite nonnegative gap floor margins and continuous finite fan score stability | PROVED | `GapSplitFloorStability`, `FiniteFanScoreStability`; continuous coordinates and strict `(0,pi)` limiting chart are explicit |
| Necessary scalar reflection preserves all five non-anchor row defects | PROVED | `SixModelReflection`; full gaps, endpoints, zero gaps and multiplicity retained |
| Specified scalar n = 3 terminal ranks | PROVED | `N3SixModelTerminal`: rank 1, rank 3, and simultaneous endpoint defects 2; not all rank placements |
| Actual projective-ray continuity and legality/floor-event helpers | PROVED | `ActualScorePreservingExpansion`; supplied finite pert family is not yet identified with all actual rows |
| Exact actual inflation to the original potential's point count | PROVED | `ActualPotentialInflation.exists_exact_actual_inflation`; threshold < final parameter < old parameter, actual legality/injectivity, no capacity premise or final-score-zero claim |
| Exact actual flat inflation, original F point count and potential | PROVED | `ActualFlatPotentialInflation`; every final row score is zero, strict scale interval retained, no capacity assumed |
| Fixed actual minimum-score deletion normal form | PROVED LOCAL BRIDGE | Explicit cap/divisibility, original over-cap and deleted-under-cap hypotheses give exact excess and zero gains |
| Closest-pair-based triangles empty above lambda > pi/6 | PROVED LOCAL GEOMETRY | `ClosestPairTriangleExclusion`; no fourth center inside any such triangle, no adjacency/merge/bare17 conclusion |
| n=4 full-floor arithmetic and small model branch helpers | PROVED PRIMITIVES ONLY | `N4R2CriticalKernelPrimitives`; the actual eight-point exclusion remains open |
| Actual maximum flat cardinality in a LOW/HIGH band | PROVED COUNTER-REDUCTION | Independent coarse power bounds the discrete cardinalities; an original counterexample supplies a genuine attained maximum |
| Each maximal-band flat deletion has at most one emitter and gain <=1 | PROVED COUNTER-REDUCTION | `FlatBandMaximumDeletion` and `HighFlatFunctionalReduction`; maximality/deletion bound constructed internally |
| Necessary ordered four-packet direction words | PROVED NECESSARY RELATION | `N4R2CriticalKernelPacket`; 16 input arms yield eight words, no inverse realization or eight-point exclusion |
| All natural n>=4 HIGH fixed masks 567 and reflected 821 | PROVED FIXED DIRECTIONS | Six real strict/normal sources; these leaf interfaces retain their explicit ten mask directions |
| Minimum cardinality among actual realizations of a band maximum | PROVED WEIGHTED MODEL | Actual choice at the same potential M; deletions strictly below M, not necessarily below sharp cap |
| Actual emission graph of that model is acyclic | PROVED NECESSARY STRUCTURE | Positive gains strictly increase original scores; no convex-position or point-count conclusion |
| Oriented closest-pair zero-gain outward witness | PROVED LOCAL GEOMETRY | Original scores orient a genuine shortest pair; lam<=pi/4 gives an actual third point beyond the endpoint |
| Fixed actual band-maximum score plateau | PROVED INTERIOR SCALES | For rho<lam'<=lam, rowScore and gapScore are fixed; Flat implies gaps<=2rho, no raw-floor or boundary Flat assertion |
| Five additional fixed representatives and seven legacy adapters | PROVED FIXED DIRECTIONS | Sixteen additional common-profile directions, explicit ten triangle conditions; self-reflected64 is counted once |
| n=4 one 35-direction scalar fixed word | PROVED CONDITIONAL SUBCASE | GenericModel7 4, tail rows2/4/5 defect4 and row6 defect2; no full eight-point exclusion |
| Minimum actual counter-cardinality, then same-cardinality maximum | PROVED ACTUAL COUNTER MODEL | Every actual deletion leaving at least3 has potential<=explicit cap; fixed-card maximum retains the weighted model |
| Critical exact excess at the actual minimum score | PROVED WITH DIVISIBILITY | F=cap+2^k and minimum deletion exactly cap with zero incoming gains; LOW consumer derives divisibility internally |
| Interior center's original full-row defect | PROVED ACTUAL GEOMETRY | Actual triangle/whole-others hull gives rowScore+3<=n and defect>=3 using original cells/defect identities |
| Defect<=2 implies a vertex of the full original hull | PROVED ACTUAL GEOMETRY | Finite separation supplies the full-hull bridge; no arbitrary maximum-score or zero-gain hull claim |
| All natural n>=4 HIGH between profile (2,3,*,3,2) | PROVED SYMBOLIC PROFILE | `symbolic_between_impossible`; internal 1024 arms and all62 surviving directions, row2 arbitrary, no caller-mask or acyclicity premise |
| Actual six-point HIGH saturated-anchor profile (2,3,*,3,2), every n >= 4 | PROVED ACTUAL PROFILE EXCLUSION | `ActualSixBetweenClosure`; saturation internally supplies the chart and rank permutation, with original-reference defects; no full R2 capacity conclusion |
| Closed actual deletion-gap boundary | PROVED FOR FIXED FLAT BAND MAXIMUM | Deleted gaps<=3rho and at most1 row with a strict gap>2rho; no Flat or potential=M at rho |
| Geometric impossibility of the maximal flat functional counter-models | OPEN | The actual reductions do not supply the missing sharp count or capacity proof |
| Actual single-positive-row split with exact potential preservation | PROVED | `SingleSplitScorePreservation`; fresh end axis, safe references, positive epsilon and full actual score table |
| Arbitrary protected actual positions/scores under selective inflation | PROVED | `ActualProtectedInflation`; exact p+(F-protectedMass) actual points, all unprotected final scores0, original F retained, strict parameter interval, including p=0 and p=s |
| Actual n4 HIGH protected scores3,2,2 and F21/F22 | PROVED CONSTRUCTION | `R2N4PureTailInflation`; genuine Fin8/Fin9 with five/six zero-score tails, original protected points and scores retained; no bare exclusion |
| Actual seven-entry row/gap indexing and generic affine cycles | PROVED LOCAL FOUNDATIONS | `N4R2CriticalReifiedRow`/`N4R2CriticalCycleSoundness`; actual permutation and sorting required; one conditional five-arc sample, not all24698 branches |
| Shared finite affine-cycle acceptance and actual scalar-row origins | PROVED LOCAL FOUNDATIONS | `N4R2SharedCycleChecker`; actual row ordering is internal, all seven gaps retained, necessary 28 low alternatives and one conditional nine-arc helper; full word/catalog replay is open |
| Internally chosen 35-bit model word and complete row orders | PROVED SCALAR SEMANTICS | `N4R2ModelWordSoundness`; genuine triangle arms imply sorting, full seven gaps and packet restrictions without caller sorting premises |
| Generic tree, reified arc and shared leaf checks | PROVED CONDITIONAL CHECKER SEMANTICS | Accepted finite data are sound with exact origin/weight/strict-field matching; low ranks 0/6 and defect-4 middle tails are explicit; concrete catalog and full eight-point R2 capacity remain open |
| Pure finite word/checker equality and actual-model transport | PROVED GENERIC BRIDGE | `N4R2ThinWordSoundness`/`N4R2ThinReplaySoundness`; all fields and branch checks match the frozen checker for every word/library; no concrete catalog acceptance assumed proved |
| Two actual nearest-neighbor distance/angle constraints | PROVED LOCAL GEOMETRY | `SharpNearestGeometry`; no three-run extraction or full critical-model capacity conclusion |
| Actual interior score-one containing fan and four-center emissions | PROVED LOCAL GEOMETRY | `ActualInteriorOneNearest`; original full hull constructs the triangle; n4 LOW selected score is exact; four-center positive-gain base does not supply the general nearest exclusion |
| General actual score-one zero-gain witness and closer point | PROVED ACTUAL GEOMETRY | `ActualInteriorOneRuns`; original interior row, lambda > 2*pi/9 and zero gain produce a real half-lambda angle and strict distance decrease; no supplied run model |
| Light nearest neighbors in an actual n4 LOW potential-18 minimum-counter model | PROVED NECESSARY FULL-HULL CONDITION | Minimum score one and strip/defect identities are internal; every weak nearest neighbor is on the original full hull and one is selected by finite real-distance minimization; no F18 capacity closure |
| Selected original n4 LOW interior score-one points number at most four | PROVED ACTUAL CARDINALITY | Actual all-pair angle gap yields double-scale legality; the selected-family consumer measures every score/interior predicate in the original configuration and transfers only actual angles and legality |
| Actual interior score-one three-class partition above lambda > pi/5 | PROVED ACTUAL PRODUCER | `ActualInteriorOnePartition`; internally generated original indices, three nonempty classes, actual same/different/apex angle bounds, and positive original deletion gain for a class singleton |
| Physical ray windows at full original hull vertices | PROVED ACTUAL PRODUCER | `ActualHullRayWindow`; actual endpoint rays, supporting normal and angular coordinates constructed internally from original full-hull membership |
| Original full-hull turn budget and at most eight selected hull vertices in n4 LOW | PROVED NECESSARY STRUCTURE | `ActualHullTurnBudget`; sum(pi-width)<=2*pi; integer budget export additionally requires at least two selected vertices and explicit actual-angle bounds |
| Arbitrary proper actual subset deletion expense | PROVED ACTUAL LEDGER | `ActualProperSubsetDeletionBudget`; every restriction leaving at least three points uses the original minimum counter, and weighted net score growth plus the original excess is at most the original removed weight |
| Two original zero-score deletions in a cap16 minimum counter | PROVED ACTUAL LEDGER | `ActualZeroPairDeletionBudget`; original potential17 is derived, the first deletion has potential16, and the second deletion can raise at most one surviving original zero-score row by one |
| Checked literal row ordering transported to actual full rows | PROVED CONDITIONAL CHECKER SEMANTICS | `N4R2RowDataReplaySoundness`; a checked complete permutation is identified with actual sorted rows before reuse of the verified cycle/leaf semantics; full concrete certificate replay remains open |
| Original n4 LOW F18 weighted profile | PROVED ACTUAL FRAME | `ActualF18Frame`; original scores1/2, heavy original hull membership, at most three heavy points, and N=9-heavy>=6 are derived internally |
| Original hull score-one and score-two cone types | PROVED ACTUAL PRODUCER | `ActualHullSmallScoreTypes`; actual full-row support, LB/LI and HA/HM/HO, physical clumps and original-index witnesses; three style/deprecation warnings retained |
| Original F18 hull light points have actual LI clumps | PROVED ACTUAL PRODUCER | `ActualF18LightHullClumps`; original minimum-score zero incoming gains and actual bisector emission exclude LB internally |
| Original n4 LOW heavy observers emit to no target | PROVED ACTUAL NECESSARY CONDITION | `ActualF18HeavyZeroGain`; generic interface needs no F18 assumption, derives the maximum-score bound and rules out actual Removable via the original minimum counter |
| Original interior-one pure-light classes have at least two points | PROVED ACTUAL NECESSARY CONDITION | `ActualInteriorOneClassSize`; heavy singleton classes remain allowed, and six other points are not falsely excluded |
| Mixed original interior-one/heavy-wide rigid sets have at most four points | PROVED ACTUAL CARDINALITY | `ActualMixedRigidCardinality`; actual heavy-wide witnesses exclude HA, then physical types supply the double-scale angle gap |
| Actual eight-point defect-two pair has only three rank-region placements | PROVED ACTUAL REDUCTION | `ActualN4R2RankRegions`; unordered ranks0/1,0/6,5/6 and actual common region; this does not assert the same restriction for a bare GenericModel |
| Actual interior-zero three-class geometry | PROVED STANDALONE PRODUCER | `ActualInteriorZeroPartition`; three nonempty actual classes, diameter endpoints, total physical spans<=pi-3*lambda, between-class angles>=2*lambda, and singleton actual gain; no F17 violating deletion set yet |
| Original nonacute heavy cannot be a weak nearest neighbor | PROVED STANDALONE NECESSARY CONDITION | `ActualHeavyNearestExclusion`; original score2 and an actual angle>=2*lambda witness internally supply zero gain, a tight angle gap and a strictly closer actual point; HA is not excluded by this theorem |
| Actual ray-window wrap supplies an independent-scale score lower bound | PROVED STANDALONE GEOMETRY | `ActualHullWindowScoreLower`; width<=pi-k*mu yields score_mu>=k-1, with mu independent of the window legality scale; the desired restricted window is not assumed constructed |
| Generic saturated scalar extraction, including seven/eight actual centers | PROVED | `SatScalarModel`/`SatScalarExtraction`; internal sigma, exact delta and full non-anchor row defects; necessary direction only |
| Uniform sharp ordinary-point bounds in later strips | OPEN | Actual inflation reduces capacity to an independently required point-count result; it does not prove that bound |
| Bare actual finite exclusion implies original potential capacity | PROVED CONDITIONAL BRIDGE | `ActualCapacityFromCardinality.potential_le_of_bare_exclusion`; independent bare exclusion remains explicit |
| Floor-free actual threshold capacities 8/10 | PROVED | Existing independent bare nine/eleven exclusions consumed through actual inflation |
| Actual common-cone emitter and least-score deletion progress | PROVED LOCAL BRIDGE | `ConeDeletionProgress`; common oriented cone is an explicit local input |
| All natural n >= 4 HIGH four-row ascending scalar mask0 | PROVED FIXED DIRECTION | `symbolic_mask0_probe`; typed leaf of the complete common-profile wrapper, retaining ten explicit ASC hypotheses |
| Arbitrary overfull common-cone existence | OPEN | The local cone consumer does not establish this geometric premise |
| Exact-floor search in natural strips 4..24, 2604 cases | DIAGNOSTIC ONLY | `JSP404_SIX_EXACT_FLOORS_ROUTE_20261005.json`; no completed finite Lean kernel certificate |
| Arbitrary-size LOW capacity when a saturated center exists | PROVED | `OneSaturatedLow.potential_le_two_pow_of_saturated`; no certificate premise |
| Arbitrary-size HIGH capacity when two saturated centers exist | PROVED | `TwoSaturatedHigh.potential_le_high_of_two_saturated`; any original anchors/chart |
| Two saturated centers, at least four centers: every other defect >= 3 | PROVED | `TwoSaturatedDeficit.rowDefect_ge_three_of_two_saturated`; actual original rows |
| Full-row restriction to selected rays / local three-term bounds | PROVED | `TriangleRestriction`; these do not imply the global sum bound |
| Geometric saturation count and half-strip threshold | PROVED | `SaturationPacking`, geometric saturation lemmas in `Induction` |
| Signed-cell normalization at arbitrary size | PROVED | `ProperGaps.ModeA.normalize`, `exists_nonnegative_model` |
| Full classification given geometric certificates | CONDITIONAL | `CertificateIntegration.sendov_alpha_eq_of_geometricCertificates` |
| Arbitrary-N lower bound given the capacity theorem | CONDITIONAL | `Integration.sendov_lower_of_selection` |
| Equality of genuine extremal quantity and formula given capacity | CONDITIONAL | `Integration.sendov_alpha_eq_of_selection` |
| N >= 17 lower bound with no extra hypothesis | OPEN | `MainTheorem.sendov_lower` still depends on `sorryAx` in this remaining branch |
| Final complete-proof submission | NOT READY | Requires the unconditional lower bound and completion audit |

Sharpness means arbitrarily close actual configurations, not an assumed
exact minimizing configuration. `Statement.lean` contains the formula and
point-configuration definitions. The upper constructions are attributed
imports from superpilot69's pinned MIT-licensed development, connected by
new local proofs; see `ThirdParty/Sendov/README.md`.

The 2026-10-05 eleven-point bundle passed all 626 producer source/kernel
checks, all 626 normal Lake targets, four actual consumer source checks,
the 9957-job full build, and the composed 34-declaration standard-axiom
gate. The two-root completion gate correctly rejects `sendov_lower` for
`sorryAx`. Frozen hashes and commands are recorded in
`research/JSP404_ELEVEN_INTEGRATION_RECEIPT_20261005.json`.

The subsequent n=4 local bundle passed five single normal Lake targets,
the actual geometry source trust=0 check, the 9961-job full build, and the
cumulative 48-declaration standard-axiom gate. The original two-root
completion gate still rejects `sorryAx`. Its precise geometric premises
and source hashes are recorded in
`research/JSP404_N4_INTEGRATION_RECEIPT_20261005.json` and
`research/JSP404_N4_GEOMETRY_SCOPE_20261005.md`.

The third foundation bundle passed five sequential genuine normal Lake
targets and the 9966-job full build. Its 28 new audited declarations raise
the accepted standard-axiom set to 76; the original two-root completion
gate still rejects `sorryAx`. Producer strict source results are retained
without rerunning frozen proofs. The precise source, log, diagnostic and
provenance hashes are in
`research/JSP404_FOUNDATIONS_RECEIPT_20261005.json`.

The fourth bundle preserves the n=5 producer's 65 strict and 65 genuine
normal target receipts, then verifies four additional foundation targets
and the new actual n=5 geometry source/target. The full build passes 10035
jobs, and the cumulative standard-axiom gate accepts 95 declarations.
The original two-root gate still rejects `sorryAx`; full n=5 and all N>=17
remain open. The subsequent actual inflation publication is recorded below.
Frozen evidence and exact scope are
in `research/JSP404_N5_INTEGRATION_RECEIPT_20261005.json`.

The fifth publication verifies all five new normal module targets, the
10040-job full build, and a cumulative 142-declaration standard-axiom
gate. The original two-root negative control still rejects `sorryAx`.
The exact actual inflation conclusion does not assert final score zero;
the induction's terminal parameter is freely weakened. Frozen sources,
unaltered producer stdout and precise limitations are recorded in
`research/JSP404_INFLATION_RECEIPT_20261006.json`.

The sixth publication preserves 40 strict symbolic-mask sources and all
40 genuine normal targets. Two new public transport/deletion modules have
genuine normal Lake targets, followed by the 10082-job full build and a
155-declaration standard-axiom gate. The original two-root negative control
still rejects `sorryAx`. Full n=4/n=5 and the arbitrary-N lower target remain
open. Exact premises and frozen hashes are recorded in
`research/JSP404_TRANSPORT_RECEIPT_20261006.json`.

The seventh publication reuses the successful flat-inflation and n=4
primitive normal targets, verifies actual-minimum-deletion and closest-pair
normal targets, and passes the 10086-job full build. Its 24 new public
exports raise the standard-axiom gate to 179. The original two-root gate
still rejects `sorryAx`. Exact frozen scope and producer logs are in
`research/JSP404_FLAT_GEOMETRY_RECEIPT_20261006.json`.

The eighth publication preserves six strict and six genuine normal
567/821 sources and the existing verified maximum-band/packet targets.
The new HIGH functional consumer has a genuine normal target. The full
10098-job build and 197-declaration standard-axiom gate pass; the original
root gate still rejects `sorryAx`. Frozen evidence and exact conditions are
in `research/JSP404_MAXIMUM_BAND_RECEIPT_20261006.json`.

The ninth publication adds the genuine weighted minimum-cardinality model,
its local outward closest-pair witness, an interior score plateau, one
conditional n=4 fixed word, five fixed-direction cohorts and seven typed
legacy adapters. Fifty cohort sources passed strict and genuine normal
checks; the new closest-pair normal target passed. The full 10153-job build
and 245-declaration standard-axiom gate pass. Replayed unused-variable/simp
lint is retained, and the original root still rejects sorryAx. At that revision, nineteen
fixed common-profile directions were directly callable and all62 remained open.
Exact bindings are in `research/JSP404_MINIMUM_CARD_RECEIPT_20261006.json`.

The tenth publication adds the internally selected minimum actual counter,
its fixed-card maximum and derived sharp deletion cap; full actual hull
consequences; the closed actual deletion-gap boundary; and a 51-source
frozen cohort with ten more fixed directions. Four genuinely built core
targets were reused. Full 10208-job build and trust0 audit passed once each,
with 292 public declarations in the standard-axiom gate. Replayed generated
unused-variable/simp lint is retained and the lower root still rejects
sorryAx. At that revision, direct common-profile coverage was29 and all62
remained open; arbitraryN>=17 is still open. The exact frozen receipt is
`research/JSP404_MINIMAL_COUNTER_GEOMETRY_RECEIPT_20261006.json`.

The eleventh publication completes the uniform symbolic HIGH between
profile for every n >= 4, internally covering all 1024 arms and all 62 typed
directions. It also adds the actual small-cone LOW consumer, arbitrary
protected-position/score inflation, actual F = 21/F = 22 n = 4 pure-tail scenes,
full-row/cycle foundations and two local nearest-neighbor metric lemmas.
All 346 symbolic normal targets have actual producer records. Eight cache
reuse targets pass, and the one default full build passes 10406 jobs.
The first audit's seven missing helper imports are preserved as a failed
attempt; only the audit imports were repaired. The successful trust0
composed gate accepts 654 selected declarations (647 through the default
root plus 7 explicit audit imports), and the original negative gate still
rejects only lower sorryAx. Raw generated lint/deprecation warnings are
counted and retained; no original arbitrary-N, full NoSAT, bare eight-point or prize
completion follows. Exact scope and frozen evidence are in
`research/JSP404_SYMBOLIC_BETWEEN_PROTECTED_RECEIPT_20261006.json`.


The twelfth publication, recorded on 2026-10-07 UTC, adds two actual
six-point saturated-anchor profile consumers, four actual interior-fan
support exports and thirteen shared affine-cycle/complete-row foundations.
All three frozen sources have genuine strict0 and normal producer evidence;
three cache confirmations pass. One incremental full build passes 10409
jobs and one composed trust0 audit accepts 673 selected declarations
(666 through the root plus seven existing explicit audit imports).
The original negative gate still rejects only the lower root's sorryAx.
The shared checker retains five owned lint warnings; the other new sources
have zero owned warnings. Its failed first source snapshot was not saved,
so only the real failed stdout and original source hash are claimed.
All-word/49k catalog replay, bare8, general twisted runs and the original
arbitrary-N theorem remain open. Exact limits and frozen evidence are in
`research/JSP404_ACTUAL_LOCAL_FOUNDATIONS_RECEIPT_20261007.json`.


The thirteenth publication adds 56 selected declarations from thirteen
new modules: model-word/full-row semantics, generic tree/arc/leaf checks,
exact pure-checker transport, actual interior-one witnesses and nearest
hull consequences, all-pair angle gaps, and a selected original interior
score-one cardinality bound. The new consumer itself passed strict0 and a
genuine normal build. One incremental full build passes 10422 jobs and
one composed trust0 gate accepts 729 declarations (722 through the root
plus seven existing explicit audit imports). The original negative gate
still rejects only lower sorryAx. All new owned sources have zero warnings;
old dependency diagnostics and five shared-checker lints are retained.
The gzip-backed 375786-arc Python parity report is NOT_KERNEL. Seven F18
proof notes and a dependency map are PAPER only, even though their paper
classification covers t0..3. The map's older pending Cardinality1 entry is
superseded by its new exact-source PASS receipt; frozen map bytes remain
unchanged. Concrete catalog/shard/pilot coverage, the full eight-point R2
capacity, complete typed F18, F17 and arbitrary-N remain open. Exact scope
and all failure/copy boundaries are in
`research/JSP404_REPLAY_NEAREST_RECEIPT_20261007.json`.

## Integrated material

- Initial user-designated trunk, a historical 2026-09-22 snapshot:
  `lane/integration` at
  `edef86b0d216e7e535a81802d9d43ee6a60b8478`.
- Owner branch `b436a89e72bda007d970f230f95806ed61eacec6`:
  `SaturatedStructure.lean` B1 -> L2-min -> full L2 -> L3,
  plus strict-checker/cross-map material.
- Kernelized geometry from angle-certificate branch
  `d66a6ab9cbe324d3353dbe7300880fb438838589`, followed by
  `0b525bee0ab85f30028a7b76de31356d2ac394e4`: three-center base,
  geometry/deletion bridges, induction, Kraft equivalence and actual
  geometric saturation / half-strip lemmas.
- Wave-1/2 gadget semantics, signed caps, residual arithmetic, ghost
  counterexample, four-center high machinery and alignment invariant.
- `KraftResidual.lean`, copied unchanged from remote commit
  `000e0c50a1adebb0d4ead6e623dae5a2d01cbd4b`: defect-histogram and
  first-overfull-level arithmetic. This is an equivalent algebraic
  formulation of capacity; it does not prove that actual legal
  configurations have nonnegative residuals. The preceding remote
  `KraftPacking` case bundle adds open premises and is not imported as
  a solution to the geometric cases.

At the historical 2026-09-22 remote check, `lane/l1-lowp` and
`lane/v1-vacuum` pointed at their base
`278c44c6e3c45df93de966402d76eb219d139291`. That statement is not the
current remote snapshot. A 2026-10-05 remote check finds:

- `lane/l1-lowp`: `2e19fd3f57ab1b7e9acf00e92e763f16f54db060`.
- `lane/v1-vacuum`: `1e35549f46fee53a28384400aea52813d05f1e94`.
- `lane/integration`: `2917368e2a8fec5456303047ae30a5376473bbb4`.
- AIR: `8f775228238a7efd3ee430a05ea92102f344c64a`.

These are remote-reference snapshots. Proof coverage comes from the typed
source and axiom audits above; it is not inferred from a branch name or an
old RUNNING label.

## Remaining global routes

1. **Gadget route:** arbitrary-size low and high consequences for faithful
   skeletons, followed by the geometry-to-skeleton adapter. `ProperGaps`
   now proves that strict remainders force nonnegative cells, and closed
   remainders can be normalized without changing angles or weight. This
   closes the signed-cell obstruction for capacity transfer; it does not
   assert transport of gadget witnesses or supply the geometry adapter.
2. **Geometric route:** prove the arbitrary-size `CertExists` progress
   lemma or the equivalent Kraft packing bound. Both n = 1 and n = 2
   boundaries and final wiring are proved: `GeometricCertificates`, now
   quantified only over n>=3, implies the full extremal equality.
   This remaining premise itself is OPEN.

The s = 4 high reduction is proved conditional on `AllBadStrip`; it does
not settle arbitrary s. Finite enumerations do not prove the general
vacuum statement. Saturated-point lemmas constrain some profiles but do
not yet bound the total mass in every profile.

Further proof details: `FIRST_STRIP_AND_CELLS.md`, `KRAFT_CRUX_AUDIT.md`,
and `LOW_CORRIDOR.md`. The competitor update at `fc6047f` was read and
qualified against its original archive; its three-term constraints do not
close the global packing step.
`KRAFT_CRUX_AUDIT.md` rejects the incorrect zero-saturation shortcut.
`LOW_CORRIDOR.md` records the completed one-saturated LOW case: actual
row identification, unique direction-bin graphs, coloring, weighted
counting and reference-chart invariance are all proved. The remaining
geometric packing cases, all with n>=3, are LOW with no saturated center
and HIGH with zero or one saturated center. The entire n=2 boundary is
proved by the varying fan-bisector inequality `W*lambda <= 2*pi`.
`TwoSaturatedHigh` closes the complete
two-saturated HIGH case: its remaining normalized mass is <=1/4,
including the three-center boundary through the established base case.
`TWO_SATURATED_RESEARCH.md` records the local HIGH progress and its
completed global corridor/counting assembly.

`FIVE_POINT_ROUTE.md` records the independent fan-bisector argument that
now proves the original theorem exactly for 3<=N<=8. For rejected global
shortcuts and reproducible evidence, see `GLOBAL_PACKING_RESEARCH.md`,
`NO_SATURATION_LOW_RESEARCH.md`, `ONE_SATURATED_HIGH_RESEARCH.md`,
`AVERAGED_BIN_PACKING.md`, and `ONE_SATURATED_HIGH_GEOMETRY.md`.
Experimental success of an adaptive partition is not a proof that one
exists for every configuration.

## Corrected and falsified interfaces

- `maxGap_boundary_emission` (`GeometricDeletion.lean`) is false as
  stated. Checked countermodels: `s = 2` unconditionally, `s = 3`
  conditionally at `lam > pi/2`, and `s = 4` on the square at
  `lam = 5 pi/12` (low regime, all row gains zero;
  `MaxGapCountermodel2.maxGap_boundary_emission_countermodel_s4`,
  standard axioms only). Restricting the quantifier to `4 <= s` is
  NOT a repair — the square is legal at `s = 4`. The square is flat
  with `potential = 4 = sendovCap 2 false`, so it does not refute the
  strict over-capacity consumer domain used by `CertExists` — provided
  `n`/`big` carry the consumer bindings `Nat.floor (pi/lam) = n` and
  `big = false → pi/lam - n < 1/2`; with free `n`/`big` the square
  refutes even that domain (`n = 1`). See `notes/MAXGAP_SPEC_AUDIT.md`.
- The research shortcut "no saturated centers implies K <= 1 in both
  regimes" is false. `PentagonPacking.strict_no_saturation_counterexample`
  proves a proper, nonnegative strict model with K = 5/4 and no saturation.
  The target high cap K <= 5/4 is not contradicted. Numerical nine-point
  evidence also rules out repairing the shortcut by excluding flat cases.
- Loose selection without `Proper`: ghost-vertex counterexample.
- Old geometric LOW selection: disproved with two points, lambda = 3 pi,
  n = 0 by `not_legacySelectionLow` (standard axioms only). The repaired
  interface requires lambda <= pi and a nonzero chart reference.
- The low staircase cap now requires fractional part < 1/2; `big` is no
  longer unrelated to the strip.
- Capped LP infeasibility is not structural inconsistency; the delta
  clamp and warm-cache identity bug are recorded in the historical lane
  reports.

## Verification and completion gate

`verification/oct5-review/ProofAudit.lean` explicitly prints both unconditional root
statements and their transitive axioms. It also audits the integrated
supporting results. `verification/oct7-semantics-review/oct7-semantics-composed-audit.txt` records the latest
output. A green Lake build with a lower-root `sorryAx` is not completion.

Completion requires both unconditional root halves, original-problem
correspondence including every N >= 3, no missing proof hidden in an
extra hypothesis, standard-only root axiom closures, a reproducible
pinned public commit, and a complete-proof reference PR under the awards
repository's contribution rules.

See `INTEGRATION_AUDIT_20260922.md` for source revisions and the detailed
scope audit. Older handoffs and `FINAL_DAG.md` are historical snapshots;
this file supersedes their current-status claims.
