# Actual F18 rigid-four cover: source-only candidate

Status: SCOPED_PASS_ACTUAL_F18_RIGID_FOUR_COVER. Final strict trust-zero and genuine target-only normal checks both exited zero on the same final source. Both selected declarations print only `propext`, `Classical.choice`, and `Quot.sound`. Frozen dependencies and earlier receipts are unchanged.

Source: `Jsp000404/ActualF18OneHeavyThreeInterior.lean` (252 lines, 12046 bytes).
SHA-256: `72e32b914b2af44f0b4d9662672c20228828f9b88b0cad542ab5c0a40a7ced2e`.

Selected declarations:

- `Jsp404.ActualF18OneHeavyThreeInterior.actual_f18_rigid_four_cover_contradiction`
- `Jsp404.ActualF18OneHeavyThreeInterior.actual_one_heavy_three_interior_contradiction`

The first declaration uses an original actual minimal counterexample model in the n=4 LOW band with sharp cap 16 and original potential 18. Four injectively selected original points each satisfy either original interior score one, or original score two together with a genuine pair of original rays making angle at least twice the original scale. Two distinct selected points are original interior score-one points. Every original point outside the four-point selection is an original hull point of original score one. This last assumption is an explicit original profile case, not a supplied partition, capacity certificate, block-size result, or desired conclusion.

At each of the two interior points the theorem invokes the verified `ActualRigidFourNonapex` producer. Its original apex class is nonempty and contains none of the four selected points. All its members are therefore original hull light points by the coverage assumption. The actual partition gives angle at least three times the scale from every apex member to every other noncenter point outside that apex class. The verified `ActualPureLightBlock.actual_F18_pure_light_block_card_ge_four` therefore makes each internally produced apex block have at least four members.

The two apex blocks are disjoint. A common actual member would make the actual triangle formed with the two selected interior points have two angles at least three times the scale: each interior point is in the other's original nonapex class. Since the LOW model has scale greater than 2*pi/9, the two angles already sum to more than pi. The physical triangle angle-sum identity and nonnegativity of the third angle give a contradiction. No identification of labels in the two separately produced partitions is used.

The disjoint union of the two apex blocks has at least eight members and lies outside the four selected points. `ActualF18Frame.actual_f18_frame` supplies original total cardinality at most nine; injectivity makes the outside set have at most five members. This proves the profile contradiction. The same core can be instantiated by a cover consisting of one nonacute heavy plus three interior light points, or two nonacute heavy points plus two interior light points; the latter instantiation is not a separate exported wrapper here.

The second declaration supplies the first instantiation for an original eight-point model with one score-two point having an actual angle at least twice the scale, three injectively selected original interior light points, and all other original points hull light. It derives original potential 18 internally from the unique-heavy score profile, then forms the four-point selection and invokes the shared core.

Every angle, row score, hull predicate, and partition in these arguments belongs to the original actual configuration. There is no caller-supplied class structure, deletion gain, nearest-neighbor conclusion, subset hull assertion, or subset capacity. The R4 dependency uses complete selected hull-window widths; this candidate does not infer that every selected triangle angle is at least twice the scale. An acute HA heavy without a genuine wide-angle witness is outside the scope. This is a scoped F18 profile exclusion, not a proof of all F18, F17, or the arbitrary-N sharp lower bound.

Static API review: the actual Nonapex, PureLightBlock, and Frame signatures were read directly. The finite-set operations use the public membership, image-cardinality, complement-cardinality, and disjoint-union APIs. Those interfaces, finite subtype/image membership, the eight-point potential sum, and the concrete four-point injection have now been checked by Lean. An independent read-only review also confirmed the original-profile coverage requirement and the two-block argument.

Validation evidence: final strict attempt 2 exited zero in 25.18 real seconds (guard elapsed 25.290 seconds), maximum reported process RSS 5751111680 bytes and process-group RSS 6352814080 bytes. Genuine normal attempt 1 exited zero in 37.21 real seconds (guard elapsed 37.239 seconds), maximum reported process RSS 5620482048 bytes and process-group RSS 6196330496 bytes. It built the own target and completed 9049 jobs. No own-source warnings occurred in either final check; inherited normal warnings are recorded in the receipt. Both bounded guards remained below 8 GiB and 180 seconds, and both source snapshots match the final source. Sole compute was immediately returned to the finite-data owner after the normal process exited.

First strict attempt 1 genuinely failed at the concrete four-point injection: simplification left three reverse equalities `inside a = heavy` without applying the available `heavy ≠ inside a`. The only source repair adds explicit symmetry in these remaining cases. Its exact original source and raw log are retained as `failed-strict1.source.lean` and `failed-strict1.stdout.txt`; that failed log's placeholder `sorryAx` output is diagnostic data and is not a passing theorem result. No proof premise or mathematical scope changed.
