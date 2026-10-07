# Three narrow two-cluster centers: arbitrary positive scale

Status: SCOPED_PASS. The exact source passed strict trust-zero and a
genuine normal target build. Both selected declarations depend only on
propext, Classical.choice, and Quot.sound.

Source: `Jsp000404/SmallTwoClusterGeometry.lean`.
Checked exports:

* twice_base_lt_side_of_small_apex;
* no_three_small_two_clusters.

This is a geometric helper at arbitrary positive lambda. Actual
Section4Legality supplies positivity, injectivity, and the actual angle
upper bounds. The only extra scale bound is R<lambda/2. Three selected
centers are injectively indexed. Each has explicit TwoClusters data:
a Boolean code on the original actual indices, same-class physical
angles at most R, different-class physical angles at least 2*lambda,
and a distinct actual same-class companion for every noncentral target.
No score, counter Model, potential, point-capacity field, or five-point
capacity theorem occurs in this public interface or its proof.

The data fields contain angles of the actual configuration, not an
abstract angular array or accepting table. This core intentionally takes
these geometric premises explicitly. A later actual-model top theorem
must construct them internally from its original row/clump and zero-gain
producers. This leaf does not claim that model-producer bridge is done.

Two actual triangle angles at most R are impossible, since 2R<lambda
and the third angle is at most pi-lambda. Splitting by the three centers'
actual Boolean codes gives either a small angle or a zero-small branch.

For the one-small branch, relabel the small-angle center A, with other
centers B,C. Their actual angles beta,gamma are at least 2*lambda.
Let alpha be the actual angle at A. It is positive by actual legality
and distinctness, and alpha<lambda/2. Therefore beta,gamma>4*alpha and
9*alpha<pi. In particular, 4*alpha<pi/2 and beta belongs to
[4*alpha,pi-4*alpha]. Reflect beta about pi/2 when necessary to apply
the true sine monotonicity interval. Jordan's inequality then gives

    sin beta >= sin(4 alpha) >= 8 alpha/pi > 2 alpha >= 2 sin alpha.

The strict step uses alpha>0 and pi<4. The actual sine rule is

    sin beta * BC = sin alpha * AC.

Actual BC>0 and sin(alpha)>0 give AC>2BC. No factor-two side conclusion
is a caller premise. This fills the genuine gap in naively copying the
n4 proof: two large angles at ABu would only give the remaining angle
at u <= pi-4*lambda, which need not be below lambda/2 at arbitrary scale.

Choose B's C-class companion u. It differs from A,B,C. The small angle
CBu excludes u from C's B-class by the two-small-angle rule, so the
Boolean code at C puts u in A's class. The checked small-angle metric
comparison gives Au<Cu<BC. Triangle inequality gives AC<=Au+Cu<2BC,
contradicting the internally proved factor-two bound. No A-code(u) case
or additional scale split is needed.

For zero small angles, choose A's B-class companion u. Two-small-angle
exclusions force u into C's class at B and A's class at C. Three checked
metric comparisons all use common target u and give

    uB < uA,  uC < uB,  uA < uC.

This is a strict distance cycle. Labels of different observers are not
identified; each Boolean deduction uses a single observer's code.

Independent read-only mathematical review checked both branches,
all point distinctness, observer-specific code deductions, the Jordan
bound, the actual sine-rule product direction and all metric endpoints.
The strict check and genuine normal build validated the trigonometric
and geometric API elaboration and both axiom reports. No source repairs
or failed Lean attempts occurred; the original source bytes are frozen.

The frozen 227-line ActualNoThreeNonacuteHeavy candidate remains unchanged
at SHA be02f1480b0cca691b7ba753c2d84566d1592f9be84672bd5beea3df98162037.
Old READY sources and receipts were not edited. This core alone does not
establish an arbitrary-n model exclusion, full F17/F18 capacity, or the
original arbitrary-N lower bound.

Final verification: strict trust-zero exited 0 in 7.67 seconds with
maximum RSS 3,176,546,304 bytes; genuine normal target build exited 0 in
6.61 seconds with maximum RSS 3,236,495,360 bytes and built the target
in 3363 jobs. Both guarded runs stayed below 8 GiB and 180 seconds.
Both own-source warning counts were zero; inherited warnings are counted
separately in the receipt and preserved in the raw normal output.

Final source SHA-256: 55d261ffc65167b022ed93dceccab25cd4172ad4bba76de9163fa7bb37b75fb9.
