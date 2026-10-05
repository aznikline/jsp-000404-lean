# Actual minimum counterexamples and full-hull row defects

Parent publication: 29648b59337f6eb61cacbb1ebc9f7ecbe7ed8f44.
Frozen producer strict and genuine normal checks were reused, and all four
core targets were confirmed genuinely up to date without compiling them
again. The 10208-job full build and trust0 composed audit passed once each.
The public standard-axiom gate passed 292 declarations; the original root
negative gate still exits1 for sorryAx. Frozen generator unused-variable/simp
lint is recorded honestly. Exact source/receipt/raw-byte bindings are in
research/JSP404_MINIMAL_COUNTER_GEOMETRY_RECEIPT_20261006.json.

## An actual minimum counterexample, then fixed-cardinality maximum

ActualMinimalBandCounterexample first chooses the least actual cardinality
among configurations whose original potential exceeds an explicit cap
in the same parameter band. Every actual deletion leaving at least three
points consequently has potential at most cap. This stronger deletion
bound is constructed internally from minimum counter-cardinality.
It is different from the prior minimum-cardinality realization of a global
band maximum M, whose deletions are only known to be strictly below M.

For cap>=2, the selected counter has at most cap+1 actual points. This follows by an
actual restriction to cap+1 centers, whose potential is at least its
cardinality. It is not a bound by n+1 or a general sharp point-count theorem.

At this selected cardinality, independently bounded natural potentials
attain a maximum. This second choice keeps the actual minimum-counter
property and the same deletion bound. With an actual minimum row score k
and the explicit divisibility condition 2^k divides cap, the critical form
is F=cap+2^k: deleting that actual minimum point gives exactly cap, zero
incoming gains and unchanged survivor scores. The LOW power-of-two
consumer supplies its own divisibility and chooses the minimum internally.
The model remains weighted; it is not assumed or proved Flat.

For these fixed-cardinality actual maxima, rho<lam'<=lam preserves potential,
rowScore and gapScore throughout the lower band. The closed gap constraint
is g<=(gapScore(lam,g)+2)*rho. Raw floors need not remain constant, and no
score plateau or Flat at rho itself is asserted.

## Full original row and full actual convex hull

InteriorRowDefect proves that a center lying in an actual triangle of three
other distinct centers has original full rowScore+3<=n and rowDefect>=3,
at n=floor(pi/lam). It retains every other original center. Caratheodory
extracts that triangle from membership in the convex hull of all other
centers, using legality to exclude supports of size zero, one or two.

The actual rowCells<=n result supplies the needed conversion from the
original defect rowBig+(n-rowCells); it is not a replacement definition.

The separate FullHullInteriorDefect leaf has now also been checked. Finite
strict separation proves that a point outside the hull of all other
centers is an extreme point of the full hull of the original range.
Thus a non-full-hull vertex has actual defect at least three, and defect
at most two implies a vertex of the full actual hull. The core receipt's
older WIP paragraph records an earlier stage; the separate final leaf
receipt establishes the later verified full-hull statements.

There is no claim that an arbitrary maximum-score or zero-gain point lies
on the hull, no selected-subset substitution for the full hull, and no
convex-position or sharp-capacity conclusion.

## Five more fixed-direction pairs

The 51-source frozen cohort adds 79/992,127/1012,75/960,575/949,31/944.
Each theorem retains ModelSix n, n>=4, HIGH and four specified defects
2,3,*,3,2, together with all ten explicit direction hypotheses. Typed
reflection is a necessary-model transport. These ten distinct directions
bring directly callable common-profile coverage from nineteen to twenty-nine.
Full 31-representative/all62 coverage, all scalar profiles, and the original
arbitrary-N theorem remain open.

## Closed deletion-gap boundary for the fixed flat maximum

BandMaximumDeletionBoundary keeps one fixed actual flat band maximum with
potential equal to its cardinality. The original actual cyclic gaps are at
most 2rho. Each actual deletion has cyclic gaps at most 3rho, and at most
one surviving actual row has any cyclic gap strictly greater than 2rho.
The nine checked declarations retain original actual row/deleted-index
identities. Two hypothetical large rows are tested at one common scale
strictly above rho, contradicting the proved single incoming emitter bound.

The inequalities are deliberately closed for gap upper bounds and strict
for the large-gap predicate. At rho itself no Flat, potential equality or
score plateau is claimed. Rebuilding every Nat.floor partition at rho, or
asserting a sharper deletion threshold from these bounds, would change the
proved statement. The initial rejected source snapshot and genuine failure
log are retained separately from the final strict/normal successful source.

## Original boundary

The original statement and alpha definitions are unchanged. N=3..16 and
prior local capacities remain proved; MainTheorem still has its N>=17
sorryAx branch. Bare17/bare21, complete n4/n5 capacity, general weighted
counter impossibility and the prize submission are not complete.
LowNonflatDeletionCorrection, other packet/kernel WIP and private quota
ledgers are outside this publication. No integer diagnostic configuration
is presented as an actual planar counterexample to the original theorem.
