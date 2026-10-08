# HIGH4 R1 endpoint: weighted interior consumer

PAPER / SOURCE-ONLY INTERFACE AUDIT. This note reports no new kernel result,
solver run or actual counterconfiguration. Existing frozen proofs are unchanged.

The original model in scope is
`ActualMinimalBandCounterexample.Model o e (pi/5) (pi/(4+1/2)) 20 (s+1) c lam`.
The original SAT point v, original score-two point a, and positivity of every
original row are explicit case hypotheses. The model supplies the full original
deletion cap. It is not a model for a restricted configuration.

## Actual critical profile and endpoint

The candidate `ActualHighR1PositiveCriticalProfile` supplies exactly the missing
routine producer: `actual_high_r1_positive_critical_profile` outputs floor4,
HIGH, v distinct from a, score(v)=3, score=1 outside {v,a}, potential22 and s=6.
It excludes a second SAT using `potential_le_high_of_two_saturated` and a second
score-two point using the checked `ActualN4R2Capacity.actual_r2_capacity`.
Its original-count calculation is Phi=2N+8; a real light deletion and the original
cap force Phi=22, hence N=7. This producer was SOURCE_ONLY and undergoing its
own validation when this note was written; this audit does not promote it.

The checked seven-point leaf `ActualHighR1HeavyEndpoint` internally constructs
the physical SAT chart and puts a at sorted rank0 or5. Its initial ordinary API
repair changed no mathematical hypothesis. The endpoint is a constraint, not
an impossibility theorem. A SAT chart has beta=pi-4lambda with
lambda/2 <= beta < lambda in HIGH. Its nonanchor rays have actual angle at v
at most beta. The LOW strict inequality beta<lambda/2 cannot be imported.

## Exactly which deletions have zero gain

Every original light q is a minimum-score point, and its weight2 divides cap20.
The generic public `actual_minimum_score_critical_form` therefore gives its
deleted potential20, zero incoming gain at every original observer, and exact
preservation of the other original scores. This applies independently to every
light target; no caller supplies an accepted gain array.

It does not give zero gain for deleting the heavy or SAT. In the original Phi22
ledger, deleting a leaves original mass18, so the total expense is at most2.
Deleting v leaves mass14, so the total expense is at most6. A score-one observer
may gain1 when a is deleted; a score-two observer may gain1 when v is deleted.
An original light observer could gain2 when v is deleted, paying expense6.
These are allowed budget patterns, not asserted actual realizations. Thus the
F18/general-LOW all-target heavy-zero-gain interface cannot be reused.

## Actual light structures that remain valid

`ActualInteriorOnePartition.actualPartition` requires original legality,
lambda>pi/5, an original non-hull point p and its original score1. Those geometric
hypotheses hold in this HIGH case. Its three classes are nonempty and physical:
same-class angles <= beta, different-class angles >=2lambda, and apex to
nonapex angles >=3lambda. These are the true generic statements, independently
of the later LOW/F18 weighted consumers.

The generic `ActualHullSmallScoreTypes.exists_actual_hull_one_type` also has no
LOW hypothesis. At a hull light p, the LB branch is excluded by the internally
derived zero incoming gains and the existing common-cone deletion obstruction.
Consequently a HIGH light-hull LI producer is possible with the actual clumps
separated by2lambda and bound pi-3lambda. This does not make those clumps smaller
than lambda/2, and no nearest-point corollary is implied here.

## Selected minimal consumer

Root assigned NEW `ActualHighR1InteriorClassWeight.lean` to implement a weighted
interior producer, with only this original input:

```lean
H : ActualMinimalBandCounterexample.Model o e
  (Real.pi/5) (Real.pi/((4 : Real)+1/2)) 20 (s+1) c lam
v : Fin (s+1)
hsat : rowDefect 4 lam (directionRow o e c v) = 1
a : Fin (s+1)
ha : rowScore lam (directionRow o e c a) = 2
hpositive : forall q, 1 <= rowScore lam (directionRow o e c q)
p : Fin (s+1)
hp : rowScore lam (directionRow o e c p) = 1
hpnot : not (IsHullVertex c p)
```

Original non-hull membership is the interior case hypothesis. No caller supplies
potential22, card7, a partition, hull certificates for other points, class
weights, zero gains, a LOW half-scale bound, or a nearest map. The new profile
producer is consumed internally, with its unverified status kept explicit until
its separate checks succeed.

The returned actual partition has original-index classes, each of mass at least4,
and their total mass is20. A singleton light class contradicts the zero gain of
that real light deletion via the existing generic singleton-emission theorem.
A singleton heavy of mass4 and a singleton SAT of mass8 are allowed.

The class containing v has mass at least8. Every class has mass at most12; every
class not containing v has mass at most8, because the other classes include v's
mass8 and another nonempty class of mass at least4. These are the correct HIGH
replacements for the F18 mass16 and uniform class upper bound8.

The finite mass examples (12,4,4), (10,6,4), and (8,8,4) respect these inequalities
and the original mass multiset {8,4,2,2,2,2} outside p. In (12,4,4), the first
class can be exactly {SAT,heavy} and the other classes two lights each. This is
a counterbridge to the old mass-only F18 exclusion, not an actual geometric
countermodel or a proof that the desired R1 exclusion is false. The endpoint
constraint alone supplies no contradictory class-mass inequality in the
currently checked APIs.

## One possible subsequent geometric use (not implemented here)

The new SAT-sensitive class bounds may recover the two-interior apex exclusion
without incorrectly assuming every class has mass at most8. Suppose distinct
interior lights p,q satisfy q in p's apex. The usual 3lambda+2lambda>pi triangle
argument sends p and both nonapex classes of p into one class K at q. Their
mass is initially at least10. Since SAT-free classes have mass at most8, K must
contain v. If v also lay in p's apex, the three angles of triangle(p,q,v) would
each be at most beta: the two same-class bounds and the true SAT fan bound.
This contradicts 3beta<pi. Therefore v is nonapex at p; those two nonapex
classes have mass at least8+4=12, and adding p gives mass at least14 in K,
contradicting the correct upper bound12. This is a concrete PAPER route, not a
kernel theorem or permission to append further consumers to the assigned file.

No LOW/F18 complete theorem, all-target zero gain, subset counter-model,
half-lambda nearest argument, or general R1 capacity is claimed by this note.
