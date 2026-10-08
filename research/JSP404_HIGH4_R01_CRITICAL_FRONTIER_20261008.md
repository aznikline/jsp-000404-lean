# HIGH4 R0/R1: actual critical profiles and next producer

PAPER ONLY. This is mathematical/interface analysis, not a new kernel result. No solver, numerical probe, external-agent request or existing-source edit was performed. Root subsequently reported the all62 A/B terminal chain and unconditional actual R2 capacity verified. The new endpoint leaf described below subsequently passed strict trust-zero and genuine normal checks on exact final source `ae4d9aa67003638117c32ef19ecf294192a714e18d2e501b42086cfed62e6802`; this does not promote the remaining PAPER reductions or endpoint exclusions to kernel results.

R0/R1 are a different remaining frontier in the current proof chain. With a saturated anchor v, R counts ORIGINAL nonanchor score-two rows, equivalently defect-two rows at floor4. R0 has none; R1 has one. The actual R2 capacity entry point requires two distinct such points. Existing score-preserving protected inflation retains the protected anchor/low scores and turns the unprotected tail into score-zero points; it does not create a second score-two point. A future operation might connect the domains, but no existing geometric producer proves that connection.

There is an important domain distinction. `ActualHighMaximumMassReduction.exists_flat_high_band_counter_maximizer` and `HighFlatFunctionalReduction.exists_high_flat_functional_counter_model` range over all actual HIGH configurations and do not promise to preserve the original SAT anchor or R classification. A global minimum counter or maximum realization cannot simply be declared to remain in the caller's R0/R1 subdomain. The producer below concerns a GIVEN original minimal-counter Model having a SAT point and R<=1. To transfer it to a capacity theorem for arbitrary SAT configurations one must either treat all classes of a global minimal model, or construct an appropriate SAT-preserving minimal family and justify its deletion caps using the already closed escape cases.

For the fixed HIGH4 model use lower endpoint pi/5, upper endpoint pi/(4+1/2), cap20. Its legal scale and endpoints internally imply floor(pi/lambda)=4 and 1/2 <= pi/lambda-4 <1. No additional band hypothesis is mathematically needed when these endpoints are built into H.

The next small actual producer can have the following signature (proposal only; not implemented or checked):

```lean
proposed_high4_r01_model_potential {s : Nat}
    (o : Orientation Real Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : Real}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/5) (Real.pi/((4 : Real)+1/2)) 20 (s+1) c lam)
    (v : Fin (s+1))
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hR : ∀ a b : Fin (s+1),
      rowScore lam (directionRow o e c a) = 2 →
      rowScore lam (directionRow o e c b) = 2 → a = b) :
    potential lam (directionRows o e c) = 21 ∨
      potential lam (directionRows o e c) = 22
```

This asks the caller for the original Model, an actual SAT point and the actual at-most-one score-two condition. It asks for no minimum-score point, potential value, unique-SAT assertion, chart, word, gain budget or capacity certificate. Root subsequently reported unconditional `ActualN4R2Capacity.actual_r2_capacity` and its complete terminal dependency chain verified. With that theorem, hR follows internally from H and hsat: two distinct score-two points give the R2 premises and contradict H.over_cap. The displayed routine critical-profile producer itself has not been implemented here.

The side facts and the displayed potential alternative need no new geometric theorem:

1. `FivePointCapacity.potential_le_high_cap_of_le_five` gives the actual HIGH cap20 at original sizes at most5. Thus H has at least6 points; every needed one-point deletion leaves at least3.
2. `TwoSaturatedHigh.potential_le_high_of_two_saturated` (lines54-62) excludes a second actual defect-one point, since it would give original potential<=20. It requires actual legality, floor4, nonzero reference and two distinct SAT witnesses; it does not need any assumed uniqueness or a caller capacity premise.
3. Actual row-cell bounds, defect>=1 and score=4-defect give all original scores<=3. Any score3 point has defect1, so v is the unique score3 point and every other score is<=2.
4. hR then gives either all nonanchor scores<=1 (R0), or an internally selected unique score-two point a distinct from v and all points outside {v,a} have score<=1 (R1). It does NOT imply every nonanchor score<=1 in the R1 branch.
5. Choose a real minimum-score index internally. Because there are at least6 points but at most one score3 and at most one score2, its score is0 or1. Its weight is1 or2, and both divide cap20. Apply `ActualMinimalBandCounterexample.actual_minimum_score_critical_form` (lines110-125), the GENERIC-cap theorem, with that derived divisibility. The LOW specialization with cap2^n cannot be applied here. The result is Phi=20+2^minimumScore, hence21 or22.

The two critical alternatives have concrete ORIGINAL score distributions:

| Alternative | R0 | R1 |
|---|---|---|
| Minimum0, Phi21 | (3; 1^L,0^Z), 2L+Z=13, Z positive odd; original N=14-L in8..14 | (3,2; 1^L,0^Z), 2L+Z=9, Z positive odd; original N=11-L in7..11 |
| Minimum1, Phi22 | Exactly8 original points, profile(3,1,1,1,1,1,1,1) | Exactly7 original points, profile(3,2,1,1,1,1,1) |

In the first row, the already proved general `ActualProtectedInflation.exists_exact_protected_actual_inflation` (line185) can be instantiated with just the SAT protected in R0, or SAT plus the unique score-two point protected in R1. Choose threshold pi/5; its returned smaller scale stays in HIGH4. It yields actual pure-zero-tail configurations with the same Phi21: R0 has14 points, (3;0^13); R1 has11 points, (3,2;0^9). These are physical complete configurations, not subsets. Their original minimum-counter status is NOT inherited, and no such inheritance is needed if they are used as standalone finite exclusion targets. These specialized wrappers have not been implemented in this paper task.

The original deletion rigidity also transfers without a new geometric assumption:

- In Phi21, every original score-zero target is minimum. The generic critical form with divisor1 gives deleted potential20, incoming gain zero at EVERY other original observer, and preservation of all surviving original scores.
- In Phi22, all original scores are positive, and every original score-one target is minimum. The same theorem with divisor2 gives deleted potential20 and incoming gain zero at EVERY other observer.
- In Phi21, deleting a score-one target retains original mass19 and has actual deleted potential<=20. The generic actual multiplicative deletion ledger and `ActualZeroPairDeletionBudget.weighted_gain_budget_le_one` / `positive_score_gain_eq_zero` give zero gain at every ORIGINAL positive-score observer. A zero-score observer can gain at most1, and at most one can emit. This reuses the GENERIC arithmetic, not the LOW-specific public F17 observer theorem.

Therefore deleting a minimum point in either alternative preserves R0/R1 exactly, and light deletion in the Phi21 alternative cannot create score2 from a zero row. The resulting potential is20, or19/20 for a Phi21 light deletion, so the new R2 capacity theorem provides no contradiction. This is a precise obstruction to the naive single-deletion promotion strategy; it is not a proof that every conceivable future transformation is impossible. `ActualMinimumCardBandMaximizer.actual_positive_gain_score_lt` is a related fact for a DIFFERENT maximum-realization Model type; one must not pass the present cap20 counter-Model to that interface. For this H, use its actual deletion cap, generic critical form, or `removable_of_gain1_ge` with `not_actual_removable`.

Anchor deletion is not a free promotion to R2 either. `OneSaturatedHigh.rowDefect_succAbove_eq_one_of_big_ends` (line5026) assumes an existing defect-two row and its actual two big endpoint gaps, and promotes it to SAT after deleting v. It destroys the original anchor and pays its weight8. R0 has no defect-two point for this interface; R1 has only one. A bound on the reduced configuration does not alone pay the removed8 or produce two distinct remaining defect-two points.

The most economical NEW geometric target after the routine critical producer is the ORIGINAL seven-point R1 all-positive profile:

```lean
proposed_actual_high4_r1_seven_impossible
    (o : Orientation Real Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : Real} (hn : Nat.floor (Real.pi/lam) = 4)
    (hhigh : (1/2 : Real) ≤ Real.pi/lam-4)
    {c : Fin 7 → Plane₂} (hleg : Section4Legality c lam)
    {v a : Fin 7} (hva : v ≠ a)
    (hv : rowScore lam (directionRow o e c v) = 3)
    (ha : rowScore lam (directionRow o e c a) = 2)
    (htail : ∀ i : Fin 7, i ≠ v → i ≠ a →
      rowScore lam (directionRow o e c i) = 1) : False
```

This is a new target, not a proved fact. Phi22 is derived from the actual profile rather than supplied. The actual saturated window and chart should be produced internally from v. Its six nonanchor rows have defects(2,3,3,3,3,3), whereas the R2 critical adapter uses FIVE nonanchor rows with defects(2,2,3,3,3). The public R2 capacity theorem cannot be applied merely by naming the unique R1 heavy twice or by deleting a light point: distinctness fails in the former, and deletion rigidity keeps only one heavy in the latter. The stronger weak A terminal has a different contract: it needs only a defect-at-most-two point at sorted fan rank1 and a defect-at-most-three point at rank3. Its reflected use exchanges ranks1/3. This DOES yield a useful endpoint constraint after an actual light deletion, without a second heavy.


A new independently checked leaf, `Jsp000404/ActualHighR1HeavyEndpoint.lean`, implements that smaller constraint for the explicit actual Fin7 profile. Initial source SHA256 is `10d8e59d77b7ab608d1f51db23e5f179aa89f6cf7577bb6900ada38da092970d`; its final source SHA256 is `ae4d9aa67003638117c32ef19ecf294192a714e18d2e501b42086cfed62e6802`, and its only selected theorem is `Jsp404.ActualHighR1HeavyEndpoint.exists_actual_high_r1_heavy_endpoint`. It internally produces a physical SAT chart and proves that the score-two point has nonanchor rank0 or5 in that chart. It does not prove the seven-point configuration impossible.

The exact same-chart restriction bridge is as follows. Internally extract theta and sort its six physical nonanchor rays. For original heavy rank1/3, retain original sorted rays0..4; for rank2/4, retain rays1..5. Include the actual SAT anchor as new index0, and define the five new angles by composing the ORIGINAL theta with the ORIGINAL sorting permutation and this monotone selection. The new physical chart uses the same reference vector and is a restriction of the original actual chart. These five angles are strictly increasing, so the new chart's sorting permutation is the identity. Restriction monotonicity gives every retained original positive row new score at least1, and gives the original heavy new score at least2. At floor4 these are exactly the weak A bounds3 and2. The heavy now has rank1 or3, contradicting weak A or its reflected instance. Only original ranks0/5 remain.

This bridge uses neither exact preservation of deleted scores nor Phi22, deletion gains or a counter-Model. Its public finite-profile hypotheses are original legality/floor4/HIGH, one SAT point, one distinct score-two point, and score1 at each other original point. In particular the stated Fin7 size/profile are explicit caller assumptions. An original minimal HIGH Model to this Fin7 all-positive R1 profile remains a PAPER routine counting/critical-reduction obligation; it is not hidden in the endpoint leaf. The LOW half-scale nearest/clump conclusions are not imported into this HIGH argument. The HIGH parameter is retained for the scoped interface even though the proof currently uses the stronger floor4-only hypotheses.

A concrete sufficient geometric selector for this seven-point target would produce a valid adaptive four-bin cover in the actual saturated chart and two distinct ORIGINAL score-one tail rows whose reduced directions occupy at most two bins each. Each contributes slack at least4-2=2; together they supply the quarter saving4 consumed by the verified `OneSaturatedHigh.potential_le_high_of_saturated_slack_family` / slack-sum interfaces. This existence statement remains unproved. It must be derived from actual directions and all triangle caps, not supplied as a caller field and not replaced with the target total-mass inequality. A different real metric or adaptive-cover certificate may be needed.

Existing geometry closes proper subdomains only. `potential_le_two_pow_of_saturated_narrow` (line196) needs actual spread beta<alpha=5*lambda-pi; `potential_le_high_of_saturated_delete_narrow` (line4255) needs that condition after one actual deletion; `potential_le_high_of_saturated_delete_pair` (line4473) additionally needs a deleted-weight budget<=4. These predicates are not consequences of R<=1 in the existing source. In HIGH, the SAT window beta=pi-4*lambda is in[lambda/2,lambda), while alpha=(1-delta)*lambda<=lambda/2. The new LOW maximal-clump and nearest-point tools require the opposite strict half-scale remainder bound and cannot simply be reused in this HIGH domain.

The repository paper notes provide exact-integer, non-kernel illustrations of this distinction. `notes/ONE_SATURATED_HIGH_GEOMETRY.md` has a legal n4 R0 profile(3,1,1,1) with wide anchor spread defeating its simple two-group selector; `notes/ONE_SATURATED_HIGH_RESEARCH.md` (lines219-291) has an n4 R0 equality configuration with13 points, profile(3;0^12), Phi20, and no reservable fixed-coordinate quarter-face. These are not counterexamples to the desired capacity or to an overcap-only future reduction. They show why unconditional narrow/fixed-face shortcuts cannot be assumed and why sparse-row or adaptive geometric selection is a genuinely separate obligation.

No existing Lean file was changed; the new endpoint leaf is a separately checked endpoint constraint. This note does not claim R0/R1 capacity, the new seven-point exclusion, a universal sparse-row selector, or the original all-N lower bound.
