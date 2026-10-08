# Seven-point necessary weak floor profiles

SOURCE_ONLY, no Lean or solver run. The candidate is
`Jsp000404/SevenWeakFloorProfiles.lean`, initial SHA256
`277869e1be7ab9a0ea9ef201ef811db8a52937368c7fe361a9535cf2f7d3a190`.

The scope is exactly `SatScalarModel.GenericModel 6 4`. Its row permutation
retains all five non-diagonal chords. The existing generic
`N4R2CriticalReifiedRow.linearGaps_length` and `SatScalarModel.rowxs_length`
give six complete gaps: left endpoint, four adjacent differences, right endpoint.
No zero gap or multiplicity is discarded.

The candidate reuses generic `linearFloorSum_le_floor`,
`linearGapScore_add_bigCount`, `StrongGapBudget.linear_score_eq` and
`StrongGapBudget.linearGaps_nonneg`. The model's sorted row bounds imply
the raw floor sum is at most floor(4+delta)=4. This internally resolves the
natural-subtraction truncation in `rowDefect`; the exact identity is
sum_k(floor(modelGap k)-1)+rowDefect=4. No caller floor ceiling is added.

`weak_two_profile` accepts rowDefect<=2 and internally selects one of21
pointwise lower profiles. IDs0..5 mean gap0..5 respectively is at least3.
IDs6..20 are pairs(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),
(2,3),(2,4),(2,5),(3,4),(3,5),(4,5), with both selected gaps at least2.
`positive_profile` accepts rowDefect<=3 and selects one of six gap>=2 cells.
Both conclusions are necessary overlapping covers; they do not assert raw
floors equal3 or2. Exact defect2 and3 are admitted without extra premises.

The five selected candidate declarations are modelGaps_length,
modelGap_nonneg, modelGap_score_sum, positive_profile and weak_two_profile,
all under namespace `Jsp404.SevenWeakFloorProfiles`. There is no HIGH
assumption, order oracle, upper-floor hypothesis, DBM result, cycle replay,
full word coverage or seven-point impossibility conclusion. The explicit
floor upper constraints for a future finite core are deliberately not assumed.

Only this new candidate and note were created; existing true sources were
not edited. Kernel and genuine normal validation remain pending.
