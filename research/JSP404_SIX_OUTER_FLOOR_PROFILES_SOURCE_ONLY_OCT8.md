# SixOuter complete floor-profile producer

Status: **SOURCE_ONLY**, no Lean invocation or kernel-check claim. Owned source: `Jsp000404/SixOuterFloorProfiles.lean`. The source is specific to `SatScalarModel.GenericModel 5 4`; it imposes no HIGH lower bound on `delta` beyond the original model's `0 ≤ delta < 1`.

## Complete actual model row

`modelGaps M i` is the original model's complete linear gap list, through the public `SatScalarExtraction.toModelSix` interface. Its length is five: four off-diagonal shared-chord entries and both genuine endpoints `theta i` and `theta i + (4 + delta)`. `modelGap M i : Fin 5 → ℝ` indexes that complete list, and `ofFn_modelGap` returns it unchanged. Zero-score gaps retain all original floor-zero and floor-one possibilities.

`fullGaps M i ord` explicitly expands the same five gaps for four proposed original labels. `fullGaps_eq_modelGap_of_perm_sorted` proves equality only after both complete-label permutation and actual scalar sorting have been established. Those premises belong to the semantic decoder helper, not an exclusion theorem accepting an arbitrary caller order.

`actualRowOrder M i` is internally selected: all nonself labels are insertion-sorted by `M.d i`, then indexed by `Fin 4`. Its public permutation, sorting and gap-equality theorems are `actualRowOrder_perm`, `actualRowOrder_sorted` and `actualRowOrder_gaps`. The pullback order needs only totality and transitivity; no false antisymmetry of distance values on all labels is assumed.

`modelGap_nonneg M i k` applies to every row and gap, including unrestricted row zero. No desired gap inequality is a model field or a caller premise.

## Genuine natural-floor profiles

`modelGap_score_sum M i c hdef` derives the complete equality

`sum_k (floor(modelGap M i k) - 1) + c = 4`

from the original row defect. It uses the already public exact full-row accounting, not a selected positive-gap budget.

For defect two the complete score sum is two. Either one score is at least two, giving a real gap at least three, or exactly two distinct indices have score one, giving real gaps at least two. These are the five singleton-three profiles and ten unordered-pair-two profiles in `SixOuterReplay.profileLower`. The source proves the table indexing exhaustively with ordinary finite `decide` on its literal values; it does not use `native_decide`, external certificates, or any solver conclusion.

The generic export is `defect_two_weak_profile M i hdef`, and the fixed core export is:

`row1_weak_profile M (hdef : rowDefect M 1 = 2)`

`∃ p : Fin 15, ∀ k : Fin 5, (SixOuterReplay.profileLower p k : ℝ) ≤ modelGap M 1 k`.

For defect three the complete score sum is one. A positive score is selected internally, equals one, and every other score equals zero. The public floor-interval bound then gives the exact tail profile:

`row3_tail_profile M (hdef : rowDefect M 3 = 3)`

`∃ t : Fin 5, 2 ≤ modelGap M 3 t ∧ modelGap M 3 t < 3 ∧ ∀ k ≠ t, modelGap M 3 k < 2`.

The generic corresponding export is `defect_three_tail_profile`. The selected positive tail is unique because every other actual full gap is below two.

## Scope and verification boundary

The source imports the new pure `SixOuterReplay.profileLower` table, owned by integration. It does not modify any old PASS source. The model may be necessary scalar data; no planar realizability is inferred from arbitrary GenericModel fields.

This leaf supplies complete model-row orders, gaps and profile witnesses. It proves neither decoder/cycle soundness nor any leaf acceptance, 1024-word coverage, mass bound, actual six-point extraction, or capacity result. The mask000 pilot's 75 contexts and the remaining words require separate semantic and kernel verification. This file has not been compiled; an authorized check must preserve the candidate and any real failures before updating its status.
