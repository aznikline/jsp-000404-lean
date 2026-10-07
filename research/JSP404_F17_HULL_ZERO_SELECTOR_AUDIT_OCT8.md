# F17 hull-zero selector audit

Status: bounded **PAPER audit**, no Lean/Git/quota operation. No unconditional F17 selector was found. This note gives a concrete actual-angle consumer target and states exactly which existence assertion remains open. It does not use the vacuous pure-interior separated-block route.

Let the original actual n4 LOW minimal Model have potential 17. All weights and scores below are original. Deleting a proper actual set `S` while retaining at least three centers has the already proved ledger

`restrictionExpense + 1 ≤ removedWeight`.

For two original zero targets `q,r`, this gives `restrictionExpense ≤ 1`. The Model and minimum-cardinality hypothesis remain on the original configuration throughout.

## Controls tested first

### Regular heptagon at lambda = pi/4

Take the seven actual unit-circle vertices. At every original vertex the complete projective cyclic gaps are five copies of `π/7` and the wrap gap `2π/7`. Thus every original score is zero, potential is 7, and every single-target incoming gain is zero: a single deletion merges gaps to either `2π/7` or `3π/7`, both below `2λ` and also at most `2ρ=4π/9`.

Now delete two adjacent original hull vertices `q,r`. At each of the two surviving hull vertices immediately adjacent to that removed pair, three original gaps merge into a new wrap gap `4π/7`. Its score is one, since `2λ=π/2 < 4π/7 < 3λ`. Both surviving observers emit. Equivalently, the retained ray cone at each has width `π-4π/7=3π/7 < π/2`.

The total retained expense is at least two. This does **not** contradict the legitimate potential-7 configuration; it lacks the original F17 excess and its corresponding one-unit expense budget. It does show that the local exclusion below is an extra F17 restriction, rather than a consequence of actual legality, zero scores, zero single-target gains, or the closed boundary alone.

### Known actual F16 five-point control

At `λ=7π/30`, the actual configuration

`B=(0,-1000), U=(-50,0), V=(-49,1), W=(49,1), Z=(50,0)`

has original scores `3,1,1,1,1` and potential 16. It has no original zero targets, so the two-zero deletion predicate below does not apply. A potential-16 restriction is never treated as another minimum counter, and no equality classification of actual FiveLow capacity is used. This control continues to rule out the false shortcut that a small five-point restriction with a high-score observer and four light hull points must exceed capacity.

## A genuine local hull-zero exclusion

Choose two distinct **original hull zero targets** `q,r`. Let `C` be the actual retained point configuration obtained by deleting exactly those targets. For a retained original hull point `a`, write `A_C(a)` for the maximum actual angle between any two retained noncentral rays at `a`.

Original full-hull membership of a retained point implies its hull membership in `C`, by the forward preservation of an extreme point in a convex subset that contains it. It does not identify the entire new hull with the original hull minus the targets. New hull vertices may appear.

The actual hull Window of `C` at `a` has width `A_C(a)`. Therefore

`A_C(a) ≤ π - mλ` implies `rowScore_C(a) ≥ m - 1`

by its genuine wrap gap `π-A_C(a) ≥ mλ` and the natural-floor definition. This can be implemented with the checked actual hull-window producer and `ActualHullWindowScoreLower` without a caller Window or abstract gap.

Consequently, an original F17 Model forbids each of the following actual situations after deleting `q,r`:

1. Two distinct retained original **hull zero observers** `a,b` both satisfy `A_C(a), A_C(b) ≤ π-2λ`. Each has actual score growth at least one and expense at least one, so the combined expense is at least two.
2. A retained original **hull score-one observer** `a` satisfies `A_C(a) ≤ π-3λ`. Its new score is at least two, so its expense is at least two.
3. A retained original **hull score-two observer** `a` satisfies `A_C(a) ≤ π-4λ`. Its new score is at least three, so its expense is at least four.
4. A retained original **hull zero observer** `a` satisfies `A_C(a) ≤ π-3λ`. Its new score is at least two, so its expense is at least three even without a second observer.

Each contradicts the original two-zero budget `restrictionExpense ≤ 1`. The hull requirement on the deleted targets is not needed by the ledger; it is retained here to focus the requested geometric selection problem. The observer hull requirements justify the physical cone-to-wrap bridge. All observer indices must be distinct from the deleted targets; the two zero observers in case 1 must also be distinct from each other.

This is a concrete actual consumer target with a complete sufficient proof. It is not a construction of the target pair. The original minimum Model supplies every cap used in the argument; no desired deletion cap or intermediate criticality is assumed.

## Stronger type-aware outside-gap constraint

There is a sharper PAPER actual-row lemma than the generic total-score cone bound above. At a retained original hull observer `a`, let `e₀` be its genuine original outside wrap gap and `t=gapScore(λ,e₀)`. Actual legality gives `e₀≥λ`, so its natural floor is `t+1`. Let `E` be the genuine outside wrap after the two deletions. Then

`E ≥ (t+2)λ` forces actual row growth at `a` of at least one.

To prove this, the new outside gap is the original outside gap merged with the deleted end chains of original internal gaps. If any swallowed internal gap had positive original score, let `m≥1` count such positive gaps and let `S` be the sum of all their original scores. Each contributes at least its score plus one natural floor, while `e₀` contributes `t+1`. Floor superadditivity therefore gives new outside score at least `t+S+m`; after subtracting the old scores consumed by the merge, the gain is at least `m≥1`. If no swallowed internal gap had positive score, the asserted threshold gives new outside score at least `t+1`, again a gain of at least one. Other disjoint internal merges have nonnegative gain. This is a statement about the actual complete hull row and its actual end-chain merge, not a supplied abstract gap budget.

Thus every retained original positive-score hull observer in the F17 two-zero deletion obeys the strict current-scale inequality

`E < (t+2)λ`.

The corresponding actual cone triggers are:

| Original actual hull type | Original outside score `t` | A new cone of this width forces growth |
| --- | ---: | --- |
| LI, score one | 0 | `≤ π-2λ` |
| HO, score two | 0 | `≤ π-2λ` |
| LB, score one | 1 | `≤ π-3λ` |
| HM, score two | 1 | `≤ π-3λ` |
| HA, score two | 2 | `≤ π-4λ` |

For LI/HO/HM this strengthens the generic total-score thresholds. Any such positive-observer gain alone costs at least two and violates the one-unit budget. The public actual Types producer can internally determine the outside score; a future consumer should not ask the caller to supply the type or outside floor. The unresolved selector may therefore use any of these type-aware positive-observer triggers in addition to cases 1 and 4 for zero observers.

## Exact unresolved selector predicate

The open geometric task is to prove, internally from the original F17 Model and its actual points, the existence of original hull zero targets `q≠r` for which the actual restriction `C` satisfies at least one of cases 1–4 above. The maximum-angle conditions quantify only over the actual retained point indices and can be replaced by internally produced hull Window endpoints.

No such existence proof was found in this audit. In particular:

- original F17 does not itself supply two original hull zero points; configurations with at most one such point are outside this pair route;
- after deleting two adjacent hull vertices, an interior ray may replace the deleted boundary ray and shield the old neighboring hull observer from the anticipated cone shrinkage;
- a pair that increases only one retained zero row has expense one and merely meets the allowed budget;
- selecting a narrow cone on a subset unrelated to the two-target deletion does not give this two-zero expense bound.

Thus the regular-heptagon two-emitter pattern is a tested sufficient pattern, not a universal hull-ear theorem for F17 with interior points. Neither a fan-adjacency assumption nor absence of shielding may be inserted without an actual producer proof.

There is a useful PAPER localization for this cone-only predicate. Suppose the original strict hull has at least five vertices and the two hull-zero targets are nonadjacent. At every retained original hull observer except their possible common hull neighbor, the two surviving extreme rays are the same as in the original configuration or in one of the actual single deletions. An undeleted original hull vertex blocks a nonadjacent target from becoming the replacement extreme ray. Original interior rays may replace an extreme earlier and provide additional shielding; they do not invalidate this blocking statement. Since single original zero deletions preserve every original row score, none of those observers can meet a cone threshold that would force score growth. Nonadjacent target pairs in a cycle of at least five hull vertices have at most one common neighbor. Therefore the two-zero-observer alternative in case 1 can only come from an adjacent target pair in that range. The four-vertex hull has an essential exception: opposite targets have two common neighbors. Single-observer alternatives and internal-gap growth still require separate analysis. This localization does not produce the required adjacent pair.

## Additional closed-boundary target under the original maximum

There is a second rigorously justified PAPER consequence if the original input is the stronger **FixedCardModel** F17 maximum used by `ActualF17ZeroDeletionBoundary`.

Delete any two original zero targets. For every retained original positive-score observer, its complete restricted row score equals its original score at every strictly interior scale `ρ < λ' ≤ λ`:

1. The original fixed-card maximum gives the original potential and every original row score plateau at `λ'`.
2. The original zero targets still have total removed weight two at `λ'`.
3. Original proper-subset capacity gives restricted expense at most one directly at `λ'`.
4. A gain at a retained original positive observer would cost at least two, so that observer has zero restriction gain.

This does not assert that the twice-deleted configuration is critical or maximal. It uses the original smaller-scale Model each time.

For any fixed actual cyclic gap `h` of that twice-deleted positive observer, let `a=gapScore(λ,h)`. Individual gap scores also plateau: all are monotone as the scale shrinks, while their row sum stays constant. Taking the open-band limit gives the closed bound

`h ≤ (a+2)ρ`.

If the inequality were violated, an interior scale below `h/(a+2)` would increase that gap score, contradicting the established plateau. Equality is allowed. Nothing here asserts the score at `ρ` itself or turns a closed inequality into a strict one. This target needs the original FixedCardModel maximum; the λ-only Model/F17 pair exclusion in cases 1–3 does not need that stronger hypothesis.

The type-aware merge lemma also shows that the twice-deleted positive observer's outside score equals its original outside score `t`: the outside length cannot decrease, while an increase of its score would trigger forbidden row growth. Hence that particular actual outside gap satisfies `E≤(t+2)ρ` in the original FixedCardModel case. This is still a closed boundary assertion.

This positive-observer/two-zero boundary bridge could strengthen a future actual hull-pair selector, but no selection theorem using it has been proved here.

## Implementation boundary

No new Lean source is proposed as already checked. A small future consumer can choose an actual two-target restriction internally, inherit only the retained observers' original extreme-point property, obtain its actual hull Windows, and combine their wrap lower bounds with the existing original proper-subset ledger. The remaining task is the actual selection predicate above, including the shielding issue. The global F17 selector remains **UNKNOWN**.
