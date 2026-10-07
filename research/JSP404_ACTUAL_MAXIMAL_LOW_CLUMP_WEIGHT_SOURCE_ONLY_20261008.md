# Uniform maximal LOW-row clump weight producer

SOURCE_ONLY. No Lean/Lake command has run for this new source. This is a bounded parameterization of the verified n4 argument, not a general capacity theorem or a new framework. Old PASS sources remain byte-identical.

New source: `Jsp000404/ActualMaximalLowClumpWeight.lean`.
Source SHA: 89b3d3f7b68c988c2097bddcfb2254db5d0096149be56245cafd1be06be3a1ac.
Candidate exports: `Jsp404.ActualMaximalLowClumpWeight.actual_maximal_observer_gain_eq_zero` and `Jsp404.ActualMaximalLowClumpWeight.exists_actual_maximal_low_clump_weight`.

## Exact public assumptions and outputs

Let n>=4, Q=2^n, W=2^(n-2), and delta=Phi-Q (natural subtraction; the original H.over_cap makes it positive). The caller supplies only the original actual LOW minimum-counter Model

`Model o e (pi/(n+1/2)) (pi/n) Q s c lam`,

a nonzero actual reference e, an original point p with kappa(p)=n-2, and an actual nonacute witness angle(a,p,b)>=2lam with distinct noncentral endpoints. The zero-gain theorem does not need the nonacute witness.

The main theorem returns `Nonempty (Data n o e c lam p)`, whose fields are:

- `geometry : ActualMaximalLowRowClumps.Data n o c lam p`, internally produced actual full-hull window/cut with two nonempty ray clumps, separation2lam and each same-side angle at most R=pi-n*lam<lam/2;
- `card_ge_two`: each original side has at least two original points;
- `weight_lower`: each side's ORIGINAL weight is at least delta+W.

No caller clumps, full-hull status, zero gain, restricted score, subset cap, turn budget, global capacity conclusion or accepted certificate is an input. No subset is promoted to a minimum-counter Model.

## Independent proof audit

1. The verified generic `low_model_nonsaturated (n:=n)` internally excludes every original SAT by the actual one-saturated LOW capacity. Together with floor n and complete row accounting it gives every original kappa<=n-2.
2. The verified general three-point LOW bound rules out s=3 for an over-cap Model. Thus deleting one point leaves at least three points, exactly the domain needed by the genuine minimal-counter deletion cap.
3. If a distinct target creates positive gain at p, the original target score is no greater than p's score. The general checked `removable_of_gain1_ge` weighted ledger makes the target removable. This contradicts `not_actual_removable` from H.minimum_card. Hence every original p-observer gain is zero, without a caller maximum-zero assumption.
4. The actual generic clump producer needs original full-hull membership. It is derived from kappa(p)=n-2 and the exact row identity kappa=n-defect, giving defect2, then the verified `FullHullInteriorDefect.low_defect_is_full_hull_vertex`. LOW band inequalities and the genuine nonacute pair supply all other inputs internally.
5. A one-point side would have actual angle at least2lam to every other noncentral ray. The checked actual single-deletion gain lemma would give gain>=1 at p, contradicting step3. Therefore each side has at least two points.
6. Delete one whole side. The retained complement contains p plus the other side, hence at least three points. Since the removed side is nonempty, the restriction is proper. Both facts are proved as original finite-set/cardinality facts.
7. The retained p remains an actual hull vertex by genuine extreme-point inheritance. Only injective legality and hull membership are inherited, never a restricted counter Model. An actual retained window is produced from the original physical points.
8. Its two boundary rays are in the same original side. The generic clump geometry bounds their actual angle, and hence the actual window width, by R=pi-n*lam. The checked `rowScore_ge_sub_one_of_actual_window` with k=n gives new kappa>=n-1. The old kappa was n-2, so the actual restriction gain is at least one.
9. The retained p's single expense term is at least W*(2^gain-1)>=W. The verified generic `actual_proper_subset_gain_budget` gives expense+(Phi-Q)<=removedWeight. Therefore removedWeight>=delta+W.

This uses natural powers symbolically. The only generalization requiring a changed geometric call is replacing the n4 `newscore>=3` helper by its already verified general window lower bound `newscore>=n-1`. No new mathematical premise was found missing.

## Actual dependencies and consumers

- `ActualMinimalBandCounterexample.low_model_nonsaturated` and `not_actual_removable`: original nonsaturation, score cap and real deletion cap.
- `ActualMaximalLowRowClumps.exists_actual_maximal_low_row_clumps`: actual generic clump geometry, not a supplied cut.
- `FullHullInteriorDefect.low_defect_is_full_hull_vertex`: original defect2 hull producer.
- `ActualHullWindowScoreLower.rowScore_ge_sub_one_of_actual_window`: actual retained-window score growth for arbitrary n.
- `ActualProperSubsetDeletionBudget.actual_proper_subset_gain_budget`: the original weighted whole-subset expense ledger.

For n=5 the interface gives Q=32, W=8, original kappa3 and per-side original weight at least(Phi-32)+8. A pure-zero side therefore needs at least that many original points; a pure score-k side has that mass as a cardinality/weight constraint. These are direct possible consumers of the Data fields, not additional implemented global theorems.

The source does NOT prove that an arbitrary LOW counter has such a maximal-score row, nor cover its acute-row case, counters whose maximum score is below n-2, or general n>=5 capacity. No original arbitrary-N lower/prize conclusion is asserted.

## Preserved n4 producers

`ActualHeavyClumpWeight.lean` remains SHA25de371c7fad631f6217b38f56e3d73e1525b4678a4167d8a1c82e1170994936.
`ActualF18HeavyZeroGain.lean` remains SHA53991270c06ee2b0429905d2aacc8fdd6a27a20943558995d387e81da9e62d84.

The new source is awaiting a separately allocated strict/genuine-normal check. It has not contributed a kernel declaration yet.
