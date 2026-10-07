# Original F18 three-heavy NoHO consumer — SOURCE_ONLY

This note records the new candidate `Jsp000404/ActualF18ThreeHeavyNoHO.lean`.
No Lean invocation has been made for this candidate. It is neither a PASS
receipt nor a statement that the original problem has been solved.

The only public declaration is
`Jsp404.ActualF18ThreeHeavyNoHO.actual_F18_three_heavy_no_obtuse_false`.
Its inputs are the original n4 LOW minimum-counter Model, original mass
18, exactly three original score-two indices, and the actual-angle bound
at every original heavy center:

`angle(c a,c g,c b) ≤ pi − 2*lam`

for three distinct original indices. No hull set, apex, receiver,
cardinality, window, capacity, weight certificate or subset Model is a
caller input. The angle bound is the NoHO case predicate; it is not
inferred from the score-two property alone.

The original F18 frame gives six original centers. Every original heavy
is an original full-hull vertex. There are two internally split cases.

1. If no heavy has an actual angle at least `2*lam`, the checked actual
   hull type producer rules out HM and HO and supplies the HA angle cap
   `pi − 3*lam`. Selecting the three original heavy hull vertices gives
   nine integer turn units, contradicting the actual turn bound eight.
2. Otherwise choose one original nonacute heavy. The general cloud
   theorem `DevinF18TwoHeavyApex.actual_interior_apex_has_heavy_of_nonacute`
   selects an original heavy in the canonical apex of every original
   interior. The checked NonacuteApex theorem forces every selected
   receiver to be acute. Pairwise disjoint canonical apexes make the
   receiver choice injective.

Write S for the original hull set, T for the three original heavies,
I for the original interiors and R for the image of those receivers.
All four sets are defined internally on original indices; R is a subset
of T, and T is a subset of S. The established identities are

`S.card + I.card = 6`, `T.card = 3`, `R.card = I.card`.

The integer weight at an original hull vertex is

`1 + indicator(T) + indicator(R)`.

Original legality supplies its baseline angle cap, the public NoHO case
supplies the second unit at every heavy, and the internally produced HA
window supplies the third unit at every receiver. Consequently the
actual selected-hull budget gives

`S.card + T.card + R.card ≤ 8`,

while the three identities give a left side of nine.

The finite-set budget and acute-window support proofs are private. The
acute-window argument is adapted from the reviewed cloud candidate
`DevinF18TwoHeavyApex` (source hash
`13caf59d07692d00826884a7419ca5a296c39ae9323904a236c4677bb37506a4`).
No private cloud declaration is referenced. Its general public
apex-heavy theorem remains a dependency requiring separate local
verification; this note does not promote a cloud report to a local PASS.

HO has only the legality exterior baseline here. No claim that every
score-two hull center contributes two exterior turn units is used.
No restriction inherits a minimum-counter Model or original hull status
in the reverse direction. Only the new source and this new note were
written; frozen sources and receipts were not modified.
