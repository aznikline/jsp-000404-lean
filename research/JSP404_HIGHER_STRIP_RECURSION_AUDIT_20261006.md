# Higher-strip recursion and closest-pair extraction

## Exact next requirements

The repository's original `Statement.alphaN` uses `n = clog 2 N - 1`.
The next independent actual exclusions required by the frozen
`ActualCapacityFromCardinality` consumer are:

| Original N | n | Angle lower bound | Bare exclusion threshold | Potential cap |
|---|---:|---|---|---:|
| 17..20 | 4 | 7*pi/9 | 17 actual points, lambda > 2*pi/9 | 16 |
| 21..32 | 4 | 4*pi/5 | 21 actual points, lambda > pi/5 | 20 |
| 33..40 | 5 | 9*pi/11 | 33 actual points, lambda > 2*pi/11 | 32 |
| 41..64 | 5 | 5*pi/6 | 41 actual points, lambda > pi/6 | 40 |

Each threshold is strict: the genuine maximum-angle contradiction supplies
`lambda` strictly above `pi - alphaN N`. No seventeen-, twenty-one-,
thirty-three-, or forty-one-point exclusion is asserted in this report.

## Original perfect-GC argument: no hidden center reduction

The complete Russian paper was downloaded from the primary
[Mathnet archive](https://www.mathnet.ru/eng/fpm81), and printed pages 509,
510 and 512 were rendered and visually checked. Lemmas 4.10/4.11 replace
internal directions while explicitly retaining the same centers `o1..os`.
Lemma 4.12 has no `s <= n+1`, maximality, minimality, or irreducibility
hypothesis. Its induction directly asserts a maximizing exponent profile
with tail `n-s+1`. The English counterpart has the same unfilled step.

Choosing a minimum center count among maximum-potential configurations
does not supply the asserted profile: it gives genuine deletion-charge
constraints, being formalized separately in `ActualMinimumDeletionNormalForm`.
A geometric merge or deletion theorem is still needed to reduce centers.

**PROVED arithmetic obstruction to truncation.** In the LOW profile at
`s=n+2`, truncating its negative exponents to zero gives

`(n-1, n-2, ..., 0, 0, 0)`

and total weight `(2^n-1)+2 = 2^n+1`. In particular at `n=4,s=6`,
`(3,2,1,0,0,0)` has weight seventeen, not sixteen. Every additional
zero exponent contributes another point. Truncation is not a correction
of the claimed geometric maximizing argument.

## New actual metric extraction

Owned new source: `Jsp000404/ClosestPairTriangleExclusion.lean`.
The entire source has a genuine strict PASS with four standard-three-axiom
declarations and zero warnings, and is now frozen.

**FORMALLY PROVED deduction.** For an actual finite configuration legal at
`lambda > pi/6`, choose a globally closest distinct pair `p,q` internally.
Every third point `r` satisfies

`angle(p,r,q) <= pi/3`.

This is the shortest-side/smallest-angle relation. If another point `r`
lies in the triangle with vertices `p,q,x`, positivity of the legal margin
excludes boundary collinearity. Strict betweenness then gives the actual
surrounding-angle identity

`angle(p,r,q) + angle(p,r,x) + angle(q,r,x) = 2*pi`.

The latter two angles are at most `pi-lambda`, hence
`angle(p,r,q) >= 2*lambda > pi/3`, a contradiction.

The Lean extraction selects the closest pair with `Finite.exists_min`;
the caller supplies only the original actual legality and the threshold,
not a closest-pair certificate, circle order, convex-hull exclusion, or
capacity. It uses existing noncollinearity and strict-nesting proofs.

This is applicable throughout the n=4 thresholds and both n=5 thresholds,
including HIGH's strict `lambda > pi/6`. It is not a uniform higher-n
recurrence: the n=6 LOW/HIGH thresholds are below or at pi/6.

**PROVED paper refinement.** If the triangle's base angles are `a,b` and
the angle opposite `pq` is `c`, then `c <= a,b`. The other endpoint's cap
and the triangle sum give `a+c >= lambda`, so `a >= lambda/2`, and likewise
`b >= lambda/2`. Thus the closest-pair axis has only guaranteed half-lambda
clearance from external rays. The missing full-lambda clearance cannot be
substituted into the endpoint split theorem.

This half-lambda obstruction is exact, not an estimate artifact: set
`p=(0,0)`, `q=(1,0)`, `r=(1+cos(lambda),sin(lambda))` for
`0 < lambda <= 2*pi/3`. Then `pq=qr=1 <= pr`, and the triangle angles
are `lambda/2, pi-lambda, lambda/2`. It is legal, while the closest-pair
axis at `p` has only lambda/2 clearance from the remaining point `r`.

## False adjacency and collapse inference: exact actual counterexample

Take `lambda=pi/4`, `p=(-1,0)`, `q=(1,0)`, `x=(0,2)`, `y=(0,-2)`.
The pair `pq` is the unique closest pair: its length is two, while the
other lengths are sqrt(5) or four. The largest angle is
`2*arctan(2) < 3*pi/4`, because `tan(3*pi/8)=1+sqrt(2)>2`.
Hence this is a legal actual n=4 LOW configuration.

All triangles with base `pq` contain no further center. Nevertheless in
the row at `x`, the ray `xy` lies strictly between `xp` and `xq`. All three
point downwards, so this is the same oriented lift, not a projective seam
artifact. The blocker is beyond the base on its other side; it is not
inside the triangle `xpq`.

Collapsing `p,q` to their midpoint also makes `x`, the merged center and
`y` collinear, destroying legality. Therefore closest-pair triangle
emptiness implies neither fan adjacency nor a legal pair collapse.
Its numerical potential is below the target cap, so it does not refute
an over-capacity-specific theorem; it refutes the unconditional inference.

## Remaining merge/recursion gap

No complete geometric operation has been proved which both removes a
center and preserves potential, or which transforms a large subset at
the current threshold into nine/eleven points at their stronger thresholds.
Simple restriction retains lambda; shrinking a projective period does
not automatically preserve the endpoint caps or actual realizability.

The original maximizing profile and the new closest-pair structure do not
fill this gap. The valid metric extraction adds a necessary constraint
without assuming the capacity to be proved. It does not close bare17,
bare21, arbitrary-n capacity, or the original prize goal.

## Validation and handoff

Frozen source SHA-256:
`cd3919627e9c29065d07bcf4972241a42bd5a16eb75d8678b6ca9648f734b747`.

Actual single-file `lake env lean --trust=0` final check exited zero with
four standard-three-axiom declarations `[propext, Classical.choice, Quot.sound]`
and zero warnings. Raw log:
`.lake/closest-pair-triangle-exclusion-final-strict-20261006.log`.
Elapsed 4.023 seconds; `/usr/bin/time -l` maximum RSS 3,145,482,240 bytes
(2.929 GiB); sampled actual Lean peak 3,072,016,384 bytes, below the 3.5-GiB
actual-process cap. Group peak 3,773,005,824 bytes was recorded only.
No cap interruption occurred, and a real `.olean` was generated.

The verified declarations are `exists_closest_pair`,
`closest_pair_angle_le_pi_div_three`, `closest_pair_triangle_empty`, and
`exists_closest_pair_with_empty_triangles`. The first check also exited zero
but had one `letI` style warning; changing it to `let` was followed by the
genuine clean final check, not merely a claimed unverified repair.

All owned Lean processes exited before the slot was explicitly handed to
the seventh normal/full-audit publication. This agent does not repeat those
normal builds. No literal `sorry`, `native_decide`, or custom axiom appears.
No existing frozen source, root import, audit, commit, or quota operation
was edited or performed.
