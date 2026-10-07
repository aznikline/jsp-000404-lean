# Uniform maximal-obtuse exclusion candidate

SOURCE_ONLY, no Lean/Lake run. This is one bounded actual consumer of the now-verified general maximal LOW clump-weight producer. It does not assert a general capacity theorem or existence of maximal-score/nonacute rows.

New source: `Jsp000404/ActualMaximalLowObtuseExclusion.lean`, 323 lines, SHA 0a2945b68b3e2476254ac7ac72a2e0506ceba955a90e54b477d4d6f10ad2f295.
Single candidate export: `Jsp404.ActualMaximalLowObtuseExclusion.actual_maximal_obtuse_other_nonacute_false`.

## Exact API

For every n>=4, original actual LOW minimum-counter Model with cap Q=2^n, two distinct original rows B,C of score n-2, an actual angle at B strictly greater than pi-2lambda, and a genuine nonacute actual angle at C at least2lambda, the conclusion is False.

The caller supplies no paid gap, internal floor, clump, label alignment, score/gain budget, subset capacity or restricted Model. Every weighted side is internally produced by `ActualMaximalLowClumpWeight.exists_actual_maximal_low_clump_weight`.

## New actual list/window bridge

The bridge strengthens the VERY SAME paid cut in B's already produced geometry, so no equality of independently selected Boolean partitions is assumed.

1. Let its physical window width be alpha, paid cut g=theta(right)-theta(left), and physical outside E=pi-alpha.
2. Repackage that exact actual Window as a Support using the public fields. The small support proof is copied from verified ActualHullWindowScoreLower; no private old declaration is referenced. Therefore E and g are genuine members of the COMPLETE original cyclic-gap list, whose sum is pi and whose elements are nonnegative.
3. The original obtuse witness is bounded above by alpha, so E<2lambda. The generic paid cut already has g>=2lambda; thus E and g are distinct.
4. Erase one occurrence of g and then one occurrence of E. List.perm_cons_erase preserves the sum and mapped-score sums with multiplicities; no set conversion drops repeated gap values.
5. The remaining real sum is pi-g-E=alpha-g<=pi-nlambda<lambda/2. Every remaining gap is bounded by this nonnegative sum, hence has score zero. The outside E also has score zero.
6. Original row score n-2, transported to the actual window reference, must therefore equal gapScore(lambda,g). Its raw floor is at least n-1; hence g>=(n-1)lambda.
7. Rebuild only the separation proof field of that same Clumps object, keeping endpoints, actual gap, cuts and labels. The existing actual different_angle_ge theorem now gives the required (n-1)lambda on B's opposite sides.

This establishes the needed geometric implication as an explicit SOURCE_ONLY proof, rather than accepting it as a caller premise. It has not yet been kernel checked. The argument does not need a new general platform or an externally supplied internal-floor budget.

## Actual transport to C and original weight contradiction

Let W=2^(n-2), delta=Phi-Q>0. Internally choose B's and C's original clump-weight Data. B is nonacute because n>=4 and lambda<=pi/n imply4lambda<=pi, so its actual obtuse witness is in particular at least2lambda.

Choose T as B's original side opposite C. Every v in T is distinct from B and C. The new same-cut bridge gives angle(C,B,v)>=(n-1)lambda. If v and B were in different C sides, C's actual geometry would give angle(B,C,v)>=2lambda. The original triangle sum, nonnegative third angle and pi<(n+1/2)lambda contradict their sum of at least(n+1)lambda. Thus every v in T lies on C's same side as B. This label equality is a CONCLUSION from physical angles, not an assumed relation between B/C partitions.

B's far side T has original weight at least delta+W. Adding B itself contributes W, so C's containing side has weight at least delta+2W. C's other side has weight at least delta+W. Their original total excludes C and is exactly Phi-W. The exact natural identity Q=4W makes Phi-W=delta+3W. The two lower bounds demand at least2delta+3W, contradicting delta>0.

All mass is original actual mass. No restricted counter-model, maximum-zero field, desired gap conclusion or caller budget enters the proof.

## Scope and preservation

The private window support and list-score bridge are minimal local support for this consumer; no additional exported framework was introduced. The existing n4 cloud consumer is not modified. General producer source remains SHA89b3d3f7b68c988c2097bddcfb2254db5d0096149be56245cafd1be06be3a1ac. Old n4 weight source remains SHA25de371c7fad631f6217b38f56e3d73e1525b4678a4167d8a1c82e1170994936.

No mathematical premise was found missing in the bounded static audit. Ordinary Lean/API issues are still possible because the candidate has not run a compiler. No kernel success, actual original max-row existence, general n>=5 capacity, original arbitrary-N lower theorem or prize conclusion is claimed.
