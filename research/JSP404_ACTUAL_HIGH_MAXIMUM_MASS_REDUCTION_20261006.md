# Actual HIGH maximum-mass counterexample reduction

Owned new source: `Jsp000404/ActualHighMaximumMassReduction.lean` only, plus
this independent receipt. Earlier sources, root imports, audits and Git are
unchanged. The final source has passed genuine strict and normal target
checks and is now frozen. The exported declaration depends only on the
standard three axioms `[propext, Classical.choice, Quot.sound]`.

## Exact interface

`exists_flat_high_band_counter_maximizer` takes an actual configuration
`c : Fin s -> Plane₂`, `s >= 3`, a nonzero reference `e`, and:

- `n >= 4`;
- original `Section4Legality c lam`;
- `floor(pi/lam) = n`;
- `delta = pi/lam-n >= 1/2`;
- `sendovCap n true < potential lam (directionRows o e c)`.

The strict inequality `delta < 1` follows from the actual floor hypothesis;
it need not be an additional caller hypothesis. The conclusion constructs:

- `M > sendovCap n true = 2^n+2^(n-2)`;
- `M <= 2^(n+1)`, from the independent classical coarse bound;
- `BandMaximal o e (pi/(n+1)) (pi/(n+1/2)) M`;
- a scale in `(pi/(n+1), pi/(n+1/2)]`;
- an actual `d : Fin M -> Plane₂`, legal at that scale, with all row scores
  zero and potential exactly `M`.

The caller supplies neither maximality, flatness, a cardinality capacity,
a maximum exponent profile, nor an attained real angle optimum.

## Static derivation

The floor upper inequality gives `pi/lam < n+1`. Since `lam > 0`, this is
`pi/(n+1) < lam`. HIGH's delta inequality gives
`n+1/2 <= pi/lam`, hence `lam <= pi/(n+1/2)`. Both denominators are positive.

The generic `ActualMaximumMassReduction.exists_flat_band_maximizer` is
instantiated with `k=n+1`, `rho=pi/(n+1)`, and `upper=pi/(n+1/2)`.
Its required classical comparison is equality after the Nat-to-Real cast.
It constructs an actual attained maximum `M` at least the original potential.
The original strict excess therefore gives the displayed strict cap excess.
The generic constructor also supplies the actual flat realization of `M`.

Only the independent bound `2^(n+1)` is used to construct the maximum.
The sharp HIGH cap is used solely as the original counterexample threshold.
No sharp HIGH capacity is assumed or proved by this reduction.

## Practical bounds and outstanding mathematics

For n=4 the model has `21 <= M <= 32` in
`(pi/5, 2*pi/9]`. For n=5 it has `41 <= M <= 64` in
`(pi/6, 2*pi/11]`. These are reductions to real maximal counter-models,
not proofs that such models are impossible.

The separate maximum-deletion consumer belongs to root. This module does
not duplicate its incoming-charge or emitter bound. Bare17/bare21 exclusions,
general sharp HIGH capacity, allN and the prize remain open.

## Verification and release

Frozen source SHA-256:
`57177e34a7531726c299725b3448448b2662fd42ee0f8763942738c7efc58655`.
The generic dependency was consumed only after its owner confirmed genuine
strict/normal PASS and source freeze, at SHA-256
`994f865b569a9954304eade3ad1e4f16be9bdfdf77080d5c412085b516c4f41c`.

Both completed checks used this exact frozen HIGH source:

| Check | Actual exit | Seconds | time-l maximum RSS | Sampled actual Lean peak |
|---|---:|---:|---:|---:|
| `lake env lean --trust=0` | 0 | 4.682 | 3,149,856,768 B | 3,085,221,888 B |
| `lake build Jsp000404.ActualHighMaximumMassReduction` | 0 | 9.207 | 3,166,076,928 B | 3,107,766,272 B |

Both actual Lean peaks were below the 3.5-GiB admission cap, without cap
interruption. Group peaks 3,831,283,712 B and 3,881,730,048 B respectively
were recorded only, not used as admission values.

Raw logs are `.lake/actual-high-maximum-mass-strict-20261006.log` and
`.lake/actual-high-maximum-mass-normal-20261006.log`. The strict scope printed
the exported declaration's standard-three-axiom dependency and had zero
warnings. The normal target built the unchanged generic dependency and HIGH
module sequentially and finished successfully; this was one specified
target, not a full root build. Existing dependency warnings were replayed;
the owned HIGH source had no warning and again printed standard three axioms.

The real generated `.olean` is
`.lake/build/lib/lean/Jsp000404/ActualHighMaximumMassReduction.olean`.
It has 214,544 bytes and SHA-256
`cfb23a2efee0c70d0ea18ccf3d7fb01b535dd4436d60e2e268e8d7e8ed08e753`.
All owned Lean processes exited before the slot was explicitly handed to
root's FlatBand maximum-deletion consumer, then the uniform producer.
No further compilation or source edits are planned by this owner.

No literal `sorry`, `native_decide`, or custom axiom occurs in the owned source.
