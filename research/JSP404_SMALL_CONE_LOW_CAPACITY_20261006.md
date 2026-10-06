# Genuine small-cone LOW capacity without saturation

Owned source: `Jsp000404/SmallConeLowCapacity.lean`, plus this receipt.
The whole new source has passed genuine strict and target-normal checks,
with four standard-three-axiom exports, and is frozen. No old source,
root import, audit, Git or quota operation was changed.

## Exact actual cone capacity

For any actual legal `c : Fin s -> Plane₂`, `s>=3`, nonzero reference `e`,
actual `n=floor(pi/lam)>=3`, and actual anchor `v`, suppose every outgoing
actual ray pair has ordinary vector angle at most beta. If

`beta < (n+1)*lam-pi`,

then the true full original potential is at most `2^n`. This budget is
equivalent to `delta+beta/lam<1`, where delta is the actual period remainder.
The cone width `omega=beta/lam` is independent of delta. No fake SatChart
identifies the two numbers. There is no saturation or caller-supplied
window, bins, mass bound, or capacity field in this interface.

In LOW, `delta<1/2` and `beta<lam/2` imply the displayed joint budget.
Thus a physical half-lambda cone gives the sharp LOW capacity even when
its anchor is not saturated.

## Actual window, common bins and full-row transport

The old OneSaturatedHigh narrow-window proof retains an unused SAT
hypothesis in its public signature. That hypothesis cannot be fabricated.
The new private chart reuses its valid actual geometry and counting logic
without that signature restriction.

The actual rays construct a reference and angles `theta_i in [0,beta]`.
Every tail chord is genuinely in `[lam,U]`, where `U=pi-lam+beta`, by the
two endpoint triangle caps. Put `m=n-1` and
`width=(pi-2*lam+beta)/m`. The true period lower bound gives positive width;
the joint budget gives `width<lam`. The common cover ends exactly at U.
Its actual endpoint padding satisfies

`lam-theta_i<=lam`,
`theta_i+pi-U=lam+theta_i-beta<=lam`.

The existing anchored-row identity includes the actual anchor direction
in each original full remaining row. Empty-bin arithmetic and the actual
binary graph packing therefore bound those rows' total weight by `2^m`.
The anchor's universal actual score bound is `<=n-1`, from the verified
cell/defect identities, without SAT. Adding its weight gives `2^n`.
Reference invariance returns the entire true potential to the original chart.

## beta=0 and typed domain

There is no beta>0 hypothesis. The physical diagonal ray pair and its
nonzero vector derive beta>=0. For n>=3, the corridor numerator is at
least `(n-2)*lam`, hence strictly positive even when beta=0. Thus no
zero-width branch is silently omitted. Actual legal three-point families
cannot have a zero-width ray cone, but the proof does not need to exclude
that case by an additional assumption.

## Downstream actual counterexample constraints

An actual LOW counterexample has, at every anchor, two distinct other
actual centers whose outgoing ray angle is at least lam/2. A finite maximum
over the actual ray pairs constructs this witness internally.

Let `rho=pi/(n+1/2)`. The same original LOW counterexample cannot have a
saturated row at rho. Original legality weakens genuinely to rho, its
actual floor is n, and the saturated-angle theorem at rho gives physical
spread at most `rho/2`. Since the original scale is strictly greater than
rho, this is a small cone at the original scale. The new non-SAT capacity
consumer contradicts the original excess. No SAT-at-rho to SAT-at-lam
transfer is assumed; the ordinary physical rays are reused instead.

This excludes boundary SAT only. It does not prove that all NoSAT models
are empty, the entire LOW capacity, bare17/bare21, or allN.

## Validation and handoff

Frozen source SHA-256:
`abe98cda61b5ac13447ee5d960dfb2943114f9602b64f1fadd22377631fa7188`.
Every statement is explicitly typed, with autoImplicit disabled.

| Check | Actual exit | Seconds | time-l maximum RSS | Sampled actual Lean peak |
|---|---:|---:|---:|---:|
| Single-file strict0 | 0 | 5.187 | 3,197,272,064 B | 3,143,286,784 B |
| Genuine specified target normal | 0 | 5.519 | 3,201,204,224 B | 3,200,925,696 B |

Both succeeded on the first attempt, printing the four exports with only
`[propext, Classical.choice, Quot.sound]`, and no warning in the owned
source. Old normal dependency warnings were replayed and retained. The
actual-process cap was 8 GiB with no interruption; group peaks
3,845,160,960 B and 3,974,987,776 B were recorded only.

Raw logs: `.lake/small-cone-low-capacity-strict-20261006.log` and
`.lake/small-cone-low-capacity-normal-20261006.log`.
True normal `.olean`:
`.lake/build/lib/lean/Jsp000404/SmallConeLowCapacity.olean`.
It has 876,768 bytes and SHA-256
`f9d63fd53508e3806cf5bf66cd58d6c9e852aad596caa5d5b553e608839e36ac`.

Verified exports: `potential_le_two_pow_of_cone_budget`,
`potential_le_two_pow_of_low_small_cone`,
`exists_large_anchor_angle_of_low_counter`, and
`no_low_boundary_saturation_of_counter`.

All owned Lean/Lake processes exited before a fresh sole window was handed
to the protected inflation owner. No duplicate full root build was performed.
There is no sorry, native_decide or custom axiom in the source.
