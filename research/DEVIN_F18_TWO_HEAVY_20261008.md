# F18 two-heavy branch (t = 2): actual kernel closure

Module: `Jsp000404/DevinF18TwoHeavyApex.lean` (new; imports only
`ActualF18NonacuteApex`, `ActualMixedRigidCardinality`, `ActualHullTurnBudget`).

Every hypothesis is the original actual minimum-counter
`ActualMinimalBandCounterexample.Model o e (pi/(4+1/2)) (pi/4) 16 (s+1) c lam`,
`potential = 18`, plus (for the headline) `(heavyIndices o e c lam).card = 2`.
The point count `s+1 = 7`, the hull/interior split, HA/HM/HO kinds, interior
partitions, class weights, heavy clumps and turn budgets are produced
internally from checked seed tools. No cover, partition, deletion bound or
capacity is a caller premise.

## Theorems

| Theorem | Scope |
|---|---|
| `actual_interior_apex_has_heavy_of_nonacute` | any F18: a nonacute heavy forces every interior apex to contain a *different* heavy |
| `actual_obtuse_heavy_interior_false` | any F18: heavy with an angle `> pi-2lam` (HO) + interior point impossible |
| `actual_two_interior_nonacute_heavy_false` | heavy count `<= 2`, nonacute heavy: two interior points impossible |
| `actual_all_heavy_nonacute_interior_false` | any F18: all heavies nonacute + interior point impossible |
| `actual_F18_two_heavy_nonacute_interior_false` | t = 2, a nonacute heavy, an interior point: impossible |
| `actual_obtuse_heavy_other_nonacute_false` | any F18: an HO heavy and a different nonacute heavy cannot coexist |
| `actual_F18_two_heavy_false` | **whole t = 2 F18 branch impossible** |

## Paper argument (checked before Lean)

Notation: original weight `w(q) = 2^score`; total 18; erasing a heavy leaves 14.
Heavy-clump tool: a nonacute heavy has two clumps, cross angle `>= 2lam`,
each of original weight `>= 6`, hence weights exactly a split of 14.
Interior-class tool: three classes, weights `>= 4`, total 16, so each `<= 8`;
apex vs. other class angle `>= 3lam`; different classes `>= 2lam`.
Triangle step: angles `>= 3lam` and `>= 2lam` in one triangle give
`5lam > pi` since `lam > 2pi/9`.

1. *Apex has a heavy (nonacute h).* Apex `U` of interior `p` excludes `h`
   (NonacuteApex). If `U` is pure light it has `>= 4` hull lights
   (PureLightBlock), weight `>= 8`. For `q in U`, `angle(q,p,h) >= 3lam`, so
   `q` is in `h`'s clump of `p` (triangle step); that clump has weight
   `>= 2 + 8 = 10`, other clump `>= 6`, total `> 14`.
2. *HO + interior.* Far clump `T` of HO heavy `h` (w.r.t. `p`) has
   `angle(v,h,p) >= 3lam` (HO cone dichotomy), so `T` lies in the class of
   `h` at `p`; that class weight `>= 4 + 6 = 10 > 8`.
3. *HO + other nonacute C.* Same far clump `T` of HO `B` w.r.t. `C` forces
   `T` into `C`'s clump containing `B`: weight `>= 4 + 6 = 10`, other `>= 6`,
   total `> 14`.
4. *t = 2, interior p, nonacute h.* By 2 the heavy is not HO-obtuse, so all
   its angles `<= pi - 2lam`. By 1 the apex of `p` holds the other heavy `C`,
   which by NonacuteApex is acute, i.e. HA with cap `pi - 3lam`. Two interior
   points would need two distinct apex heavies other than `h` (disjoint
   apices), impossible, so the other six points are hull vertices: budget
   `2 + 3 + 4*1 = 9 > 8`.
5. *t = 2, interior, both heavies acute (HA2).* Budget on all hull vertices:
   `|hull| + 2 + 2 <= 8`, so `|hull| <= 4`, at most two hull lights and at
   least three interior points. A pure-light apex would need four hull lights,
   so each interior apex contains a heavy; apices are disjoint, so three
   interior points need three distinct heavies.
6. *t = 2, all seven hull.* If a heavy is acute: `7 + 2 > 8`. If both
   nonacute and one is HO-obtuse: step 3. Otherwise caps `pi - 2lam` on both:
   `7 + 1 + 1 > 8`.

Controls/traps checked: heavy singleton classes are never prohibited (step 1
only uses the pure-light case); hull means original `IsHullVertex`; every
mass comparison uses a single cover (one heavy's two clumps, or one interior
point's three classes); no fractional scores. All weight lower bounds are
F18 Model consequences (incoming-gain zero / whole-clump deletion) that fail
for valid F16 configurations, so valid F16/SAT/four-LI controls are not
contradicted: the theorems never apply to them (no `Model` instance).

## Scope

Proves only the t = 2 (two heavy, hence N = 7) branch of F18. Does not
touch t = 0, 1, 3, other potentials, or the original all-N lower theorem,
which remains open. Not integrated into the root import file.
