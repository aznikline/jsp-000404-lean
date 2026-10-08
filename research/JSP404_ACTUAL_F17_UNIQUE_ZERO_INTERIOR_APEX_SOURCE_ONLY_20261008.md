# Actual F17 unique-zero interior apexes — SOURCE_ONLY

The new candidate is `Jsp000404/ActualF17UniqueZeroInteriorApex.lean`,
343 lines, source SHA
`8a3a58cd9e031f7380903ce15a66692546ce0030f80c688932e1b1b7a23ec399`.
The file did not exist when this task began. Only this new file and this
new note were written. No Lean, solver, Git, quota operation or old-source
edit was performed. This module is SOURCE_ONLY and is not part of the
existing 2677 selected-declaration audit gate.

The actual parent `ActualF17UniqueZeroClassWeight.lean` is consumed at its
verified final source
`a8623225cf23b802643038f113eaa1d0256be886ae4649e400d337aacfda6f9f`.
Its scoped receipt is
`research/JSP404_ACTUAL_F17_UNIQUE_ZERO_CLASS_WEIGHT_RECEIPT_20261008.json`
(SHA `5d3c8fadb53a0cfcff8cd616b6745580dc0184d7c0174401144930dfafd38bf0`).
The earlier failed 1f04 candidate is not passing evidence. The parent
was not modified while constructing this consumer.

## Exact original premises

Every public entry takes the original actual n4 LOW whole-band
minimum-counter `H : ActualMinimalBandCounterexample.Model ... 16 ...`,
a nonzero direction reference, an original zero z, and positivity of
all original indices other than z. No class data, weights, cardinality,
capacity, gain array, common cone, hull selection or subset Model is a
caller premise.

The interior subcases explicitly take original score one and original
non-hull status. In the two-center entries both p and q have these
properties and are distinct. No theorem treats the unique zero as a
score-one center or assumes that z is an original hull vertex.

The heavy entry takes original score two and an actual pair of distinct
rays making angle at least `2*lam` at that heavy. No HM/HO label or
caller-supplied clumps is accepted. The checked original heavy-clump
producer constructs the physical clumps internally.

## Exact public signatures

These are the exact declaration headers from the frozen candidate;
proof bodies are omitted here. The namespace is
`Jsp404.ActualF17UniqueZeroInteriorApex`.

```lean
noncomputable def actualClassWeight {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (z : Fin (s + 1)) (hz : rowScore lam (directionRow o e c z) = 0)
    (hpositive : ∀ q : Fin (s + 1), q ≠ z → 1 ≤ rowScore lam (directionRow o e c q))
    (p : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = 1)
    (hnot : ¬ IsHullVertex c p) : ActualF17UniqueZeroClassWeight.Data o e c lam z p
```

```lean
theorem actual_two_interior_not_apex {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (z : Fin (s + 1)) (hz : rowScore lam (directionRow o e c z) = 0)
    (hpositive : ∀ r : Fin (s + 1), r ≠ z → 1 ≤ rowScore lam (directionRow o e c r))
    (p q : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = 1)
    (hq : rowScore lam (directionRow o e c q) = 1)
    (hpnot : ¬ IsHullVertex c p) (hqnot : ¬ IsHullVertex c q) (hpq : p ≠ q) :
    (actualClassWeight o e he H z hz hpositive p hp hpnot).partition.classOf
      ⟨q, hpq.symm⟩ ≠ 1
```

```lean
theorem actual_interior_apex_full_hull_or_zero {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (z : Fin (s + 1)) (hz : rowScore lam (directionRow o e c z) = 0)
    (hpositive : ∀ r : Fin (s + 1), r ≠ z → 1 ≤ rowScore lam (directionRow o e c r))
    (p : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = 1)
    (hpnot : ¬ IsHullVertex c p) :
    ∀ q ∈ (actualClassWeight o e he H z hz hpositive p hp hpnot).classMembers 1,
      IsHullVertex c q ∨ q = z
```

```lean
theorem actual_two_interior_apex_disjoint {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (z : Fin (s + 1)) (hz : rowScore lam (directionRow o e c z) = 0)
    (hpositive : ∀ r : Fin (s + 1), r ≠ z → 1 ≤ rowScore lam (directionRow o e c r))
    (p q : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = 1)
    (hq : rowScore lam (directionRow o e c q) = 1)
    (hpnot : ¬ IsHullVertex c p) (hqnot : ¬ IsHullVertex c q) (hpq : p ≠ q) :
    Disjoint ((actualClassWeight o e he H z hz hpositive p hp hpnot).classMembers 1)
      ((actualClassWeight o e he H z hz hpositive q hq hqnot).classMembers 1)
```

```lean
theorem actual_nonacute_heavy_not_in_interior_apex {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (z : Fin (s + 1)) (hz : rowScore lam (directionRow o e c z) = 0)
    (hpositive : ∀ r : Fin (s + 1), r ≠ z → 1 ≤ rowScore lam (directionRow o e c r))
    (p : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = 1)
    (hpnot : ¬ IsHullVertex c p)
    (h : Fin (s + 1)) (hh : rowScore lam (directionRow o e c h) = 2)
    (hwide : ∃ a b : Fin (s + 1), a ≠ h ∧ b ≠ h ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c h) (c b)) :
    h ∉ (actualClassWeight o e he H z hz hpositive p hp hpnot).classMembers 1
```

## Internal arguments and scope

The canonical `actualClassWeight` is a fixed choice of the checked
unique-zero actual producer. Its original three class masses sum to
fifteen, every pair of different classes has mass at least seven, and
any individual class has mass at most eight. A heavy singleton remains
possible; the class containing z may have mass three.

For mutual nonapex, if q belongs to p's apex, every original member of
p's two other classes must belong to q's class of p. Otherwise the
actual triangle has angles at least `3*lam` and `2*lam`, impossible
because `5*lam>pi`. Including p gives original mass at least nine in a
class of q bounded by eight. The actual index inequalities follow from
class membership and the explicit p/q distinction.

For the hull-or-zero statement, suppose an apex member q differs from z
and is not an original hull vertex. The checked interior-defect theorem
gives defect at least three at the actual floor-four scale. Together
with the actual score/defect identity and positivity away from z, this
forces original score one at q. The previous mutual-nonapex consumer
then excludes that membership. This concludes `IsHullVertex c q ∨ q=z`;
it does not remove the unique-zero alternative.

For disjointness, a shared member would give two actual angles at least
`3*lam` in the p/q/member triangle. The mutual nonapex results justify
the required nonapex classes of the opposite centers. The triangle sum
then contradicts `6*lam>pi`. In particular at most one such apex can
contain z, without asserting that any apex does contain z.

For a nonacute heavy in p's apex, the same actual `3*lam`/`2*lam`
triangle obstruction places p and both of its nonapex classes into one
physical clump at the heavy. Their original mass is at least `2+7=9`.
The checked heavy-clump theorem gives opposite original mass at least
`(17-16)+4=5`. The checked critical reduction internally gives original
potential seventeen; the original heavy weighs four, so its entire
others mass is thirteen. The actual Bool clumps partition those original
others, and `9+5>13` is impossible. No Bool labels are shared between
observers or transported without an actual triangle proof.

## Intended selected audit list

There are five `#print axioms` commands: one canonical choice and four
necessary-structure consumers. The intended standard-axiom acceptance
set is `{propext, Classical.choice, Quot.sound}`; no actual print result
has yet been obtained for this new module.

- `Jsp404.ActualF17UniqueZeroInteriorApex.actualClassWeight`
- `Jsp404.ActualF17UniqueZeroInteriorApex.actual_two_interior_not_apex`
- `Jsp404.ActualF17UniqueZeroInteriorApex.actual_interior_apex_full_hull_or_zero`
- `Jsp404.ActualF17UniqueZeroInteriorApex.actual_two_interior_apex_disjoint`
- `Jsp404.ActualF17UniqueZeroInteriorApex.actual_nonacute_heavy_not_in_interior_apex`

These are necessary structures in the unique-original-zero subdomain.
They do not prove that any particular apex contains a heavy or that a
permitted heavy singleton is impossible. None excludes all four Z=1
profiles, constructs a mandatory deletion selector, excludes the
all-zero N=17 profile, or proves the arbitrary-cardinality original
problem. Compilation must wait for Root's formal single-process window;
no candidate result is promoted by this note.
