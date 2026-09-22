import Jsp000404.GadgetSelection
import Mathlib.Algebra.BigOperators.Fin

/-!
# AllBad — the incompatible-alignment combinatorics (Lane B3)

The crux of the high regime (`notes/LANE_B.md` §5–6): a saturated
vertex with **no local `δ ≥ 1` gadget** — a *bad* vertex — has its
bit pattern equal to the threshold step at the heavy (`q = n`) gap.
This file formalises, in position space, the exact condition that
edge-side consistency forces between two bad saturated vertices —
the condition extracted by `tools/allbad_dump.py` over all all-bad
skeletons of the `W > 5/2` profiles at `s = n = 4`.

## The extracted invariant (PROVED here at position level)

At a bad vertex `v` with heavy gap at position `hp`, the three
directions have bits `bit p = (p > hp)`: the unique bit transition
sits exactly at the heavy gap (`hp = 2` gives the all-equal
pattern).  Write the three slots relative to `hp` as

    L = hp      (direction just before the heavy gap)
    R = hp + 1  (direction just after it)
    O = hp + 2  (the remaining, "opposite", direction)

Then (`sidePos_L`, `sidePos_R`, `sidePos_O`, all `by decide`):

* `j = L` ⟹ `side(j, k) = -1` for both shared directions `k`;
* `j = R` ⟹ `side(j, k) = +1` for both shared directions `k`;
* `j = O` ⟹ `side(j, L) = +1`, `side(j, R) = -1`.

Edge-side consistency `side_i(j,k) = -side_j(i,k)` therefore forces
(`bad_pair_slots`, `by decide`): two bad vertices `i, j` see each
other **only** as

* `(L,R)` or `(R,L)` — *complementary adjacency*: each is adjacent
  to the other's heavy gap, on complementary sides; or
* `(O,O)` — *mutually opposite*: each sits opposite the other's
  heavy gap, and consistency then forces the *crossed* assignment
  (`bad_pair_OO`): `i`'s L-neighbour is `j`'s R-neighbour and
  vice versa.

Same-side `(L,L)`, `(R,R)` and mixed `(L,O)`, `(O,L)`, `(R,O)`,
`(O,R)` adjacency are edge-inconsistent — this is the precise
"incompatible alignment" condition.

Checker evidence (`tools/allbad_dump.py`, all `W>5/2` profiles):
every signature-consistent all-bad pair satisfies exactly one of
`(L,R), (R,L), (O,O)`; the `(O,O)` case survives exact LP
feasibility only in the two-saturated profiles `(0,0,1,1)`,
`(0,0,1,2)`, `(0,0,1,3)` — in the three-saturated profile
`(0,0,0,2)` every `(O,O)` candidate is LP-infeasible, while
`(L,R)`/`(R,L)` all-bad triples are feasible at `δ_min = 2`.

## Contents

* `badBit`, `sidePos` — position-space model of a bad fan.
* `sidePos_L/_R/_O` — the signature table (finite checks).
* `bad_arc_iff` — equivalence of the threshold form with the
  "no local gadget" dichotomy (`bits equal ⟺ heavy ∉ arc`).
* `thirdPos`, `badPairConsistent`, `bad_pair_slots`,
  `bad_pair_OO` — the two-vertex alignment theorem.
* `VertexData.Saturated`, `saturated_iff_heavy` — saturation at
  `n = 4` forces a single `q = 4` cell.
* `VertexData.Bad`, `VertexData.sideOf`, `sideOf_eq`,
  `two_shared`, `bad_pair_of_skeleton` — the lift to
  `Skeleton 4` of `Gadget.lean`.
-/

namespace Jsp404

/-! ### Position-space model -/

/-- Bit of the direction at position `p` in a bad saturated fan
whose heavy gap sits at position `hp`: the threshold step at `hp`
(`hp = 2` yields the all-`false` pattern). -/
def badBit (hp p : Fin 3) : Bool := decide (hp < p)

/-- Edge-side signature in position space: the side (`+1`/`-1`) on
which direction `k` lies relative to edge direction `j` in a bad
fan with heavy gap `hp`. -/
def sidePos (hp pj pk : Fin 3) : ℤ :=
  (if pk > pj then 1 else -1) *
    (if badBit hp pk = badBit hp pj then 1 else -1)

/-- `j` at the L slot (`pos = hp`, just before the heavy gap):
both shared directions lie on side `-1`. -/
theorem sidePos_L : ∀ hp pk : Fin 3, pk ≠ hp →
    sidePos hp hp pk = -1 := by decide

/-- `j` at the R slot (`pos = hp + 1`, just after the heavy gap):
both shared directions lie on side `+1`. -/
theorem sidePos_R : ∀ hp pk : Fin 3, pk ≠ hp + 1 →
    sidePos hp (hp + 1) pk = 1 := by decide

/-- `j` at the O slot (`pos = hp + 2`): `+1` toward the L
direction (`pos = hp`), `-1` toward the R direction (`pos = hp+1`). -/
theorem sidePos_O : ∀ hp pk : Fin 3, pk ≠ hp + 2 →
    sidePos hp (hp + 2) pk = (if pk = hp then 1 else -1) := by
  decide

/-- The two characterisations of *bad* coincide at position level:
for a threshold fan, `bits j = bits k` iff the arc `j→k` avoids the
heavy gap — i.e. no pair is simultaneously (direct ∧ containing
heavy) [pure cap] or (complementary ∧ avoiding heavy) [charge]. -/
theorem bad_arc_iff : ∀ hp pj pk : Fin 3, pj ≠ pk →
    (decide (hp < pj) = decide (hp < pk) ↔
      ¬(min pj pk ≤ hp ∧ hp < max pj pk)) := by decide

/-! ### Two-vertex alignment -/

/-- The third position: the unique element of `Fin 3` not among
`{a, b}` (meaningful when `a ≠ b`). -/
def thirdPos (a b : Fin 3) : Fin 3 :=
  if a ≠ 0 ∧ b ≠ 0 then 0 else if a ≠ 1 ∧ b ≠ 1 then 1 else 2

theorem thirdPos_eq : ∀ a b c : Fin 3, a ≠ b → c ≠ a → c ≠ b →
    c = thirdPos a b := by decide

/-- Edge-side consistency of a bad pair: `hi`, `hj` are the
heavy-gap positions, `pi`/`pj` the positions of `j` at `i` / `i` at
`j`, `a`/`b` the positions of the first shared vertex at `i`/`j`
(the second shared vertex sits at the third positions). -/
abbrev badPairConsistent (hi hj pi pj a b : Fin 3) : Prop :=
  sidePos hi pi a = -sidePos hj pj b ∧
    sidePos hi pi (thirdPos pi a) = -sidePos hj pj (thirdPos pj b)

/-- **The incompatible-alignment theorem.**  Two bad saturated
vertices sharing an edge see each other only as `(L,R)`, `(R,L)`
(complementary adjacency to the heavy gap) or `(O,O)` (mutually
opposite).  `(L,L)`, `(R,R)`, `(L,O)`, `(R,O)` and their swaps are
edge-inconsistent. -/
theorem bad_pair_slots : ∀ hi hj pi pj a b : Fin 3,
    a ≠ pi → b ≠ pj → badPairConsistent hi hj pi pj a b →
    (pi = hi ∧ pj = hj + 1) ∨ (pi = hi + 1 ∧ pj = hj) ∨
      (pi = hi + 2 ∧ pj = hj + 2) := by decide

/-- In the `(O,O)` case consistency forces the *crossed* heavy-gap
neighbourhood: `i`'s L-direction (`pos = hi`) sits at `j`'s R slot
(`pos = hj + 1`) and `i`'s R-direction sits at `j`'s L slot. -/
theorem bad_pair_OO : ∀ hi hj pi pj a b : Fin 3,
    a ≠ pi → b ≠ pj → badPairConsistent hi hj pi pj a b →
    pi = hi + 2 →
    pj = hj + 2 ∧ (a = hi → b = hj + 1) ∧ (a = hi + 1 → b = hj) := by
  decide

/-! ### Lift to `Skeleton 4` -/

/-- A vertex is *saturated* at `n = 4`: its exponent is `n − 1`. -/
def VertexData.Saturated (v : VertexData 4) : Prop := v.kexp = 3

/-- At `n = 4`, under `0 ≤ q` and `Σq ≤ 4` (the checker's
`q`-tuple constraints), saturation forces a single heavy cell
`q = 4`. -/
theorem saturated_iff_heavy (v : VertexData 4)
    (hq0 : ∀ g, 0 ≤ v.q g) (hqsum : ∑ g, v.q g ≤ 4) :
    v.Saturated ↔
      ∃ g0, v.q g0 = 4 ∧ ∀ g ≠ g0, v.q g = 0 := by
  unfold VertexData.Saturated VertexData.kexp
  rw [Fin.sum_univ_three] at hqsum ⊢
  have h0 := hq0 0; have h1 := hq0 1; have h2 := hq0 2
  have h3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  constructor
  · intro h
    have hq4 : v.q 0 = 4 ∨ v.q 1 = 4 ∨ v.q 2 = 4 := by omega
    rcases hq4 with e | e | e
    · refine ⟨0, e, fun g hg => ?_⟩
      have hg' : g = 1 ∨ g = 2 := by
        have := h3 g; tauto
      rcases hg' with rfl | rfl <;> omega
    · refine ⟨1, e, fun g hg => ?_⟩
      have hg' : g = 0 ∨ g = 2 := by
        have := h3 g; tauto
      rcases hg' with rfl | rfl <;> omega
    · refine ⟨2, e, fun g hg => ?_⟩
      have hg' : g = 0 ∨ g = 1 := by
        have := h3 g; tauto
      rcases hg' with rfl | rfl <;> omega
  · rintro ⟨g0, e, hrest⟩
    have hg : g0 = 0 ∨ g0 = 1 ∨ g0 = 2 := h3 g0
    rcases hg with rfl | rfl | rfl
    · have z1 := hrest 1 (by decide)
      have z2 := hrest 2 (by decide)
      omega
    · have z1 := hrest 0 (by decide)
      have z2 := hrest 2 (by decide)
      omega
    · have z1 := hrest 0 (by decide)
      have z2 := hrest 1 (by decide)
      omega

/-- A vertex is *bad* (combinatorial form): its bit pattern is the
threshold step at the heavy gap `hp`. -/
def VertexData.Bad (v : VertexData 4) (i : Fin 4) (hp : Fin 3) :
    Prop :=
  ∀ k : Fin 4, k ≠ i → v.bits k = decide (hp < v.pos k)

/-- Edge-side signature of a vertex: the side on which `k` lies
relative to edge direction `j` (mirrors the checker `side`). -/
def VertexData.sideOf (v : VertexData 4) (j k : Fin 4) : ℤ :=
  (if v.pos k > v.pos j then 1 else -1) *
    (if v.bits k = v.bits j then 1 else -1)

/-- A bad vertex's `sideOf` reduces to the position-space
`sidePos`. -/
theorem VertexData.sideOf_eq (v : VertexData 4)
    {i j k : Fin 4} {hp : Fin 3}
    (hb : v.Bad i hp) (hj : j ≠ i) (hk : k ≠ i) :
    v.sideOf j k = sidePos hp (v.pos j) (v.pos k) := by
  unfold VertexData.sideOf sidePos badBit
  rw [hb j hj, hb k hk]

/-- Two bad saturated vertices joined by an edge-side-consistent
edge see each other only as `(L,R)`, `(R,L)` or `(O,O)`.  Here
`k1, k2` are the two shared vertices of the edge `i j`. -/
theorem bad_pair_of_skeleton (sk : Skeleton 4) {i j k1 k2 : Fin 4}
    (hij : i ≠ j)
    (hk1i : k1 ≠ i) (hk1j : k1 ≠ j) (hk2i : k2 ≠ i) (hk2j : k2 ≠ j)
    (hkk : k1 ≠ k2) (hi hj : Fin 3)
    (hbi : (sk.vtx i).Bad i hi) (hbj : (sk.vtx j).Bad j hj)
    (hinj : Set.InjOn (sk.vtx i).pos {x | x ≠ i})
    (hjinj : Set.InjOn (sk.vtx j).pos {x | x ≠ j})
    (hec : ∀ k : Fin 4, k ≠ i → k ≠ j →
        (sk.vtx i).sideOf j k = -(sk.vtx j).sideOf i k) :
    ((sk.vtx i).pos j = hi ∧ (sk.vtx j).pos i = hj + 1) ∨
      ((sk.vtx i).pos j = hi + 1 ∧ (sk.vtx j).pos i = hj) ∨
        ((sk.vtx i).pos j = hi + 2 ∧ (sk.vtx j).pos i = hj + 2) := by
  -- positions of j, k1, k2 are pairwise distinct at each end
  have pi_k1 : (sk.vtx i).pos k1 ≠ (sk.vtx i).pos j :=
    fun h => hk1j (hinj hk1i (Ne.symm hij) h)
  have pi_k2 : (sk.vtx i).pos k2 ≠ (sk.vtx i).pos j :=
    fun h => hk2j (hinj hk2i (Ne.symm hij) h)
  have pi_kk : (sk.vtx i).pos k2 ≠ (sk.vtx i).pos k1 :=
    fun h => hkk (hinj hk2i hk1i h).symm
  have pj_k1 : (sk.vtx j).pos k1 ≠ (sk.vtx j).pos i :=
    fun h => hk1i (hjinj hk1j hij h)
  have pj_k2 : (sk.vtx j).pos k2 ≠ (sk.vtx j).pos i :=
    fun h => hk2i (hjinj hk2j hij h)
  have pj_kk : (sk.vtx j).pos k2 ≠ (sk.vtx j).pos k1 :=
    fun h => hkk (hjinj hk2j hk1j h).symm
  -- the second shared vertex occupies the third position
  have tpi : (sk.vtx i).pos k2 =
      thirdPos ((sk.vtx i).pos j) ((sk.vtx i).pos k1) :=
    thirdPos_eq _ _ _ (Ne.symm pi_k1) pi_k2 pi_kk
  have tpj : (sk.vtx j).pos k2 =
      thirdPos ((sk.vtx j).pos i) ((sk.vtx j).pos k1) :=
    thirdPos_eq _ _ _ (Ne.symm pj_k1) pj_k2 pj_kk
  -- edge consistency, transported to position space
  have e1 := hec k1 hk1i hk1j
  rw [VertexData.sideOf_eq _ hbi (Ne.symm hij) hk1i,
    VertexData.sideOf_eq _ hbj hij hk1j] at e1
  have e2 := hec k2 hk2i hk2j
  rw [VertexData.sideOf_eq _ hbi (Ne.symm hij) hk2i,
    VertexData.sideOf_eq _ hbj hij hk2j] at e2
  rw [tpi, tpj] at e2
  exact bad_pair_slots hi hj _ _ _ _ pi_k1 pj_k1 ⟨e1, e2⟩

/-- Existence of the two shared vertices of an edge in `Fin 4`. -/
theorem two_shared {i j : Fin 4} (hij : i ≠ j) :
    ∃ k1 k2 : Fin 4, k1 ≠ i ∧ k1 ≠ j ∧ k2 ≠ i ∧ k2 ≠ j ∧
      k1 ≠ k2 := by
  have hcard : ({i, j}ᶜ : Finset (Fin 4)).card = 2 := by
    rw [Finset.card_compl, Finset.card_pair hij]
    decide
  obtain ⟨k1, k2, hne, hset⟩ := Finset.card_eq_two.mp hcard
  have h1 : k1 ∉ ({i, j} : Finset (Fin 4)) :=
    Finset.mem_compl.mp (hset.symm ▸ Finset.mem_insert_self _ _)
  have h2 : k2 ∉ ({i, j} : Finset (Fin 4)) :=
    Finset.mem_compl.mp
      (hset.symm ▸ Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))
  simp only [Finset.mem_insert, Finset.mem_singleton,
    not_or] at h1 h2
  exact ⟨k1, k2, h1.1, h1.2, h2.1, h2.2, hne⟩

#print axioms Jsp404.saturated_iff_heavy
#print axioms Jsp404.bad_pair_slots
#print axioms Jsp404.bad_pair_OO
#print axioms Jsp404.bad_pair_of_skeleton

end Jsp404
