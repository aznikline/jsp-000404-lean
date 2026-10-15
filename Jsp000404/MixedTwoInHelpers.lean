import Jsp000404.DeletionRigidity

/-!
# Mixed two-in helpers

Equivalent file split of `Jsp000404.MixedTwoInCentral` (original bytes in the
lane verification snapshot); declarations, statements and proofs are verbatim.
Split only so each unit elaborates within the 180 s guard.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

section TwoInCentral

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (4 + 1) → Plane₂} {v : Fin (4 + 1)}
  {theta : Fin 4 → ℝ}

variable (C : SatChart o e n lam c v theta)
include C


/-- Four pairwise-distinct elements of `Fin 4` cover it. -/
theorem fin4_cover {a b d e : Fin 4} (hab : a ≠ b) (had : a ≠ d)
    (hae : a ≠ e) (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e) :
    ∀ j : Fin 4, j = a ∨ j = b ∨ j = d ∨ j = e := by
  intro j
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have had' : a.val ≠ d.val := fun h => had (Fin.ext h)
  have hae' : a.val ≠ e.val := fun h => hae (Fin.ext h)
  have hbd' : b.val ≠ d.val := fun h => hbd (Fin.ext h)
  have hbe' : b.val ≠ e.val := fun h => hbe (Fin.ext h)
  have hde' : d.val ≠ e.val := fun h => hde (Fin.ext h)
  have hav := a.2; have hbv := b.2; have hdv := d.2; have hev := e.2
  have hv := j.2
  have : j.val = a.val ∨ j.val = b.val ∨ j.val = d.val ∨ j.val = e.val := by
    omega
  rcases this with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

/-- A non-short-witness leaves both end gaps `≥ λ`. -/
theorem not_short_witness_bounds {i j : Fin 4} (hij : i ≠ j)
    (h : ¬ ShortWitness (lam := lam) (c := c) o e v theta i j) :
    lam ≤ dirRep o e (c ∘ v.succAbove) i j - theta i ∧
      lam ≤ theta i + Real.pi - dirRep o e (c ∘ v.succAbove) i j := by
  constructor
  · by_contra hc
    push_neg at hc
    exact h ⟨hij, Or.inl hc⟩
  · by_contra hc
    push_neg at hc
    exact h ⟨hij, Or.inr hc⟩

/-- A gap `< λ` contributes `0` to the score. -/
theorem gapScore_zero_of_lt' {g : ℝ} (hg : g < lam) : gapScore lam g = 0 := by
  unfold gapScore
  have : ⌊g / lam⌋₊ = 0 := by
    rw [Nat.floor_eq_zero, div_lt_one C.hlam]
    exact hg
  omega

/-- If the score of a `n − 2` row concentrates on one gap `g`, its floor
is `n − 1`, hence `(n − 1)λ ≤ g`. -/
theorem big_gap_lower {g : ℝ} (hg0 : 0 ≤ g)
    (hs : gapScore lam g = n - 2) :
    (↑(n - 1) : ℝ) * lam ≤ g := by
  have hn3 := C.hn3
  have hfl : ⌊g / lam⌋₊ = n - 1 := by
    unfold gapScore at hs; omega
  have h := floor_mul_le_gap C.hlam hg0
  rw [hfl] at h
  exact h

/-- Expand `linearGapScore` on an explicit three-element row. -/
theorem linScore4 (θ A B D : ℝ) :
    linearGapScore lam θ (θ + Real.pi) [A, B, D] =
      gapScore lam (A - θ) + gapScore lam (B - A) + gapScore lam (D - B) +
        gapScore lam (θ + Real.pi - D) := by
  simp only [linearGapScore]
  ring_nf

/-- `⌊π / λ⌋ = n` gives `π < (n+1)λ`. -/
theorem pi_lt_succ_mul (hn : ⌊Real.pi / lam⌋₊ = n) :
    Real.pi < (↑n + 1) * lam := by
  have h := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn] at h
  rw [div_lt_iff₀ C.hlam] at h
  push_cast at h
  linarith

/-- Legality restricted to the non-anchor subfamily `c ∘ v.succAbove`:
the fields carry over pointwise through the injective reindexing. -/
theorem SatChart.hleg_sub : Section4Legality (c ∘ v.succAbove) lam where
  lam_pos := C.hlam
  inj := fun _ _ h => Fin.succAbove_right_injective (C.hleg.inj h)
  triAngle := fun i j k hij hjk hik =>
    C.hleg.triAngle _ _ _
      (fun hh => hij (Fin.succAbove_right_injective hh))
      (fun hh => hjk (Fin.succAbove_right_injective hh))
      (fun hh => hik (Fin.succAbove_right_injective hh))

/-- **Direction distinctness.** In a legal configuration the outgoing
projective directions from one vertex to two distinct vertices differ:
equal `dirRep` values force the `oangle` between the two chord vectors to
`0` or `π`, so the three points are collinear — excluded by
`legal_triple_not_collinear`. -/
theorem legal_dirRep_ne {s : ℕ} {c' : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c' lam) (he : e ≠ 0)
    {i j k : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    dirRep o e c' i j ≠ dirRep o e c' i k := by
  intro hdir
  have hX0 : c' j - c' i ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hij).symm
  have hY0 : c' k - c' i ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hik).symm
  have hdir' : linRep (o.oangle e (c' j - c' i)) =
      linRep (o.oangle e (c' k - c' i)) := hdir
  have hcl1 := linRep_class (o.oangle e (c' j - c' i))
  have hcl2 := linRep_class (o.oangle e (c' k - c' i))
  have hXY : o.oangle (c' j - c' i) (c' k - c' i) =
      o.oangle e (c' k - c' i) - o.oangle e (c' j - c' i) := by
    have h := o.oangle_add hX0 he hY0
    rw [o.oangle_rev e (c' j - c' i)] at h
    rw [← h]
    abel
  have hπ : o.oangle (c' j - c' i) (c' k - c' i) = 0 ∨
      o.oangle (c' j - c' i) (c' k - c' i) = (Real.pi : ℝ) := by
    rcases hcl1 with h1 | h1 <;> rcases hcl2 with h2 | h2
    · left
      rw [hXY, ← h1, ← h2, hdir', sub_self]
    · right
      rw [hXY, ← h1, eq_sub_of_add_eq h2.symm, hdir', sub_right_comm,
        sub_self, zero_sub, Real.Angle.neg_coe_pi]
    · right
      rw [hXY, ← h2, eq_sub_of_add_eq h1.symm, hdir', sub_sub_self]
    · left
      rw [hXY, eq_sub_of_add_eq h2.symm, eq_sub_of_add_eq h1.symm, hdir',
        sub_self]
  rcases (o.oangle_eq_zero_or_eq_pi_iff_right_eq_smul).mp hπ with hzero | ⟨r, hr⟩
  · exact hX0 hzero
  · have hk_mem : c' k ∈ affineSpan ℝ ({c' i, c' j} : Set Plane₂) := by
      have hk_eq : c' k = AffineMap.lineMap (c' i) (c' j) r := by
        rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, ← hr]
        abel
      rw [hk_eq]
      exact AffineMap.lineMap_mem_affineSpan_pair r (c' i) (c' j)
    have hcol : Collinear ℝ ({c' i, c' j, c' k} : Set Plane₂) := by
      have h0 := collinear_insert_of_mem_affineSpan_pair hk_mem
      rwa [Set.insert_comm (c' k) (c' i), Set.pair_comm (c' k) (c' j)] at h0
    exact legal_triple_not_collinear hleg hij hik hjk hcol

end TwoInCentral

end Jsp404
