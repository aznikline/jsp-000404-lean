import Jsp000404.GeometricDeletion
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Actual deletion progress from a common oriented cone

Every ray from `q` is assumed to make angle at most `π/2 - λ` with one
fixed nonzero vector `u`. A point of least `u`-projection among the other
actual points sees the ray to `q` at angle at least `λ` from every other
ray. Legality gives the complementary upper bound, so it emits to `q`.

If `q` has least original row score, its deletion preserves or increases
the actual potential. No capacity, floor-strip, saturation, or desired
emission premise is used. The cone concerns actual oriented rays, not
an unoriented projective gap. Its existence for arbitrary overfull
configurations is not asserted.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ConeDeletionProgress

/-- An actual point of least projection supplies all the lower angles
needed by the geometric emission lemma. Projection ties are allowed. -/
theorem exists_angle_lower_of_common_cone {s : ℕ} (hs : 2 ≤ s)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (_hleg : Section4Legality c lam) (q : Fin (s + 1))
    (u : Plane₂) (_hu : u ≠ 0)
    (hcone : ∀ j : Fin (s + 1), j ≠ q →
      InnerProductGeometry.angle (c j - c q) u ≤ Real.pi / 2 - lam) :
    ∃ i : Fin (s + 1), i ≠ q ∧
      ∀ j : Fin (s + 1), j ≠ i → j ≠ q →
        lam ≤ ∠ (c q) (c i) (c j) := by
  classical
  let S : Finset (Fin (s + 1)) := Finset.univ.erase q
  have hS : S.Nonempty := by
    let z : Fin s := ⟨0, by omega⟩
    exact ⟨q.succAbove z, Finset.mem_erase.mpr
      ⟨Fin.succAbove_ne q z, Finset.mem_univ _⟩⟩
  let proj (j : Fin (s + 1)) : ℝ := inner ℝ u (c j - c q)
  obtain ⟨i, hiS, hmin⟩ := Finset.exists_min_image S proj hS
  have hi : i ≠ q := (Finset.mem_erase.mp hiS).1
  refine ⟨i, hi, ?_⟩
  intro j _hji hjq
  have hp : 0 ≤ inner ℝ u (c j - c i) := by
    have hjS : j ∈ S := Finset.mem_erase.mpr ⟨hjq, Finset.mem_univ _⟩
    have h := hmin j hjS
    change inner ℝ u (c i - c q) ≤ inner ℝ u (c j - c q) at h
    rw [inner_sub_right, inner_sub_right] at h
    rw [inner_sub_right]
    linarith
  have hhalf : Real.pi / 2 ≤
      InnerProductGeometry.angle (-u) (c j - c i) :=
    InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mp (by
      rw [inner_neg_left]
      linarith)
  have hcone_i : InnerProductGeometry.angle (-u) (c q - c i) ≤
      Real.pi / 2 - lam := by
    rw [show c q - c i = -(c i - c q) by abel,
      InnerProductGeometry.angle_neg_neg,
      InnerProductGeometry.angle_comm]
    exact hcone i hi
  have htriangle := InnerProductGeometry.angle_le_angle_add_angle
    (-u) (c q - c i) (c j - c i)
  change lam ≤ InnerProductGeometry.angle (c q - c i) (c j - c i)
  linarith

/-- The lower angles are actual emission, using precisely the original
triangle upper bounds from `Section4Legality`. -/
theorem exists_emitter_of_common_cone {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (q : Fin (s + 1))
    (u : Plane₂) (hu : u ≠ 0)
    (hcone : ∀ j : Fin (s + 1), j ≠ q →
      InnerProductGeometry.angle (c j - c q) u ≤ Real.pi / 2 - lam) :
    ∃ i : Fin (s + 1), i ≠ q ∧
      1 ≤ rowGain lam (directionRow o e c i) (deleteIndex o e c q i) := by
  obtain ⟨i, hi, hangle⟩ := exists_angle_lower_of_common_cone hs hleg q u hu hcone
  exact ⟨i, hi, rowGain_pos_of_forall_angle_ge o e c hleg he hi (by omega) hangle⟩

/-- If the apex has least original row score, the cone produces a
genuine actual deletion whose potential is at least the original one. -/
theorem potential_le_delete_of_min_score_common_cone {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (q : Fin (s + 1))
    (u : Plane₂) (hu : u ≠ 0)
    (hcone : ∀ j : Fin (s + 1), j ≠ q →
      InnerProductGeometry.angle (c j - c q) u ≤ Real.pi / 2 - lam)
    (hmin : ∀ i : Fin (s + 1),
      rowScore lam (directionRow o e c q) ≤ rowScore lam (directionRow o e c i)) :
    potential lam (directionRows o e c) ≤
      potential lam (directionRows o e (c ∘ q.succAbove)) := by
  obtain ⟨i, hi, hg⟩ := exists_emitter_of_common_cone hs o e he hleg q u hu hcone
  rw [potential_sub_config o e q lam]
  exact removable_of_gain1_ge hleg.lam_pos
    (fun v i => deleteIndex o e c v i) (directionRows o e c) q
    (fun i => directionRow_sorted o e c i)
    (fun i b hb => Set.mem_Ico.mp (directionRow_mem_Ico o e c hb))
    (fun i => by
      change 2 ≤ (directionRow o e c i).length
      rw [directionRow_length o e c i]
      omega)
    (fun i hi => deleteIndex_lt o e c hi)
    i hi hg (hmin i)

/-- The actual zero-gain normal form excludes this common oriented cone.
No conclusion about an arbitrary full no-saturation configuration is made. -/
theorem not_common_cone_of_zero_incoming {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (q : Fin (s + 1))
    (hzero : ∀ i : Fin (s + 1), i ≠ q →
      rowGain lam (directionRow o e c i) (deleteIndex o e c q i) = 0)
    (u : Plane₂) (hu : u ≠ 0) :
    ¬ ∀ j : Fin (s + 1), j ≠ q →
      InnerProductGeometry.angle (c j - c q) u ≤ Real.pi / 2 - lam := by
  intro hcone
  obtain ⟨i, hi, hg⟩ := exists_emitter_of_common_cone hs o e he hleg q u hu hcone
  rw [hzero i hi] at hg
  omega

/-- A least-weight actual over-capacity configuration whose deletion is
under that cap cannot have the cone. The cap is explicit local data. -/
theorem not_common_cone_of_min_score_overfull_delete {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (q : Fin (s + 1))
    (hmin : ∀ i : Fin (s + 1),
      rowScore lam (directionRow o e c q) ≤ rowScore lam (directionRow o e c i))
    (cap : ℕ) (hover : cap < potential lam (directionRows o e c))
    (hdelete : potential lam (directionRows o e (c ∘ q.succAbove)) ≤ cap)
    (u : Plane₂) (hu : u ≠ 0) :
    ¬ ∀ j : Fin (s + 1), j ≠ q →
      InnerProductGeometry.angle (c j - c q) u ≤ Real.pi / 2 - lam := by
  intro hcone
  have h := potential_le_delete_of_min_score_common_cone hs o e he hleg q u hu hcone hmin
  omega

#print axioms exists_angle_lower_of_common_cone
#print axioms exists_emitter_of_common_cone
#print axioms potential_le_delete_of_min_score_common_cone
#print axioms not_common_cone_of_zero_incoming
#print axioms not_common_cone_of_min_score_overfull_delete

end Jsp404.ConeDeletionProgress
