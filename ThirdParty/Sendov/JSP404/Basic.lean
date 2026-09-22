import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card

/-!
# The geometric extremal quantity in JSP-000404 / Erdős problem 504

All angles in this file are the actual unoriented Euclidean angles supplied by Mathlib.
Configurations are finite sets, so their cardinalities count distinct points. The value
`alpha n` is the supremum of the angles guaranteed in every configuration of `n` points.
The meaningful domain of this definition is `3 ≤ n`.

`maxAngle` includes a zero only to give the empty set of triangles a harmless value.
For a configuration with at least three points, its maximum is attained by a triple
of pairwise distinct points; see `hasLargeAngle_maxAngle`.
-/

noncomputable section

namespace JSP404

abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A configuration contains an angle at least `θ`, using three distinct points. -/
def HasLargeAngle (s : Finset Point) (θ : ℝ) : Prop :=
  ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ θ ≤ EuclideanGeometry.angle a b c

/-- Every configuration of `n` distinct planar points contains an angle at least `θ`. -/
def Guaranteed (n : ℕ) (θ : ℝ) : Prop :=
  ∀ s : Finset Point, s.card = n → HasLargeAngle s θ

/-- The angle threshold in the Erdős–Szekeres / Blumenthal problem. -/
def alpha (n : ℕ) : ℝ := sSup {θ : ℝ | Guaranteed n θ}

/-- All unoriented angles formed by pairwise distinct points of a configuration. -/
def angleValues (s : Finset Point) : Finset ℝ := by
  classical
  exact ((s.product (s.product s)).filter fun t =>
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2).image
    (fun t => EuclideanGeometry.angle t.1 t.2.1 t.2.2)

@[simp] theorem mem_angleValues {s : Finset Point} {θ : ℝ} :
    θ ∈ angleValues s ↔
      ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ EuclideanGeometry.angle a b c = θ := by
  classical
  simp only [angleValues, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨a, b, c⟩, ⟨hmem, hab, hac, hbc⟩, hθ⟩
    rcases Finset.mem_product.mp hmem with ⟨ha, hmem⟩
    rcases Finset.mem_product.mp hmem with ⟨hb, hc⟩
    exact ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hθ⟩
  · rintro ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hθ⟩
    exact ⟨⟨a, b, c⟩,
      ⟨Finset.mem_product.mpr ⟨ha, Finset.mem_product.mpr ⟨hb, hc⟩⟩, hab, hac, hbc⟩, hθ⟩

/-- The largest angle in a configuration, with value zero if it has fewer than three points. -/
def maxAngle (s : Finset Point) : ℝ := by
  classical
  exact (insert 0 (angleValues s)).max' (by simp)

theorem maxAngle_nonneg (s : Finset Point) : 0 ≤ maxAngle s := by
  classical
  exact Finset.le_max' _ 0 (by simp)

theorem angle_le_maxAngle {s : Finset Point} {a b c : Point}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    EuclideanGeometry.angle a b c ≤ maxAngle s := by
  classical
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem <|
    mem_angleValues.mpr ⟨a, ha, b, hb, c, hc, hab, hac, hbc, rfl⟩

theorem maxAngle_le {s : Finset Point} {θ : ℝ} (hθ : 0 ≤ θ)
    (h : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s,
      a ≠ b → a ≠ c → b ≠ c → EuclideanGeometry.angle a b c ≤ θ) :
    maxAngle s ≤ θ := by
  classical
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hθ
  · obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, rfl⟩ := mem_angleValues.mp hx
    exact h a ha b hb c hc hab hac hbc

theorem maxAngle_le_pi (s : Finset Point) : maxAngle s ≤ Real.pi :=
  maxAngle_le Real.pi_pos.le (fun _ _ _ _ _ _ _ _ _ => EuclideanGeometry.angle_le_pi _ _ _)

theorem hasLargeAngle_zero {s : Finset Point} (hs : 3 ≤ s.card) : HasLargeAngle s 0 := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hs
  exact ⟨a, ha, b, hb, c, hc, hab, hac, hbc, EuclideanGeometry.angle_nonneg _ _ _⟩

theorem hasLargeAngle_maxAngle {s : Finset Point} (hs : 3 ≤ s.card) :
    HasLargeAngle s (maxAngle s) := by
  classical
  have hm : maxAngle s ∈ insert 0 (angleValues s) := Finset.max'_mem _ _
  rcases Finset.mem_insert.mp hm with hm | hm
  · rw [hm]
    exact hasLargeAngle_zero hs
  · obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hangle⟩ := mem_angleValues.mp hm
    exact ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hangle.ge⟩

theorem hasLargeAngle_iff_le_maxAngle {s : Finset Point} {θ : ℝ} (hs : 3 ≤ s.card) :
    HasLargeAngle s θ ↔ θ ≤ maxAngle s := by
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hθ⟩
    exact hθ.trans (angle_le_maxAngle ha hb hc hab hac hbc)
  · intro hθ
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hm⟩ := hasLargeAngle_maxAngle hs
    exact ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hθ.trans hm⟩

theorem hasLargeAngle_mono {s t : Finset Point} {θ : ℝ} (hst : s ⊆ t)
    (h : HasLargeAngle s θ) : HasLargeAngle t θ := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hθ⟩ := h
  exact ⟨a, hst ha, b, hst hb, c, hst hc, hab, hac, hbc, hθ⟩

theorem maxAngle_mono {s t : Finset Point} (hst : s ⊆ t) : maxAngle s ≤ maxAngle t := by
  apply maxAngle_le (maxAngle_nonneg _)
  intro a ha b hb c hc hab hac hbc
  exact angle_le_maxAngle (hst ha) (hst hb) (hst hc) hab hac hbc

theorem guaranteed_zero {n : ℕ} (hn : 3 ≤ n) : Guaranteed n 0 := by
  intro s hs
  exact hasLargeAngle_zero (hs ▸ hn)

theorem guaranteed_le_pi {n : ℕ} {θ : ℝ} (h : Guaranteed n θ) : θ ≤ Real.pi := by
  obtain ⟨s, hs⟩ := Finset.exists_card_eq (α := Point) n
  obtain ⟨a, _, b, _, c, _, _, _, _, hθ⟩ := h s hs
  exact hθ.trans (EuclideanGeometry.angle_le_pi _ _ _)

theorem guaranteed_bddAbove (n : ℕ) : BddAbove {θ : ℝ | Guaranteed n θ} :=
  ⟨Real.pi, fun _ h => guaranteed_le_pi h⟩

theorem alpha_nonneg {n : ℕ} (hn : 3 ≤ n) : 0 ≤ alpha n :=
  le_csSup (guaranteed_bddAbove n) (guaranteed_zero hn)

theorem alpha_le_pi {n : ℕ} (hn : 3 ≤ n) : alpha n ≤ Real.pi :=
  csSup_le ⟨0, guaranteed_zero hn⟩ (fun _ h => guaranteed_le_pi h)

theorem le_alpha {n : ℕ} {θ : ℝ} (h : Guaranteed n θ) : θ ≤ alpha n :=
  le_csSup (guaranteed_bddAbove n) h

/-- A single configuration gives an upper bound on the universal threshold. -/
theorem alpha_le_of_configuration {n : ℕ} {s : Finset Point} {θ : ℝ}
    (hn : 3 ≤ n) (hs : s.card = n)
    (h : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s,
      a ≠ b → a ≠ c → b ≠ c → EuclideanGeometry.angle a b c ≤ θ) :
    alpha n ≤ θ := by
  apply csSup_le ⟨0, guaranteed_zero hn⟩
  intro φ hφ
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hφ⟩ := hφ s hs
  exact hφ.trans (h a ha b hb c hc hab hac hbc)

theorem alpha_le_maxAngle {n : ℕ} {s : Finset Point} (hn : 3 ≤ n) (hs : s.card = n) :
    alpha n ≤ maxAngle s :=
  alpha_le_of_configuration hn hs (fun _ ha _ hb _ hc hab hac hbc =>
    angle_le_maxAngle ha hb hc hab hac hbc)

/-- Increasing the number of points preserves every universally guaranteed angle. -/
theorem guaranteed_mono {m n : ℕ} {θ : ℝ} (hmn : m ≤ n)
    (h : Guaranteed m θ) : Guaranteed n θ := by
  intro s hs
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq (hs ▸ hmn)
  exact hasLargeAngle_mono hts (h t ht)

theorem alpha_mono {m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) : alpha m ≤ alpha n :=
  csSup_le_csSup (guaranteed_bddAbove n) ⟨0, guaranteed_zero hm⟩
    (fun _ h => guaranteed_mono hmn h)

/-- The supremum defining `alpha` is itself a universal guarantee.
This does not assert that any configuration attains the infimum of its maximum angles. -/
theorem guaranteed_alpha {n : ℕ} (hn : 3 ≤ n) : Guaranteed n (alpha n) := by
  intro s hs
  exact (hasLargeAngle_iff_le_maxAngle (hs ▸ hn)).mpr (alpha_le_maxAngle hn hs)

theorem guaranteed_iff_le_alpha {n : ℕ} {θ : ℝ} (hn : 3 ≤ n) :
    Guaranteed n θ ↔ θ ≤ alpha n := by
  constructor
  · exact le_alpha
  · intro hθ s hs
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hα⟩ := guaranteed_alpha hn s hs
    exact ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hθ.trans hα⟩

/-- The actual maxima of all configurations of a fixed cardinality. -/
def configurationMaxima (n : ℕ) : Set ℝ :=
  {θ | ∃ s : Finset Point, s.card = n ∧ maxAngle s = θ}

theorem configurationMaxima_nonempty (n : ℕ) : (configurationMaxima n).Nonempty := by
  obtain ⟨s, hs⟩ := Finset.exists_card_eq (α := Point) n
  exact ⟨maxAngle s, s, hs, rfl⟩

theorem configurationMaxima_bddBelow (n : ℕ) : BddBelow (configurationMaxima n) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨s, _, rfl⟩
  exact maxAngle_nonneg s

/-- The supremum of guaranteed angles equals the infimum of configuration maxima. -/
theorem alpha_eq_sInf {n : ℕ} (hn : 3 ≤ n) : alpha n = sInf (configurationMaxima n) := by
  apply le_antisymm
  · apply le_csInf (configurationMaxima_nonempty n)
    rintro _ ⟨s, hs, rfl⟩
    exact alpha_le_maxAngle hn hs
  · apply le_alpha
    intro s hs
    apply (hasLargeAngle_iff_le_maxAngle (hs ▸ hn)).mpr
    exact csInf_le (configurationMaxima_bddBelow n) ⟨s, hs, rfl⟩

/-- Every strict upper bound on `alpha` is witnessed by an actual configuration.
This is the approximation interface needed when no optimal configuration exists. -/
theorem exists_configuration_maxAngle_lt {n : ℕ} {θ : ℝ} (hn : 3 ≤ n)
    (hθ : alpha n < θ) :
    ∃ s : Finset Point, s.card = n ∧ maxAngle s < θ := by
  classical
  have hng : ¬ Guaranteed n θ := fun h => (not_le_of_gt hθ) (le_alpha h)
  obtain ⟨s, hs⟩ := not_forall.mp hng
  obtain ⟨hcard, hangle⟩ := not_imp.mp hs
  refine ⟨s, hcard, lt_of_not_ge ?_⟩
  intro hle
  exact hangle ((hasLargeAngle_iff_le_maxAngle (hcard ▸ hn)).mpr hle)

/-- A matching lower bound and arbitrarily close upper constructions identify `alpha`.
The upper construction need not attain the limiting value. -/
theorem alpha_eq_of_bounds {n : ℕ} {θ : ℝ} (hn : 3 ≤ n)
    (hlower : Guaranteed n θ)
    (hupper : ∀ ε : ℝ, 0 < ε →
      ∃ s : Finset Point, s.card = n ∧ maxAngle s ≤ θ + ε) :
    alpha n = θ := by
  apply le_antisymm _ (le_alpha hlower)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨s, hs, hmax⟩ := hupper ε hε
  exact (alpha_le_maxAngle hn hs).trans hmax

/-- The triangle angle sum supplies a first nonzero universal lower bound. -/
theorem hasLargeAngle_pi_div_three {s : Finset Point} (hs : 3 ≤ s.card) :
    HasLargeAngle s (Real.pi / 3) := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hs
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi c hab.symm
  by_cases h₁ : Real.pi / 3 ≤ EuclideanGeometry.angle a b c
  · exact ⟨a, ha, b, hb, c, hc, hab, hac, hbc, h₁⟩
  by_cases h₂ : Real.pi / 3 ≤ EuclideanGeometry.angle b c a
  · exact ⟨b, hb, c, hc, a, ha, hbc, hab.symm, hac.symm, h₂⟩
  exact ⟨c, hc, a, ha, b, hb, hac.symm, hbc.symm, hab, by linarith⟩

theorem guaranteed_pi_div_three {n : ℕ} (hn : 3 ≤ n) : Guaranteed n (Real.pi / 3) := by
  intro s hs
  exact hasLargeAngle_pi_div_three (hs ▸ hn)

theorem pi_div_three_le_alpha {n : ℕ} (hn : 3 ≤ n) : Real.pi / 3 ≤ alpha n :=
  le_alpha (guaranteed_pi_div_three hn)

end JSP404
