import Jsp000404.ActualMaximumMassReduction

/-! Fixed actual configurations attaining a band maximum have a score plateau
down to the open lower boundary. This concerns gapScore, not raw floors:
a raw floor may change from zero to one while gapScore stays zero.
-/

open scoped EuclideanGeometry BigOperators

namespace Jsp404.BandMaximumScorePlateau

private theorem sum_map_le {α : Type*} (l : List α) (f g : α → ℕ)
    (hle : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (hle a (by simp))
        (ih (fun x hx => hle x (by simp [hx])))

private theorem map_eq_of_sum_eq {α : Type*} (l : List α) (f g : α → ℕ)
    (hle : ∀ x ∈ l, f x ≤ g x) (heq : (l.map f).sum = (l.map g).sum) :
    ∀ x ∈ l, f x = g x := by
  induction l generalizing f g with
  | nil => simp
  | cons a l ih =>
      have hhead : f a ≤ g a := hle a (by simp)
      have htail : ∀ x ∈ l, f x ≤ g x := fun x hx => hle x (by simp [hx])
      have ht := sum_map_le l f g htail
      simp only [List.map_cons, List.sum_cons] at heq
      have ha : f a = g a := by omega
      have heqt : (l.map f).sum = (l.map g).sum := by omega
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact ih f g htail heqt x hx

theorem gapScore_le_of_scale_le {scale scale' g : ℝ} (hpos : 0 < scale')
    (hsmall : scale' ≤ scale) (hg : 0 ≤ g) :
    gapScore scale g ≤ gapScore scale' g := by
  unfold gapScore
  exact Nat.sub_le_sub_right
    (Nat.floor_mono (div_le_div_of_nonneg_left hg hpos hsmall)) 1

private theorem actual_gaps_nonneg {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    (i : Fin s) : ∀ g ∈ cycGaps (directionRow o e c i), 0 ≤ g := by
  apply cycGaps_nonneg (directionRow_sorted o e c i)
    (fun x hx => directionRow_mem_Ico o e c hx)
  intro hnil
  have hlen := directionRow_length o e c i
  rw [hnil] at hlen
  simp at hlen
  omega

theorem actual_rowScore_le_of_scale_le {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    {scale scale' : ℝ} (hpos : 0 < scale') (hsmall : scale' ≤ scale) (i : Fin s) :
    rowScore scale (directionRow o e c i) ≤ rowScore scale' (directionRow o e c i) :=
  sum_map_le _ _ _ fun g hg => gapScore_le_of_scale_le hpos hsmall
    (actual_gaps_nonneg hs o e c i g hg)

/-- Every smaller scale still in the band preserves the actual potential
and every whole-row score. The maximum is an attained band maximum. -/
theorem actual_band_maximum_score_plateau {s M : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    {rho upper scale scale' : ℝ} (hrho : 0 ≤ rho)
    (hleg : Section4Legality c scale) (_habove : rho < scale) (hupper : scale ≤ upper)
    (hpot : potential scale (directionRows o e c) = M)
    (hmax : ActualMaximumMassReduction.BandMaximal o e rho upper M)
    (hlo : rho < scale') (hsmall : scale' ≤ scale) :
    potential scale' (directionRows o e c) = M ∧
      ∀ i : Fin s, rowScore scale' (directionRow o e c i) =
        rowScore scale (directionRow o e c i) := by
  have hpos : 0 < scale' := hrho.trans_lt hlo
  have hleg' : Section4Legality c scale' := by
    refine ⟨hpos, hleg.inj, ?_⟩
    intro i j k hij hjk hik
    have h := hleg.triAngle i j k hij hjk hik
    linarith
  have hrow := actual_rowScore_le_of_scale_le hs o e c hpos hsmall
  have hpow : ∀ i ∈ (Finset.univ : Finset (Fin s)),
      2 ^ rowScore scale (directionRow o e c i) ≤
        2 ^ rowScore scale' (directionRow o e c i) :=
    fun i _ => Nat.pow_le_pow_right (by decide : 0 < 2) (hrow i)
  have hmono : potential scale (directionRows o e c) ≤
      potential scale' (directionRows o e c) := Finset.sum_le_sum hpow
  have hbound := hmax hs c scale' hlo (hsmall.trans hupper) hleg'
  have hnew : potential scale' (directionRows o e c) = M := by omega
  have hsum : (∑ i : Fin s, 2 ^ rowScore scale (directionRow o e c i)) =
      ∑ i : Fin s, 2 ^ rowScore scale' (directionRow o e c i) := hpot.trans hnew.symm
  have heq := (Finset.sum_eq_sum_iff_of_le hpow).mp hsum
  refine ⟨hnew, ?_⟩
  intro i
  exact (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))
    (heq i (Finset.mem_univ i))).symm

/-- Equality of nonnegative gap-score sums forces each actual gap score
to remain unchanged. No raw-floor equality is asserted. -/
theorem actual_band_maximum_gap_score_plateau {s M : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    {rho upper scale scale' : ℝ} (hrho : 0 ≤ rho)
    (hleg : Section4Legality c scale) (habove : rho < scale) (hupper : scale ≤ upper)
    (hpot : potential scale (directionRows o e c) = M)
    (hmax : ActualMaximumMassReduction.BandMaximal o e rho upper M)
    (hlo : rho < scale') (hsmall : scale' ≤ scale) :
    ∀ i : Fin s, ∀ g ∈ cycGaps (directionRow o e c i),
      gapScore scale' g = gapScore scale g := by
  have hrow := (actual_band_maximum_score_plateau hs o e c hrho hleg habove hupper
    hpot hmax hlo hsmall).2
  intro i g hg
  exact (map_eq_of_sum_eq _ _ _
    (fun x hx => gapScore_le_of_scale_le (hrho.trans_lt hlo) hsmall
      (actual_gaps_nonneg hs o e c i x hx)) (hrow i).symm g hg).symm

theorem actual_band_maximum_flat_plateau {s M : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    {rho upper scale scale' : ℝ} (hrho : 0 ≤ rho)
    (hleg : Section4Legality c scale) (habove : rho < scale) (hupper : scale ≤ upper)
    (hpot : potential scale (directionRows o e c) = M)
    (hmax : ActualMaximumMassReduction.BandMaximal o e rho upper M)
    (hflat : Flat scale (directionRows o e c))
    (hlo : rho < scale') (hsmall : scale' ≤ scale) :
    Flat scale' (directionRows o e c) := by
  have hrow := (actual_band_maximum_score_plateau hs o e c hrho hleg habove hupper
    hpot hmax hlo hsmall).2
  intro i
  change rowScore scale' (directionRow o e c i) = 0
  rw [hrow i]
  exact hflat i

/-- A flat maximizer's actual gaps are bounded by twice the lower band
boundary, by testing scales arbitrarily close to that boundary. -/
theorem actual_flat_band_maximum_gap_le_two_rho {s M : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    {rho upper scale : ℝ} (hrho : 0 ≤ rho)
    (hleg : Section4Legality c scale) (habove : rho < scale) (hupper : scale ≤ upper)
    (hpot : potential scale (directionRows o e c) = M)
    (hmax : ActualMaximumMassReduction.BandMaximal o e rho upper M)
    (hflat : Flat scale (directionRows o e c)) :
    ∀ i : Fin s, ∀ g ∈ cycGaps (directionRow o e c i), g ≤ 2 * rho := by
  intro i g hg
  by_contra hnot
  have hgt : 2 * rho < g := by linarith
  have hmin : rho < min scale (g / 2) := lt_min habove (by linarith)
  let scale' := (rho + min scale (g / 2)) / 2
  have hlo : rho < scale' := by dsimp [scale']; linarith
  have hlt : scale' < min scale (g / 2) := by dsimp [scale']; linarith
  have hsmall : scale' ≤ scale := hlt.le.trans (min_le_left _ _)
  have hf := actual_band_maximum_flat_plateau hs o e c hrho hleg habove hupper
    hpot hmax hflat hlo hsmall
  have hb := cycGaps_lt_two_mul_of_rowScore_zero (hrho.trans_lt hlo) (hf i) g hg
  have hltg : scale' < g / 2 := hlt.trans_le (min_le_right _ _)
  linarith

#print axioms gapScore_le_of_scale_le
#print axioms actual_rowScore_le_of_scale_le
#print axioms actual_band_maximum_score_plateau
#print axioms actual_band_maximum_gap_score_plateau
#print axioms actual_band_maximum_flat_plateau
#print axioms actual_flat_band_maximum_gap_le_two_rho

end Jsp404.BandMaximumScorePlateau
