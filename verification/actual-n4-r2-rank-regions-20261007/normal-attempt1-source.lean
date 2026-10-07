import Jsp000404.SatScalarExtraction
import Jsp000404.FivePointCapacity

set_option autoImplicit false

/-!
Actual eight-center two-low rank regions.

The arbitrary-size actual two-defect-two cluster theorem supplies the
common region. The real angle-rank permutation then gives only the pairs
(0,1), (0,6), or (5,6). No six-center pure-tail theorem is used, and no
classification of a bare GenericModel is claimed.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualN4R2RankRegions

/-- The rank positions and their actual common region are retained together.
The first branch has all other ranks below both lows; the middle branch
has them between the lows; the last branch has them above both lows. -/
def RankRegions (angle : Fin 7 → ℝ) (lo hi : Fin 7) : Prop :=
  (lo = 5 ∧ hi = 6 ∧ ∀ z, z ≠ lo → z ≠ hi → angle z < angle lo) ∨
  (lo = 0 ∧ hi = 6 ∧ ∀ z, z ≠ lo → z ≠ hi → angle lo < angle z ∧ angle z < angle hi) ∨
  (lo = 0 ∧ hi = 1 ∧ ∀ z, z ≠ lo → z ≠ hi → angle hi < angle z)

private theorem ranks_of_below {angle : Fin 7 → ℝ} (hmono : StrictMono angle)
    {lo hi : Fin 7} (horder : lo < hi)
    (hbelow : ∀ z, z ≠ lo → z ≠ hi → angle z < angle lo) :
    lo = 5 ∧ hi = 6 := by
  have hhi : hi = 6 := by
    by_contra h
    have h6hi : (6 : Fin 7) ≠ hi := Ne.symm h
    have h6lo : (6 : Fin 7) ≠ lo := by omega
    have h6lt := hmono.lt_iff_lt.mp (hbelow 6 h6lo h6hi)
    omega
  have hlo : lo = 5 := by
    by_contra h
    have h5lo : (5 : Fin 7) ≠ lo := Ne.symm h
    have h5hi : (5 : Fin 7) ≠ hi := by rw [hhi]; decide
    have h5lt := hmono.lt_iff_lt.mp (hbelow 5 h5lo h5hi)
    omega
  exact ⟨hlo, hhi⟩

private theorem ranks_of_between {angle : Fin 7 → ℝ} (hmono : StrictMono angle)
    {lo hi : Fin 7} (horder : lo < hi)
    (hbetween : ∀ z, z ≠ lo → z ≠ hi → angle lo < angle z ∧ angle z < angle hi) :
    lo = 0 ∧ hi = 6 := by
  have hlo : lo = 0 := by
    by_contra h
    have h0lo : (0 : Fin 7) ≠ lo := Ne.symm h
    have h0hi : (0 : Fin 7) ≠ hi := by omega
    have hlt0 := hmono.lt_iff_lt.mp (hbetween 0 h0lo h0hi).1
    omega
  have hhi : hi = 6 := by
    by_contra h
    have h6lo : (6 : Fin 7) ≠ lo := by rw [hlo]; decide
    have h6hi : (6 : Fin 7) ≠ hi := Ne.symm h
    have h6lt := hmono.lt_iff_lt.mp (hbetween 6 h6lo h6hi).2
    omega
  exact ⟨hlo, hhi⟩

private theorem ranks_of_above {angle : Fin 7 → ℝ} (hmono : StrictMono angle)
    {lo hi : Fin 7} (horder : lo < hi)
    (habove : ∀ z, z ≠ lo → z ≠ hi → angle hi < angle z) :
    lo = 0 ∧ hi = 1 := by
  have hlo : lo = 0 := by
    by_contra h
    have h0lo : (0 : Fin 7) ≠ lo := Ne.symm h
    have h0hi : (0 : Fin 7) ≠ hi := by omega
    have hlt0 := hmono.lt_iff_lt.mp (habove 0 h0lo h0hi)
    omega
  have hhi : hi = 1 := by
    by_contra h
    have h1lo : (1 : Fin 7) ≠ lo := by rw [hlo]; decide
    have h1hi : (1 : Fin 7) ≠ hi := Ne.symm h
    have hlt1 := hmono.lt_iff_lt.mp (habove 1 h1lo h1hi)
    omega
  exact ⟨hlo, hhi⟩

private theorem ranked_angle_strictMono
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
    {c : Fin 8 → Plane₂} {v : Fin 8} {theta : Fin 7 → ℝ}
    (C : SatChart o e 4 lam c v theta) :
    StrictMono (theta ∘ SatScalarExtraction.sigma C) := by
  intro i j hij
  change theta (SatScalarExtraction.sigma C i) < theta (SatScalarExtraction.sigma C j)
  rw [SatScalarExtraction.sigma_spec C i, SatScalarExtraction.sigma_spec C j]
  exact SatScalarExtraction.sortedTheta_strictMono C hij

private theorem ordered_chart_rank_regions
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
    {c : Fin 8 → Plane₂} {v : Fin 8} {theta : Fin 7 → ℝ}
    (C : SatChart o e 4 lam c v theta)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    {lo hi : Fin 7} (horder : lo < hi)
    (hlo : rowDefect 4 lam
      (directionRow o e c (v.succAbove (SatScalarExtraction.sigma C lo))) = 2)
    (hhi : rowDefect 4 lam
      (directionRow o e c (v.succAbove (SatScalarExtraction.sigma C hi))) = 2) :
    RankRegions (theta ∘ SatScalarExtraction.sigma C) lo hi := by
  have hmono := ranked_angle_strictMono C
  have htheta : theta (SatScalarExtraction.sigma C lo) <
      theta (SatScalarExtraction.sigma C hi) := hmono horder
  have hne : SatScalarExtraction.sigma C lo ≠ SatScalarExtraction.sigma C hi :=
    SatScalarExtraction.sigma_ne C (ne_of_lt horder)
  have hclass := theta_regions_collapse (SatScalarExtraction.theta_injective C)
    htheta (fun {x y} hxa hxb hya hyb hxy =>
      two_defect_two_theta_clusters o e C.he C.hlam C.hn
        (by decide : 4 ≤ 7) C.hleg C hsat hne hlo hhi htheta hxa hxb hya hyb hxy)
  have hneq {z r : Fin 7} (h : z ≠ r) :
      SatScalarExtraction.sigma C z ≠ SatScalarExtraction.sigma C r :=
    SatScalarExtraction.sigma_ne C h
  rcases hclass with hbelow | hbetween | habove
  · have hb : ∀ z, z ≠ lo → z ≠ hi →
        (theta ∘ SatScalarExtraction.sigma C) z < (theta ∘ SatScalarExtraction.sigma C) lo :=
      fun z hzlo hzhi => hbelow _ (hneq hzlo) (hneq hzhi)
    obtain ⟨hl, hh⟩ := ranks_of_below hmono horder hb
    exact Or.inl ⟨hl, hh, hb⟩
  · have hm : ∀ z, z ≠ lo → z ≠ hi →
        (theta ∘ SatScalarExtraction.sigma C) lo < (theta ∘ SatScalarExtraction.sigma C) z ∧
        (theta ∘ SatScalarExtraction.sigma C) z < (theta ∘ SatScalarExtraction.sigma C) hi :=
      fun z hzlo hzhi => hbetween _ (hneq hzlo) (hneq hzhi)
    obtain ⟨hl, hh⟩ := ranks_of_between hmono horder hm
    exact Or.inr (Or.inl ⟨hl, hh, hm⟩)
  · have ha : ∀ z, z ≠ lo → z ≠ hi →
        (theta ∘ SatScalarExtraction.sigma C) hi < (theta ∘ SatScalarExtraction.sigma C) z :=
      fun z hzlo hzhi => habove _ (hneq hzlo) (hneq hzhi)
    obtain ⟨hl, hh⟩ := ranks_of_above hmono horder ha
    exact Or.inr (Or.inr ⟨hl, hh, ha⟩)

/-- In an actual eight-center saturated chart, the two actual defect-two
rows have unordered rank pair `(0,1)`, `(0,6)`, or `(5,6)`. The actual
common below/between/above region is included in the conclusion. No tail
defect hypothesis, caller rank array, or bare scalar model is needed. -/
theorem actual_chart_low_rank_regions
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
    {c : Fin 8 → Plane₂} {v : Fin 8} {theta : Fin 7 → ℝ}
    (C : SatChart o e 4 lam c v theta)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    {a b : Fin 7} (hab : a ≠ b)
    (hda : rowDefect 4 lam (directionRow o e c (v.succAbove a)) = 2)
    (hdb : rowDefect 4 lam (directionRow o e c (v.succAbove b)) = 2) :
    ∃ lo hi : Fin 7, lo < hi ∧
      ((SatScalarExtraction.sigma C lo = a ∧ SatScalarExtraction.sigma C hi = b) ∨
       (SatScalarExtraction.sigma C lo = b ∧ SatScalarExtraction.sigma C hi = a)) ∧
      RankRegions (theta ∘ SatScalarExtraction.sigma C) lo hi := by
  obtain ⟨ra, hra⟩ := (SatScalarExtraction.sigma_bijective C).surjective a
  obtain ⟨rb, hrb⟩ := (SatScalarExtraction.sigma_bijective C).surjective b
  have hne : ra ≠ rb := fun h =>
    hab (hra.symm.trans ((congrArg (SatScalarExtraction.sigma C) h).trans hrb))
  have hdefa : rowDefect 4 lam
      (directionRow o e c (v.succAbove (SatScalarExtraction.sigma C ra))) = 2 := by
    simpa only [hra] using hda
  have hdefb : rowDefect 4 lam
      (directionRow o e c (v.succAbove (SatScalarExtraction.sigma C rb))) = 2 := by
    simpa only [hrb] using hdb
  rcases lt_or_gt_of_ne hne with horder | horder
  · exact ⟨ra, rb, horder, Or.inl ⟨hra, hrb⟩,
      ordered_chart_rank_regions C hsat horder hdefa hdefb⟩
  · exact ⟨rb, ra, horder, Or.inr ⟨hrb, hra⟩,
      ordered_chart_rank_regions C hsat horder hdefb hdefa⟩

/-- The original legal configuration internally supplies its saturated
ray window, actual ranking and the three possible two-low regions. All
input defects are measured in the caller's original reference chart. -/
theorem exists_actual_low_rank_regions
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} {c : Fin 8 → Plane₂} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi / lam) = 4)
    {v A B : Fin 8} (hvA : v ≠ A) (hvB : v ≠ B) (hAB : A ≠ B)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hdA : rowDefect 4 lam (directionRow o e c A) = 2)
    (hdB : rowDefect 4 lam (directionRow o e c B) = 2) :
    ∃ e' : Plane₂, e' ≠ 0 ∧ ∃ theta : Fin 7 → ℝ, ∃ sigma : Fin 7 → Fin 7,
      Function.Bijective sigma ∧ StrictMono (theta ∘ sigma) ∧
      (∀ i, theta i ∈ Set.Icc 0 (Real.pi - 4 * lam) ∧
        o.oangle e' (c (v.succAbove i) - c v) = (theta i : Real.Angle)) ∧
      ∃ lo hi : Fin 7, lo < hi ∧
        ((v.succAbove (sigma lo) = A ∧ v.succAbove (sigma hi) = B) ∨
         (v.succAbove (sigma lo) = B ∧ v.succAbove (sigma hi) = A)) ∧
        RankRegions (theta ∘ sigma) lo hi := by
  obtain ⟨e', he', theta, htheta⟩ := saturated_ray_window o e he
    (s := 7) (by decide) (by decide) hleg.lam_pos hn hleg v hsat
  let C : SatChart o e' 4 lam c v theta :=
    ⟨he', by decide, hleg.lam_pos, hn, hleg, htheta⟩
  have href (i : Fin 8) : rowDefect 4 lam (directionRow o e' c i) =
      rowDefect 4 lam (directionRow o e c i) :=
    rowDefect_directionRow_reference_eq o e' e he' he c hleg.inj i hleg.lam_pos (by decide) hn
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hvA.symm
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hvB.symm
  have hab : a ≠ b := by
    intro h
    exact hAB (ha.symm.trans ((congrArg v.succAbove h).trans hb))
  have hsat' : rowDefect 4 lam (directionRow o e' c v) = 1 := (href v).trans hsat
  have hda : rowDefect 4 lam (directionRow o e' c (v.succAbove a)) = 2 := by
    rw [ha, href]
    exact hdA
  have hdb : rowDefect 4 lam (directionRow o e' c (v.succAbove b)) = 2 := by
    rw [hb, href]
    exact hdB
  obtain ⟨lo, hi, horder, hswap, hregions⟩ :=
    actual_chart_low_rank_regions C hsat' hab hda hdb
  refine ⟨e', he', theta, SatScalarExtraction.sigma C,
    SatScalarExtraction.sigma_bijective C, ranked_angle_strictMono C, htheta,
    lo, hi, horder, ?_, hregions⟩
  rcases hswap with ⟨hl, hh⟩ | ⟨hl, hh⟩
  · exact Or.inl ⟨(congrArg v.succAbove hl).trans ha, (congrArg v.succAbove hh).trans hb⟩
  · exact Or.inr ⟨(congrArg v.succAbove hl).trans hb, (congrArg v.succAbove hh).trans ha⟩

#print axioms actual_chart_low_rank_regions
#print axioms exists_actual_low_rank_regions

end Jsp404.ActualN4R2RankRegions
