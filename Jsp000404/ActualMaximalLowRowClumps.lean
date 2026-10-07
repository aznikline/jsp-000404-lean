import Jsp000404.ActualHullSmallScoreTypes
import Jsp000404.ActualMixedRigidCardinality

set_option autoImplicit false

/-! Actual two-clump producer for a maximal nonsaturated LOW row.

The original full-hull window and the internal cut are chosen here.
The score, legality, full-hull membership and an actual wide pair are
the only geometric inputs. This file is SOURCE_ONLY until a separate
strict and genuine-normal verification receipt is published.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualMaximalLowRowClumps

private noncomputable def innerGaps (l : List ℝ) : List ℝ :=
  (l.dropLast.zip l.tail).map (fun ab => cyclicDiff ab.1 ab.2)

private noncomputable def positiveGaps (lam : ℝ) (l : List ℝ) : List ℝ :=
  l.filter (fun g => decide (0 < gapScore lam g))

private theorem cyclicDiff_eq_sub_of_le {a b : ℝ} (hab : a ≤ b) :
    cyclicDiff a b = b - a := by
  by_cases h : a = b
  · simp [cyclicDiff, h]
  · have hlt : a < b := lt_of_le_of_ne hab h
    simp [cyclicDiff, h, hlt]

private theorem innerGaps_cons (a b : ℝ) (l : List ℝ) :
    innerGaps (a :: b :: l) = cyclicDiff a b :: innerGaps (b :: l) := by
  simp [innerGaps, List.dropLast_cons_cons]

private theorem innerGap_spec (l : List ℝ) :
    l.SortedLE → ∀ g, g ∈ innerGaps l →
      ∃ a b : ℝ, a ∈ l ∧ b ∈ l ∧ a ≤ b ∧ g = b - a ∧
        ∀ z ∈ l, z ≤ a ∨ b ≤ z := by
  induction l with
  | nil =>
      intro hs g hg
      simp [innerGaps] at hg
  | cons a l ih =>
      intro hs g hg
      cases l with
      | nil => simp [innerGaps] at hg
      | cons b bs =>
          have hp := List.pairwise_cons.mp hs.pairwise
          have ht : (b :: bs).SortedLE := hp.2.sortedLE
          have hab : a ≤ b := hp.1 b (by simp)
          rw [innerGaps_cons, List.mem_cons] at hg
          rcases hg with hg | hg
          · refine ⟨a, b, by simp, by simp, hab,
              hg.trans (cyclicDiff_eq_sub_of_le hab), ?_⟩
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact Or.inl le_rfl
            · exact Or.inr (by simpa using ht.pairwise.rel_head hz)
          · obtain ⟨u, v, hu, hv, huv, hgap, hcut⟩ := ih ht g hg
            refine ⟨u, v, List.mem_cons_of_mem _ hu,
              List.mem_cons_of_mem _ hv, huv, hgap, ?_⟩
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact Or.inl (hp.1 u hu)
            · exact hcut z hz

private theorem innerGaps_nonneg {l : List ℝ} (hs : l.SortedLE) :
    ∀ g ∈ innerGaps l, 0 ≤ g := by
  intro g hg
  obtain ⟨a, b, _, _, hab, rfl, _⟩ := innerGap_spec l hs g hg
  exact sub_nonneg.mpr hab

private theorem support_inner_sum {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (S : ActualHullSmallScoreTypes.Support o c lam p) :
    (innerGaps (directionRow o S.window.base c p)).sum = S.window.width := by
  have h := cycGaps_sum_eq_pi (directionRow_sorted o S.window.base c p) S.nonempty
  rw [cycGaps_eq_map_append_wrap _ S.nonempty, List.sum_append,
    List.sum_cons, List.sum_nil, S.wrap_eq] at h
  change (innerGaps (directionRow o S.window.base c p)).sum +
    (Real.pi - S.window.width + 0) = Real.pi at h
  linarith

private theorem support_score_split {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (S : ActualHullSmallScoreTypes.Support o c lam p) :
    rowScore lam (directionRow o S.window.base c p) =
      ((innerGaps (directionRow o S.window.base c p)).map (gapScore lam)).sum +
        gapScore lam (Real.pi - S.window.width) := by
  unfold rowScore
  rw [cycGaps_eq_map_append_wrap _ S.nonempty, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, S.wrap_eq]
  rfl

private theorem score_mul_lower {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g)
    {k : ℕ} (hk : 1 ≤ k) (hscore : k ≤ gapScore lam g) :
    ((k + 1 : ℕ) : ℝ) * lam ≤ g := by
  have hf : k + 1 ≤ ⌊g / lam⌋₊ := by
    unfold gapScore at hscore
    omega
  have hf' : ((k + 1 : ℕ) : ℝ) ≤ (⌊g / lam⌋₊ : ℝ) := by exact_mod_cast hf
  exact (le_div_iff₀ hlam).mp
    (hf'.trans (Nat.floor_le (div_nonneg hg hlam.le)))

private theorem score_filter (lam : ℝ) (l : List ℝ) :
    ((positiveGaps lam l).map (gapScore lam)).sum =
      (l.map (gapScore lam)).sum := by
  induction l with
  | nil => simp [positiveGaps]
  | cons g l ih =>
      by_cases hg : 0 < gapScore lam g
      · simpa [positiveGaps, hg] using congrArg (fun x => gapScore lam g + x) ih
      · have hz : gapScore lam g = 0 := by omega
        simpa [positiveGaps, hg, hz] using ih

/-- Each positive score costs one additional lambda, with multiplicity. -/
private theorem score_and_count_lower (lam : ℝ) (hlam : 0 < lam)
    (l : List ℝ) : (∀ g ∈ l, 0 ≤ g) →
      (((l.map (gapScore lam)).sum + (positiveGaps lam l).length : ℕ) : ℝ) * lam ≤
        l.sum := by
  induction l with
  | nil => intro h; simp [positiveGaps]
  | cons g l ih =>
      intro hnonneg
      have hg0 := hnonneg g (by simp)
      have ht := ih (fun x hx => hnonneg x (List.mem_cons_of_mem _ hx))
      by_cases hg : 0 < gapScore lam g
      · have hm := score_mul_lower hlam hg0 hg le_rfl
        have hfilter : positiveGaps lam (g :: l) = g :: positiveGaps lam l := by
          simp [positiveGaps, hg]
        simp only [List.map_cons, List.sum_cons, hfilter, List.length_cons]
        push_cast at hm ht ⊢
        nlinarith
      · have hz : gapScore lam g = 0 := by omega
        have hfilter : positiveGaps lam (g :: l) = positiveGaps lam l := by
          simp [positiveGaps, hg]
        simp only [List.map_cons, List.sum_cons, hfilter, hz, zero_add]
        linarith

private theorem outside_score_lower {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (S : ActualHullSmallScoreTypes.Support o c lam p)
    (hlam : 0 < lam) :
    ((gapScore lam (Real.pi - S.window.width) + 1 : ℕ) : ℝ) * lam ≤
      Real.pi - S.window.width := by
  have hg0 : 0 ≤ Real.pi - S.window.width := hlam.le.trans S.outside_ge_scale
  have heq : gapScore lam (Real.pi - S.window.width) + 1 =
      ⌊(Real.pi - S.window.width) / lam⌋₊ := by
    unfold gapScore
    have hf := S.outside_floor_pos
    omega
  rw [heq]
  exact (le_div_iff₀ hlam).mp (Nat.floor_le (div_nonneg hg0 hlam.le))

private theorem clumps_of_support_gap {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (S : ActualHullSmallScoreTypes.Support o c lam p)
    {g bound : ℝ} {score : ℕ}
    (hg : g ∈ innerGaps (directionRow o S.window.base c p))
    (hscore : gapScore lam g = score) (hlam : 0 < lam)
    (hgap : 2 * lam ≤ g) (hbound : S.window.width - g ≤ bound) :
    Nonempty (ActualHullSmallScoreTypes.Clumps S.window score (2 * lam) bound) := by
  obtain ⟨a, b, ha, hb, hab, hgab, hcut⟩ :=
    innerGap_spec _ (directionRow_sorted o S.window.base c p) g hg
  obtain ⟨i, hi, hai⟩ := (mem_directionRow o S.window.base c).mp ha
  obtain ⟨j, hj, hbj⟩ := (mem_directionRow o S.window.base c).mp hb
  have hia : S.window.theta i = a := (hai.trans (S.dirRep_eq i hi)).symm
  have hjb : S.window.theta j = b := (hbj.trans (S.dirRep_eq j hj)).symm
  have hlt : S.window.theta i < S.window.theta j := by rw [hia, hjb]; linarith
  refine ⟨{
    leftRay := i
    rightRay := j
    left_ne_center := hi
    right_ne_center := hj
    left_lt_right := hlt
    no_middle := ?_
    actual_gap := ?_
    gap_score := ?_
    gap_lower := ?_
    remaining_width := ?_ }⟩
  · intro k hk
    have hmem : S.window.theta k ∈ directionRow o S.window.base c p := by
      rw [← S.dirRep_eq k hk]
      exact (mem_directionRow o S.window.base c).mpr ⟨k, hk, rfl⟩
    simpa only [hia, hjb] using hcut (S.window.theta k) hmem
  · rw [hia, hjb, ← hgab, cycGaps_eq_map_append_wrap _ S.nonempty]
    exact List.mem_append_left _ hg
  · rw [hia, hjb, ← hgab]
    exact hscore
  · rw [hia, hjb, ← hgab]
    exact hgap
  · rw [hia, hjb]
    linarith

/-- All rays and both nonempty clumps come from the original actual row. -/
structure Data {s : ℕ} (n : ℕ) (o : Orientation ℝ Plane₂ (Fin 2))
    (c : Fin s → Plane₂) (lam : ℝ) (p : Fin s) where
  window : ActualHullRayWindow.Window o c lam p
  internalScore : ℕ
  internalScore_pos : 1 ≤ internalScore
  clumps : ActualHullSmallScoreTypes.Clumps window internalScore (2 * lam)
    (Real.pi - (n : ℝ) * lam)
  remainder_nonneg : 0 ≤ Real.pi - (n : ℝ) * lam
  remainder_lt_half : Real.pi - (n : ℝ) * lam < lam / 2

/-- A maximal nonsaturated LOW full-hull row with a genuine wide pair
has one internally selected positive gap and two actual ray clumps.
No cut, gap, clump, score budget, or prescribed type is a caller input. -/
theorem exists_actual_maximal_low_row_clumps {s n : ℕ} (hs : 3 ≤ s) (hn : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlower : Real.pi / ((n : ℝ) + 1 / 2) < lam)
    (hupper : lam ≤ Real.pi / (n : ℝ))
    (p : Fin s) (hp : IsHullVertex c p)
    (hscore : rowScore lam (directionRow o e c p) = n - 2)
    (hwide : ∃ a b : Fin s, a ≠ p ∧ b ≠ p ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c p) (c b)) : Nonempty (Data n o c lam p) := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hden : 0 < (n : ℝ) + 1 / 2 := by linarith
  have hstrict : Real.pi < ((n : ℝ) + 1 / 2) * lam := by
    have h := (div_lt_iff₀ hden).mp hlower
    nlinarith
  have hnext : Real.pi < ((n : ℝ) + 1) * lam := by
    nlinarith [hleg.lam_pos]
  have hhalf : Real.pi - (n : ℝ) * lam < lam / 2 := by nlinarith
  have hrem : 0 ≤ Real.pi - (n : ℝ) * lam := by
    have h := (le_div_iff₀ hnpos).mp hupper
    nlinarith
  obtain ⟨S⟩ := ActualHullSmallScoreTypes.exists_actual_hull_full_row_support o hs hleg p hp
  have hscoreW : rowScore lam (directionRow o S.window.base c p) = n - 2 :=
    (rowScore_directionRow_reference_eq o e S.window.base he S.window.base_ne_zero
      c hleg.inj p lam).symm.trans hscore
  let gs := innerGaps (directionRow o S.window.base c p)
  let k := (gs.map (gapScore lam)).sum
  let b := gapScore lam (Real.pi - S.window.width)
  let t := (positiveGaps lam gs).length
  have hsplit : k + b = n - 2 := by
    have h := support_score_split S
    simpa only [gs, k, b, hscoreW] using h.symm
  have hnonneg : ∀ g ∈ gs, 0 ≤ g := innerGaps_nonneg (directionRow_sorted o S.window.base c p)
  have hsum : gs.sum = S.window.width := support_inner_sum S
  have hinner : ((k + t : ℕ) : ℝ) * lam ≤ S.window.width := by
    have h := score_and_count_lower lam hleg.lam_pos gs hnonneg
    simpa only [k, t, hsum] using h
  have houter : ((b + 1 : ℕ) : ℝ) * lam ≤ Real.pi - S.window.width :=
    outside_score_lower S hleg.lam_pos
  have ht : t ≤ 1 := by
    by_contra hnot
    have hnum : n + 1 ≤ k + t + b + 1 := by omega
    have hnumR : (n : ℝ) + 1 ≤ (k : ℝ) + (t : ℝ) + (b : ℝ) + 1 := by
      exact_mod_cast hnum
    have hmul := mul_le_mul_of_nonneg_right hnumR hleg.lam_pos.le
    push_cast at hinner houter
    nlinarith
  have hk : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := by omega
    have hnumR : (b : ℝ) + 1 = (n : ℝ) - 1 := by
      have hh : b + 2 = n := by omega
      have hhR : (b : ℝ) + 2 = (n : ℝ) := by exact_mod_cast hh
      linarith
    have hnumMul := congrArg (fun z : ℝ => z * lam) hnumR
    obtain ⟨a,d,ha,hd,_had,hbig⟩ := hwide
    have hangle := ActualMixedRigidCardinality.actual_window_angle_le_width
      S.window hleg a d ha hd
    push_cast at houter
    nlinarith
  have ht1 : t = 1 := by
    by_contra hne
    have ht0 : t = 0 := by omega
    have hnil : positiveGaps lam gs = [] := List.length_eq_zero_iff.mp ht0
    have hz := score_filter lam gs
    rw [hnil] at hz
    have hk0 : k = 0 := by simpa only [List.map_nil, List.sum_nil, k] using hz.symm
    omega
  obtain ⟨g, hglist⟩ := List.length_eq_one_iff.mp ht1
  have hgmem : g ∈ positiveGaps lam gs := by rw [hglist]; simp
  have hgdata : g ∈ gs ∧ 0 < gapScore lam g := by simpa [positiveGaps] using hgmem
  have hgs : gapScore lam g = k := by
    have h := score_filter lam gs
    rw [hglist] at h
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, k] using h
  have hglower := score_mul_lower hleg.lam_pos (hnonneg g hgdata.1) hgdata.2 le_rfl
  have hgap : 2 * lam ≤ g := by
    have hkR : (1 : ℝ) ≤ (gapScore lam g : ℝ) := by exact_mod_cast hgdata.2
    have hmul := mul_le_mul_of_nonneg_right hkR hleg.lam_pos.le
    push_cast at hglower
    nlinarith
  have hbudget : b + gapScore lam g + 2 = n := by omega
  have hbudgetR : (b : ℝ) + (gapScore lam g : ℝ) + 2 = (n : ℝ) := by
    exact_mod_cast hbudget
  have hbudgetMul := congrArg (fun z : ℝ => z * lam) hbudgetR
  have hbound : S.window.width - g ≤ Real.pi - (n : ℝ) * lam := by
    push_cast at houter hglower
    nlinarith
  obtain ⟨D⟩ := clumps_of_support_gap S hgdata.1 hgs hleg.lam_pos hgap hbound
  exact ⟨{
    window := S.window
    internalScore := k
    internalScore_pos := hk
    clumps := D
    remainder_nonneg := hrem
    remainder_lt_half := hhalf }⟩

#print axioms exists_actual_maximal_low_row_clumps

end Jsp404.ActualMaximalLowRowClumps
