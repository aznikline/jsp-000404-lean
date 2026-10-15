import Jsp000404.K3bGeometryPart2
import Jsp000404.K3bArcAux4

namespace Jsp404

open Finset
open scoped EuclideanGeometry EuclideanSpace

variable (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)

/-- Defect `2` splits into Type I (`B = 1`, `cells = n−1`) and
Type II (`B = 2`, `cells = n`). -/
theorem rowDefect_eq_two_type {lam : ℝ} (hlam : 0 < lam) {n : ℕ}
    (hn3 : 3 ≤ n) {l : List ℝ} (hcells : rowCells lam l ≤ n)
    (hdef : rowDefect n lam l = 2) :
    (rowBig lam l = 1 ∧ rowCells lam l = n - 1) ∨
      (rowBig lam l = 2 ∧ rowCells lam l = n) := by
  unfold rowDefect at hdef
  have hbig := rowBig_le_rowCells lam hlam l
  rcases Nat.lt_or_ge (rowBig lam l) 1 with h0 | h1
  · have hB0 := Nat.lt_one_iff.mp h0
    have hC0 := rowCells_eq_zero_of_rowBig_eq_zero lam hlam hB0
    omega
  · rcases Nat.lt_or_ge (rowBig lam l) 3 with h2 | h3
    · interval_cases (rowBig lam l) <;> omega
    · omega

/-- `rowBig` as a `Fin`-indexed indicator sum over `gapAfter`. -/
theorem rowBig_eq_sum_indicator {lam : ℝ} {l : List ℝ} (hs : l.SortedLE) :
    rowBig lam l =
      ∑ t : Fin l.length, (if lam ≤ gapAfter l t then (1 : ℕ) else 0) := by
  unfold rowBig
  rw [← sum_ite_eq_length_filter]
  rw [cycGaps_eq_ofFn_gapAfter hs, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]

/-- The wrap-arc gap sum over `Ici b` telescopes to the complementary
arc `l[b] → l[0]`. -/
theorem gapAfter_sum_Ici {l : List ℝ} (hs : l.SortedLE)
    (b : Fin l.length)
    (hb : l.get ⟨0, Nat.zero_lt_of_lt b.2⟩ ≠ l.get b) :
    ∑ t ∈ Finset.Ici b, gapAfter l t =
      cyclicDiff (l.get b) (l.get ⟨0, Nat.zero_lt_of_lt b.2⟩) := by
  have h0 : (0 : ℕ) < l.length := Nat.zero_lt_of_lt b.2
  set z : Fin l.length := ⟨0, h0⟩ with hz
  have hne : l ≠ [] := List.ne_nil_of_length_pos h0
  have hunion : (Finset.univ : Finset (Fin l.length)) =
      Finset.Ico z b ∪ Finset.Ici b := by
    ext t
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Ico,
      Finset.mem_Ici]
    constructor
    · intro _
      rcases Nat.lt_or_ge t.1 b.1 with h | h
      · exact Or.inl ⟨Nat.zero_le _, h⟩
      · exact Or.inr h
    · intro _; trivial
  have hdisj : Disjoint (Finset.Ico z b) (Finset.Ici b) := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    rw [Finset.mem_Ico] at ht1
    rw [Finset.mem_Ici] at ht2
    exact (not_lt_of_ge ht2) ht1.2
  have htotal := gapAfter_sum (ds := l) hne
  have hU : ∑ t : Fin l.length, gapAfter l t =
      ∑ t ∈ Finset.Ico z b, gapAfter l t +
        ∑ t ∈ Finset.Ici b, gapAfter l t := by
    rw [hunion, Finset.sum_union hdisj]
  have hico := cyclicDiff_eq_Ico_sum_gapAfter hs
    (show z ≤ b from Nat.zero_le _)
  have hrev := cyclicDiff_add_rev hb
  linarith

/-- Wrap-arc cell bound: cells of indices `≥ b` fit inside the
complementary arc `l[b] → l[0]`. -/
theorem arc_cells_le_arc_wrap {lam : ℝ} (hlam : 0 < lam) {l : List ℝ}
    (hs : l.SortedLE) (hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi)
    (b : Fin l.length)
    (hb : l.get ⟨0, Nat.zero_lt_of_lt b.2⟩ ≠ l.get b) :
    (∑ t ∈ Finset.Ici b, (⌊gapAfter l t / lam⌋₊ : ℝ)) * lam ≤
      cyclicDiff (l.get b) (l.get ⟨0, Nat.zero_lt_of_lt b.2⟩) := by
  have hne : l ≠ [] := List.ne_nil_of_length_pos (Nat.zero_lt_of_lt b.2)
  rw [← gapAfter_sum_Ici hs b hb, Finset.sum_mul]
  exact Finset.sum_le_sum fun t _ =>
    floor_mul_le_gap hlam (gapAfter_nonneg hs hmem hne t)

/-- A row has at most one primitive gap of floor `≥ n − 1`: two would
already contribute `2(n−1) > n ≥ cells`. -/
theorem floor_gap_index_eq_of_cells {n : ℕ} (hn3 : 3 ≤ n)
    {l : List ℝ} (hs : l.SortedLE) {lam : ℝ}
    (hcells : rowCells lam l ≤ n)
    {s₁ s₂ : Fin l.length}
    (h1 : n - 1 ≤ ⌊gapAfter l s₁ / lam⌋₊)
    (h2 : n - 1 ≤ ⌊gapAfter l s₂ / lam⌋₊) :
    s₁ = s₂ := by
  by_contra hne
  have hsum : ⌊gapAfter l s₁ / lam⌋₊ + ⌊gapAfter l s₂ / lam⌋₊ ≤
      rowCells lam l := by
    have hsub : ({s₁, s₂} : Finset (Fin l.length)) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hle := Finset.sum_le_sum_of_subset hsub
      (f := fun t => ⌊gapAfter l t / lam⌋₊)
    rw [Finset.sum_pair hne] at hle
    rw [rowCells_eq_sum_floor hs]
    exact hle
  omega

/-- **Receiving-arc dichotomy.**  If a consecutive-index arc `T` of a
defect-`2` row carries at most one primitive λ-cell while its gap
length reaches `λ`, the complement `univ \ T` contains a primitive gap
of floor `≥ n − 1`.  Type I contributes it directly (the unique big gap
cannot sit inside `T`); Type II forces `∑_T = 1`, hence exactly one big
gap inside and the `floor = n − 1` gap outside. -/
theorem defect_two_big_gap_avoids_arc {lam : ℝ} (hlam : 0 < lam) {n : ℕ}
    (hn : Nat.floor (Real.pi / lam) = n) (hn3 : 3 ≤ n)
    {l : List ℝ} (hs : l.SortedLE)
    (hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi)
    (hcells : rowCells lam l ≤ n) (hdef : rowDefect n lam l = 2)
    (T : Finset (Fin l.length))
    (hTcells : ∑ t ∈ T, ⌊gapAfter l t / lam⌋₊ ≤ 1)
    (hTlen : lam ≤ ∑ t ∈ T, gapAfter l t) :
    ∃ s ∈ Finset.univ \ T, (n - 1) ≤ ⌊gapAfter l s / lam⌋₊ := by
  classical
  have hne : l ≠ [] := by
    intro hnil
    subst hnil
    rcases Finset.eq_empty_or_nonempty T with hT0 | hT0
    · rw [hT0, Finset.sum_empty] at hTlen
      exact absurd hTlen (not_le_of_gt hlam)
    · obtain ⟨t, -⟩ := hT0
      exact absurd t.2 (by omega : ¬ t.1 < 0)
  have hnn : ∀ t : Fin l.length, 0 ≤ gapAfter l t :=
    fun t => gapAfter_nonneg hs hmem hne t
  have htot : ∑ t : Fin l.length, ⌊gapAfter l t / lam⌋₊ =
      rowCells lam l := (rowCells_eq_sum_floor hs).symm
  have hsplit_f : ∑ t ∈ Finset.univ \ T, ⌊gapAfter l t / lam⌋₊ +
      ∑ t ∈ T, ⌊gapAfter l t / lam⌋₊ = rowCells lam l := by
    have h := Finset.sum_sdiff (s₁ := T) (s₂ := Finset.univ)
      (Finset.subset_univ T) (f := fun t => ⌊gapAfter l t / lam⌋₊)
    rwa [htot] at h
  have hsplit_g : ∑ t ∈ Finset.univ \ T, gapAfter l t +
      ∑ t ∈ T, gapAfter l t = Real.pi := by
    have h := Finset.sum_sdiff (s₁ := T) (s₂ := Finset.univ)
      (Finset.subset_univ T) (f := fun t => gapAfter l t)
    have htotal := gapAfter_sum (ds := l) hne
    rwa [htotal] at h
  have hind_le : ∀ t : Fin l.length,
      (if lam ≤ gapAfter l t then (1 : ℕ) else 0) ≤
        ⌊gapAfter l t / lam⌋₊ := by
    intro t
    by_cases hb : lam ≤ gapAfter l t
    · rw [if_pos hb]
      exact (one_le_floor_iff_ge lam _ hlam).mpr hb
    · rw [if_neg hb]
      exact Nat.zero_le _
  rcases rowDefect_eq_two_type hlam hn3 hcells hdef with ⟨hB, hC⟩ | ⟨hB, hC⟩
  · -- Type I: the unique big index carries all `n−1` cells.
    have hex : ∃ s : Fin l.length, lam ≤ gapAfter l s := by
      rw [rowBig_eq_sum_indicator hs] at hB
      by_contra hcon
      push_neg at hcon
      have h0 : ∑ t : Fin l.length,
          (if lam ≤ gapAfter l t then (1 : ℕ) else 0) = 0 :=
        Finset.sum_eq_zero fun t _ => if_neg (not_le.mpr (hcon t))
      omega
    obtain ⟨s₀, hsbig⟩ := hex
    have hfl : ⌊gapAfter l s₀ / lam⌋₊ = rowCells lam l := by
      rw [← htot]
      symm
      apply Finset.sum_eq_single s₀
      · intro t _ ht
        by_contra hf
        have htf : 1 ≤ ⌊gapAfter l t / lam⌋₊ :=
          Nat.one_le_iff_ne_zero.mpr hf
        have htbig : lam ≤ gapAfter l t :=
          (one_le_floor_iff_ge lam _ hlam).mp htf
        rw [rowBig_eq_sum_indicator hs] at hB
        have hsub : ({s₀, t} : Finset (Fin l.length)) ⊆ Finset.univ :=
          Finset.subset_univ _
        have h2 := Finset.sum_le_sum_of_subset hsub
          (f := fun u => if lam ≤ gapAfter l u then (1 : ℕ) else 0)
        rw [Finset.sum_pair ht.symm, if_pos hsbig, if_pos htbig] at h2
        omega
      · intro habs; exact absurd (Finset.mem_univ s₀) habs
    refine ⟨s₀, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · intro hmemT
      have hle := Finset.single_le_sum
        (fun t _ => Nat.zero_le _ : ∀ t ∈ T,
          0 ≤ ⌊gapAfter l t / lam⌋₊) hmemT
      omega
    · omega
  · -- Type II: arc cells forced to `1`, unique big outside.
    have hT1 : ∑ t ∈ T, ⌊gapAfter l t / lam⌋₊ = 1 := by
      rcases Nat.eq_zero_or_pos (∑ t ∈ T, ⌊gapAfter l t / lam⌋₊)
        with h0 | hpos
      · exfalso
        have hcn : ∑ t ∈ Finset.univ \ T, ⌊gapAfter l t / lam⌋₊ = n := by
          omega
        have hlen : (n : ℝ) * lam ≤
            ∑ t ∈ Finset.univ \ T, gapAfter l t := by
          calc (n : ℝ) * lam
              _ = ((∑ t ∈ Finset.univ \ T,
                    ⌊gapAfter l t / lam⌋₊ : ℕ) : ℝ) * lam := by
                  rw [← hcn]
              _ = (∑ t ∈ Finset.univ \ T,
                    (⌊gapAfter l t / lam⌋₊ : ℝ)) * lam := by
                  rw [Nat.cast_sum]
              _ = ∑ t ∈ Finset.univ \ T,
                    (⌊gapAfter l t / lam⌋₊ : ℝ) * lam := by
                  rw [Finset.sum_mul]
              _ ≤ ∑ t ∈ Finset.univ \ T, gapAfter l t :=
                  Finset.sum_le_sum fun t _ =>
                    floor_mul_le_gap hlam (hnn t)
        have hpi : Real.pi < ((n : ℝ) + 1) * lam := by
          have hfl' := Nat.lt_floor_add_one (Real.pi / lam)
          rw [hn, div_lt_iff₀ hlam] at hfl'
          linarith
        have hcomp : ∑ t ∈ Finset.univ \ T, gapAfter l t ≤
            Real.pi - lam := by linarith
        linarith
      · omega
    have hBT : ∑ t ∈ T, (if lam ≤ gapAfter l t then (1 : ℕ) else 0) = 1 := by
      have hle : ∑ t ∈ T, (if lam ≤ gapAfter l t then (1 : ℕ) else 0) ≤
          ∑ t ∈ T, ⌊gapAfter l t / lam⌋₊ :=
        Finset.sum_le_sum fun t _ => hind_le t
      have hpos : 0 < ∑ t ∈ T,
          (if lam ≤ gapAfter l t then (1 : ℕ) else 0) := by
        obtain ⟨t, htT, htfl⟩ : ∃ t ∈ T,
            0 < ⌊gapAfter l t / lam⌋₊ := by
          by_contra hcon
          push_neg at hcon
          have h0 : ∑ t ∈ T, ⌊gapAfter l t / lam⌋₊ = 0 :=
            Finset.sum_eq_zero fun t ht =>
              Nat.eq_zero_of_le_zero (hcon t ht)
          omega
        have htb : lam ≤ gapAfter l t :=
          (one_le_floor_iff_ge lam _ hlam).mp htfl
        exact Finset.sum_pos' (fun u _ => Nat.zero_le _)
          ⟨t, htT, by rw [if_pos htb]; omega⟩
      omega
    have hBTc : ∑ t ∈ Finset.univ \ T,
        (if lam ≤ gapAfter l t then (1 : ℕ) else 0) = 1 := by
      have h := Finset.sum_sdiff (s₁ := T) (s₂ := Finset.univ)
        (Finset.subset_univ T)
        (f := fun t => if lam ≤ gapAfter l t then (1 : ℕ) else 0)
      rw [rowBig_eq_sum_indicator hs] at hB
      omega
    obtain ⟨s₀, hsmem, hsbig⟩ : ∃ s ∈ Finset.univ \ T,
        lam ≤ gapAfter l s := by
      by_contra hcon
      push_neg at hcon
      have h0 : ∑ t ∈ Finset.univ \ T,
          (if lam ≤ gapAfter l t then (1 : ℕ) else 0) = 0 :=
        Finset.sum_eq_zero fun t ht => if_neg (not_le.mpr (hcon t ht))
      omega
    refine ⟨s₀, hsmem, ?_⟩
    have hfl : ⌊gapAfter l s₀ / lam⌋₊ =
        ∑ t ∈ Finset.univ \ T, ⌊gapAfter l t / lam⌋₊ := by
      symm
      apply Finset.sum_eq_single s₀
      · intro t htT ht
        by_contra hf
        have htf : 1 ≤ ⌊gapAfter l t / lam⌋₊ :=
          Nat.one_le_iff_ne_zero.mpr hf
        have htbig : lam ≤ gapAfter l t :=
          (one_le_floor_iff_ge lam _ hlam).mp htf
        have hsub : ({s₀, t} : Finset (Fin l.length)) ⊆ Finset.univ \ T :=
          Finset.insert_subset_iff.mpr ⟨hsmem,
            Finset.singleton_subset_iff.mpr htT⟩
        have h2 := Finset.sum_le_sum_of_subset hsub
          (f := fun u => if lam ≤ gapAfter l u then (1 : ℕ) else 0)
        rw [Finset.sum_pair ht.symm, if_pos hsbig, if_pos htbig] at h2
        omega
      · intro habs; exact absurd hsmem habs
    have hcn : ∑ t ∈ Finset.univ \ T, ⌊gapAfter l t / lam⌋₊ = n - 1 := by
      omega
    omega

/-- **Outer-remainder budget.**  Outside the receiving arc `T` and
the unique `floor ≥ n−1` gap `s`, the remaining primitive gaps of a
defect-`2` row total at most `π − nλ = δλ` — the row has less than
`λ` of room left once the `λ`-sized arc and the `≥ (n−1)λ` big gap
are accounted for.  This is the `R_out/λ + ρ_G + ρ_arc = δ` budget
(in a discretized form) shared by both defect-`2` types. -/
theorem defect_two_outer_budget {lam : ℝ} (hlam : 0 < lam) {n : ℕ}
    (hn : Nat.floor (Real.pi / lam) = n) (hn3 : 3 ≤ n)
    {l : List ℝ} (hs : l.SortedLE)
    (hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi)
    (hcells : rowCells lam l ≤ n) (hdef : rowDefect n lam l = 2)
    (T : Finset (Fin l.length))
    (hTcells : ∑ t ∈ T, ⌊gapAfter l t / lam⌋₊ ≤ 1)
    (hTlen : lam ≤ ∑ t ∈ T, gapAfter l t) :
    ∃ s ∈ Finset.univ \ T, (n - 1) ≤ ⌊gapAfter l s / lam⌋₊ ∧
      ∑ t ∈ (Finset.univ \ T) \ {s}, gapAfter l t ≤
        Real.pi - n * lam := by
  classical
  have hne : l ≠ [] := by
    intro hnil
    subst hnil
    rcases Finset.eq_empty_or_nonempty T with hT0 | hT0
    · rw [hT0, Finset.sum_empty] at hTlen
      exact absurd hTlen (not_le_of_gt hlam)
    · obtain ⟨t, -⟩ := hT0
      exact absurd t.2 (by omega : ¬ t.1 < 0)
  have hnn : ∀ t : Fin l.length, 0 ≤ gapAfter l t :=
    fun t => gapAfter_nonneg hs hmem hne t
  obtain ⟨s, hs_out, hf_out⟩ := defect_two_big_gap_avoids_arc
    hlam hn hn3 hs hmem hcells hdef T hTcells hTlen
  refine ⟨s, hs_out, hf_out, ?_⟩
  have hsplit_g : ∑ t ∈ Finset.univ \ T, gapAfter l t +
      ∑ t ∈ T, gapAfter l t = Real.pi := by
    have h := Finset.sum_sdiff (s₁ := T) (s₂ := Finset.univ)
      (Finset.subset_univ T) (f := fun t => gapAfter l t)
    have htotal := gapAfter_sum (ds := l) hne
    rwa [htotal] at h
  have hcomp : ∑ t ∈ Finset.univ \ T, gapAfter l t ≤
      Real.pi - lam := by linarith
  have hG : (↑n - 1) * lam ≤ gapAfter l s := by
    have hf : ((n - 1 : ℕ) : ℝ) ≤ (⌊gapAfter l s / lam⌋₊ : ℝ) := by
      exact_mod_cast hf_out
    have hfm := mul_le_mul_of_nonneg_right hf hlam.le
    have h2 := floor_mul_le_gap hlam (hnn s)
    rw [Nat.cast_sub (by omega : (1:ℕ) ≤ n), Nat.cast_one] at hfm
    linarith
  have hrest : ∑ t ∈ (Finset.univ \ T) \ {s}, gapAfter l t =
      ∑ t ∈ Finset.univ \ T, gapAfter l t - gapAfter l s := by
    have h := Finset.sum_sdiff (s₁ := {s}) (s₂ := Finset.univ \ T)
      (Finset.singleton_subset_iff.mpr hs_out)
      (f := fun t => gapAfter l t)
    rw [Finset.sum_singleton] at h
    linarith
  rw [hrest]
  linarith

/-- **Type II receiving structure.**  In a Type II defect-`2` row
(`rowBig = 2`, `rowCells = n`), a receiving arc `T` (cells `≤ 1`,
length `≥ λ`) carries exactly one primitive big gap — of `floor = 1` —
while the `floor = n−1` big gap lies outside, and every other
primitive gap on either side is `< λ`.  The `floor`-`1` gap inside
the arc is forced because a zero-cell arc would put all `n` cells
outside, whose gaps then have total length `≥ nλ`, and with
`Σ_T gap ≥ λ` the whole circle would have length `≥ (n+1)λ > π`. -/
theorem defect_two_type_II_arc_structure {lam : ℝ} (hlam : 0 < lam)
    {n : ℕ} (hn : Nat.floor (Real.pi / lam) = n) (hn3 : 3 ≤ n)
    {l : List ℝ} (hs : l.SortedLE)
    (hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi)
    (hcells : rowCells lam l ≤ n) (hdef : rowDefect n lam l = 2)
    (hII : rowBig lam l = 2)
    (T : Finset (Fin l.length))
    (hTcells : ∑ t ∈ T, ⌊gapAfter l t / lam⌋₊ ≤ 1)
    (hTlen : lam ≤ ∑ t ∈ T, gapAfter l t) :
    ∃ s_out ∈ Finset.univ \ T, ∃ s_in ∈ T,
      ⌊gapAfter l s_out / lam⌋₊ = n - 1 ∧
      ⌊gapAfter l s_in / lam⌋₊ = 1 ∧
      (∀ t : Fin l.length, t ∉ T → t ≠ s_out → gapAfter l t < lam) ∧
      (∀ t : Fin l.length, t ∈ T → t ≠ s_in → gapAfter l t < lam) := by
  classical
  have hne : l ≠ [] := by
    intro hnil
    subst hnil
    rcases Finset.eq_empty_or_nonempty T with hT0 | hT0
    · rw [hT0, Finset.sum_empty] at hTlen
      exact absurd hTlen (not_le_of_gt hlam)
    · obtain ⟨t, -⟩ := hT0
      exact absurd t.2 (by omega : ¬ t.1 < 0)
  have hnn : ∀ t : Fin l.length, 0 ≤ gapAfter l t :=
    fun t => gapAfter_nonneg hs hmem hne t
  have hC : rowCells lam l = n := by
    rcases rowDefect_eq_two_type hlam hn3 hcells hdef with
      ⟨hB1, -⟩ | ⟨-, hC⟩
    · omega
    · exact hC
  have htot : ∑ t : Fin l.length, ⌊gapAfter l t / lam⌋₊ =
      rowCells lam l := (rowCells_eq_sum_floor hs).symm
  obtain ⟨s_out, hs_out, hf_out⟩ := defect_two_big_gap_avoids_arc
    hlam hn hn3 hs hmem hcells hdef T hTcells hTlen
  -- `floor s_out = n−1`: `floor = n` would leave only one big gap.
  have hf_out_eq : ⌊gapAfter l s_out / lam⌋₊ = n - 1 := by
    have hle : ⌊gapAfter l s_out / lam⌋₊ ≤ n := by
      have h := Finset.single_le_sum
        (fun t (_ : t ∈ Finset.univ) =>
          (Nat.zero_le _ : 0 ≤ ⌊gapAfter l t / lam⌋₊))
        (Finset.mem_univ s_out)
      rw [htot, hC] at h
      exact h
    rcases Nat.lt_or_ge (⌊gapAfter l s_out / lam⌋₊) n with hlt | hge
    · omega
    · exfalso
      have hfn : ⌊gapAfter l s_out / lam⌋₊ = n := by omega
      have hrest : (∑ t ∈ Finset.univ \ {s_out},
          ⌊gapAfter l t / lam⌋₊) = 0 := by
        have h := Finset.sum_sdiff (s₁ := {s_out}) (s₂ := Finset.univ)
          (Finset.subset_univ _)
          (f := fun t => ⌊gapAfter l t / lam⌋₊)
        rw [Finset.sum_singleton, htot, hC, hfn] at h
        omega
      have hall0 : ∀ t : Fin l.length, t ≠ s_out →
          ⌊gapAfter l t / lam⌋₊ = 0 := by
        intro t ht
        have hmem' : t ∈ Finset.univ \ {s_out} :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ t,
            fun h => ht (Finset.mem_singleton.mp h)⟩
        exact (Finset.sum_eq_zero_iff.mp hrest) t hmem'
      have hrow1 : rowBig lam l = 1 := by
        rw [rowBig_eq_sum_indicator hs]
        have hsum1 : ∑ t : Fin l.length,
            (if lam ≤ gapAfter l t then (1 : ℕ) else 0) =
            (if lam ≤ gapAfter l s_out then (1 : ℕ) else 0) := by
          apply Finset.sum_eq_single
          · intro t _ ht
            have h0 := hall0 t ht
            rw [Nat.floor_eq_zero, div_lt_one hlam] at h0
            exact if_neg (not_le.mpr h0)
          · intro habs
            exact absurd (Finset.mem_univ s_out) habs
        rw [hsum1, if_pos]
        exact (one_le_floor_iff_ge lam _ hlam).mp (by omega)
      omega
  -- The arc carries exactly one cell.
  have hsplit_f : ∑ t ∈ Finset.univ \ T, ⌊gapAfter l t / lam⌋₊ +
      ∑ t ∈ T, ⌊gapAfter l t / lam⌋₊ = rowCells lam l := by
    have h := Finset.sum_sdiff (s₁ := T) (s₂ := Finset.univ)
      (Finset.subset_univ T) (f := fun t => ⌊gapAfter l t / lam⌋₊)
    rwa [htot] at h
  have hsplit_g : ∑ t ∈ Finset.univ \ T, gapAfter l t +
      ∑ t ∈ T, gapAfter l t = Real.pi := by
    have h := Finset.sum_sdiff (s₁ := T) (s₂ := Finset.univ)
      (Finset.subset_univ T) (f := fun t => gapAfter l t)
    have htotal := gapAfter_sum (ds := l) hne
    rwa [htotal] at h
  have hTcells_eq : ∑ t ∈ T, ⌊gapAfter l t / lam⌋₊ = 1 := by
    by_contra hcon
    have hT0 : ∑ t ∈ T, ⌊gapAfter l t / lam⌋₊ = 0 := by omega
    have hcomp' : ∑ t ∈ Finset.univ \ T, ⌊gapAfter l t / lam⌋₊ =
        n := by omega
    have hgap_comp : (n : ℝ) * lam ≤
        ∑ t ∈ Finset.univ \ T, gapAfter l t := by
      have hle : ∀ t ∈ Finset.univ \ T,
          (⌊gapAfter l t / lam⌋₊ : ℝ) * lam ≤ gapAfter l t :=
        fun t _ => floor_mul_le_gap hlam (hnn t)
      have hsumle := Finset.sum_le_sum hle
      rw [← Finset.sum_mul, ← Nat.cast_sum, hcomp'] at hsumle
      exact hsumle
    have hdelta' : Real.pi - n * lam < lam := by
      have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
      rw [hn, div_lt_iff₀ hlam] at hfloor'; linarith
    linarith
  have hcomp : ∑ t ∈ Finset.univ \ T, ⌊gapAfter l t / lam⌋₊ =
      n - 1 := by omega
  -- `s_in`: the unique arc element with `floor = 1`.
  obtain ⟨s_in, hs_in, hf_in⟩ : ∃ t ∈ T,
      ⌊gapAfter l t / lam⌋₊ = 1 := by
    have hex : ∃ t ∈ T, ⌊gapAfter l t / lam⌋₊ ≠ 0 := by
      by_contra h
      push_neg at h
      rw [Finset.sum_eq_zero h] at hTcells_eq
      omega
    obtain ⟨t, ht, htf⟩ := hex
    refine ⟨t, ht, ?_⟩
    have hle := Finset.single_le_sum
      (fun u (_ : u ∈ T) => (Nat.zero_le _ : 0 ≤ ⌊gapAfter l u / lam⌋₊))
      ht
    omega
  refine ⟨s_out, hs_out, s_in, hs_in, hf_out_eq, hf_in, ?_, ?_⟩
  · -- outside `T`, only `s_out` has a nonzero floor.
    have hrest : (∑ t ∈ (Finset.univ \ T) \ {s_out},
        ⌊gapAfter l t / lam⌋₊) = 0 := by
      have h := Finset.sum_sdiff (s₁ := {s_out}) (s₂ := Finset.univ \ T)
        (Finset.singleton_subset_iff.mpr hs_out)
        (f := fun t => ⌊gapAfter l t / lam⌋₊)
      rw [Finset.sum_singleton, hf_out_eq, hcomp] at h
      omega
    intro t ht hts
    have hmem' : t ∈ (Finset.univ \ T) \ {s_out} :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ t, ht⟩,
        fun h => hts (Finset.mem_singleton.mp h)⟩
    have h0 := (Finset.sum_eq_zero_iff.mp hrest) t hmem'
    rw [Nat.floor_eq_zero, div_lt_one hlam] at h0
    exact h0
  · -- inside `T`, only `s_in` has a nonzero floor.
    have hrest : (∑ t ∈ T \ {s_in}, ⌊gapAfter l t / lam⌋₊) = 0 := by
      have h := Finset.sum_sdiff (s₁ := {s_in}) (s₂ := T)
        (Finset.singleton_subset_iff.mpr hs_in)
        (f := fun t => ⌊gapAfter l t / lam⌋₊)
      rw [Finset.sum_singleton, hf_in, hTcells_eq] at h
      omega
    intro t ht hts
    have hmem' : t ∈ T \ {s_in} := Finset.mem_sdiff.mpr
      ⟨ht, fun h => hts (Finset.mem_singleton.mp h)⟩
    have h0 := (Finset.sum_eq_zero_iff.mp hrest) t hmem'
    rw [Nat.floor_eq_zero, div_lt_one hlam] at h0
    exact h0

#print axioms rowDefect_eq_two_type
#print axioms defect_two_big_gap_avoids_arc
#print axioms defect_two_outer_budget
#print axioms defect_two_type_II_arc_structure


end Jsp404
