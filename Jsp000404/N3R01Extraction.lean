import Jsp000404.N3R01Terminal
import Jsp000404.ChartInvariance

/-! Extraction of the seven-nonanchor terminal from actual saturated charts.
The scalar corridor/triple constraints are derived from actual point geometry;
none is an additional assumed capacity or arbitrary angle array. -/

namespace Jsp404.N3R01Extraction
open Classical
open scoped EuclideanGeometry EuclideanSpace
open N3R01Terminal

section ActualEightChart
variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
  {c : Fin 8 → Plane₂} {v : Fin 8} {theta : Fin 7 → ℝ}
  (C : SatChart o e 3 lam c v theta)

include C

/-- Distinct non-anchor centres have distinct anchor directions:
`Up` runs in the direction of increasing `theta`. -/
theorem theta_injective : Function.Injective theta := by
  intro i j hij
  by_contra hne
  rcases up_or_up C hne with h | h
  · exact absurd hij (ne_of_lt (up_theta_lt C hne h))
  · exact absurd hij.symm (ne_of_lt (up_theta_lt C (Ne.symm hne) h))

/-- The seven non-anchor `theta`s are distinct. -/
theorem theta_card : (Finset.image theta Finset.univ).card = 7 := by
  classical
  rw [Finset.card_image_of_injective _ (theta_injective C),
    Finset.card_univ, Fintype.card_fin]

/-- Sorted `theta` values as a strict-mono enumeration. -/
noncomputable def sortedTheta : Fin 7 → ℝ :=
  (Finset.image theta Finset.univ).orderEmbOfFin (theta_card C)

theorem sortedTheta_strictMono : StrictMono (sortedTheta C) := fun _ _ h =>
  ((Finset.image theta Finset.univ).orderEmbOfFin _).strictMono h

/-- Rank-to-index bijection: `sigma C i` is the centre whose `theta` is the
`i`-th smallest. -/
noncomputable def sigma : Fin 7 → Fin 7 := fun i =>
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (theta_card C) i)).choose

theorem sigma_spec (i : Fin 7) : theta (sigma C i) = sortedTheta C i :=
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (theta_card C) i)).choose_spec.2

theorem sigma_injective : Function.Injective (sigma C) := by
  intro i j hij
  apply (sortedTheta_strictMono C).injective
  rw [← sigma_spec C i, ← sigma_spec C j, hij]

theorem sigma_bijective : Function.Bijective (sigma C) :=
  Finite.injective_iff_bijective.mp (sigma_injective C)

theorem sigma_ne {i j : Fin 7} (h : i ≠ j) : sigma C i ≠ sigma C j :=
  fun hh => h (sigma_injective C hh)

/-- A lower-`theta` centre is always `Up` of a higher one, at `sigma`-ranks. -/
theorem sigma_up {i j : Fin 7} (hij : i < j) :
    Up o e c v (sigma C i) (sigma C j) := by
  have hlt : theta (sigma C i) < theta (sigma C j) := by
    rw [sigma_spec C i, sigma_spec C j]
    exact sortedTheta_strictMono C hij
  exact up_of_theta_lt' C (sigma_ne C hij.ne) hlt

/-- Corridor bounds in model coordinates. -/
theorem corridor {i j : Fin 7} (hij : i < j) :
    sortedTheta C i + lam ≤
        dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j) ∧
      dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j) ≤
        Real.pi - lam + sortedTheta C j := by
  have hcor := up_corridor C (sigma_ne C hij.ne) (sigma_up C hij)
  rwa [sigma_spec C i, sigma_spec C j] at hcor

/-- Triple `Up`-constraints in model coordinates. -/
theorem triangle {i j k : Fin 7} (hij : i < j) (hjk : j < k) :
    (dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j) + lam ≤
          dirRep o e (c ∘ v.succAbove) (sigma C j) (sigma C k) ∧
        dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j) <
          dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C k) ∧
        dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C k) <
          dirRep o e (c ∘ v.succAbove) (sigma C j) (sigma C k)) ∨
      (dirRep o e (c ∘ v.succAbove) (sigma C j) (sigma C k) + lam ≤
          dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j) ∧
        dirRep o e (c ∘ v.succAbove) (sigma C j) (sigma C k) <
          dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C k) ∧
        dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C k) <
          dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j)) := by
  have hneij : sigma C i ≠ sigma C j := sigma_ne C hij.ne
  have hnejk : sigma C j ≠ sigma C k := sigma_ne C hjk.ne
  have hneik : sigma C i ≠ sigma C k := sigma_ne C (hij.trans hjk).ne
  have hupij := sigma_up C hij
  have hupjk := sigma_up C hjk
  obtain ⟨-, hbetween⟩ := up_trans C hneij hnejk hneik hupij hupjk
  have hcap := up_cap C hneij hnejk hneik hupij hupjk
  rcases le_or_gt 0 (dirRep o e (c ∘ v.succAbove) (sigma C j) (sigma C k) -
    dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j)) with hs | hs
  · rw [abs_of_nonneg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, h1, h2⟩
    · exfalso; linarith
  · rw [abs_of_neg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso; linarith
    · exact Or.inr ⟨by linarith, h1, h2⟩

/-- The scalar `n = 3` model of the eight-centre configuration. -/
noncomputable def model : SevenModel where
  lam := lam
  p := Real.pi
  hlam := C.hlam
  hp := by
    have h1 := C.hnl
    have h2 := C.hβ
    push_cast at h1 h2
    constructor <;> linarith
  t := sortedTheta C
  ht := sortedTheta_strictMono C
  ht0 := by
    have h := (C.htheta (sigma C 0)).1.1
    rwa [sigma_spec C 0] at h
  ht6 := by
    have h := (C.htheta (sigma C 6)).1.2
    rw [sigma_spec C 6] at h
    push_cast at h ⊢
    linarith
  d := fun i j => dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j)
  hcor := fun _ _ h => corridor C h
  htr := fun _ _ _ h1 h2 => triangle C h1 h2

/-- A real eight-centre configuration cannot admit a saturated third-strip
chart. This covers both LOW and HIGH, with no row/minimality assumptions. -/
theorem eight_chart_impossible : False :=
  seven_model_impossible (model C)

#print axioms eight_chart_impossible
end ActualEightChart

/-- Original point-geometric exclusion: the actual saturation supplies the
chart and its reference direction, so no scalar-model premise is assumed. -/
theorem eight_centre_n3_saturated_impossible
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 3)
    {c : Fin 8 → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin 8) (hsat : rowDefect 3 lam (directionRow o e c v) = 1) :
    False := by
  obtain ⟨e', he', theta, htheta⟩ :=
    saturated_ray_window o e he (s := 7) (by omega) (by omega) hlam hn
      hleg v hsat
  exact eight_chart_impossible
    (⟨he', by omega, hlam, hn, hleg, htheta⟩ : SatChart o e' 3 lam c v theta)

#print axioms eight_centre_n3_saturated_impossible

namespace Six
section ActualSevenChart
variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
  {c : Fin 7 → Plane₂} {v : Fin 7} {theta : Fin 6 → ℝ}
  (C : SatChart o e 3 lam c v theta)

include C

/-- Distinct non-anchor centres have distinct anchor directions:
`Up` runs in the direction of increasing `theta`. -/
theorem theta_injective : Function.Injective theta := by
  intro i j hij
  by_contra hne
  rcases up_or_up C hne with h | h
  · exact absurd hij (ne_of_lt (up_theta_lt C hne h))
  · exact absurd hij.symm (ne_of_lt (up_theta_lt C (Ne.symm hne) h))

/-- The five non-anchor `theta`s are distinct. -/
theorem theta_card : (Finset.image theta Finset.univ).card = 6 := by
  classical
  rw [Finset.card_image_of_injective _ (theta_injective C),
    Finset.card_univ, Fintype.card_fin]

/-- Sorted `theta` values as a strict-mono enumeration. -/
noncomputable def sortedTheta : Fin 6 → ℝ :=
  (Finset.image theta Finset.univ).orderEmbOfFin (theta_card C)

theorem sortedTheta_strictMono : StrictMono (sortedTheta C) := fun _ _ h =>
  ((Finset.image theta Finset.univ).orderEmbOfFin _).strictMono h

/-- Rank-to-index bijection: `sigma C i` is the centre whose `theta` is the
`i`-th smallest. -/
noncomputable def sigma : Fin 6 → Fin 6 := fun i =>
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (theta_card C) i)).choose

theorem sigma_spec (i : Fin 6) : theta (sigma C i) = sortedTheta C i :=
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (theta_card C) i)).choose_spec.2

theorem sigma_injective : Function.Injective (sigma C) := by
  intro i j hij
  apply (sortedTheta_strictMono C).injective
  rw [← sigma_spec C i, ← sigma_spec C j, hij]

theorem sigma_bijective : Function.Bijective (sigma C) :=
  Finite.injective_iff_bijective.mp (sigma_injective C)

theorem sigma_ne {i j : Fin 6} (h : i ≠ j) : sigma C i ≠ sigma C j :=
  fun hh => h (sigma_injective C hh)

/-- A lower-`theta` centre is always `Up` of a higher one, at `sigma`-ranks. -/
theorem sigma_up {i j : Fin 6} (hij : i < j) :
    Up o e c v (sigma C i) (sigma C j) := by
  have hlt : theta (sigma C i) < theta (sigma C j) := by
    rw [sigma_spec C i, sigma_spec C j]
    exact sortedTheta_strictMono C hij
  exact up_of_theta_lt' C (sigma_ne C hij.ne) hlt

/-- Corridor bounds in model coordinates. -/
theorem corridor {i j : Fin 6} (hij : i < j) :
    sortedTheta C i + lam ≤
        dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j) ∧
      dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j) ≤
        Real.pi - lam + sortedTheta C j := by
  have hcor := up_corridor C (sigma_ne C hij.ne) (sigma_up C hij)
  rwa [sigma_spec C i, sigma_spec C j] at hcor

/-- Triple `Up`-constraints in model coordinates. -/
theorem triangle {i j k : Fin 6} (hij : i < j) (hjk : j < k) :
    (dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j) + lam ≤
          dirRep o e (c ∘ v.succAbove) (sigma C j) (sigma C k) ∧
        dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j) <
          dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C k) ∧
        dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C k) <
          dirRep o e (c ∘ v.succAbove) (sigma C j) (sigma C k)) ∨
      (dirRep o e (c ∘ v.succAbove) (sigma C j) (sigma C k) + lam ≤
          dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j) ∧
        dirRep o e (c ∘ v.succAbove) (sigma C j) (sigma C k) <
          dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C k) ∧
        dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C k) <
          dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j)) := by
  have hneij : sigma C i ≠ sigma C j := sigma_ne C hij.ne
  have hnejk : sigma C j ≠ sigma C k := sigma_ne C hjk.ne
  have hneik : sigma C i ≠ sigma C k := sigma_ne C (hij.trans hjk).ne
  have hupij := sigma_up C hij
  have hupjk := sigma_up C hjk
  obtain ⟨-, hbetween⟩ := up_trans C hneij hnejk hneik hupij hupjk
  have hcap := up_cap C hneij hnejk hneik hupij hupjk
  rcases le_or_gt 0 (dirRep o e (c ∘ v.succAbove) (sigma C j) (sigma C k) -
    dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j)) with hs | hs
  · rw [abs_of_nonneg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, h1, h2⟩
    · exfalso; linarith
  · rw [abs_of_neg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso; linarith
    · exact Or.inr ⟨by linarith, h1, h2⟩

noncomputable def rawRow (i : Fin 6) : List ℝ :=
  directionRow o e (c ∘ v.succAbove) (sigma C i)

theorem rawRow_perm (i : Fin 6) :
    (rawRow C i).Perm (((List.finRange 6).erase i).map fun j =>
      dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j)) := by
  let u := sigma C i
  have hp1 : List.Perm (directionRow o e (c ∘ v.succAbove) u)
      (((List.finRange 6).erase u).map
        (dirRep o e (c ∘ v.succAbove) u)) := List.perm_insertionSort _ _
  have hmap : List.Perm ((List.finRange 6).erase u)
      (((List.finRange 6).erase i).map (sigma C)) := by
    apply List.Subperm.antisymm
    · apply List.Nodup.subperm ((List.nodup_finRange 6).erase u)
      intro x hx
      rw [(List.nodup_finRange 6).mem_erase_iff] at hx
      obtain ⟨j, hj⟩ := (sigma_bijective C).surjective x
      refine List.mem_map.mpr ⟨j, ?_, hj⟩
      rw [(List.nodup_finRange 6).mem_erase_iff]
      exact ⟨fun hji => hx.1 (by rw [← hj, hji]), List.mem_finRange _⟩
    · apply List.Nodup.subperm
        (((List.nodup_finRange 6).erase i).map (sigma_injective C))
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      rw [(List.nodup_finRange 6).mem_erase_iff] at hj ⊢
      exact ⟨fun h => hj.1 (sigma_injective C h), List.mem_finRange _⟩
  have hp2 := hmap.map (dirRep o e (c ∘ v.succAbove) u)
  have hp := hp1.trans hp2
  simpa only [rawRow, u, List.map_map, Function.comp_def] using hp


noncomputable def model : SixModel where
  lam := lam
  p := Real.pi
  hlam := C.hlam
  hp := by
    have h1 := C.hnl
    have h2 := C.hβ
    push_cast at h1 h2
    constructor <;> linarith
  t := sortedTheta C
  ht := sortedTheta_strictMono C
  ht0 := by
    have h := (C.htheta (sigma C 0)).1.1
    rwa [sigma_spec C 0] at h
  ht5 := by
    have h := (C.htheta (sigma C 5)).1.2
    rw [sigma_spec C 5] at h
    push_cast at h ⊢
    linarith
  d := fun i j => dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j)
  symm i j hij := phi_comm C (sigma_ne C hij)
  rowxs := rawRow C
  row_sorted i := (directionRow_sorted o e (c ∘ v.succAbove) (sigma C i)).pairwise
  row_perm := rawRow_perm C
  hcor := fun _ _ h => corridor C h
  htr := fun _ _ _ h1 h2 => triangle C h1 h2

/-- Every genuine non-anchor row in a seven-centre third-strip saturated
chart has zero score, with no row-profile or minimality assumption. -/
theorem seven_chart_nonanchor_score_zero (u : Fin 6) :
    rowScore lam (directionRow o e c (v.succAbove u)) = 0 := by
  obtain ⟨r, rfl⟩ := (sigma_bijective C).surjective u
  have hz := six_model_rows_zero (model C) r
  change linearGapScore lam (sortedTheta C r) (sortedTheta C r + Real.pi)
    (rawRow C r) = 0 at hz
  have hdef := score_add_defect C (by omega : 2 ≤ 6) (sigma C r)
  rw [sigma_spec C r] at hdef
  change linearGapScore lam (sortedTheta C r) (sortedTheta C r + Real.pi)
    (rawRow C r) + _ = 3 at hdef
  rw [hz] at hdef
  have hcells := rowCells_directionRow_le_of_floor_eq o e c C.hlam
    (v.succAbove (sigma C r)) (by omega : 2 ≤ 7) C.hn
  have hs := rowScore_eq_sub_defect lam C.hlam 3 _ hcells
  omega

#print axioms seven_chart_nonanchor_score_zero
end ActualSevenChart
end Six

/-- The stronger seven-centre result on the original direction rows. -/
theorem seven_centre_n3_nonanchor_score_zero
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 3)
    {c : Fin 7 → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin 7) (hsat : rowDefect 3 lam (directionRow o e c v) = 1)
    (w : Fin 7) (hw : w ≠ v) :
    rowScore lam (directionRow o e c w) = 0 := by
  obtain ⟨e', he', theta, htheta⟩ :=
    saturated_ray_window o e he (s := 6) (by omega) (by omega) hlam hn
      hleg v hsat
  have C : SatChart o e' 3 lam c v theta :=
    ⟨he', by omega, hlam, hn, hleg, htheta⟩
  obtain ⟨u, hu⟩ := Fin.exists_succAbove_eq hw
  have hz := Six.seven_chart_nonanchor_score_zero C u
  rw [hu, rowScore_directionRow_reference_eq o e' e he' he c hleg.inj w lam] at hz
  exact hz

#print axioms seven_centre_n3_nonanchor_score_zero
end Jsp404.N3R01Extraction
