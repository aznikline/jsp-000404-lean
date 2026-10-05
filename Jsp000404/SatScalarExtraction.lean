import Jsp000404.MixedStarExclusion
import Jsp000404.SatScalarModel
import Jsp000404.SixModelCompression

/-!
# Actual generic anchored-chart scalar extraction

The input is the existing geometric `SatChart`; none of the normalized
corridor, triangle or row-signature facts is assumed as an extra hypothesis.
The output retains every actual non-anchor row defect after an internal
angle-rank bijection, positive scaling, and full-list row normalization.
In particular m=6 and m=7 cover actual seven- and eight-centre charts.
No inverse planar realization or scalar capacity conclusion is claimed.
-/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.SatScalarExtraction

open Classical
open scoped EuclideanGeometry EuclideanSpace
open SatScalarModel

/-- Scaling actual consecutive gaps commutes with the existing gap score. -/
theorem linearGapScore_scale (lam left right : ℝ) (xs : List ℝ) :
    linearGapScore lam left right xs =
      linearGapScore 1 (left / lam) (right / lam) (xs.map fun x => x / lam) := by
  induction xs generalizing left with
  | nil => simp [linearGapScore, gapScore, sub_div]
  | cons x xs ih =>
    simp only [linearGapScore, List.map_cons]
    rw [ih x]
    congr 1
    simp [gapScore, sub_div]

section GenericChart

variable {m n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
  {c : Fin (m + 1) → Plane₂} {v : Fin (m + 1)} {theta : Fin m → ℝ}
  (C : SatChart o e n lam c v theta)

include C

theorem theta_injective : Function.Injective theta := by
  intro i j hij
  by_contra hne
  rcases up_or_up C hne with h | h
  · exact absurd hij (ne_of_lt (up_theta_lt C hne h))
  · exact absurd hij.symm (ne_of_lt (up_theta_lt C (Ne.symm hne) h))

theorem theta_card : (Finset.image theta Finset.univ).card = m := by
  rw [Finset.card_image_of_injective _ (theta_injective C),
    Finset.card_univ, Fintype.card_fin]

noncomputable def sortedTheta : Fin m → ℝ :=
  (Finset.image theta Finset.univ).orderEmbOfFin (theta_card C)

theorem sortedTheta_strictMono : StrictMono (sortedTheta C) := fun _ _ h =>
  ((Finset.image theta Finset.univ).orderEmbOfFin _).strictMono h

noncomputable def sigma : Fin m → Fin m := fun i =>
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (theta_card C) i)).choose

theorem sigma_spec (i : Fin m) : theta (sigma C i) = sortedTheta C i :=
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (theta_card C) i)).choose_spec.2

theorem sigma_injective : Function.Injective (sigma C) := by
  intro i j hij
  apply (sortedTheta_strictMono C).injective
  rw [← sigma_spec C i, ← sigma_spec C j, hij]

theorem sigma_bijective : Function.Bijective (sigma C) :=
  Finite.injective_iff_bijective.mp (sigma_injective C)

theorem sigma_ne {i j : Fin m} (hij : i ≠ j) : sigma C i ≠ sigma C j :=
  fun h => hij (sigma_injective C h)

theorem sigma_up {i j : Fin m} (hij : i < j) :
    Up o e c v (sigma C i) (sigma C j) := by
  apply up_of_theta_lt' C (sigma_ne C (ne_of_lt hij))
  rw [sigma_spec C i, sigma_spec C j]
  exact sortedTheta_strictMono C hij

noncomputable def rawChord (i j : Fin m) : ℝ :=
  dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j)

noncomputable def normalizedChord (i j : Fin m) : ℝ := rawChord C i j / lam

noncomputable def normalizedTheta (i : Fin m) : ℝ := sortedTheta C i / lam

noncomputable def delta (_C : SatChart o e n lam c v theta) : ℝ :=
  Real.pi / lam - (n : ℝ)

noncomputable def normalizedRow (i : Fin m) : List ℝ :=
  (directionRow o e (c ∘ v.succAbove) (sigma C i)).map fun x => x / lam

theorem delta_bounds : delta C ∈ Set.Ico 0 1 := by
  have hlow := Nat.floor_le (div_nonneg Real.pi_pos.le C.hlam.le)
  rw [C.hn] at hlow
  have hhi := Nat.lt_floor_add_one (Real.pi / lam)
  rw [C.hn] at hhi
  unfold delta
  constructor <;> linarith

theorem normalizedTheta_bounds (i : Fin m) :
    0 ≤ normalizedTheta C i ∧ normalizedTheta C i ≤ delta C := by
  have h := (C.htheta (sigma C i)).1
  rw [sigma_spec C i] at h
  have hd : delta C = (Real.pi - (n : ℝ) * lam) / lam := by
    unfold delta
    field_simp [C.hlam.ne']
  refine ⟨div_nonneg h.1 C.hlam.le, ?_⟩
  rw [hd]
  exact (div_le_div_iff_of_pos_right C.hlam).mpr h.2

theorem raw_corridor {i j : Fin m} (hij : i < j) :
    sortedTheta C i + lam ≤ rawChord C i j ∧
      rawChord C i j ≤ Real.pi - lam + sortedTheta C j := by
  have h := up_corridor C (sigma_ne C (ne_of_lt hij)) (sigma_up C hij)
  rwa [sigma_spec C i, sigma_spec C j] at h

theorem raw_triangle {i j k : Fin m} (hij : i < j) (hjk : j < k) :
    (rawChord C i j + lam ≤ rawChord C j k ∧
        rawChord C i j < rawChord C i k ∧ rawChord C i k < rawChord C j k) ∨
      (rawChord C j k + lam ≤ rawChord C i j ∧
        rawChord C j k < rawChord C i k ∧ rawChord C i k < rawChord C i j) := by
  have hneij := sigma_ne C (ne_of_lt hij)
  have hnejk := sigma_ne C (ne_of_lt hjk)
  have hneik := sigma_ne C (ne_of_lt (lt_trans hij hjk))
  have hupij := sigma_up C hij
  have hupjk := sigma_up C hjk
  obtain ⟨-, hbetween⟩ := up_trans C hneij hnejk hneik hupij hupjk
  have hcap := up_cap C hneij hnejk hneik hupij hupjk
  change lam ≤ |rawChord C j k - rawChord C i j| at hcap
  change (rawChord C i j < rawChord C i k ∧ rawChord C i k < rawChord C j k) ∨
    (rawChord C j k < rawChord C i k ∧ rawChord C i k < rawChord C i j) at hbetween
  rcases le_or_gt 0 (rawChord C j k - rawChord C i j) with hs | hs
  · rw [abs_of_nonneg hs] at hcap
    rcases hbetween with h | h
    · exact Or.inl ⟨by linarith, h⟩
    · exfalso
      linarith [h.1, h.2]
  · rw [abs_of_neg hs] at hcap
    rcases hbetween with h | h
    · exfalso
      linarith [h.1, h.2]
    · exact Or.inr ⟨by linarith, h⟩

/-- The actual sorted chord row permutes onto every shared model chord;
no list entry or multiplicity is discarded. -/
theorem normalizedRow_perm (i : Fin m) :
    (normalizedRow C i).Perm
      (((List.finRange m).erase i).map (normalizedChord C i)) := by
  let u := sigma C i
  have hp1 : List.Perm (directionRow o e (c ∘ v.succAbove) u)
      (((List.finRange m).erase u).map
        (dirRep o e (c ∘ v.succAbove) u)) := List.perm_insertionSort _ _
  have hmap : List.Perm ((List.finRange m).erase u)
      (((List.finRange m).erase i).map (sigma C)) := by
    apply List.Subperm.antisymm
    · apply List.Nodup.subperm ((List.nodup_finRange m).erase u)
      intro x hx
      rw [(List.nodup_finRange m).mem_erase_iff] at hx
      obtain ⟨j, hj⟩ := (sigma_bijective C).surjective x
      refine List.mem_map.mpr ⟨j, ?_, hj⟩
      rw [(List.nodup_finRange m).mem_erase_iff]
      exact ⟨fun hji => hx.1 (by rw [← hj, hji]), List.mem_finRange _⟩
    · apply List.Nodup.subperm
        (((List.nodup_finRange m).erase i).map (sigma_injective C))
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      rw [(List.nodup_finRange m).mem_erase_iff] at hj ⊢
      exact ⟨fun h => hj.1 (sigma_injective C h), List.mem_finRange _⟩
  have hp2 := hmap.map (dirRep o e (c ∘ v.succAbove) u)
  have hp := hp1.trans hp2
  have hscaled := hp.map (fun x => x / lam)
  change List.Perm
    ((directionRow o e (c ∘ v.succAbove) (sigma C i)).map fun x => x / lam)
    (((List.finRange m).erase i).map fun j =>
      dirRep o e (c ∘ v.succAbove) (sigma C i) (sigma C j) / lam)
  simpa only [u, List.map_map,
    Function.comp_def] using hscaled

/-- The actual normalized scalar model obtained from a saturated chart. -/
noncomputable def model : GenericModel m n where
  hn3 := C.hn3
  delta := delta C
  hdelta := delta_bounds C
  theta := normalizedTheta C
  htheta := by
    intro i j hij
    exact (div_lt_div_iff_of_pos_right C.hlam).mpr (sortedTheta_strictMono C hij)
  theta_bounds := normalizedTheta_bounds C
  d := normalizedChord C
  symm i j hij := by
    unfold normalizedChord rawChord
    rw [phi_comm C (sigma_ne C hij)]
  corridor i j hij := by
    obtain ⟨hlo, hhi⟩ := raw_corridor C hij
    have hlo' := (div_le_div_iff_of_pos_right C.hlam).mpr hlo
    have hhi' := (div_le_div_iff_of_pos_right C.hlam).mpr hhi
    constructor
    · simpa only [normalizedTheta, normalizedChord, add_div,
        div_self C.hlam.ne'] using hlo'
    · have hperiod : (n : ℝ) + delta C = Real.pi / lam := by unfold delta; ring
      rw [hperiod]
      simpa only [normalizedTheta, normalizedChord, add_div, sub_div,
        div_self C.hlam.ne'] using hhi'
  triangle i j k hij hjk := by
    rcases raw_triangle C hij hjk with h | h
    · apply Or.inl
      refine ⟨?_, (div_lt_div_iff_of_pos_right C.hlam).mpr h.2.1,
        (div_lt_div_iff_of_pos_right C.hlam).mpr h.2.2⟩
      simpa only [normalizedChord, add_div, div_self C.hlam.ne'] using
        (div_le_div_iff_of_pos_right C.hlam).mpr h.1
    · apply Or.inr
      refine ⟨?_, (div_lt_div_iff_of_pos_right C.hlam).mpr h.2.1,
        (div_lt_div_iff_of_pos_right C.hlam).mpr h.2.2⟩
      simpa only [normalizedChord, add_div, div_self C.hlam.ne'] using
        (div_le_div_iff_of_pos_right C.hlam).mpr h.1
  rowxs := normalizedRow C
  row_sorted i := by
    rw [normalizedRow, List.pairwise_map]
    exact (directionRow_sorted o e (c ∘ v.succAbove) (sigma C i)).pairwise.imp
      (fun h => (div_le_div_iff_of_pos_right C.hlam).mpr h)
  row_perm := normalizedRow_perm C

/-- The actual normalized strip remainder is preserved exactly, so an
actual HIGH-band bound transfers to the model without a new assumption. -/
theorem model_delta : (model C).delta = Real.pi / lam - (n : ℝ) := rfl

/-- Every extracted normalized defect equals the genuine geometric row defect. -/
theorem model_rowDefect (hm : 2 ≤ m) (i : Fin m) :
    SatScalarModel.rowDefect (model C) i =
      Jsp404.rowDefect n lam (directionRow o e c (v.succAbove (sigma C i))) := by
  have h := score_add_defect C hm (sigma C i)
  rw [linearGapScore_scale] at h
  have hright : (theta (sigma C i) + Real.pi) / lam =
      normalizedTheta C i + ((n : ℝ) + delta C) := by
    rw [sigma_spec C i]
    unfold normalizedTheta delta
    ring
  rw [hright, sigma_spec C i] at h
  change linearGapScore 1 (normalizedTheta C i)
    (normalizedTheta C i + ((n : ℝ) + delta C)) (normalizedRow C i) + _ = n at h
  change n - linearGapScore 1 (normalizedTheta C i)
    (normalizedTheta C i + ((n : ℝ) + delta C)) (normalizedRow C i) = _
  omega

/-- All chart hypotheses are geometric; the scalar model and its row-signature
identification are conclusions. -/
theorem exists_model (hm : 2 ≤ m) :
    ∃ σ : Fin m → Fin m, Function.Bijective σ ∧ ∃ M : GenericModel m n,
      M.delta = Real.pi / lam - (n : ℝ) ∧
        ∀ i, SatScalarModel.rowDefect M i =
          Jsp404.rowDefect n lam (directionRow o e c (v.succAbove (σ i))) := by
  exact ⟨sigma C, sigma_bijective C, model C, model_delta C, model_rowDefect C hm⟩

#print axioms linearGapScore_scale
#print axioms theta_injective
#print axioms sigma_bijective
#print axioms normalizedRow_perm
#print axioms model_delta
#print axioms model_rowDefect
#print axioms exists_model

end GenericChart

/-- A generic five-row model is exactly compatible with the frozen
six-centre model interface; no compression or geometry is inferred. -/
noncomputable def toModelSix {n : ℕ} (M : GenericModel 5 n) :
    SixModelCompression.ModelSix n where
  hn := M.hn3
  delta := M.delta
  hdelta := M.hdelta
  theta := M.theta
  htheta := M.htheta
  theta_bounds := M.theta_bounds
  d := M.d
  symm := M.symm
  corridor := M.corridor
  triangle := M.triangle
  rowxs := M.rowxs
  row_sorted := M.row_sorted
  row_perm := M.row_perm

theorem toModelSix_rowDefect {n : ℕ} (M : GenericModel 5 n) (i : Fin 5) :
    SixModelCompression.rowDefect (toModelSix M) i =
      SatScalarModel.rowDefect M i := rfl

/-- Concrete actual seven-centre extraction, with all six genuine
non-anchor defects and their full row lists. -/
theorem exists_model_seven {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)}
    {e : Plane₂} {lam : ℝ} {c : Fin 7 → Plane₂} {v : Fin 7}
    {theta : Fin 6 → ℝ} (C : SatChart o e n lam c v theta) :
    ∃ σ : Fin 6 → Fin 6, Function.Bijective σ ∧
      ∃ M : GenericModel 6 n, M.delta = Real.pi / lam - (n : ℝ) ∧
        ∀ i, SatScalarModel.rowDefect M i =
          Jsp404.rowDefect n lam (directionRow o e c (v.succAbove (σ i))) := by
  exact exists_model C (by decide)

/-- Concrete actual eight-centre extraction, with all seven genuine
non-anchor defects and their full row lists. -/
theorem exists_model_eight {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)}
    {e : Plane₂} {lam : ℝ} {c : Fin 8 → Plane₂} {v : Fin 8}
    {theta : Fin 7 → ℝ} (C : SatChart o e n lam c v theta) :
    ∃ σ : Fin 7 → Fin 7, Function.Bijective σ ∧
      ∃ M : GenericModel 7 n, M.delta = Real.pi / lam - (n : ℝ) ∧
        ∀ i, SatScalarModel.rowDefect M i =
          Jsp404.rowDefect n lam (directionRow o e c (v.succAbove (σ i))) := by
  exact exists_model C (by decide)

#print axioms toModelSix_rowDefect
#print axioms exists_model_seven
#print axioms exists_model_eight

end Jsp404.SatScalarExtraction
