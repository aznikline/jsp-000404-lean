import Jsp000404.ScalarRowCompression

/-!
Normalized necessary six-centre scalar geometry and its finite compression.
The witness below preserves the scalar constraints and all five row defects;
it makes no assertion that compressed coordinates arise from planar points.
-/

namespace Jsp404.SixModelCompression

open IntegerCompression ScalarCompression

/-- Five non-anchor centres, with shared chords and explicitly sorted rows. -/
structure ModelSix (n : ℕ) where
  hn : 3 ≤ n
  delta : ℝ
  hdelta : delta ∈ Set.Ico 0 1
  theta : Fin 5 → ℝ
  htheta : StrictMono theta
  theta_bounds : ∀ i, 0 ≤ theta i ∧ theta i ≤ delta
  d : Fin 5 → Fin 5 → ℝ
  symm : ∀ i j, i ≠ j → d i j = d j i
  corridor : ∀ i j, i < j → theta i + 1 ≤ d i j ∧
    d i j ≤ (n : ℝ) + delta - 1 + theta j
  triangle : ∀ i j k, i < j → j < k →
    (d i j + 1 ≤ d j k ∧ d i j < d i k ∧ d i k < d j k) ∨
    (d j k + 1 ≤ d i j ∧ d j k < d i k ∧ d i k < d i j)
  rowxs : Fin 5 → List ℝ
  row_sorted : ∀ i, (rowxs i).Pairwise (· ≤ ·)
  row_perm : ∀ i, (rowxs i).Perm (((List.finRange 5).erase i).map (d i))

noncomputable def rowDefect {n : ℕ} (M : ModelSix n) (i : Fin 5) : ℕ :=
  n - linearGapScore 1 (M.theta i) (M.theta i + ((n : ℝ) + M.delta)) (M.rowxs i)

/-- The ten independent shared chords. -/
def unorderedPairs : Finset (Fin 5 × Fin 5) :=
  Finset.univ.filter (fun p => p.1 < p.2)

theorem unorderedPairs_card : unorderedPairs.card = 10 := by decide

noncomputable def labels {n : ℕ} (M : ModelSix n) : Finset ℕ :=
  {0, 1, n - 1, n} ∪ unorderedPairs.image (fun p => ⌊M.d p.1 p.2⌋₊)

theorem markers_mem {n : ℕ} (M : ModelSix n) :
    0 ∈ labels M ∧ 1 ∈ labels M ∧ n - 1 ∈ labels M ∧ n ∈ labels M := by
  classical
  simp [labels]

theorem labels_card {n : ℕ} (M : ModelSix n) : (labels M).card ≤ 14 := by
  classical
  have hmarkers : ({0, 1, n - 1, n} : Finset ℕ).card ≤ 4 := by
    have h0 := Finset.card_insert_le 0 ({1, n - 1, n} : Finset ℕ)
    have h1 := Finset.card_insert_le 1 ({n - 1, n} : Finset ℕ)
    have h2 := Finset.card_le_two (a := n - 1) (b := n)
    omega
  have himage := Finset.card_image_le
    (s := unorderedPairs) (f := fun p => ⌊M.d p.1 p.2⌋₊)
  have hunion := Finset.card_union_le
    ({0, 1, n - 1, n} : Finset ℕ)
    (unorderedPairs.image (fun p => ⌊M.d p.1 p.2⌋₊))
  unfold labels
  rw [unorderedPairs_card] at himage
  omega

theorem chord_bounds {n : ℕ} (M : ModelSix n) (i j : Fin 5) (hne : i ≠ j) :
    1 ≤ M.d i j ∧ M.d i j < (n : ℝ) + M.delta := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hc := M.corridor i j hij
    have hi := M.theta_bounds i
    have hj := M.theta_bounds j
    have hj1 : M.theta j < 1 := lt_of_le_of_lt hj.2 M.hdelta.2
    constructor <;> linarith
  · rw [M.symm i j hne]
    have hc := M.corridor j i hji
    have hi := M.theta_bounds i
    have hj := M.theta_bounds j
    have hi1 : M.theta i < 1 := lt_of_le_of_lt hi.2 M.hdelta.2
    constructor <;> linarith

theorem chord_floor_mem {n : ℕ} (M : ModelSix n) (i j : Fin 5) (hne : i ≠ j) :
    ⌊M.d i j⌋₊ ∈ labels M := by
  classical
  rcases lt_or_gt_of_ne hne with hij | hji
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨(i, j), by simp [unorderedPairs, hij], rfl⟩
  · rw [M.symm i j hne]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨(j, i), by simp [unorderedPairs, hji], rfl⟩

theorem labels_le_top {n : ℕ} (M : ModelSix n) : ∀ k ∈ labels M, k ≤ n := by
  classical
  intro k hk
  rcases Finset.mem_union.mp hk with hk | hk
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact Nat.zero_le n
    · exact (show 1 ≤ n by have := M.hn; omega)
    · exact Nat.sub_le n 1
    · exact le_rfl
  · rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
    have hij : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    have hb := chord_bounds M p.1 p.2 (ne_of_lt hij)
    have hlt : ⌊M.d p.1 p.2⌋₊ < n + 1 := by
      apply (Nat.floor_lt (by linarith [hb.1])).mpr
      push_cast
      linarith [hb.2, M.hdelta.2]
    omega

noncomputable def compression {n : ℕ} (M : ModelSix n) : CompressedLabels (labels M) n :=
  compressedLabels (labels M) n M.hn (markers_mem M).1 (markers_mem M).2.1
    (markers_mem M).2.2.1 (markers_mem M).2.2.2 (labels_card M) (labels_le_top M)

theorem row_mem_bounds {n : ℕ} (M : ModelSix n) (i : Fin 5) :
    ∀ x ∈ M.rowxs i, 1 ≤ x ∧ x < (n : ℝ) + M.delta ∧ ⌊x⌋₊ ∈ labels M := by
  intro x hx
  have hm := (M.row_perm i).mem_iff.mp hx
  rcases List.mem_map.mp hm with ⟨j, hj, rfl⟩
  have hji : j ≠ i := ((List.nodup_finRange 5).mem_erase_iff.mp hj).1
  have hb := chord_bounds M i j hji.symm
  exact ⟨hb.1, hb.2, chord_floor_mem M i j hji.symm⟩

theorem lift_row_sorted {n : ℕ} (M : ModelSix n) (i : Fin 5) :
    ((M.rowxs i).map (lift (compression M))).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem _ (M.row_sorted i)
  intro a b ha hb hab
  have ha' := row_mem_bounds M i a ha
  have hb' := row_mem_bounds M i b hb
  exact (lift_le_iff (compression M) (by linarith [ha'.1])
    (by linarith [hb'.1]) ha'.2.2 hb'.2.2).mpr hab

/-- Concrete compressed scalar model; the planar coordinates are not modified. -/
noncomputable def compressedModel {n : ℕ} (M : ModelSix n) : ModelSix (compression M).top where
  hn := (compression M).top_bounds.1
  delta := M.delta
  hdelta := M.hdelta
  theta := M.theta
  htheta := M.htheta
  theta_bounds := M.theta_bounds
  d i j := lift (compression M) (M.d i j)
  symm i j hne := by rw [M.symm i j hne]
  corridor i j hij := by
    have hc := M.corridor i j hij
    have hb := chord_bounds M i j (ne_of_lt hij)
    have hmem := chord_floor_mem M i j (ne_of_lt hij)
    have hi : M.theta i ∈ Set.Ico 0 1 :=
      ⟨(M.theta_bounds i).1, lt_of_le_of_lt (M.theta_bounds i).2 M.hdelta.2⟩
    have hj : M.theta j ∈ Set.Ico 0 1 :=
      ⟨(M.theta_bounds j).1, lt_of_le_of_lt (M.theta_bounds j).2 M.hdelta.2⟩
    exact ⟨(lift_lower_unit_iff (compression M) (markers_mem M).1 hi
      (by linarith [hb.1]) hmem).mpr hc.1,
      (lift_upper_unit_iff (compression M) M.hn (markers_mem M).2.2.1
        (markers_mem M).2.2.2 M.hdelta hj (by linarith [hb.1]) hmem).mpr hc.2⟩
  triangle i j k hij hjk := by
    have hik := lt_trans hij hjk
    have bij := chord_bounds M i j (ne_of_lt hij)
    have bjk := chord_bounds M j k (ne_of_lt hjk)
    have bik := chord_bounds M i k (ne_of_lt hik)
    have mij := chord_floor_mem M i j (ne_of_lt hij)
    have mjk := chord_floor_mem M j k (ne_of_lt hjk)
    have mik := chord_floor_mem M i k (ne_of_lt hik)
    have hijjk := lift_unit_iff (compression M) (by linarith [bij.1])
      (by linarith [bjk.1]) mij mjk
    have hjkij := lift_unit_iff (compression M) (by linarith [bjk.1])
      (by linarith [bij.1]) mjk mij
    have hijik := lift_lt_iff (compression M) (by linarith [bij.1])
      (by linarith [bik.1]) mij mik
    have hikjk := lift_lt_iff (compression M) (by linarith [bik.1])
      (by linarith [bjk.1]) mik mjk
    have hjkik := lift_lt_iff (compression M) (by linarith [bjk.1])
      (by linarith [bik.1]) mjk mik
    have hikij := lift_lt_iff (compression M) (by linarith [bik.1])
      (by linarith [bij.1]) mik mij
    rcases M.triangle i j k hij hjk with h | h
    · exact Or.inl ⟨hijjk.mpr h.1, hijik.mpr h.2.1, hikjk.mpr h.2.2⟩
    · exact Or.inr ⟨hjkij.mpr h.1, hjkik.mpr h.2.1, hikij.mpr h.2.2⟩
  rowxs i := (M.rowxs i).map (lift (compression M))
  row_sorted := lift_row_sorted M
  row_perm i := by
    have h := (M.row_perm i).map (lift (compression M))
    simpa only [List.map_map, Function.comp_def] using h

theorem compressedModel_rowDefect {n : ℕ} (M : ModelSix n) (i : Fin 5) :
    rowDefect (compressedModel M) i = rowDefect M i := by
  exact ScalarRowCompression.anchored_row_score_complement_preserved
    (compression M) M.hn (markers_mem M).1 (markers_mem M).2.2.1
    (markers_mem M).2.2.2 M.hdelta (M.theta_bounds i)
    (M.rowxs i) (M.row_sorted i) (row_mem_bounds M i)

/-- Every normalized necessary model has a defect-preserving model in one of
the finite strips 3 through 24, with the anchor directions unchanged. -/
theorem exists_compressedModel {n : ℕ} (M : ModelSix n) :
    ∃ n', 3 ≤ n' ∧ n' ≤ 24 ∧ ∃ M' : ModelSix n',
      M'.delta = M.delta ∧ M'.theta = M.theta ∧
      ∀ i, rowDefect M' i = rowDefect M i := by
  exact ⟨(compression M).top, (compression M).top_bounds.1,
    (compression M).top_bounds.2, compressedModel M, rfl, rfl,
    compressedModel_rowDefect M⟩

#print axioms exists_compressedModel

end Jsp404.SixModelCompression
