import Jsp000404.ScalarCompression
import Jsp000404.CyclicFloorTransport

/-!
# Concrete normalized anchored-row transport

For the compression supplied by `CompressedLabels`, this file preserves the
actual interval floor count, active-gap support and row defect. The left
endpoint is the genuine anchor angle `θ`, and the right endpoint is `θ+p`.
-/

namespace Jsp404.ScalarRowCompression

open IntegerCompression ScalarCompression

private lemma min_floor_one (x : ℝ) :
    min ⌊x⌋₊ 1 = if 1 ≤ x then 1 else 0 := by
  by_cases hx : 1 ≤ x
  · have hq : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff' one_ne_zero).mpr (by simpa using hx)
    rw [ite_eq_left hx]
    omega
  · have hq : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (lt_of_not_ge hx)
    rw [ite_eq_right hx, hq]
    simp

/-- Every support indicator is determined exactly by its unit threshold. -/
private lemma support_indicator_eq {a b : ℝ} (h : 1 ≤ a ↔ 1 ≤ b) :
    min ⌊a⌋₊ 1 = min ⌊b⌋₊ 1 := by
  rw [min_floor_one, min_floor_one]
  simp only [h]

/-- Interval support transport from the first, internal and final threshold
correspondences. It does not presume an endpoint angle of zero. -/
private theorem bigCount_map (f : ℝ → ℝ) (left left' right right' : ℝ)
    (xs : List ℝ)
    (hfirst : ∀ x ∈ xs, left' + 1 ≤ f x ↔ left + 1 ≤ x)
    (hpair : ∀ x ∈ xs, ∀ y ∈ xs, f x + 1 ≤ f y ↔ x + 1 ≤ y)
    (hlast : ∀ x ∈ xs, f x + 1 ≤ right' ↔ x + 1 ≤ right)
    (hempty : left' + 1 ≤ right' ↔ left + 1 ≤ right) :
    linearBigCount 1 left' right' (xs.map f) =
      linearBigCount 1 left right xs := by
  induction xs generalizing left left' with
  | nil =>
    simp only [List.map_nil, linearBigCount, div_one]
    apply support_indicator_eq
    constructor <;> intro h
    · have hh : left' + 1 ≤ right' := by linarith
      have := hempty.mp hh
      linarith
    · have hh : left + 1 ≤ right := by linarith
      have := hempty.mpr hh
      linarith
  | cons x xs ih =>
    have hhead : min ⌊f x - left'⌋₊ 1 = min ⌊x - left⌋₊ 1 := by
      apply support_indicator_eq
      have hh := hfirst x List.mem_cons_self
      constructor <;> intro h
      · have := hh.mp (by linarith)
        linarith
      · have := hh.mpr (by linarith)
        linarith
    have htl := ih x (f x)
      (fun y hy => hpair x List.mem_cons_self y (List.mem_cons_of_mem x hy))
      (fun y hy z hz => hpair y (List.mem_cons_of_mem x hy)
        z (List.mem_cons_of_mem x hz))
      (fun y hy => hlast y (List.mem_cons_of_mem x hy))
      (hlast x List.mem_cons_self)
    simp only [List.map_cons, linearBigCount, div_one, hhead, htl]

variable {S : Finset ℕ} {n : ℕ}

private theorem lift_pairwise (C : CompressedLabels S n) {xs : List ℝ}
    (hs : xs.Pairwise (· ≤ ·))
    (hmem : ∀ x ∈ xs, 0 ≤ x ∧ ⌊x⌋₊ ∈ S) :
    (xs.map (lift C)).Pairwise (· ≤ ·) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.pairwise_cons]
    constructor
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      exact (lift_le_iff C (hmem x List.mem_cons_self).1 (hmem z (by simp [hz])).1
        (hmem x List.mem_cons_self).2 (hmem z (by simp [hz])).2).mpr
        ((List.pairwise_cons.mp hs).1 z hz)
    · exact ih (List.pairwise_cons.mp hs).2
        (fun y hy => hmem y (List.mem_cons_of_mem x hy))

private lemma lift_period (C : CompressedLabels S n) (hn : 3 ≤ n)
    {δ : ℝ} (hδ : δ ∈ Set.Ico 0 1) :
    lift C ((n : ℝ) + δ) = (C.top : ℝ) + δ := by
  have hv : 1 + δ ∈ Set.Ico 0 2 := ⟨by linarith [hδ.1], by linarith [hδ.2]⟩
  have h := lift_upper_endpoint C hn hv
  have hold : (n : ℝ) - 1 + (1 + δ) = (n : ℝ) + δ := by ring
  have hnew : (C.top : ℝ) - 1 + (1 + δ) = (C.top : ℝ) + δ := by ring
  simpa only [hold, hnew] using h

/-- Concrete active-gap support invariance for a normalized anchored row. -/
theorem anchored_row_bigCount_preserved (C : CompressedLabels S n)
    (hn : 3 ≤ n) (h0 : 0 ∈ S) (hprev : n - 1 ∈ S) (hN : n ∈ S)
    {δ θ : ℝ} (hδ : δ ∈ Set.Ico 0 1) (hθ : 0 ≤ θ ∧ θ ≤ δ)
    (xs : List ℝ)
    (hmem : ∀ x ∈ xs, 1 ≤ x ∧ x < (n : ℝ) + δ ∧ ⌊x⌋₊ ∈ S) :
    linearBigCount 1 θ (θ + ((C.top : ℝ) + δ)) (xs.map (lift C)) =
      linearBigCount 1 θ (θ + ((n : ℝ) + δ)) xs := by
  have hθ' : θ ∈ Set.Ico 0 1 := ⟨hθ.1, lt_of_le_of_lt hθ.2 hδ.2⟩
  apply bigCount_map
  · intro x hx
    exact lift_lower_unit_iff C h0 hθ' (by linarith [(hmem x hx).1])
      (hmem x hx).2.2
  · intro x hx y hy
    exact lift_unit_iff C (by linarith [(hmem x hx).1])
      (by linarith [(hmem y hy).1]) (hmem x hx).2.2 (hmem y hy).2.2
  · intro x hx
    have hh := lift_upper_unit_iff C hn hprev hN hδ hθ'
      (by linarith [(hmem x hx).1]) (hmem x hx).2.2
    constructor <;> intro h
    · have := hh.mp (by linarith)
      linarith
    · have := hh.mpr (by linarith)
      linarith
  · have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have htopreal : (3 : ℝ) ≤ C.top := by exact_mod_cast C.top_bounds.1
    constructor <;> intro _ <;> linarith [hδ.1]

/-- Concrete floor-sum transport, with the anchor offset retained. -/
theorem anchored_row_floorSum_transport (C : CompressedLabels S n)
    (hn : 3 ≤ n) (h0 : 0 ∈ S) (hN : n ∈ S)
    {δ θ : ℝ} (hδ : δ ∈ Set.Ico 0 1) (hθ : 0 ≤ θ ∧ θ ≤ δ)
    (xs : List ℝ) (hs : xs.Pairwise (· ≤ ·))
    (hmem : ∀ x ∈ xs, 1 ≤ x ∧ x < (n : ℝ) + δ ∧ ⌊x⌋₊ ∈ S) :
    linearFloorSum 1 θ (θ + ((C.top : ℝ) + δ)) (xs.map (lift C)) + n =
      linearFloorSum 1 θ (θ + ((n : ℝ) + δ)) xs + C.top := by
  have hθ' : θ ∈ Set.Ico 0 1 := ⟨hθ.1, lt_of_le_of_lt hθ.2 hδ.2⟩
  have hxs : ∀ x ∈ xs, 0 ≤ x ∧ ⌊x⌋₊ ∈ S := by
    intro x hx
    exact ⟨by linarith [(hmem x hx).1], (hmem x hx).2.2⟩
  have hqθ : ⌊θ⌋₊ ∈ S := by
    rw [Nat.floor_eq_zero.mpr hθ'.2]
    exact h0
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have htopreal : (3 : ℝ) ≤ C.top := by exact_mod_cast C.top_bounds.1
  have hp : 0 ≤ (n : ℝ) + δ := by linarith [hδ.1]
  have hqp : ⌊(n : ℝ) + δ⌋₊ ∈ S := by
    have hh : ⌊(n : ℝ) + δ⌋₊ = n := by
      apply (Nat.floor_eq_iff hp).mpr
      constructor <;> linarith [hδ.1, hδ.2]
    rw [hh]
    exact hN
  have hwindow : ∀ x ∈ xs, θ ≤ x ∧ x ≤ θ + ((n : ℝ) + δ) := by
    intro x hx
    constructor <;> linarith [(hmem x hx).1, (hmem x hx).2.1, hθ'.2, hθ.1]
  have hwindow' : ∀ y ∈ xs.map (lift C),
      θ ≤ y ∧ y ≤ θ + ((C.top : ℝ) + δ) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    constructor
    · have hh := (lift_le_iff C hθ'.1 (hxs x hx).1 hqθ (hxs x hx).2).mpr
        (hwindow x hx).1
      simpa only [lift_eq_self_of_lt_one C hθ'.1 hθ'.2] using hh
    · have hh := (lift_lt_iff C (hxs x hx).1 hp (hxs x hx).2 hqp).mpr
        (hmem x hx).2.1
      rw [lift_period C hn hδ] at hh
      linarith [hθ.1]
  let tagged := xs.map (fun x => (x, shift C x))
  have hold : tagged.map Prod.fst = xs := by
    simp [tagged, List.map_map, Function.comp_def]
  have hnew : tagged.map (fun x => x.1 + (x.2 : ℝ)) = xs.map (lift C) := by
    simp only [tagged, List.map_map, Function.comp_def]
    congr 1
    funext x
    exact (lift_eq_shift C x).symm
  have hend : θ + ((n : ℝ) + δ) +
      (((C.top : ℤ) - (n : ℤ) : ℤ) : ℝ) = θ + ((C.top : ℝ) + δ) := by
    push_cast
    ring
  have ht := linearFloorSum_integer_transport θ (θ + ((n : ℝ) + δ))
    0 ((C.top : ℤ) - (n : ℤ)) tagged
    (by simpa only [hold] using hs)
    (by simpa only [hold] using hwindow)
    (by linarith [hδ.1])
    (by simpa only [hnew] using lift_pairwise C hs hxs)
    (by simpa only [hnew, Int.cast_zero, add_zero, hend] using hwindow')
    (by simpa only [Int.cast_zero, add_zero, hend] using
      (show θ ≤ θ + ((C.top : ℝ) + δ) by linarith [hδ.1]))
  simp only [Int.cast_zero, add_zero, hold, hnew, hend, sub_zero] at ht
  have hc : (linearFloorSum 1 θ (θ + ((C.top : ℝ) + δ))
      (xs.map (lift C)) : ℤ) + (n : ℤ) =
      (linearFloorSum 1 θ (θ + ((n : ℝ) + δ)) xs : ℤ) + (C.top : ℤ) := by omega
  exact_mod_cast hc

/-- The existing gap-score definition gives the same normalized exponent
complement after the concrete coordinate compression. -/
theorem anchored_row_score_complement_preserved (C : CompressedLabels S n)
    (hn : 3 ≤ n) (h0 : 0 ∈ S) (hprev : n - 1 ∈ S) (hN : n ∈ S)
    {δ θ : ℝ} (hδ : δ ∈ Set.Ico 0 1) (hθ : 0 ≤ θ ∧ θ ≤ δ)
    (xs : List ℝ) (hs : xs.Pairwise (· ≤ ·))
    (hmem : ∀ x ∈ xs, 1 ≤ x ∧ x < (n : ℝ) + δ ∧ ⌊x⌋₊ ∈ S) :
    C.top - linearGapScore 1 θ (θ + ((C.top : ℝ) + δ)) (xs.map (lift C)) =
      n - linearGapScore 1 θ (θ + ((n : ℝ) + δ)) xs := by
  have hB := anchored_row_bigCount_preserved C hn h0 hprev hN hδ hθ xs hmem
  have hF := anchored_row_floorSum_transport C hn h0 hN hδ hθ xs hs hmem
  have ho := linearGapScore_add_bigCount 1 θ (θ + ((n : ℝ) + δ)) xs
  have hn' := linearGapScore_add_bigCount 1 θ
    (θ + ((C.top : ℝ) + δ)) (xs.map (lift C))
  omega

/-- Full concrete support-plus-cell-loss defect invariance. -/
theorem anchored_row_defect_preserved (C : CompressedLabels S n)
    (hn : 3 ≤ n) (h0 : 0 ∈ S) (hprev : n - 1 ∈ S) (hN : n ∈ S)
    {δ θ : ℝ} (hδ : δ ∈ Set.Ico 0 1) (hθ : 0 ≤ θ ∧ θ ≤ δ)
    (xs : List ℝ) (hs : xs.Pairwise (· ≤ ·))
    (hmem : ∀ x ∈ xs, 1 ≤ x ∧ x < (n : ℝ) + δ ∧ ⌊x⌋₊ ∈ S) :
    linearBigCount 1 θ (θ + ((C.top : ℝ) + δ)) (xs.map (lift C)) +
        (C.top - linearFloorSum 1 θ (θ + ((C.top : ℝ) + δ)) (xs.map (lift C))) =
      linearBigCount 1 θ (θ + ((n : ℝ) + δ)) xs +
        (n - linearFloorSum 1 θ (θ + ((n : ℝ) + δ)) xs) := by
  have hB := anchored_row_bigCount_preserved C hn h0 hprev hN hδ hθ xs hmem
  have hF := anchored_row_floorSum_transport C hn h0 hN hδ hθ xs hs hmem
  omega

#print axioms anchored_row_bigCount_preserved
#print axioms anchored_row_floorSum_transport
#print axioms anchored_row_score_complement_preserved
#print axioms anchored_row_defect_preserved

end Jsp404.ScalarRowCompression
