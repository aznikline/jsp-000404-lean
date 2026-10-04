import Jsp000404.IntegerCompression
import Jsp000404.IntervalPacking

/-!
Fractional-coordinate transport for the normalized necessary angular model.
This changes scalar coordinates, not actual planar points. Integer labels are
compressed while fractional parts are retained. Real order, unit separation,
and the corridor endpoints used by the six-centre model are preserved.
-/

namespace Jsp404.ScalarCompression

open IntegerCompression

variable {S : Finset ℕ} {n : ℕ}

noncomputable def lift (C : CompressedLabels S n) (x : ℝ) : ℝ :=
  (C.f ⌊x⌋₊ : ℝ) + (x - (⌊x⌋₊ : ℝ))

noncomputable def shift (C : CompressedLabels S n) (x : ℝ) : ℤ :=
  (C.f ⌊x⌋₊ : ℤ) - (⌊x⌋₊ : ℤ)

lemma fraction_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x - (⌊x⌋₊ : ℝ) ∧ x - (⌊x⌋₊ : ℝ) < 1 := by
  exact ⟨sub_nonneg.mpr (Nat.floor_le hx), by linarith [Nat.lt_floor_add_one x]⟩

lemma lift_eq_shift (C : CompressedLabels S n) (x : ℝ) :
    lift C x = x + (shift C x : ℝ) := by
  simp only [lift, shift, Int.cast_sub, Int.cast_natCast]
  ring

lemma lift_nonneg (C : CompressedLabels S n) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ lift C x := by
  unfold lift
  exact add_nonneg (Nat.cast_nonneg _) (fraction_bounds hx).1

lemma lift_floor (C : CompressedLabels S n) {x : ℝ} (hx : 0 ≤ x) :
    ⌊lift C x⌋₊ = C.f ⌊x⌋₊ := by
  apply (Nat.floor_eq_iff (lift_nonneg C hx)).mpr
  have hf := fraction_bounds hx
  unfold lift
  exact ⟨by linarith, by linarith⟩

lemma lift_eq_self_of_lt_one (C : CompressedLabels S n) {x : ℝ}
    (_hx : 0 ≤ x) (hx1 : x < 1) : lift C x = x := by
  have hq : ⌊x⌋₊ = 0 := (Nat.floor_eq_zero).mpr hx1
  simp [lift, hq, C.zero]

lemma lift_lt_of_floor_lt (C : CompressedLabels S n) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hqx : ⌊x⌋₊ ∈ S) (hqy : ⌊y⌋₊ ∈ S)
    (hqq : ⌊x⌋₊ < ⌊y⌋₊) : x < y ∧ lift C x < lift C y := by
  have hqreal : (⌊x⌋₊ : ℝ) + 1 ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hqq
  have hfreal : (C.f ⌊x⌋₊ : ℝ) + 1 ≤ (C.f ⌊y⌋₊ : ℝ) := by
    exact_mod_cast C.used_strict _ hqx _ hqy hqq
  have hfx := fraction_bounds hx
  have hfy := fraction_bounds hy
  unfold lift
  constructor <;> linarith

lemma lift_lt_iff (C : CompressedLabels S n) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hqx : ⌊x⌋₊ ∈ S) (hqy : ⌊y⌋₊ ∈ S) :
    lift C x < lift C y ↔ x < y := by
  rcases lt_trichotomy ⌊x⌋₊ ⌊y⌋₊ with h | h | h
  · have hh := lift_lt_of_floor_lt C hx hy hqx hqy h
    exact ⟨fun _ => hh.1, fun _ => hh.2⟩
  · unfold lift
    rw [h]
    constructor <;> intro hh <;> linarith
  · have hh := lift_lt_of_floor_lt C hy hx hqy hqx h
    constructor <;> intro hbad <;> linarith

lemma lift_le_iff (C : CompressedLabels S n) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hqx : ⌊x⌋₊ ∈ S) (hqy : ⌊y⌋₊ ∈ S) :
    lift C x ≤ lift C y ↔ x ≤ y := by
  rw [← not_lt, ← not_lt]
  exact not_congr (lift_lt_iff C hy hx hqy hqx)

/-- Unit thresholds, including equality, are preserved in both directions. -/
lemma lift_unit_iff (C : CompressedLabels S n) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hqx : ⌊x⌋₊ ∈ S) (hqy : ⌊y⌋₊ ∈ S) :
    lift C x + 1 ≤ lift C y ↔ x + 1 ≤ y := by
  have hfx := fraction_bounds hx
  have hfy := fraction_bounds hy
  by_cases hq : ⌊y⌋₊ ≤ ⌊x⌋₊
  · have hqr : (⌊y⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hq
    have hfr : (C.f ⌊y⌋₊ : ℝ) ≤ (C.f ⌊x⌋₊ : ℝ) := by
      exact_mod_cast C.monotone hq
    unfold lift
    constructor <;> intro hh <;> linarith
  · by_cases hadj : ⌊y⌋₊ = ⌊x⌋₊ + 1
    · have hqr : (⌊y⌋₊ : ℝ) = (⌊x⌋₊ : ℝ) + 1 := by exact_mod_cast hadj
      have hfr : (C.f ⌊y⌋₊ : ℝ) = (C.f ⌊x⌋₊ : ℝ) + 1 := by
        exact_mod_cast C.used_adjacent _ hqx _ hqy hadj
      unfold lift
      constructor <;> intro hh <;> linarith
    · have hsep : ⌊x⌋₊ + 2 ≤ ⌊y⌋₊ := by omega
      have hqr : (⌊x⌋₊ : ℝ) + 2 ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hsep
      have hfr : (C.f ⌊x⌋₊ : ℝ) + 2 ≤ (C.f ⌊y⌋₊ : ℝ) := by
        exact_mod_cast C.used_separated _ hqx _ hqy hsep
      unfold lift
      constructor <;> intro _ <;> linarith

lemma lift_lower_unit_iff (C : CompressedLabels S n) (h0 : 0 ∈ S)
    {θ x : ℝ} (hθ : θ ∈ Set.Ico 0 1) (hx : 0 ≤ x) (hqx : ⌊x⌋₊ ∈ S) :
    θ + 1 ≤ lift C x ↔ θ + 1 ≤ x := by
  have hqθ : ⌊θ⌋₊ = 0 := (Nat.floor_eq_zero).mpr hθ.2
  have hmem : ⌊θ⌋₊ ∈ S := by rw [hqθ]; exact h0
  simpa [lift_eq_self_of_lt_one C hθ.1 hθ.2] using
    (lift_unit_iff C hθ.1 hx hmem hqx)

/-- The upper corridor endpoint may have floor n-1 or n; both are retained. -/
lemma lift_upper_endpoint (C : CompressedLabels S n) (hn : 3 ≤ n)
    {v : ℝ} (hv : v ∈ Set.Ico 0 2) :
    lift C ((n : ℝ) - 1 + v) = (C.top : ℝ) - 1 + v := by
  have hn1 : 1 ≤ n := by omega
  have hnc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1]; norm_num
  have hz : 0 ≤ (n : ℝ) - 1 + v := by
    have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith [hv.1]
  have hlo : n - 1 ≤ ⌊(n : ℝ) - 1 + v⌋₊ := by
    apply Nat.le_floor
    rw [hnc]
    linarith [hv.1]
  have hhi : ⌊(n : ℝ) - 1 + v⌋₊ < n + 1 := by
    apply (Nat.floor_lt hz).mpr
    push_cast
    linarith [hv.2]
  have hp : (C.f (n - 1) : ℝ) + 1 = (C.top : ℝ) := by
    exact_mod_cast C.penultimate
  have ht : (C.f n : ℝ) = (C.top : ℝ) := by rw [C.top_eq]
  have hc : ⌊(n : ℝ) - 1 + v⌋₊ = n - 1 ∨ ⌊(n : ℝ) - 1 + v⌋₊ = n := by omega
  rcases hc with hc | hc <;> unfold lift <;> rw [hc]
  · rw [hnc]
    linarith
  · linarith

lemma lift_upper_unit_iff (C : CompressedLabels S n) (hn : 3 ≤ n)
    (hprev : n - 1 ∈ S) (hN : n ∈ S)
    {δ θ x : ℝ} (hδ : δ ∈ Set.Ico 0 1) (hθ : θ ∈ Set.Ico 0 1)
    (hx : 0 ≤ x) (hqx : ⌊x⌋₊ ∈ S) :
    lift C x ≤ (C.top : ℝ) + δ - 1 + θ ↔ x ≤ (n : ℝ) + δ - 1 + θ := by
  let R := (n : ℝ) - 1 + (δ + θ)
  have hv : δ + θ ∈ Set.Ico 0 2 := ⟨by linarith [hδ.1, hθ.1], by linarith [hδ.2, hθ.2]⟩
  have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hR : 0 ≤ R := by dsimp [R]; linarith [hv.1]
  have hRlo : n - 1 ≤ ⌊R⌋₊ := by
    apply Nat.le_floor
    have hnc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ n by omega)]; norm_num
    rw [hnc]
    dsimp [R]; linarith [hv.1]
  have hRhi : ⌊R⌋₊ < n + 1 := by
    apply (Nat.floor_lt hR).mpr
    dsimp [R]; push_cast; linarith [hv.2]
  have hm : ⌊R⌋₊ ∈ S := by
    have hh : ⌊R⌋₊ = n - 1 ∨ ⌊R⌋₊ = n := by omega
    rcases hh with hh | hh <;> rw [hh] <;> assumption
  have he := lift_le_iff C hx hR hqx hm
  have hu := lift_upper_endpoint C hn hv
  change lift C R = _ at hu
  rw [hu] at he
  have ha : (C.top : ℝ) - 1 + (δ + θ) = (C.top : ℝ) + δ - 1 + θ := by ring
  have hb : R = (n : ℝ) + δ - 1 + θ := by dsimp [R]; ring
  rw [ha, hb] at he
  exact he

#print axioms lift_floor
#print axioms lift_unit_iff
#print axioms lift_upper_unit_iff

end Jsp404.ScalarCompression
