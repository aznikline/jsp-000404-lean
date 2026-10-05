import Jsp000404.ActualMinimumDeletionNormalForm
import Jsp000404.ActualMinimumCardBandMaximizer
import Jsp000404.BandMaximumScorePlateau

/-!
# Minimum actual counter-cardinality, then maximum potential at that cardinality

The first selection ranges over actual band configurations whose original
potential exceeds the explicit cap. Its minimum cardinality gives the
actual deletion cap. The second selection ranges over actual configurations
of that same cardinality; an independent classical coarse bound gives an
attained greatest natural potential. This preserves the critical deletion
cap while providing a same-cardinality scale plateau.

The configurations retain their actual weighted scores. No flatness or
`card <= n+1` assertion is introduced.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualMinimalBandCounterexample

/-- Actual least cardinality among band counterexamples to the explicit cap. -/
structure Model (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (rho upper : ℝ) (cap t : ℕ) (c : Fin t → Plane₂) (lam : ℝ) : Prop where
  card_ge_three : 3 ≤ t
  scale_lower : rho < lam
  scale_upper : lam ≤ upper
  legality : Section4Legality c lam
  over_cap : cap < potential lam (directionRows o e c)
  minimum_card : ∀ {r : ℕ}, 3 ≤ r → ∀ (d : Fin r → Plane₂) (scale : ℝ),
    rho < scale → scale ≤ upper → Section4Legality d scale →
    cap < potential scale (directionRows o e d) → t ≤ r

private def CounterCard (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (rho upper : ℝ) (cap t : ℕ) : Prop :=
  3 ≤ t ∧ ∃ scale : ℝ, rho < scale ∧ scale ≤ upper ∧
    ∃ c : Fin t → Plane₂, Section4Legality c scale ∧
      cap < potential scale (directionRows o e c)

/-- Restricting the original actual points to `cap+1` points proves the
cardinality bound; no inflation or sharp capacity theorem is used. -/
theorem model_card_le_cap_succ {t cap : ℕ} (hcap2 : 2 ≤ cap)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {c : Fin t → Plane₂}
    (H : Model o e rho upper cap t c lam) : t ≤ cap + 1 := by
  classical
  by_contra hnot
  have hcard : cap + 1 ≤ t := by omega
  let pick : Fin (cap + 1) → Fin t := Fin.castLE hcard
  have hpick : Function.Injective pick := Fin.castLE_injective hcard
  have hleg := H.legality.restrict_injective pick hpick
  have hge := ActualPotentialInflation.card_le_potential lam
    (directionRows o e (c ∘ pick))
  have hover : cap < potential lam (directionRows o e (c ∘ pick)) := by omega
  have hmin := H.minimum_card (by omega : 3 ≤ cap + 1) (c ∘ pick) lam
    H.scale_lower H.scale_upper hleg hover
  omega

/-- Internally choose the least actual band counter-cardinality. -/
theorem exists_minimal_counter {s cap : ℕ} (hcap2 : 2 ≤ cap)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} (hs : 3 ≤ s) (c : Fin s → Plane₂)
    (hleg : Section4Legality c lam) (hlow : rho < lam) (hupp : lam ≤ upper)
    (hover : cap < potential lam (directionRows o e c)) :
    ∃ t : ℕ, t ≤ s ∧ t ≤ cap + 1 ∧ ∃ scale : ℝ, ∃ d : Fin t → Plane₂,
      Model o e rho upper cap t d scale := by
  classical
  let P : ℕ → Prop := CounterCard o e rho upper cap
  have hex : ∃ t, P t := ⟨s, hs, lam, hlow, hupp, c, hleg, hover⟩
  let t := Nat.find hex
  have hspec : P t := Nat.find_spec hex
  have hts : t ≤ s := Nat.find_min' hex ⟨hs, lam, hlow, hupp, c, hleg, hover⟩
  obtain ⟨ht, scale, hlo, hup, d, hd, hdover⟩ := hspec
  have H : Model o e rho upper cap t d scale := by
    refine ⟨ht, hlo, hup, hd, hdover, ?_⟩
    intro r hr p param hl hu hp hF
    exact Nat.find_min' hex ⟨hr, param, hl, hu, p, hp, hF⟩
  exact ⟨t, hts, model_card_le_cap_succ hcap2 o e H, scale, d, H⟩

/-- The actual deletion cap follows from the selected counter-cardinality.
It is not a caller-supplied capacity field for the current domain. -/
theorem actual_delete_potential_le_cap {s cap : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {c : Fin (s + 1) → Plane₂}
    (H : Model o e rho upper cap (s + 1) c lam) (q : Fin (s + 1)) :
    potential lam (directionRows o e (c ∘ q.succAbove)) ≤ cap := by
  by_contra hnot
  have hover : cap < potential lam (directionRows o e (c ∘ q.succAbove)) := by omega
  have hcard := H.minimum_card hs (c ∘ q.succAbove) lam
    H.scale_lower H.scale_upper (H.legality.erase q) hover
  omega

/-- No actual deletion can preserve the over-capacity potential. -/
theorem not_actual_removable {s cap : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {c : Fin (s + 1) → Plane₂}
    (H : Model o e rho upper cap (s + 1) c lam) (q : Fin (s + 1)) :
    ¬ Removable lam (fun v i => deleteIndex o e c v i) (directionRows o e c) q := by
  intro hrem
  have hle : potential lam (directionRows o e c) ≤
      potential lam (directionRows o e (c ∘ q.succAbove)) := by
    rw [potential_sub_config o e q lam]
    exact hrem
  have hcap := actual_delete_potential_le_cap hs o e H q
  have hover := H.over_cap
  omega

/-- Critical exact excess and all actual minimum-point incoming gains zero. -/
theorem actual_minimum_score_critical_form {s cap : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {c : Fin (s + 1) → Plane₂}
    (H : Model o e rho upper cap (s + 1) c lam) (q : Fin (s + 1))
    (hmin : ∀ i : Fin (s + 1),
      rowScore lam (directionRow o e c q) ≤ rowScore lam (directionRow o e c i))
    (hdiv : 2 ^ rowScore lam (directionRow o e c q) ∣ cap) :
    potential lam (directionRows o e c) = cap + 2 ^ rowScore lam (directionRow o e c q) ∧
      potential lam (directionRows o e (c ∘ q.succAbove)) = cap ∧
      (∀ i : Fin (s + 1), i ≠ q →
        rowGain lam (directionRow o e c i) (deleteIndex o e c q i) = 0) ∧
      (∀ i : Fin s, rowScore lam (directionRow o e (c ∘ q.succAbove) i) =
        rowScore lam (directionRow o e c (q.succAbove i))) :=
  ActualMinimumDeletionNormalForm.actual_minimum_delete_normal_form
    (by omega) o e H.legality q cap hmin hdiv H.over_cap
    (actual_delete_potential_le_cap hs o e H q)

/-- The second maximum compares only actual realizations of the fixed
cardinality. It is a different domain from a maximum over all cardinalities. -/
def FixedCardMaximal (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (rho upper : ℝ) (t M : ℕ) : Prop :=
  ∀ (d : Fin t → Plane₂) (scale : ℝ), rho < scale → scale ≤ upper →
    Section4Legality d scale → potential scale (directionRows o e d) ≤ M

structure FixedCardModel (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (rho upper : ℝ) (cap t M : ℕ) (c : Fin t → Plane₂) (lam : ℝ) : Prop
    extends Model o e rho upper cap t c lam where
  potential_eq : potential lam (directionRows o e c) = M
  maximal_same_card : FixedCardMaximal o e rho upper t M

private def AttainedAtCard (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (rho upper : ℝ) (t F : ℕ) : Prop :=
  ∃ scale : ℝ, rho < scale ∧ scale ≤ upper ∧ ∃ d : Fin t → Plane₂,
    Section4Legality d scale ∧ potential scale (directionRows o e d) = F

/-- Among the actual models of the selected cardinality, independently
bounded natural potentials have an attained greatest value. -/
theorem exists_fixed_card_maximum {t k cap : ℕ} (hk : 2 ≤ k)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {rho upper lam : ℝ} {c : Fin t → Plane₂}
    (hclassical : Real.pi / (k : ℝ) ≤ rho)
    (H : Model o e rho upper cap t c lam) :
    ∃ M : ℕ, cap < M ∧ M ≤ 2 ^ k ∧ ∃ scale : ℝ, ∃ d : Fin t → Plane₂,
      FixedCardModel o e rho upper cap t M d scale := by
  classical
  let P : ℕ → Prop := AttainedAtCard o e rho upper t
  let M := Nat.findGreatest P (2 ^ k)
  have hbound := ActualMaximumMassReduction.actual_potential_le_classical_power
    hk o e he H.card_ge_three H.legality (hclassical.trans_lt H.scale_lower)
  have hP0 : P (potential lam (directionRows o e c)) :=
    ⟨lam, H.scale_lower, H.scale_upper, c, H.legality, rfl⟩
  have hMspec : P M := Nat.findGreatest_spec hbound hP0
  have hMge : potential lam (directionRows o e c) ≤ M := Nat.le_findGreatest hbound hP0
  have hMover : cap < M := H.over_cap.trans_le hMge
  have hMbound : M ≤ 2 ^ k := Nat.findGreatest_le _
  have hmax : FixedCardMaximal o e rho upper t M := by
    intro d scale hlo hup hleg
    have hb := ActualMaximumMassReduction.actual_potential_le_classical_power
      hk o e he H.card_ge_three hleg (hclassical.trans_lt hlo)
    exact Nat.le_findGreatest hb
      (show P (potential scale (directionRows o e d)) from ⟨scale, hlo, hup, d, hleg, rfl⟩)
  obtain ⟨scale, hlo, hup, d, hleg, hpot⟩ := hMspec
  have H' : Model o e rho upper cap t d scale :=
    ⟨H.card_ge_three, hlo, hup, hleg, hpot.symm ▸ hMover, H.minimum_card⟩
  exact ⟨M, hMover, hMbound, scale, d, H', hpot, hmax⟩

/-- Same-cardinality maximization preserves the original counter-cardinality
and thus the actual critical deletion cap. -/
theorem fixed_card_critical_form {s cap : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {M : ℕ} {c : Fin (s + 1) → Plane₂}
    (H : FixedCardModel o e rho upper cap (s + 1) M c lam) (q : Fin (s + 1))
    (hmin : ∀ i : Fin (s + 1),
      rowScore lam (directionRow o e c q) ≤ rowScore lam (directionRow o e c i))
    (hdiv : 2 ^ rowScore lam (directionRow o e c q) ∣ cap) :
    M = cap + 2 ^ rowScore lam (directionRow o e c q) ∧
      potential lam (directionRows o e (c ∘ q.succAbove)) = cap ∧
      (∀ i : Fin (s + 1), i ≠ q →
        rowGain lam (directionRow o e c i) (deleteIndex o e c q i) = 0) := by
  obtain ⟨hF, hdel, hg, _⟩ := actual_minimum_score_critical_form hs o e H.toModel q hmin hdiv
  rw [H.potential_eq] at hF
  exact ⟨hF, hdel, hg⟩

/-- The public monotonicity primitive gives a full lower-band row-score
plateau using just the genuine fixed-cardinality maximum. -/
theorem actual_fixed_card_score_plateau {t cap M : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam lam' : ℝ} {c : Fin t → Plane₂}
    (H : FixedCardModel o e rho upper cap t M c lam) (hrho : 0 ≤ rho)
    (hlow : rho < lam') (hsmall : lam' ≤ lam) :
    potential lam' (directionRows o e c) = M ∧
      ∀ i : Fin t, rowScore lam' (directionRow o e c i) = rowScore lam (directionRow o e c i) := by
  have hpos : 0 < lam' := hrho.trans_lt hlow
  have hleg : Section4Legality c lam' := by
    refine ⟨hpos, H.legality.inj, ?_⟩
    intro i j k hij hjk hik
    have h := H.legality.triAngle i j k hij hjk hik
    linarith
  have hrows := BandMaximumScorePlateau.actual_rowScore_le_of_scale_le
    H.card_ge_three o e c hpos hsmall
  have hpows : ∀ i ∈ (Finset.univ : Finset (Fin t)),
      2 ^ rowScore lam (directionRow o e c i) ≤
        2 ^ rowScore lam' (directionRow o e c i) :=
    fun i _ => Nat.pow_le_pow_right (by decide : 0 < 2) (hrows i)
  have hmono : potential lam (directionRows o e c) ≤ potential lam' (directionRows o e c) :=
    Finset.sum_le_sum hpows
  have hbound := H.maximal_same_card c lam' hlow (hsmall.trans H.scale_upper) hleg
  have hnew : potential lam' (directionRows o e c) = M := by
    have := H.potential_eq
    omega
  have hsum : (∑ i : Fin t, 2 ^ rowScore lam (directionRow o e c i)) =
      ∑ i : Fin t, 2 ^ rowScore lam' (directionRow o e c i) := H.potential_eq.trans hnew.symm
  have heq := (Finset.sum_eq_sum_iff_of_le hpows).mp hsum
  refine ⟨hnew, ?_⟩
  intro i
  exact (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) (heq i (Finset.mem_univ i))).symm

/-- The same actual points remain a critical fixed-cardinality maximizer
at every smaller positive scale still inside the original band. -/
theorem actual_fixed_card_model_of_smaller_scale {t cap M : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam lam' : ℝ} {c : Fin t → Plane₂}
    (H : FixedCardModel o e rho upper cap t M c lam) (hrho : 0 ≤ rho)
    (hlow : rho < lam') (hsmall : lam' ≤ lam) :
    FixedCardModel o e rho upper cap t M c lam' := by
  have hnew := (actual_fixed_card_score_plateau o e H hrho hlow hsmall).1
  have hleg : Section4Legality c lam' := by
    refine ⟨hrho.trans_lt hlow, H.legality.inj, ?_⟩
    intro i j k hij hjk hik
    have h := H.legality.triAngle i j k hij hjk hik
    linarith
  have hMover : cap < M := by have := H.over_cap; have := H.potential_eq; omega
  have H' : Model o e rho upper cap t c lam' :=
    ⟨H.card_ge_three, hlow, hsmall.trans H.scale_upper, hleg,
      hnew.symm ▸ hMover, H.minimum_card⟩
  exact ⟨H', hnew, H.maximal_same_card⟩

private theorem sum_map_le {α : Type*} (l : List α) (f g : α → ℕ)
    (hle : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (hle a (by simp)) (ih (fun x hx => hle x (by simp [hx])))

private theorem map_eq_of_sum_eq {α : Type*} (l : List α) (f g : α → ℕ)
    (hle : ∀ x ∈ l, f x ≤ g x) (heq : (l.map f).sum = (l.map g).sum) :
    ∀ x ∈ l, f x = g x := by
  induction l generalizing f g with
  | nil => simp
  | cons a l ih =>
    have hhead := hle a (by simp)
    have htail : ∀ x ∈ l, f x ≤ g x := fun x hx => hle x (by simp [hx])
    have ht := sum_map_le l f g htail
    simp only [List.map_cons, List.sum_cons] at heq
    have ha : f a = g a := by omega
    have heqt : (l.map f).sum = (l.map g).sum := by omega
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact ih f g htail heqt x hx

private theorem actual_gaps_nonneg {t : ℕ} (ht : 3 ≤ t)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin t → Plane₂)
    (i : Fin t) : ∀ g ∈ cycGaps (directionRow o e c i), 0 ≤ g := by
  apply cycGaps_nonneg (directionRow_sorted o e c i)
    (fun x hx => directionRow_mem_Ico o e c hx)
  intro hnil
  have hlen := directionRow_length o e c i
  rw [hnil] at hlen
  simp only [List.length_nil] at hlen
  omega

/-- Each actual gap score is also fixed throughout the lower band.
The raw floor can still move from zero to one. -/
theorem actual_fixed_card_gap_score_plateau {t cap M : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam lam' : ℝ} {c : Fin t → Plane₂}
    (H : FixedCardModel o e rho upper cap t M c lam) (hrho : 0 ≤ rho)
    (hlow : rho < lam') (hsmall : lam' ≤ lam) :
    ∀ i : Fin t, ∀ g ∈ cycGaps (directionRow o e c i),
      gapScore lam' g = gapScore lam g := by
  have hrow := (actual_fixed_card_score_plateau o e H hrho hlow hsmall).2
  intro i g hg
  exact (map_eq_of_sum_eq _ _ _
    (fun x hx => BandMaximumScorePlateau.gapScore_le_of_scale_le
      (hrho.trans_lt hlow) hsmall (actual_gaps_nonneg H.card_ge_three o e c i x hx))
    (hrow i).symm g hg).symm

/-- The actual critical model's gaps have a closed lower-boundary bound,
with the original weighted gap score retained. -/
theorem actual_fixed_card_gap_le_score_boundary {t cap M : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {c : Fin t → Plane₂}
    (H : FixedCardModel o e rho upper cap t M c lam) (hrho : 0 ≤ rho) :
    ∀ i : Fin t, ∀ g ∈ cycGaps (directionRow o e c i),
      g ≤ ((gapScore lam g + 2 : ℕ) : ℝ) * rho := by
  intro i g hg
  let B : ℝ := (gapScore lam g + 2 : ℕ)
  have hB : 0 < B := by dsimp [B]; positivity
  by_contra hnot
  have hgt : B * rho < g := by simpa [B] using lt_of_not_ge hnot
  have hmin : rho < min lam (g / B) := lt_min H.scale_lower
    ((lt_div_iff₀ hB).mpr (by nlinarith))
  let lam' := (rho + min lam (g / B)) / 2
  have hlo : rho < lam' := by dsimp [lam']; linarith
  have hlt : lam' < min lam (g / B) := by dsimp [lam']; linarith
  have hsmall : lam' ≤ lam := hlt.le.trans (min_le_left _ _)
  have hscore := actual_fixed_card_gap_score_plateau o e H hrho hlo hsmall i g hg
  have hpos : 0 < lam' := hrho.trans_lt hlo
  have hg0 := actual_gaps_nonneg H.card_ge_three o e c i g hg
  have hfloor : ⌊g / lam'⌋₊ ≤ gapScore lam g + 1 := by
    change ⌊g / lam'⌋₊ - 1 = gapScore lam g at hscore
    omega
  have hratio : g / lam' < ((gapScore lam g + 2 : ℕ) : ℝ) :=
    (Nat.floor_lt (div_nonneg hg0 hpos.le)).mp (by omega)
  have hupper := (div_lt_iff₀ hpos).mp hratio
  have hltg : lam' < g / B := hlt.trans_le (min_le_right _ _)
  have hlower : B * lam' < g := by
    simpa only [mul_comm] using (lt_div_iff₀ hB).mp hltg
  dsimp [B] at hlower
  nlinarith

/-- LOW band binding independently derives divisibility of the original
power cap from an actual minimum score. -/
theorem low_minimum_score_critical_form {s n : ℕ} (hs : 3 ≤ s) (hn2 : 2 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {lam : ℝ} {c : Fin (s + 1) → Plane₂}
    (H : Model o e (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ))
      (2 ^ n) (s + 1) c lam) (q : Fin (s + 1))
    (hmin : ∀ i : Fin (s + 1),
      rowScore lam (directionRow o e c q) ≤ rowScore lam (directionRow o e c i)) :
    potential lam (directionRows o e c) = 2 ^ n + 2 ^ rowScore lam (directionRow o e c q) ∧
      potential lam (directionRows o e (c ∘ q.succAbove)) = 2 ^ n ∧
      (∀ i : Fin (s + 1), i ≠ q →
        rowGain lam (directionRow o e c i) (deleteIndex o e c q i) = 0) := by
  obtain ⟨hfloor, _, _⟩ := ActualMinimumCardBandMaximizer.low_band_strip hn2
    H.legality.lam_pos H.scale_lower H.scale_upper
  have hcells := rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos q
    (by omega) hfloor
  have hscore := rowScore_eq_sub_defect lam H.legality.lam_pos n _ hcells
  have hk : rowScore lam (directionRow o e c q) ≤ n := by omega
  obtain ⟨hF, hdel, hg, _⟩ := actual_minimum_score_critical_form hs o e H q hmin (pow_dvd_pow 2 hk)
  exact ⟨hF, hdel, hg⟩

/-- The actual minimum-score point is chosen internally in the LOW model;
its divisibility is derived from the original band, not supplied as a goal. -/
theorem low_fixed_card_model_has_critical_minimum {s n M : ℕ}
    (hs : 3 ≤ s) (hn2 : 2 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {lam : ℝ} {c : Fin (s + 1) → Plane₂}
    (H : FixedCardModel o e (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ))
      (2 ^ n) (s + 1) M c lam) :
    ∃ q : Fin (s + 1),
      (∀ i : Fin (s + 1), rowScore lam (directionRow o e c q) ≤
        rowScore lam (directionRow o e c i)) ∧
      M = 2 ^ n + 2 ^ rowScore lam (directionRow o e c q) ∧
      potential lam (directionRows o e (c ∘ q.succAbove)) = 2 ^ n ∧
      (∀ i : Fin (s + 1), i ≠ q →
        rowGain lam (directionRow o e c i) (deleteIndex o e c q i) = 0) := by
  obtain ⟨q, hmin⟩ := Finite.exists_min (fun i : Fin (s + 1) =>
    rowScore lam (directionRow o e c i))
  obtain ⟨hF, hdel, hg⟩ := low_minimum_score_critical_form hs hn2 o e H.toModel q hmin
  rw [H.potential_eq] at hF
  exact ⟨q, hmin, hF, hdel, hg⟩

/-- The independently proved saturated LOW capacity excludes saturated
points from this internally selected actual counterexample. -/
theorem low_model_nonsaturated {t n : ℕ} (hn2 : 2 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} {c : Fin t → Plane₂}
    (H : Model o e (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ))
      (2 ^ n) t c lam) :
    ∀ i : Fin t, 2 ≤ rowDefect n lam (directionRow o e c i) := by
  obtain ⟨hfloor, hdelta, _⟩ := ActualMinimumCardBandMaximizer.low_band_strip hn2
    H.legality.lam_pos H.scale_lower H.scale_upper
  intro i
  have hcells := rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos i
    (by have := H.card_ge_three; omega) hfloor
  have hd1 := one_le_rowDefect lam H.legality.lam_pos n _ (by omega) hcells
  by_contra hnot
  have hsat : rowDefect n lam (directionRow o e c i) = 1 := by omega
  have hcap := potential_le_two_pow_of_saturated o e he
    (by have := H.card_ge_three; omega) hn2 H.legality.lam_pos hfloor H.legality i hsat hdelta
  have hover := H.over_cap
  omega

/-- A real LOW counter supplies an internally selected critical model,
with original minimum counter-cardinality and a same-cardinality maximum. -/
theorem exists_low_fixed_card_critical_model {s n : ℕ} (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (c : Fin s → Plane₂) {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hlow : Real.pi / lam - (n : ℝ) < 1 / 2)
    (hover : 2 ^ n < potential lam (directionRows o e c)) :
    ∃ t : ℕ, 3 ≤ t ∧ t + 1 ≤ 2 ^ n + 1 ∧
      ∃ M : ℕ, 2 ^ n < M ∧ M ≤ 2 ^ (n + 1) ∧
        ∃ scale : ℝ, ∃ d : Fin (t + 1) → Plane₂,
          FixedCardModel o e (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ))
            (2 ^ n) (t + 1) M d scale := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hden : 0 < (n : ℝ) + 1 / 2 := by linarith
  have habove : Real.pi / ((n : ℝ) + 1 / 2) < lam := by
    have hdiv : Real.pi / lam < (n : ℝ) + 1 / 2 := by linarith
    have hm := (div_lt_iff₀ hleg.lam_pos).mp hdiv
    exact (div_lt_iff₀ hden).mpr (by nlinarith)
  have hfloor := Nat.floor_le (div_nonneg Real.pi_pos.le hleg.lam_pos.le)
  rw [hn] at hfloor
  have hm := (le_div_iff₀ hleg.lam_pos).mp hfloor
  have hbelow : lam ≤ Real.pi / (n : ℝ) := (le_div_iff₀ hnpos).mpr (by nlinarith)
  have hclassical : Real.pi / ((n + 1 : ℕ) : ℝ) ≤ Real.pi / ((n : ℝ) + 1 / 2) := by
    push_cast
    apply (div_le_div_iff₀ (by linarith : 0 < (n : ℝ) + 1) hden).mpr
    nlinarith [Real.pi_pos]
  have h16 : 16 ≤ 2 ^ n := by
    have h := Nat.pow_le_pow_right (by decide : (0 : ℕ) < 2) hn4
    norm_num at h
    exact h
  obtain ⟨r, _, hrcap, scale, p, H⟩ :=
    exists_minimal_counter (by omega : 2 ≤ 2 ^ n) o e hs c hleg habove hbelow hover
  obtain ⟨M, hMover, hMbound, scale', d, H'⟩ :=
    exists_fixed_card_maximum (k := n + 1) (by omega) o e he hclassical H
  have hr4 : 4 ≤ r := by
    by_contra hnot
    have hr3 : r = 3 := by have := H'.card_ge_three; omega
    subst r
    obtain ⟨hfs, hdelta, hpi⟩ := ActualMinimumCardBandMaximizer.low_band_strip
      (by omega : 2 ≤ n) H'.legality.lam_pos H'.scale_lower H'.scale_upper
    have hcap := base3_potential_le (o := o) (e := e) H'.legality he hpi hfs (by omega) hdelta
    have hov := H'.over_cap
    omega
  cases r with
  | zero => omega
  | succ t => exact ⟨t, by omega, hrcap, M, hMover, hMbound, scale', d, H'⟩

#print axioms model_card_le_cap_succ
#print axioms exists_minimal_counter
#print axioms actual_delete_potential_le_cap
#print axioms not_actual_removable
#print axioms actual_minimum_score_critical_form
#print axioms exists_fixed_card_maximum
#print axioms fixed_card_critical_form
#print axioms actual_fixed_card_score_plateau
#print axioms actual_fixed_card_model_of_smaller_scale
#print axioms actual_fixed_card_gap_score_plateau
#print axioms actual_fixed_card_gap_le_score_boundary
#print axioms low_minimum_score_critical_form
#print axioms low_fixed_card_model_has_critical_minimum
#print axioms low_model_nonsaturated
#print axioms exists_low_fixed_card_critical_model

end Jsp404.ActualMinimalBandCounterexample
