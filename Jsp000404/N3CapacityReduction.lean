import Jsp000404.N3SaturatedBounds
import Jsp000404.N3NoSaturatedBound

/-!
The remaining third-strip capacity problem is reduced to eleven finite,
actual point-geometric exclusions. The exclusions below are explicit
hypotheses, not axioms or proved geometric facts. Saturated configurations
are handled by the proved `N3SaturatedBounds` theorem.
-/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404.N3CapacityReduction

/-- Strong actual minimal-counterexample data. Every deletion is performed
on the actual point configuration through `q.succAbove`. -/
structure MinimalNoSaturated
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (lam : ℝ)
    (cap s : ℕ) (c : Fin (s+1) → Plane₂) : Prop where
  legality : Section4Legality c lam
  strip : Nat.floor (Real.pi / lam) = 3
  nonsaturated : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i)
  exact_potential : potential lam (directionRows o e c) = cap+1
  deletion_cap : ∀ q : Fin (s+1),
    potential lam (directionRows o e (c ∘ q.succAbove)) ≤ cap
  zero_deletion_scores : ∀ q : Fin (s+1),
    rowScore lam (directionRow o e c q) = 0 → ∀ i : Fin s,
      rowScore lam (directionRow o e (c ∘ q.succAbove) i) =
        rowScore lam (directionRow o e c (q.succAbove i))

/-- The five explicitly open LOW exclusions: (center count, positive count)
= (5,4), (6,3), (7,2), (8,1), or (9,0). -/
def LowFiniteExclusion
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (lam : ℝ) : Prop :=
  ∀ (s : ℕ), 5 ≤ s+1 → s+1 ≤ 9 → ∀ c : Fin (s+1) → Plane₂,
    MinimalNoSaturated o e lam 8 s c →
    (Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))).card ≤ 4 →
    s+1+(Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))).card = 9 →
    False

/-- The six explicitly open HIGH exclusions: (6,5), (7,4), (8,3),
(9,2), (10,1), or (11,0). -/
def HighFiniteExclusion
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (lam : ℝ) : Prop :=
  ∀ (s : ℕ), 6 ≤ s+1 → s+1 ≤ 11 → ∀ c : Fin (s+1) → Plane₂,
    MinimalNoSaturated o e lam 10 s c →
    (Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))).card ≤ 5 →
    s+1+(Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))).card = 11 →
    False

/-- Any actual third-strip counterexample supplies an actual smaller or
equal no-saturation counterexample, with every actual one-point deletion
below the cap. This uses the proved saturation capacity to remove the
saturated case from the ordinary least-cardinality counterexample. -/
theorem exists_minimal_nonsaturated_counterexample {s0 : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs0 : 3 ≤ s0) {c0 : Fin s0 → Plane₂} {lam : ℝ}
    (hleg0 : Section4Legality c0 lam) (hn : Nat.floor (Real.pi / lam) = 3)
    (big : Bool) (hbig : big = false → Real.pi / lam - 3 < 1/2)
    (cap : ℕ) (hcap : sendovCap 3 big = cap)
    (hover0 : cap < potential lam (directionRows o e c0)) :
    ∃ s : ℕ, 4 ≤ s ∧ s+1 ≤ s0 ∧ ∃ c : Fin (s+1) → Plane₂,
      Section4Legality c lam ∧
      (∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i)) ∧
      cap < potential lam (directionRows o e c) ∧
      ∀ q : Fin (s+1),
        potential lam (directionRows o e (c ∘ q.succAbove)) ≤ cap := by
  obtain ⟨m, hm3, hm0, c, hleg, hover, hminimal⟩ :=
    ThirdStripNormalForm.exists_minimal_counterexample o e cap hs0 hleg0 hover0
  have hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i) := by
    intro i
    have hc := rowCells_directionRow_le_of_floor_eq o e c hleg.lam_pos i (by omega) hn
    have h1 := one_le_rowDefect lam hleg.lam_pos 3 _ (by omega) hc
    by_contra hh
    have hsat : rowDefect 3 lam (directionRow o e c i) = 1 := by omega
    have hb := N3SaturatedBounds.saturated_strip_capacity o e he hm3 hleg.lam_pos hn
      hleg i hsat big hbig
    rw [hcap] at hb
    omega
  have h8 : 8 ≤ cap := by
    cases big <;> norm_num [sendovCap] at hcap <;> omega
  have hw := ThirdStripNormalForm.potential_le_two_card o e
    (ThirdStripNormalForm.nonsaturated_score_le_one o e (by omega) hleg.lam_pos hn hns)
  have hm5 : 5 ≤ m := by omega
  cases m with
  | zero => omega
  | succ s =>
    refine ⟨s, by omega, hm0, c, hleg, hns, hover, ?_⟩
    intro q
    exact hminimal s (by omega) (by omega) (c ∘ q.succAbove)
      (hleg.restrict_injective q.succAbove Fin.succAbove_right_injective)

/-- LOW capacity at any cardinality, conditional exactly on the five
finite actual exclusions above. -/
theorem low_capacity_of_finite_exclusion {s0 : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs0 : 3 ≤ s0) {c0 : Fin s0 → Plane₂} {lam : ℝ}
    (hleg0 : Section4Legality c0 lam) (hn : Nat.floor (Real.pi / lam) = 3)
    (hlow : 2*Real.pi/7 < lam) (hexcl : LowFiniteExclusion o e lam) :
    potential lam (directionRows o e c0) ≤ 8 := by
  have hdelta : Real.pi / lam - 3 < 1/2 := by
    have hmul : Real.pi < (7/2)*lam := by linarith
    have hd := (div_lt_iff₀ hleg0.lam_pos).mpr hmul
    linarith
  by_contra hb
  have hover0 : 8 < potential lam (directionRows o e c0) := by omega
  obtain ⟨s, hs4, hs0', c, hleg, hns, hover, hdel⟩ :=
    exists_minimal_nonsaturated_counterexample o e he hs0 hleg0 hn false
      (fun _ => hdelta) 8 (by norm_num [sendovCap]) hover0
  obtain ⟨hF, hs5, hs9, hr4, hsum⟩ :=
    N3NoSaturatedBound.low_minimal_counter_profile o e he (by omega) hleg hn hlow hns hover hdel
  have hM : MinimalNoSaturated o e lam 8 s c :=
    ⟨hleg, hn, hns, hF, hdel, fun q hq =>
      (ThirdStripNormalForm.zero_victim_normal_form o e (by omega) hleg.lam_pos
        8 q hover hq (hdel q)).2.2⟩
  exact hexcl s hs5 hs9 c hM hr4 hsum

/-- HIGH capacity at any cardinality, conditional exactly on the six
finite actual exclusions above. -/
theorem high_capacity_of_finite_exclusion {s0 : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs0 : 3 ≤ s0) {c0 : Fin s0 → Plane₂} {lam : ℝ}
    (hleg0 : Section4Legality c0 lam) (hn : Nat.floor (Real.pi / lam) = 3)
    (hquarter : Real.pi/4 < lam) (hexcl : HighFiniteExclusion o e lam) :
    potential lam (directionRows o e c0) ≤ 10 := by
  by_contra hb
  have hover0 : 10 < potential lam (directionRows o e c0) := by omega
  obtain ⟨s, hs4, hs0', c, hleg, hns, hover, hdel⟩ :=
    exists_minimal_nonsaturated_counterexample o e he hs0 hleg0 hn true
      (by simp) 10 (by norm_num [sendovCap]) hover0
  obtain ⟨hF, hs6, hs11, hr5, hsum⟩ :=
    N3NoSaturatedBound.high_minimal_counter_profile o e he (by omega) hleg hn
      hquarter hns hover hdel
  have hM : MinimalNoSaturated o e lam 10 s c :=
    ⟨hleg, hn, hns, hF, hdel, fun q hq =>
      (ThirdStripNormalForm.zero_victim_normal_form o e (by omega) hleg.lam_pos
        10 q hover hq (hdel q)).2.2⟩
  exact hexcl s hs6 hs11 c hM hr5 hsum

/-- The original third-strip cap, with the eleven explicit exclusions
still present as hypotheses. No bounded-angle model or certificate axiom
is used in this consumer. -/
theorem strip_capacity_of_finite_exclusions {s0 : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs0 : 3 ≤ s0) {c0 : Fin s0 → Plane₂} {lam : ℝ}
    (hleg0 : Section4Legality c0 lam) (hn : Nat.floor (Real.pi / lam) = 3)
    (big : Bool) (hbig : big = false → Real.pi / lam - 3 < 1/2)
    (hlowExcl : LowFiniteExclusion o e lam)
    (hhighExcl : HighFiniteExclusion o e lam) :
    potential lam (directionRows o e c0) ≤ sendovCap 3 big := by
  cases big with
  | false =>
    have hd := hbig rfl
    have hdiv : Real.pi / lam < 7/2 := by linarith
    have hm := (div_lt_iff₀ hleg0.lam_pos).mp hdiv
    have hl : 2*Real.pi/7 < lam := by linarith
    simpa [sendovCap] using
      low_capacity_of_finite_exclusion o e he hs0 hleg0 hn hl hlowExcl
  | true =>
    have hf := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn] at hf
    have hdiv : Real.pi / lam < 4 := by norm_num at hf; exact hf
    have hm := (div_lt_iff₀ hleg0.lam_pos).mp hdiv
    have hq : Real.pi/4 < lam := by linarith
    simpa [sendovCap] using
      high_capacity_of_finite_exclusion o e he hs0 hleg0 hn hq hhighExcl

#print axioms exists_minimal_nonsaturated_counterexample
#print axioms low_capacity_of_finite_exclusion
#print axioms high_capacity_of_finite_exclusion
#print axioms strip_capacity_of_finite_exclusions
end Jsp404.N3CapacityReduction
