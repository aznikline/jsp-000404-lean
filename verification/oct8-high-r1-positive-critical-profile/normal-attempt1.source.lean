import Jsp000404.ActualHighR1HeavyEndpoint
import Jsp000404.ActualMinimalBandCounterexample
import Jsp000404.ActualN4R2Capacity

set_option autoImplicit false

/-!
SOURCE_ONLY: an original minimal HIGH4 cap20 counter-model with a SAT,
a score-two point and all original scores positive has potential22 and
seven original points. The exact original profile, cardinality and SAT
fan endpoint are internal outputs. Positivity is an explicit hypothesis;
this does not reduce arbitrary R1 models to the positive branch or prove
R1 capacity.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualHighR1PositiveCriticalProfile

private theorem high_four_strip {lam : ℝ} (hlam : 0 < lam)
    (hlo : Real.pi/5 < lam) (hup : lam ≤ Real.pi/((4 : ℝ)+1/2)) :
    Nat.floor (Real.pi/lam) = 4 ∧ (1/2 : ℝ) ≤ Real.pi/lam-4 := by
  have hleft := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 5)).mp hlo
  have hright := (le_div_iff₀ (by norm_num : (0 : ℝ) < 4+1/2)).mp hup
  have hratioLo : (4 : ℝ)+1/2 ≤ Real.pi/lam :=
    (le_div_iff₀ hlam).mpr (by nlinarith only [hright])
  have hratioHi : Real.pi/lam < 5 :=
    (div_lt_iff₀ hlam).mpr (by nlinarith only [hleft])
  refine ⟨(Nat.floor_eq_iff (div_nonneg Real.pi_pos.le hlam.le)).mpr
    ⟨by linarith only [hratioLo], by linarith only [hratioHi]⟩, ?_⟩
  linarith only [hratioLo]

/-- All fields refer to the full original configuration. -/
structure Profile {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin (s+1) → Plane₂) (lam : ℝ) (v a : Fin (s+1)) : Prop where
  floor_four : Nat.floor (Real.pi/lam) = 4
  high : (1/2 : ℝ) ≤ Real.pi/lam-4
  distinct : v ≠ a
  saturated_score : rowScore lam (directionRow o e c v) = 3
  tail_score_one : ∀ q : Fin (s+1), q ≠ v → q ≠ a →
    rowScore lam (directionRow o e c q) = 1
  potential_eq : potential lam (directionRows o e c) = 22
  card_eq : s = 6

/-- Count the actual positive R1 branch. No caller potential, cardinality,
minimum-score index, gain bound or tail-profile array is required. The
already checked R2 capacity excludes another score-two point internally. -/
theorem actual_high_r1_positive_critical_profile {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/5) (Real.pi/((4 : ℝ)+1/2)) 20 (s+1) c lam)
    (v : Fin (s+1)) (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (a : Fin (s+1)) (ha : rowScore lam (directionRow o e c a) = 2)
    (hpositive : ∀ q : Fin (s+1), 1 ≤ rowScore lam (directionRow o e c q)) :
    Profile o e c lam v a := by
  classical
  obtain ⟨hn,hhigh⟩ := high_four_strip H.legality.lam_pos H.scale_lower H.scale_upper
  have hcells (q : Fin (s+1)) : rowCells lam (directionRow o e c q) ≤ 4 :=
    rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos q
      (by have := H.card_ge_three; omega) hn
  have hscore (q : Fin (s+1)) :=
    rowScore_eq_sub_defect lam H.legality.lam_pos 4 _ (hcells q)
  have hv : rowScore lam (directionRow o e c v) = 3 := by
    have h := hscore v
    rw [hsat] at h
    exact h
  have hva : v ≠ a := by
    intro h
    have hsame := congrArg (fun q => rowScore lam (directionRow o e c q)) h
    omega
  have hda : rowDefect 4 lam (directionRow o e c a) = 2 := by
    have h := hscore a
    omega
  have htail (q : Fin (s+1)) (hqv : q ≠ v) (hqa : q ≠ a) :
      rowScore lam (directionRow o e c q) = 1 := by
    have hdef := one_le_rowDefect lam H.legality.lam_pos 4
      (directionRow o e c q) (by decide : 1 ≤ 4) (hcells q)
    have hqscore := hscore q
    have hnot1 : rowDefect 4 lam (directionRow o e c q) ≠ 1 := by
      intro hq
      have hcap := potential_le_high_of_two_saturated o e he H.card_ge_three
        (by decide : 2 ≤ 4) H.legality.lam_pos hn H.legality hqv.symm hsat hq
      norm_num at hcap
      have hover := H.over_cap
      omega
    have hnot2 : rowDefect 4 lam (directionRow o e c q) ≠ 2 := by
      intro hq
      have hcap := ActualN4R2Capacity.actual_r2_capacity o e he hn hhigh
        H.legality v hsat hva.symm hqv hqa.symm hda hq
      have hover := H.over_cap
      omega
    have hp := hpositive q
    omega
  have hweight (q : Fin (s+1)) : 2 ^ rowScore lam (directionRow o e c q) =
      (2 + if q = v then 6 else 0) + if q = a then 2 else 0 := by
    by_cases hqv : q = v
    · subst q
      simp [hv,hva]
    · by_cases hqa : q = a
      · subst q
        simp [ha,hva.symm]
      · simp [htail q hqv hqa,hqv,hqa]
  have hmass : potential lam (directionRows o e c) = 2*(s+1)+8 := by
    unfold potential exponentAt directionRows
    simp_rw [hweight]
    simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    omega
  have hs7 : 7 ≤ s+1 := by
    have hover := H.over_cap
    omega
  obtain ⟨p,hpv,hpa⟩ := Fin.exists_ne_and_ne_of_two_lt v a (by omega : 2 < s+1)
  have hp : rowScore lam (directionRow o e c p) = 1 := htail p hpv hpa
  have hdelete := ActualMinimalBandCounterexample.actual_delete_potential_le_cap
    (by omega : 3 ≤ s) o e H p
  have hledger := ActualMinimumDeletionNormalForm.actual_delete_potential_eq_sum_pow_gain
    (by omega : 2 ≤ s) o e (c := c) H.legality.lam_pos p
  have hretained : (∑ q ∈ (Finset.univ : Finset (Fin (s+1))).erase p,
      2 ^ rowScore lam (directionRow o e c q)) ≤
      potential lam (directionRows o e (c ∘ p.succAbove)) := by
    rw [hledger]
    apply Finset.sum_le_sum
    intro q _hq
    exact le_mul_of_one_le_right (Nat.zero_le _) (Nat.one_le_two_pow :
      1 ≤ 2 ^ rowGain lam (directionRow o e c q) (deleteIndex o e c p q))
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin (s+1)))
    (fun q => 2 ^ rowScore lam (directionRow o e c q)) (Finset.mem_univ p)
  have hsum : 2 + (∑ q ∈ (Finset.univ : Finset (Fin (s+1))).erase p,
      2 ^ rowScore lam (directionRow o e c q)) = potential lam (directionRows o e c) := by
    simpa only [hp,pow_one,potential,exponentAt,directionRows] using hsplit
  have hF22 : potential lam (directionRows o e c) = 22 := by omega
  have hs6 : s = 6 := by omega
  exact ⟨hn,hhigh,hva,hv,htail,hF22,hs6⟩

/-- Original-index endpoint data; no reindexed configuration is returned. -/
structure EndpointData {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin (s+1) → Plane₂) (lam : ℝ) (v a : Fin (s+1)) where
  profile : Profile o e c lam v a
  reference : Plane₂
  theta : Fin s → ℝ
  chart : SatChart o reference 4 lam c v theta
  heavy_rank : Fin s
  heavy_index : v.succAbove (SatScalarExtraction.sigma chart heavy_rank) = a
  boundary : (∀ j : Fin s, heavy_rank ≤ j) ∨ (∀ j : Fin s, j ≤ heavy_rank)

/-- Internally derive potential22 and seven original points, then use the
checked actual seven-point endpoint producer. The chart and indices still
refer to the original configuration. Positivity remains explicit. -/
theorem exists_actual_high_r1_positive_critical_endpoint {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/5) (Real.pi/((4 : ℝ)+1/2)) 20 (s+1) c lam)
    (v : Fin (s+1)) (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (a : Fin (s+1)) (ha : rowScore lam (directionRow o e c a) = 2)
    (hpositive : ∀ q : Fin (s+1), 1 ≤ rowScore lam (directionRow o e c q)) :
    Nonempty (EndpointData o e c lam v a) := by
  have P := actual_high_r1_positive_critical_profile o e he H v hsat a ha hpositive
  have hs : s = 6 := P.card_eq
  subst s
  obtain ⟨D⟩ := ActualHighR1HeavyEndpoint.exists_actual_high_r1_heavy_endpoint
    o e he H.legality P.floor_four P.high v a P.distinct hsat ha P.tail_score_one
  rcases D.heavy_boundary with hlo | hhi
  · refine ⟨⟨P,D.reference,D.theta,D.chart,0,hlo,Or.inl ?_⟩⟩
    intro j
    exact Fin.zero_le j
  · refine ⟨⟨P,D.reference,D.theta,D.chart,5,hhi,Or.inr ?_⟩⟩
    intro j
    apply Fin.le_iff_val_le_val.mpr
    have hj := j.isLt
    norm_num
    omega

#print axioms actual_high_r1_positive_critical_profile
#print axioms exists_actual_high_r1_positive_critical_endpoint

end Jsp404.ActualHighR1PositiveCriticalProfile
