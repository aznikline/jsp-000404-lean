import Jsp000404.ActualMaximumMassReduction
import Jsp000404.Induction
import Jsp000404.OneSaturatedLow
import Mathlib.Logic.Relation

/-!
# A minimum-cardinality actual realization of the band maximum

The model retains the original weighted row scores. It is not declared
flat. Its maximum is over actual configurations in the entire fixed
parameter band, and its minimum cardinality is among actual realizations
of that same maximum. Actual deletions leaving at least three points
strictly lower the potential. The existing certificate implications then
give an actual emission DAG and zero-gain extreme-score rows.

No bound `card <= n+1` or sharp capacity theorem is asserted.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualMinimumCardBandMaximizer

/-- The actual weighted extremal model. `minimum_card` ranges over the
same band and same potential value as `maximal`. -/
structure Model (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (rho upper : ℝ) (M t : ℕ) (c : Fin t → Plane₂) (lam : ℝ) : Prop where
  card_ge_three : 3 ≤ t
  scale_lower : rho < lam
  scale_upper : lam ≤ upper
  legality : Section4Legality c lam
  potential_eq : potential lam (directionRows o e c) = M
  maximal : ActualMaximumMassReduction.BandMaximal o e rho upper M
  minimum_card : ∀ {r : ℕ}, 3 ≤ r → ∀ (d : Fin r → Plane₂) (scale : ℝ),
    rho < scale → scale ≤ upper → Section4Legality d scale →
    potential scale (directionRows o e d) = M → t ≤ r

private def Realizes (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (rho upper : ℝ) (M t : ℕ) : Prop :=
  3 ≤ t ∧ ∃ scale : ℝ, rho < scale ∧ scale ≤ upper ∧
    ∃ c : Fin t → Plane₂, Section4Legality c scale ∧
      potential scale (directionRows o e c) = M

/-- An attained band maximum has an actual realization of least
cardinality. The upper bound by `M` is the actual card/potential bound. -/
theorem exists_minimum_card_model {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {M : ℕ} (hs : 3 ≤ s) (c : Fin s → Plane₂)
    (hleg : Section4Legality c lam) (hlow : rho < lam) (hupp : lam ≤ upper)
    (hpot : potential lam (directionRows o e c) = M)
    (hmax : ActualMaximumMassReduction.BandMaximal o e rho upper M) :
    ∃ t : ℕ, t ≤ s ∧ t ≤ M ∧ ∃ scale : ℝ, ∃ d : Fin t → Plane₂,
      Model o e rho upper M t d scale := by
  classical
  let P : ℕ → Prop := Realizes o e rho upper M
  have hex : ∃ t, P t := ⟨s, hs, lam, hlow, hupp, c, hleg, hpot⟩
  let t := Nat.find hex
  have hspec : P t := Nat.find_spec hex
  have hts : t ≤ s := Nat.find_min' hex ⟨hs, lam, hlow, hupp, c, hleg, hpot⟩
  obtain ⟨ht, scale, hlo, hup, d, hd, hdp⟩ := hspec
  have htM : t ≤ M :=
    (ActualPotentialInflation.card_le_potential scale (directionRows o e d)).trans_eq hdp
  refine ⟨t, hts, htM, scale, d, ht, hlo, hup, hd, hdp, hmax, ?_⟩
  intro r hr p param hl hu hp hF
  exact Nat.find_min' hex ⟨hr, param, hl, hu, p, hp, hF⟩

/-- A real deletion which leaves at least three points cannot still
attain `M`: that would be a smaller realization in the same band. -/
theorem actual_delete_potential_lt {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {M : ℕ} {c : Fin (s + 1) → Plane₂}
    (H : Model o e rho upper M (s + 1) c lam) (q : Fin (s + 1)) :
    potential lam (directionRows o e (c ∘ q.succAbove)) < M := by
  have hleg := H.legality.erase q
  have hle := H.maximal hs (c ∘ q.succAbove) lam H.scale_lower H.scale_upper hleg
  by_contra hnot
  have heq : potential lam (directionRows o e (c ∘ q.succAbove)) = M := by omega
  have hcard := H.minimum_card hs (c ∘ q.succAbove) lam
    H.scale_lower H.scale_upper hleg heq
  omega

/-- Every actual one-point deletion strictly lowers the potential of
this minimum-cardinality realization. -/
theorem not_actual_removable {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {M : ℕ} {c : Fin (s + 1) → Plane₂}
    (H : Model o e rho upper M (s + 1) c lam) (q : Fin (s + 1)) :
    ¬ Removable lam (fun v i => deleteIndex o e c v i) (directionRows o e c) q := by
  intro hrem
  have hle : potential lam (directionRows o e c) ≤
      potential lam (directionRows o e (c ∘ q.succAbove)) := by
    rw [potential_sub_config o e q lam]
    exact hrem
  have hlt := actual_delete_potential_lt hs o e H q
  rw [H.potential_eq] at hle
  omega

/-- The three sufficient certificates are all excluded by the real
strict deletion bound. This does not assume their geometric dichotomy. -/
theorem no_actual_certificates {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {M : ℕ} {c : Fin (s + 1) → Plane₂}
    (H : Model o e rho upper M (s + 1) c lam) (q : Fin (s + 1)) :
    ¬ CertA lam (fun v i => deleteIndex o e c v i) (directionRows o e c) q ∧
      ¬ CertB lam (fun v i => deleteIndex o e c v i) (directionRows o e c) q ∧
      ¬ CertC lam (fun v i => deleteIndex o e c v i) (directionRows o e c) q := by
  have hnot := not_actual_removable hs o e H q
  have hnotor : ¬ (CertA lam (fun v i => deleteIndex o e c v i) (directionRows o e c) q ∨
      CertB lam (fun v i => deleteIndex o e c v i) (directionRows o e c) q ∨
      CertC lam (fun v i => deleteIndex o e c v i) (directionRows o e c) q) := by
    intro hcert
    apply hnot
    exact removable_of_cert H.legality.lam_pos
      (fun i => directionRow_sorted o e c i)
      (fun i b hb => Set.mem_Ico.mp (directionRow_mem_Ico o e c hb))
      (fun i => by
        change 2 ≤ (directionRow o e c i).length
        rw [directionRow_length o e c i]
        omega)
      (fun i hi => deleteIndex_lt o e c hi) hcert
  exact ⟨fun h => hnotor (Or.inl h),
    fun h => hnotor (Or.inr (Or.inl h)), fun h => hnotor (Or.inr (Or.inr h))⟩

/-- The geometric dichotomy remains the missing input: it is impossible
in this actual extremizer by the proved certificate implications. -/
theorem no_actual_emission_dichotomy {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {M : ℕ} {c : Fin (s + 1) → Plane₂}
    (H : Model o e rho upper M (s + 1) c lam) :
    ¬ EmissionDichotomy lam (fun v i => deleteIndex o e c v i) (directionRows o e c) := by
  intro hd
  obtain ⟨q, hcert⟩ := certA_or_C_of_dichotomy hd
  rcases hcert with ha | hc
  · exact (no_actual_certificates hs o e H q).1 ha
  · exact (no_actual_certificates hs o e H q).2.2 hc

/-- Positive actual gain strictly climbs the original weighted score. -/
theorem actual_positive_gain_score_lt {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {M : ℕ} {c : Fin (s + 1) → Plane₂}
    (H : Model o e rho upper M (s + 1) c lam)
    {i v : Fin (s + 1)} (hi : i ≠ v)
    (hg : 1 ≤ rowGain lam (directionRow o e c i) (deleteIndex o e c v i)) :
    rowScore lam (directionRow o e c i) < rowScore lam (directionRow o e c v) :=
  partner_exponent_lt_of_not_certA (no_actual_certificates hs o e H v).1 hi hg

/-- A gain-two arc must climb at least two score levels. -/
theorem actual_gain_two_score_jump {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {M : ℕ} {c : Fin (s + 1) → Plane₂}
    (H : Model o e rho upper M (s + 1) c lam)
    {i v : Fin (s + 1)} (hi : i ≠ v)
    (hg : rowGain lam (directionRow o e c i) (deleteIndex o e c v i) = 2) :
    rowScore lam (directionRow o e c i) + 1 < rowScore lam (directionRow o e c v) :=
  partner_exponent_add_one_lt_of_not_certB (no_actual_certificates hs o e H v).2.1 hi hg

/-- Two positive actual incoming arcs cannot both be within one score
level of the receiver. -/
theorem actual_no_two_close_incoming {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {M : ℕ} {c : Fin (s + 1) → Plane₂}
    (H : Model o e rho upper M (s + 1) c lam)
    {i j v : Fin (s + 1)} (hi : i ≠ v) (hj : j ≠ v) (hij : i ≠ j)
    (hgi : 1 ≤ rowGain lam (directionRow o e c i) (deleteIndex o e c v i))
    (hgj : 1 ≤ rowGain lam (directionRow o e c j) (deleteIndex o e c v j)) :
    rowScore lam (directionRow o e c i) + 1 < rowScore lam (directionRow o e c v) ∨
      rowScore lam (directionRow o e c j) + 1 < rowScore lam (directionRow o e c v) :=
  not_two_near_partners_of_not_certC (no_actual_certificates hs o e H v).2.2
    hi hj hij hgi hgj

/-- Minimum-score points have no actual incoming gain. -/
theorem actual_min_score_zero_incoming {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {M : ℕ} {c : Fin (s + 1) → Plane₂}
    (H : Model o e rho upper M (s + 1) c lam) {v : Fin (s + 1)}
    (hmin : ∀ i, rowScore lam (directionRow o e c v) ≤ rowScore lam (directionRow o e c i))
    {i : Fin (s + 1)} (hi : i ≠ v) :
    rowGain lam (directionRow o e c i) (deleteIndex o e c v i) = 0 :=
  no_gain_into_min_exponent (fun q => (no_actual_certificates hs o e H q).1) hmin hi

/-- Maximum-score points have no actual outgoing gain. -/
theorem actual_max_score_zero_outgoing {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {M : ℕ} {c : Fin (s + 1) → Plane₂}
    (H : Model o e rho upper M (s + 1) c lam) {i : Fin (s + 1)}
    (hmax : ∀ v, rowScore lam (directionRow o e c v) ≤ rowScore lam (directionRow o e c i))
    {v : Fin (s + 1)} (hi : i ≠ v) :
    rowGain lam (directionRow o e c i) (deleteIndex o e c v i) = 0 :=
  no_gain_from_max_exponent (fun q => (no_actual_certificates hs o e H q).1) hmax hi

/-- Actual positive-gain arcs, with their real deleted indices. -/
def EmissionArc {t : ℕ} (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin t → Plane₂) (lam : ℝ) (i v : Fin t) : Prop :=
  i ≠ v ∧ 1 ≤ rowGain lam (directionRow o e c i) (deleteIndex o e c v i)

/-- The genuine weighted emission graph has no directed cycle. -/
theorem actual_emission_acyclic {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {M : ℕ} {c : Fin (s + 1) → Plane₂}
    (H : Model o e rho upper M (s + 1) c lam) :
    ∀ i : Fin (s + 1), ¬ Relation.TransGen (EmissionArc o e c lam) i i := by
  have hpath : ∀ {i v : Fin (s + 1)}, Relation.TransGen (EmissionArc o e c lam) i v →
      rowScore lam (directionRow o e c i) < rowScore lam (directionRow o e c v) := by
    intro i v hp
    induction hp with
    | single h => exact actual_positive_gain_score_lt hs o e H h.1 h.2
    | tail _ h ih => exact ih.trans (actual_positive_gain_score_lt hs o e H h.1 h.2)
  intro i hcycle
  exact (Nat.lt_irrefl _) (hpath hcycle)

/-- The original LOW parameter band has the caller's actual floor and
delta, and lies below pi. -/
theorem low_band_strip {n : ℕ} (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hlo : Real.pi / ((n : ℝ) + 1 / 2) < lam)
    (hup : lam ≤ Real.pi / (n : ℝ)) :
    Nat.floor (Real.pi / lam) = n ∧
      Real.pi / lam - (n : ℝ) < 1 / 2 ∧ lam < Real.pi := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hden : 0 < (n : ℝ) + 1 / 2 := by linarith
  have hm := (le_div_iff₀ hnpos).mp hup
  have hnle : (n : ℝ) ≤ Real.pi / lam :=
    (le_div_iff₀ hlam).mpr (by nlinarith)
  have hmlow := (div_lt_iff₀ hden).mp hlo
  have hnlt : Real.pi / lam < (n : ℝ) + 1 / 2 :=
    (div_lt_iff₀ hlam).mpr (by nlinarith)
  refine ⟨(Nat.floor_eq_iff (div_nonneg Real.pi_pos.le hlam.le)).mpr
    ⟨hnle, by linarith⟩, by linarith, ?_⟩
  nlinarith [Real.pi_pos]

/-- The independently proved saturated LOW case excludes saturation
from an actual band maximizer above the original sharp cap. -/
theorem low_counter_model_nonsaturated {t n : ℕ} (hn2 : 2 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} {M : ℕ} {c : Fin t → Plane₂}
    (H : Model o e (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ)) M t c lam)
    (hover : 2 ^ n < M) :
    ∀ i : Fin t, 2 ≤ rowDefect n lam (directionRow o e c i) := by
  obtain ⟨hfloor, hdelta, _⟩ := low_band_strip hn2 H.legality.lam_pos
    H.scale_lower H.scale_upper
  intro i
  have hcells := rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos i
    (by have := H.card_ge_three; omega) hfloor
  have hd1 := one_le_rowDefect lam H.legality.lam_pos n _ (by omega) hcells
  by_contra hnot
  have hsat : rowDefect n lam (directionRow o e c i) = 1 := by omega
  have hcap := potential_le_two_pow_of_saturated o e he
    (by have := H.card_ge_three; omega) hn2 H.legality.lam_pos hfloor H.legality i hsat hdelta
  rw [H.potential_eq] at hcap
  omega

/-- A genuine original LOW counterexample gives a minimum-cardinality
weighted band maximizer with at least four points. It need not be flat. -/
theorem exists_low_counter_minimum_card_model {s n : ℕ} (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (c : Fin s → Plane₂) {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hlow : Real.pi / lam - (n : ℝ) < 1 / 2)
    (hover : 2 ^ n < potential lam (directionRows o e c)) :
    ∃ M : ℕ, 2 ^ n < M ∧ M ≤ 2 ^ (n + 1) ∧
      ∃ t : ℕ, 3 ≤ t ∧ t + 1 ≤ M ∧ ∃ scale : ℝ, ∃ d : Fin (t + 1) → Plane₂,
        Model o e (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ)) M (t + 1) d scale := by
  obtain ⟨M, hMover, hMbound, hmax, scale, hlo, hup, d, hd, _hflat, hdp⟩ :=
    ActualMaximumMassReduction.exists_flat_low_band_counter_maximizer
      hn4 o e he hs c hleg hn hlow hover
  have h16 : 16 ≤ 2 ^ n := by
    have h := Nat.pow_le_pow_right (by decide : (0 : ℕ) < 2) hn4
    norm_num at h
    exact h
  have hM3 : 3 ≤ M := by omega
  obtain ⟨r, _, hrM, scale', p, H⟩ :=
    exists_minimum_card_model o e hM3 d hd hlo hup hdp hmax
  have hr4 : 4 ≤ r := by
    by_contra hnot
    have hr3 : r = 3 := by have := H.card_ge_three; omega
    subst r
    obtain ⟨hfloor, hdelta, hpi⟩ := low_band_strip (by omega : 2 ≤ n)
      H.legality.lam_pos H.scale_lower H.scale_upper
    have hcap := base3_potential_le (o := o) (e := e)
      H.legality he hpi hfloor (by omega : 2 ≤ n) hdelta
    rw [H.potential_eq] at hcap
    omega
  cases r with
  | zero => omega
  | succ t => exact ⟨M, hMover, hMbound, t, by omega, hrM, scale', p, H⟩

/-- The weighted minimum-cardinality extremizer can be made strictly
legal at a smaller parameter, with every original row score preserved. -/
theorem exists_strict_smaller_scale_model {t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {M : ℕ} {c : Fin t → Plane₂}
    (H : Model o e rho upper M t c lam) (hrho : 0 ≤ rho) :
    ∃ lam' : ℝ, rho < lam' ∧ lam' < lam ∧ Model o e rho upper M t c lam' ∧
      (∀ i : Fin t, rowScore lam' (directionRow o e c i) = rowScore lam (directionRow o e c i)) ∧
      (∀ i : Fin t, ∀ g ∈ cycGaps (directionRow o e c i),
        ⌊g / lam'⌋₊ = ⌊g / lam⌋₊ ∧
          g < ((⌊g / lam⌋₊ : ℝ) + 1) * lam' ∧
          (0 < ⌊g / lam⌋₊ → (⌊g / lam⌋₊ : ℝ) * lam' < g)) ∧
      (∀ i j k : Fin t, i ≠ j → j ≠ k → i ≠ k →
        ∠ (c i) (c j) (c k) < Real.pi - lam') := by
  classical
  let tau := (rho + lam) / 2
  have htau : rho < tau := by dsimp [tau]; linarith [H.scale_lower]
  have htau0 : 0 < tau := hrho.trans_lt htau
  have htaulam : tau < lam := by dsimp [tau]; linarith [H.scale_lower]
  let gs := (List.ofFn fun i : Fin t => cycGaps (directionRow o e c i)).flatten
  have hgs : ∀ g ∈ gs, 0 ≤ g := by
    intro g hg
    obtain ⟨l, hl, hgl⟩ := List.mem_flatten.mp hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact cycGaps_nonneg (directionRow_sorted o e c i)
      (fun x hx => directionRow_mem_Ico o e c hx)
      (by
        intro hnil
        have hlen := directionRow_length o e c i
        rw [hnil] at hlen
        simp only [List.length_nil] at hlen
        have ht := H.card_ge_three
        omega) g hgl
  obtain ⟨lam', hlow, hsmall, hmargin⟩ :=
    GapSplitFloorStability.exists_floor_stable_scale_with_margins gs H.legality.lam_pos
      hgs htau0 htaulam
  have hrowmargin : ∀ i : Fin t, ∀ g ∈ cycGaps (directionRow o e c i),
      ⌊g / lam'⌋₊ = ⌊g / lam⌋₊ ∧
        g < ((⌊g / lam⌋₊ : ℝ) + 1) * lam' ∧
        (0 < ⌊g / lam⌋₊ → (⌊g / lam⌋₊ : ℝ) * lam' < g) := by
    intro i g hg
    exact hmargin g (List.mem_flatten.mpr
      ⟨cycGaps (directionRow o e c i), List.mem_ofFn.mpr ⟨i, rfl⟩, hg⟩)
  have hrows : ∀ i : Fin t,
      rowScore lam' (directionRow o e c i) = rowScore lam (directionRow o e c i) := by
    intro i
    unfold rowScore
    apply congrArg List.sum
    apply List.map_congr_left
    intro g hg
    unfold gapScore
    rw [(hrowmargin i g hg).1]
  have hnewpot : potential lam' (directionRows o e c) = M := by
    calc
      potential lam' (directionRows o e c) = potential lam (directionRows o e c) := by
        unfold potential exponentAt directionRows
        simp_rw [hrows]
      _ = M := H.potential_eq
  have hnewleg := ActualPotentialInflation.Section4Legality_weaken H.legality
    (htau0.trans hlow) hsmall
  have H' : Model o e rho upper M t c lam' :=
    ⟨H.card_ge_three, htau.trans hlow, hsmall.le.trans H.scale_upper,
      hnewleg, hnewpot, H.maximal, H.minimum_card⟩
  refine ⟨lam', htau.trans hlow, hsmall, H', hrows, hrowmargin, ?_⟩
  intro i j k hij hjk hik
  have h := H.legality.triAngle i j k hij hjk hik
  linarith

#print axioms exists_minimum_card_model
#print axioms actual_delete_potential_lt
#print axioms not_actual_removable
#print axioms no_actual_certificates
#print axioms no_actual_emission_dichotomy
#print axioms actual_positive_gain_score_lt
#print axioms actual_gain_two_score_jump
#print axioms actual_no_two_close_incoming
#print axioms actual_min_score_zero_incoming
#print axioms actual_max_score_zero_outgoing
#print axioms actual_emission_acyclic
#print axioms low_band_strip
#print axioms low_counter_model_nonsaturated
#print axioms exists_low_counter_minimum_card_model
#print axioms exists_strict_smaller_scale_model

end Jsp404.ActualMinimumCardBandMaximizer
