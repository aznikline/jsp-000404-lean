import Jsp000404.ActualHighR1PositiveCriticalProfile
import Jsp000404.SatScalarModelReflection

set_option autoImplicit false

/-!
SOURCE_ONLY conditional actual wiring for the seven-row lower terminal.
The terminal premise is explicit until its independent kernel producer is
verified. All actual charts, sorted indices, original score transfers and
finite cardinalities are internally produced. This file alone is not an
unconditional positive-R1 exclusion or R1 capacity theorem.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualHighR1SevenLowerAdapter

/-- Exact weak necessary scalar terminal: row4 is deliberately free.
Only GenericModel's own delta<1 is used; no HIGH premise is added here. -/
def SevenLowerTerminal : Prop :=
  ∀ M : SatScalarModel.GenericModel 6 4,
    SatScalarModel.rowDefect M 0 ≤ 2 →
    SatScalarModel.rowDefect M 1 ≤ 3 →
    SatScalarModel.rowDefect M 2 ≤ 3 →
    SatScalarModel.rowDefect M 3 ≤ 3 →
    SatScalarModel.rowDefect M 5 ≤ 3 → False

/-- Conditional actual seven-point profile exclusion. A verified scalar
provider can later fill the single explicit terminal premise. No caller
chart, order, word, potential, deletion gain or model is accepted. -/
theorem actual_seven_positive_r1_false_of_terminal
    (hterminal : SevenLowerTerminal)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 7 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi/lam) = 4)
    (hhigh : (1/2 : ℝ) ≤ Real.pi/lam-4)
    (v a : Fin 7) (hva : v ≠ a)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (ha : rowScore lam (directionRow o e c a) = 2)
    (htail : ∀ q : Fin 7, q ≠ v → q ≠ a →
      rowScore lam (directionRow o e c q) = 1) : False := by
  obtain ⟨D⟩ := ActualHighR1HeavyEndpoint.exists_actual_high_r1_heavy_endpoint
    o e he hleg hn hhigh v a hva hsat ha htail
  let M := SatScalarExtraction.model D.chart
  have href (q : Fin 7) : rowScore lam (directionRow o e c q) =
      rowScore lam (directionRow o D.reference c q) :=
    rowScore_directionRow_reference_eq o e D.reference he D.chart.he c hleg.inj q lam
  have hmodel (i : Fin 6) : SatScalarModel.rowDefect M i =
      rowDefect 4 lam (directionRow o D.reference c
        (v.succAbove (SatScalarExtraction.sigma D.chart i))) := by
    simpa only [M] using SatScalarExtraction.model_rowDefect D.chart (by decide : 2 ≤ 6) i
  have hbound (i : Fin 6) : SatScalarModel.rowDefect M i ≤ 3 := by
    let q := v.succAbove (SatScalarExtraction.sigma D.chart i)
    have hqv : q ≠ v := Fin.succAbove_ne v _
    have hold : 1 ≤ rowScore lam (directionRow o e c q) := by
      by_cases hqa : q = a
      · rw [hqa,ha]
        omega
      · simpa only [htail q hqv hqa] using (le_rfl : (1 : ℕ) ≤ 1)
    have hnew : 1 ≤ rowScore lam (directionRow o D.reference c q) := by
      rw [← href q]
      exact hold
    rw [hmodel]
    have hc := rowCells_directionRow_le_of_floor_eq o D.reference c hleg.lam_pos q
      (by decide : 2 ≤ 7) hn
    have hs := rowScore_eq_sub_defect lam hleg.lam_pos 4 _ hc
    change rowDefect 4 lam (directionRow o D.reference c q) ≤ 3
    omega
  have hheavy (i : Fin 6)
      (hpoint : v.succAbove (SatScalarExtraction.sigma D.chart i) = a) :
      SatScalarModel.rowDefect M i ≤ 2 := by
    rw [hmodel,hpoint]
    have hnew : rowScore lam (directionRow o D.reference c a) = 2 := by
      rw [← href a]
      exact ha
    have hc := rowCells_directionRow_le_of_floor_eq o D.reference c hleg.lam_pos a
      (by decide : 2 ≤ 7) hn
    have hs := rowScore_eq_sub_defect lam hleg.lam_pos 4 _ hc
    omega
  rcases D.heavy_boundary with hlo | hhi
  · exact hterminal M (hheavy 0 hlo) (hbound 1) (hbound 2) (hbound 3) (hbound 5)
  · apply hterminal (SatScalarModelReflection.reflect M)
    · simpa only [SatScalarModelReflection.reflect_rowDefect,
        show (0 : Fin 6).rev = 5 by decide] using hheavy 5 hhi
    · simpa only [SatScalarModelReflection.reflect_rowDefect,
        show (1 : Fin 6).rev = 4 by decide] using hbound 4
    · simpa only [SatScalarModelReflection.reflect_rowDefect,
        show (2 : Fin 6).rev = 3 by decide] using hbound 3
    · simpa only [SatScalarModelReflection.reflect_rowDefect,
        show (3 : Fin 6).rev = 2 by decide] using hbound 2
    · simpa only [SatScalarModelReflection.reflect_rowDefect,
        show (5 : Fin 6).rev = 0 by decide] using hbound 0

/-- Conditional exclusion of the original positive HIGH R1 minimal Model.
Potential22 and seven original points are conclusions of the existing
actual critical producer, not caller assumptions. The same original
configuration and indices are passed to the actual seven-point adapter. -/
theorem actual_high_r1_positive_model_false_of_terminal {s : ℕ}
    (hterminal : SevenLowerTerminal)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/5) (Real.pi/((4 : ℝ)+1/2)) 20 (s+1) c lam)
    (v : Fin (s+1)) (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (a : Fin (s+1)) (ha : rowScore lam (directionRow o e c a) = 2)
    (hpositive : ∀ q : Fin (s+1), 1 ≤ rowScore lam (directionRow o e c q)) : False := by
  have P := ActualHighR1PositiveCriticalProfile.actual_high_r1_positive_critical_profile
    o e he H v hsat a ha hpositive
  have hs : s = 6 := P.card_eq
  subst s
  exact actual_seven_positive_r1_false_of_terminal hterminal o e he H.legality
    P.floor_four P.high v a P.distinct hsat ha P.tail_score_one

#print axioms actual_seven_positive_r1_false_of_terminal
#print axioms actual_high_r1_positive_model_false_of_terminal

end Jsp404.ActualHighR1SevenLowerAdapter
