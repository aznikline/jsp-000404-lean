import Jsp000404.DeletionRigidityGaps
import Jsp000404.GeometricDeletion

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

/-- **Zero gain ⇒ a small facing sweep** (general size).  If erasing
`v`'s direction from row `i` produces `rowGain = 0`, then at least one
of the two cyclic sweeps incident to the ray `i → v` is `< λ`: there
exist centers `p` (predecessor side) and `q` (successor side) with
`linRep(∠piv) < λ ∨ linRep(∠viq) < λ`.  This is the combinatorial
content consumed by the all-zero-gain six-centre analysis: a deleted
point's ray must sit within `λ` (in sweep) of a neighbouring center's
ray on at least one side.  Bridges `rowGain_eq_mergeGain_sweeps` with
`not_both_big_of_mergeGain_zero`. -/
theorem exists_small_facing_sweep_of_rowGain_zero {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} (hinj : Function.Injective c)
    {lam : ℝ} (hlam : 0 < lam)
    {i v : Fin s} (hiv : i ≠ v) (h3 : 3 ≤ s)
    (hne : ∃ j : Fin s, j ≠ i ∧ dirRep o e c i j ≠ dirRep o e c i v)
    (hg : rowGain lam (directionRow o e c i) (deleteIndex o e c v i) = 0) :
    ∃ p q : Fin s, p ≠ i ∧ q ≠ i ∧
      (linRep (o.oangle (c p - c i) (c v - c i)) < lam ∨
        linRep (o.oangle (c v - c i) (c q - c i)) < lam) ∧
      (∀ y ∈ directionRow o e c i,
        cyclicDiff y (dirRep o e c i v) = 0 ∨
          cyclicDiff (dirRep o e c i p) (dirRep o e c i v) ≤
            cyclicDiff y (dirRep o e c i v)) ∧
      (∀ y ∈ directionRow o e c i,
        cyclicDiff (dirRep o e c i v) y = 0 ∨
          cyclicDiff (dirRep o e c i v) (dirRep o e c i q) ≤
            cyclicDiff (dirRep o e c i v) y) := by
  obtain ⟨p, q, hpi, hqi, hmg, -, -, hadj1, hadj2⟩ :=
    rowGain_eq_mergeGain_sweeps o e c hlam he hinj hiv h3 hne
  rw [hg] at hmg
  have hboth := not_both_big_of_mergeGain_zero hlam hmg.symm
  exact ⟨p, q, hpi, hqi, by
    rw [not_and_or] at hboth
    exact hboth.imp (lt_of_not_ge ·) (lt_of_not_ge ·), hadj1, hadj2⟩

/-- Strengthened facing consequence below the `2λ` ceiling: when every
cyclic gap of row `i` is `< 2λ` — the score-`0` profile of a defect-`3`
row at `n = 3` — zero gain at the deleted direction forces the merged
pair of incident sweeps to sum to `< 2λ`, i.e. the merged gap in the
reduced row is again below the `2λ` threshold.  This is the deletion
constraint consumed by the six-centre `n = 3` exclusion: each tail
deletion certifies an actual pair of neighbouring directions whose
combined sweep stays under `2λ`. -/
theorem exists_facing_sweep_sum_lt_two_of_rowGain_zero {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} (hinj : Function.Injective c)
    {lam : ℝ} (hlam : 0 < lam)
    {i v : Fin s} (hiv : i ≠ v) (h3 : 3 ≤ s)
    (hne : ∃ j : Fin s, j ≠ i ∧ dirRep o e c i j ≠ dirRep o e c i v)
    (hgap : ∀ g ∈ cycGaps (directionRow o e c i), g < 2 * lam)
    (hg : rowGain lam (directionRow o e c i)
      (deleteIndex o e c v i) = 0) :
    ∃ p q : Fin s, p ≠ i ∧ q ≠ i ∧
      linRep (o.oangle (c p - c i) (c v - c i)) +
        linRep (o.oangle (c v - c i) (c q - c i)) < 2 * lam ∧
      (∀ y ∈ directionRow o e c i,
        cyclicDiff y (dirRep o e c i v) = 0 ∨
          cyclicDiff (dirRep o e c i p) (dirRep o e c i v) ≤
            cyclicDiff y (dirRep o e c i v)) ∧
      (∀ y ∈ directionRow o e c i,
        cyclicDiff (dirRep o e c i v) y = 0 ∨
          cyclicDiff (dirRep o e c i v) (dirRep o e c i q) ≤
            cyclicDiff (dirRep o e c i v) y) := by
  obtain ⟨p, q, hpi, hqi, hmg, hm1, hm2, hadj1, hadj2⟩ :=
    rowGain_eq_mergeGain_sweeps o e c hlam he hinj hiv h3 hne
  rw [hg] at hmg
  exact ⟨p, q, hpi, hqi, add_lt_two_mul_of_mergeGain_zero hlam
    (linRep_mem_Ico _).1 (linRep_mem_Ico _).1
    (hgap _ hm1) (hgap _ hm2) hmg.symm, hadj1, hadj2⟩


end Jsp404
