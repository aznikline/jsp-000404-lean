import Jsp000404.ActualN4R2CapacityAssembly
import Jsp000404.SatScalarExtraction
import Jsp000404.SatScalarModelReflection
import Jsp000404.SixExactFloorKernelSymbolicBetweenTerminal

/-! SOURCE_ONLY conditional actual six-point potential-22 adapter.

The two explicit scalar closures below are interfaces for the still unfinished
SixWeak A/B all-direction kernel replays. They are hypotheses, not new facts.
Every actual chart, rank and row defect is constructed from original points.
The finite rank dispatch reuses the frozen HIGH between result for ranks0/4.
No claim of a compiled adapter or completed R2 capacity is made here.
-/

set_option autoImplicit false
set_option pp.fullNames true
open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualN4R2Critical22Adapter

open SatScalarModel

/-- Required future A75 all62 terminal; no word or row certificate input. -/
def WeakAComplete : Prop :=
  ∀ M : GenericModel 5 4, SatScalarModel.rowDefect M 1 ≤ 2 →
    SatScalarModel.rowDefect M 3 ≤ 3 → False

/-- Required future B225 all62 terminal; all other rows are unrestricted. -/
def WeakBComplete : Prop :=
  ∀ M : GenericModel 5 4, SatScalarModel.rowDefect M 0 ≤ 2 →
    SatScalarModel.rowDefect M 2 ≤ 2 → False

private theorem between_generic (M : GenericModel 5 4)
    (hhigh : (1 / 2 : ℝ) ≤ M.delta)
    (h0 : SatScalarModel.rowDefect M 0 = 2)
    (h1 : SatScalarModel.rowDefect M 1 = 3)
    (h3 : SatScalarModel.rowDefect M 3 = 3)
    (h4 : SatScalarModel.rowDefect M 4 = 2) : False := by
  exact SixExactFloorKernel.symbolic_between_impossible
    (SatScalarExtraction.toModelSix M) (by decide) hhigh
    ((SatScalarExtraction.toModelSix_rowDefect M 0).trans h0)
    ((SatScalarExtraction.toModelSix_rowDefect M 1).trans h1)
    ((SatScalarExtraction.toModelSix_rowDefect M 3).trans h3)
    ((SatScalarExtraction.toModelSix_rowDefect M 4).trans h4)

/-- Ten unordered low-rank pairs, with no caller rank placement selection.
A and its reflection handle seven pairs; B and its reflection handle0/2 and
2/4; the frozen HIGH between theorem handles0/4. -/
theorem scalar_profile_impossible_of_weak_closures
    (hA : WeakAComplete) (hB : WeakBComplete) (M : GenericModel 5 4)
    (hhigh : (1 / 2 : ℝ) ≤ M.delta) (a b : Fin 5) (hab : a ≠ b)
    (ha : SatScalarModel.rowDefect M a = 2)
    (hb : SatScalarModel.rowDefect M b = 2)
    (htail : ∀ i : Fin 5, i ≠ a → i ≠ b → SatScalarModel.rowDefect M i = 3) :
    False := by
  have hbound (i : Fin 5) : SatScalarModel.rowDefect M i ≤ 3 := by
    by_cases hia : i = a
    · simp [hia, ha]
    by_cases hib : i = b
    · simp [hib, hb]
    exact (htail i hia hib).le
  by_cases h1 : SatScalarModel.rowDefect M 1 ≤ 2
  · exact hA M h1 (hbound 3)
  by_cases h3 : SatScalarModel.rowDefect M 3 ≤ 2
  · apply hA (SatScalarModelReflection.reflect M)
    · simpa only [SatScalarModelReflection.reflect_rowDefect,
        show (1 : Fin 5).rev = 3 by decide] using h3
    · simpa only [SatScalarModelReflection.reflect_rowDefect,
        show (3 : Fin 5).rev = 1 by decide] using hbound 1
  by_cases h02 : SatScalarModel.rowDefect M 0 ≤ 2 ∧ SatScalarModel.rowDefect M 2 ≤ 2
  · exact hB M h02.1 h02.2
  by_cases h24 : SatScalarModel.rowDefect M 2 ≤ 2 ∧ SatScalarModel.rowDefect M 4 ≤ 2
  · apply hB (SatScalarModelReflection.reflect M)
    · simpa only [SatScalarModelReflection.reflect_rowDefect,
        show (0 : Fin 5).rev = 4 by decide] using h24.2
    · simpa only [SatScalarModelReflection.reflect_rowDefect,
        show (2 : Fin 5).rev = 2 by decide] using h24.1
  have hends : (a = 0 ∧ b = 4) ∨ (a = 4 ∧ b = 0) := by
    fin_cases a <;> fin_cases b <;> simp_all
  rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact between_generic M hhigh ha (htail 1 (by decide) (by decide))
      (htail 3 (by decide) (by decide)) hb
  · exact between_generic M hhigh hb (htail 1 (by decide) (by decide))
      (htail 3 (by decide) (by decide)) ha

/-- Original six-point score profile3,2,2,1,1,1 supplies its own saturated
chart, complete five-row scalar model, rank positions and full row defects.
Only the two explicit future scalar terminals remain as proof inputs. -/
theorem actual_six_profile_impossible_of_weak_closures
    (hA : WeakAComplete) (hB : WeakBComplete)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (c : Fin 6 → Plane₂) (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi / lam) = 4)
    (hhigh : (1 / 2 : ℝ) ≤ Real.pi / lam - 4)
    {v a b : Fin 6} (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hv : rowScore lam (directionRow o e c v) = 3)
    (ha : rowScore lam (directionRow o e c a) = 2)
    (hb : rowScore lam (directionRow o e c b) = 2)
    (htails : ∀ r : Fin 6, r ≠ v → r ≠ a → r ≠ b →
      rowScore lam (directionRow o e c r) = 1) : False := by
  have hcells (r : Fin 6) : rowCells lam (directionRow o e c r) ≤ 4 :=
    rowCells_directionRow_le_of_floor_eq o e c hleg.lam_pos r (by decide) hn
  have hscore (r : Fin 6) : rowScore lam (directionRow o e c r) =
      4 - rowDefect 4 lam (directionRow o e c r) :=
    rowScore_eq_sub_defect lam hleg.lam_pos 4 _ (hcells r)
  have hsat : rowDefect 4 lam (directionRow o e c v) = 1 := by
    have h := hscore v
    omega
  have hda : rowDefect 4 lam (directionRow o e c a) = 2 := by
    have h := hscore a
    omega
  have hdb : rowDefect 4 lam (directionRow o e c b) = 2 := by
    have h := hscore b
    omega
  have htail (r : Fin 6) (hrv : r ≠ v) (hra : r ≠ a) (hrb : r ≠ b) :
      rowDefect 4 lam (directionRow o e c r) = 3 := by
    have h := hscore r
    have ht := htails r hrv hra hrb
    omega
  obtain ⟨e', he', theta, htheta⟩ := saturated_ray_window o e he
    (s := 5) (by decide) (by decide : 2 ≤ 4) hleg.lam_pos hn hleg v hsat
  let C : SatChart o e' 4 lam c v theta :=
    ⟨he', by decide, hleg.lam_pos, hn, hleg, htheta⟩
  have href (r : Fin 6) : rowDefect 4 lam (directionRow o e' c r) =
      rowDefect 4 lam (directionRow o e c r) :=
    rowDefect_directionRow_reference_eq o e' e he' he c hleg.inj r
      hleg.lam_pos (by decide) hn
  obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq hva.symm
  obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq hvb.symm
  obtain ⟨lo, hlo⟩ := (SatScalarExtraction.sigma_bijective C).surjective a'
  obtain ⟨hi, hhi⟩ := (SatScalarExtraction.sigma_bijective C).surjective b'
  let rankPoint (i : Fin 5) : Fin 6 := v.succAbove (SatScalarExtraction.sigma C i)
  have hinj : Function.Injective rankPoint := by
    intro i j h
    exact SatScalarExtraction.sigma_injective C (Fin.succAbove_right_injective h)
  have hpA : rankPoint lo = a := by simpa only [rankPoint, hlo] using ha'
  have hpB : rankPoint hi = b := by simpa only [rankPoint, hhi] using hb'
  have hne : lo ≠ hi := by
    intro h
    exact hab (hpA.symm.trans ((congrArg rankPoint h).trans hpB))
  let M := SatScalarExtraction.model C
  have hdef (i : Fin 5) : SatScalarModel.rowDefect M i =
      rowDefect 4 lam (directionRow o e c (rankPoint i)) :=
    (SatScalarExtraction.model_rowDefect C (by decide : 2 ≤ 5) i).trans (href _)
  have hdlo : SatScalarModel.rowDefect M lo = 2 := by rw [hdef, hpA]; exact hda
  have hdhi : SatScalarModel.rowDefect M hi = 2 := by rw [hdef, hpB]; exact hdb
  have hdtail (i : Fin 5) (hilo : i ≠ lo) (hihi : i ≠ hi) :
      SatScalarModel.rowDefect M i = 3 := by
    rw [hdef]
    apply htail (rankPoint i) (Fin.succAbove_ne v _)
    · intro h
      exact hilo (hinj (h.trans hpA.symm))
    · intro h
      exact hihi (hinj (h.trans hpB.symm))
  have hhighM : (1 / 2 : ℝ) ≤ M.delta := by
    change (1 / 2 : ℝ) ≤ (SatScalarExtraction.model C).delta
    rw [SatScalarExtraction.model_delta]
    exact hhigh
  exact scalar_profile_impossible_of_weak_closures hA hB M hhighM lo hi hne hdlo hdhi hdtail

/-- Exact interface needed by the already checked conditional R2 assembly.
The original potential22 hypothesis is accepted by that named interface;
the stronger complete score-profile contradiction does not need its value. -/
theorem named_no_critical22_six_of_weak_closures
    (hA : WeakAComplete) (hB : WeakBComplete)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hn : Nat.floor (Real.pi / lam) = 4)
    (hhigh : (1 / 2 : ℝ) ≤ Real.pi / lam - 4) :
    ActualN4R2CapacityAssembly.NamedNoCrit22Six o e lam := by
  intro c hleg v a b hva hvb hab hv ha hb ht _hF
  exact actual_six_profile_impossible_of_weak_closures hA hB o e he c hleg hn hhigh
    hva hvb hab hv ha hb ht

#print axioms scalar_profile_impossible_of_weak_closures
#print axioms actual_six_profile_impossible_of_weak_closures
#print axioms named_no_critical22_six_of_weak_closures

end Jsp404.ActualN4R2Critical22Adapter
