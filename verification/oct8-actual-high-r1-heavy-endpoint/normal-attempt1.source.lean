import Jsp000404.SixWeakAllComplete
import Jsp000404.SatScalarExtraction
import Jsp000404.SatScalarModelReflection
import Jsp000404.FivePointCapacity
import Jsp000404.PositiveRowCount

set_option autoImplicit false

/-!
SOURCE_ONLY: the actual seven-point HIGH4 profile (3,2,1,1,1,1,1)
has its score-two point at one end of the internally produced SAT fan.
No caller chart, ordering, deletion gain, potential or Model is used.
This is a finite-profile endpoint constraint, not R1 capacity.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualHighR1HeavyEndpoint

private theorem strictMono_fin_five_eq_id (f : Fin 5 → Fin 5) (hf : StrictMono f) :
    ∀ i, f i = i := by
  have h01 := hf (by decide : (0 : Fin 5) < 1)
  have h12 := hf (by decide : (1 : Fin 5) < 2)
  have h23 := hf (by decide : (2 : Fin 5) < 3)
  have h34 := hf (by decide : (3 : Fin 5) < 4)
  have h0 : f 0 = 0 := Fin.ext (by omega)
  have h1 : f 1 = 1 := Fin.ext (by omega)
  have h2 : f 2 = 2 := Fin.ext (by omega)
  have h3 : f 3 = 3 := Fin.ext (by omega)
  have h4 : f 4 = 4 := Fin.ext (by omega)
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

private noncomputable def orderedKeep
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
    {c : Fin 7 → Plane₂} {v : Fin 7} {theta : Fin 6 → ℝ}
    (C : SatChart o e 4 lam c v theta) (J : Fin 5 → Fin 6) : Fin 6 → Fin 7 :=
  Fin.cases v (fun j => v.succAbove (SatScalarExtraction.sigma C (J j)))

private theorem orderedKeep_injective
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
    {c : Fin 7 → Plane₂} {v : Fin 7} {theta : Fin 6 → ℝ}
    (C : SatChart o e 4 lam c v theta) (J : Fin 5 → Fin 6) (hJ : Function.Injective J) :
    Function.Injective (orderedKeep C J) := by
  intro x
  refine Fin.cases ?_ ?_ x
  · intro y
    refine Fin.cases ?_ ?_ y
    · intro _h
      rfl
    · intro j h
      change v = v.succAbove (SatScalarExtraction.sigma C (J j)) at h
      exact False.elim (Fin.succAbove_ne v _ h.symm)
  · intro i y
    refine Fin.cases ?_ ?_ y
    · intro h
      change v.succAbove (SatScalarExtraction.sigma C (J i)) = v at h
      exact False.elim (Fin.succAbove_ne v _ h)
    · intro j h
      change v.succAbove (SatScalarExtraction.sigma C (J i)) =
        v.succAbove (SatScalarExtraction.sigma C (J j)) at h
      have hij := hJ (SatScalarExtraction.sigma_injective C (Fin.succAbove_right_injective h))
      exact congrArg Fin.succ hij

/-- A monotone selection of five actual nonanchor rays preserves their
physical chart. Row-score monotonicity supplies the weak A inequalities;
no preservation of an exact deleted potential or row score is needed. -/
private theorem odd_rank_in_ordered_slice_false
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
    {c : Fin 7 → Plane₂} {v : Fin 7} {theta : Fin 6 → ℝ}
    (C : SatChart o e 4 lam c v theta)
    (hpos : ∀ q : Fin 7, 1 ≤ rowScore lam (directionRow o e c q))
    (a : Fin 7) (ha : 2 ≤ rowScore lam (directionRow o e c a))
    (J : Fin 5 → Fin 6) (hJ : StrictMono J)
    (j : Fin 5) (hj : j = 1 ∨ j = 3)
    (hpoint : v.succAbove (SatScalarExtraction.sigma C (J j)) = a) : False := by
  classical
  let keep := orderedKeep C J
  have hkeep : Function.Injective keep := orderedKeep_injective C J hJ.injective
  let d : Fin 6 → Plane₂ := c ∘ keep
  let phi : Fin 5 → ℝ := fun i => theta (SatScalarExtraction.sigma C (J i))
  have hleg : Section4Legality d lam := C.hleg.restrict_injective keep hkeep
  have htheta : ∀ i : Fin 5, phi i ∈ Set.Icc 0 (Real.pi-4*lam) ∧
      o.oangle e (d ((0 : Fin 6).succAbove i)-d 0) = (phi i : Real.Angle) := by
    intro i
    simpa [d,keep,orderedKeep,phi] using C.htheta (SatScalarExtraction.sigma C (J i))
  let D : SatChart o e 4 lam d 0 phi :=
    ⟨C.he,by decide,C.hlam,C.hn,hleg,htheta⟩
  have hmonoOld : StrictMono (fun i : Fin 6 => theta (SatScalarExtraction.sigma C i)) := by
    intro i k hik
    simpa only [SatScalarExtraction.sigma_spec] using SatScalarExtraction.sortedTheta_strictMono C hik
  have hmonoNew : StrictMono phi := hmonoOld.comp hJ
  have hsigmaMono : StrictMono (SatScalarExtraction.sigma D) := by
    intro i k hik
    apply hmonoNew.lt_iff_lt.mp
    simpa only [SatScalarExtraction.sigma_spec] using SatScalarExtraction.sortedTheta_strictMono D hik
  have hsigma : ∀ i : Fin 5, SatScalarExtraction.sigma D i = i :=
    strictMono_fin_five_eq_id _ hsigmaMono
  let M := SatScalarExtraction.model D
  have hmodel (i : Fin 5) : SatScalarModel.rowDefect M i =
      rowDefect 4 lam (directionRow o e d i.succ) := by
    have hm := SatScalarExtraction.model_rowDefect D (by decide : 2 ≤ 5) i
    simpa only [M,hsigma,Fin.succAbove_zero] using hm
  have hnewpos (i : Fin 6) : 1 ≤ rowScore lam (directionRow o e d i) := by
    have hm := PositiveRowCount.rowScore_le_restrict o e c C.hlam
      (by decide : 2 ≤ 6) keep hkeep i
    exact (hpos (keep i)).trans hm
  have hnewheavy : 2 ≤ rowScore lam (directionRow o e d j.succ) := by
    have hm := PositiveRowCount.rowScore_le_restrict o e c C.hlam
      (by decide : 2 ≤ 6) keep hkeep j.succ
    have hold : 2 ≤ rowScore lam (directionRow o e c (keep j.succ)) := by
      simpa [keep,orderedKeep,hpoint] using ha
    exact hold.trans hm
  have hbound (i : Fin 5) : SatScalarModel.rowDefect M i ≤ 3 := by
    rw [hmodel]
    have hc := rowCells_directionRow_le_of_floor_eq o e d C.hlam i.succ
      (by decide : 2 ≤ 6) C.hn
    have hs := rowScore_eq_sub_defect lam C.hlam 4 _ hc
    have hp := hnewpos i.succ
    omega
  have hheavy : SatScalarModel.rowDefect M j ≤ 2 := by
    rw [hmodel]
    have hc := rowCells_directionRow_le_of_floor_eq o e d C.hlam j.succ
      (by decide : 2 ≤ 6) C.hn
    have hs := rowScore_eq_sub_defect lam C.hlam 4 _ hc
    omega
  rcases hj with rfl | rfl
  · exact SixWeakAllComplete.complete M hheavy (hbound 3)
  · apply SixWeakAllComplete.complete (SatScalarModelReflection.reflect M)
    · simpa only [SatScalarModelReflection.reflect_rowDefect,
        show (1 : Fin 5).rev = 3 by decide] using hheavy
    · simpa only [SatScalarModelReflection.reflect_rowDefect,
        show (3 : Fin 5).rev = 1 by decide] using hbound 1

/-- An actual SAT chart together with its actual heavy boundary witness. -/
structure Data (o : Orientation ℝ Plane₂ (Fin 2))
    (c : Fin 7 → Plane₂) (lam : ℝ) (v a : Fin 7) where
  reference : Plane₂
  theta : Fin 6 → ℝ
  chart : SatChart o reference 4 lam c v theta
  heavy_boundary : v.succAbove (SatScalarExtraction.sigma chart 0) = a ∨
    v.succAbove (SatScalarExtraction.sigma chart 5) = a

/-- Scoped actual seven-point R1 profile. The SAT chart, sorted angle
indices and ordered six-point restrictions are all internal outputs.
No caller potential22, zero gains, chart or angle ordering is required. -/
theorem exists_actual_high_r1_heavy_endpoint
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 7 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi/lam) = 4)
    (_hhigh : (1/2 : ℝ) ≤ Real.pi/lam-4)
    (v a : Fin 7) (hva : v ≠ a)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (ha : rowScore lam (directionRow o e c a) = 2)
    (htail : ∀ q : Fin 7, q ≠ v → q ≠ a → rowScore lam (directionRow o e c q) = 1) :
    Nonempty (Data o c lam v a) := by
  classical
  have hv : rowScore lam (directionRow o e c v) = 3 := by
    have hc := rowCells_directionRow_le_of_floor_eq o e c hleg.lam_pos v (by decide : 2 ≤ 7) hn
    have hs := rowScore_eq_sub_defect lam hleg.lam_pos 4 _ hc
    omega
  have hall (q : Fin 7) : 1 ≤ rowScore lam (directionRow o e c q) := by
    by_cases hqv : q = v
    · subst q
      omega
    · by_cases hqa : q = a
      · subst q
        omega
      · have hq := htail q hqv hqa
        omega
  obtain ⟨e',he',theta,htheta⟩ := saturated_ray_window o e he
    (s := 6) (by decide) (by decide : 2 ≤ 4) hleg.lam_pos hn hleg v hsat
  let C : SatChart o e' 4 lam c v theta := ⟨he',by decide,hleg.lam_pos,hn,hleg,htheta⟩
  have href (q : Fin 7) : rowScore lam (directionRow o e c q) =
      rowScore lam (directionRow o e' c q) :=
    rowScore_directionRow_reference_eq o e e' he he' c hleg.inj q lam
  have hall' (q : Fin 7) : 1 ≤ rowScore lam (directionRow o e' c q) := by
    rw [← href q]
    exact hall q
  have ha' : 2 ≤ rowScore lam (directionRow o e' c a) := by
    rw [← href a]
    omega
  obtain ⟨a',haPoint⟩ := Fin.exists_succAbove_eq hva.symm
  obtain ⟨r,hr⟩ := (SatScalarExtraction.sigma_bijective C).surjective a'
  have hpoint : v.succAbove (SatScalarExtraction.sigma C r) = a := by rw [hr,haPoint]
  have hcast : StrictMono (Fin.castSucc : Fin 5 → Fin 6) := by
    intro i j hij
    exact hij
  have hsucc : StrictMono (Fin.succ : Fin 5 → Fin 6) := by
    intro i j hij
    exact Fin.succ_lt_succ_iff.mpr hij
  have hboundary : v.succAbove (SatScalarExtraction.sigma C 0) = a ∨
      v.succAbove (SatScalarExtraction.sigma C 5) = a := by
    fin_cases r
    · exact Or.inl hpoint
    · exact False.elim (odd_rank_in_ordered_slice_false C hall' a ha'
        Fin.castSucc hcast 1 (Or.inl rfl) (by
          apply (congrArg (fun k : Fin 6 => v.succAbove (SatScalarExtraction.sigma C k))
            (show Fin.castSucc (1 : Fin 5) = (⟨1, by decide⟩ : Fin 6) by decide)).trans
          exact hpoint))
    · exact False.elim (odd_rank_in_ordered_slice_false C hall' a ha'
        Fin.succ hsucc 1 (Or.inl rfl) (by
          apply (congrArg (fun k : Fin 6 => v.succAbove (SatScalarExtraction.sigma C k))
            (show Fin.succ (1 : Fin 5) = (⟨2, by decide⟩ : Fin 6) by decide)).trans
          exact hpoint))
    · exact False.elim (odd_rank_in_ordered_slice_false C hall' a ha'
        Fin.castSucc hcast 3 (Or.inr rfl) (by
          apply (congrArg (fun k : Fin 6 => v.succAbove (SatScalarExtraction.sigma C k))
            (show Fin.castSucc (3 : Fin 5) = (⟨3, by decide⟩ : Fin 6) by decide)).trans
          exact hpoint))
    · exact False.elim (odd_rank_in_ordered_slice_false C hall' a ha'
        Fin.succ hsucc 3 (Or.inr rfl) (by
          apply (congrArg (fun k : Fin 6 => v.succAbove (SatScalarExtraction.sigma C k))
            (show Fin.succ (3 : Fin 5) = (⟨4, by decide⟩ : Fin 6) by decide)).trans
          exact hpoint))
    · exact Or.inr hpoint
  exact ⟨{reference := e',theta := theta,chart := C,heavy_boundary := hboundary}⟩

#print axioms exists_actual_high_r1_heavy_endpoint

end Jsp404.ActualHighR1HeavyEndpoint
