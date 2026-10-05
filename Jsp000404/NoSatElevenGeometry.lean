import Jsp000404.NoSatFiveGeometry
import Jsp000404.NoSatElevenDBMTerminal

/-! Actual eleven-point angular exclusion. Every ordered triangle supplies
its separation, strict betweenness and both endpoint caps to the finite
terminal. The public theorem constructs its actual point order internally. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404.NoSatElevenGeometry

/-- Ordered actual points instantiate the complete-cap model. -/
noncomputable def model
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 11 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hhigh : Real.pi/4 < lam)
    (hup : ∀ i j : Fin 11, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle)) :
    NoSatElevenDBMTerminal.ElevenModel lam Real.pi where
  hlam := hleg.lam_pos
  hp := by linarith
  d := dirRep o e c
  hrange := fun _ _ _ => linRep_mem_Ico _
  htr := fun _ _ _ hij hjk => NoSatFiveGeometry.ordered_triangle o e he hleg hup hij hjk

/-- The finite terminal is consumed on actual ordered points. -/
theorem ordered_eleven_centres_angle_bound_impossible
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 11 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hhigh : Real.pi/4 < lam)
    (hup : ∀ i j : Fin 11, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle)) : False :=
  NoSatElevenDBMTerminal.eleven_model_impossible (model o e he hleg hhigh hup)

/-- Bare eleven-point exclusion with only original triangle-angle legality
and lambda>pi/4. It requires no floor, score, or saturation hypothesis. -/
theorem eleven_centres_angle_bound_impossible
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 11 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hhigh : Real.pi/4 < lam) : False := by
  obtain ⟨sigma, hsigma, hup⟩ := ActualProjectionOrder.exists_ordered_config o e he hleg
  exact ordered_eleven_centres_angle_bound_impossible o e he
    (hleg.restrict_injective sigma hsigma.1) hhigh (fun i j hij => hup i j hij)

/-- The same actual exclusion bounds arbitrary configuration size. -/
theorem centres_high_card_le_ten {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hhigh : Real.pi/4 < lam) : s ≤ 10 := by
  by_contra hh
  have hs : 11 ≤ s := by omega
  let pick : Fin 11 → Fin s := Fin.castLE hs
  have hpick : Function.Injective pick := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun a : Fin s => a.val) hij
  exact eleven_centres_angle_bound_impossible o e he
    (hleg.restrict_injective pick hpick) hhigh

#print axioms eleven_centres_angle_bound_impossible
#print axioms centres_high_card_le_ten
end Jsp404.NoSatElevenGeometry
