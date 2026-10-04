import Jsp000404.NoSatFiveGeometry
import Jsp000404.NoSatNineDBMTerminal

/-! Actual nine-point angular exclusion. The bare finite terminal uses only
the complete three-angle-cap constraints. There is no row-score, deletion,
saturation, floor, or minimality premise in the underlying geometric result. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404.NoSatNineGeometry

/-- Ordered actual points instantiate the bare complete-cap model. -/
noncomputable def model
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 9 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlow : 2*Real.pi/7 < lam)
    (hup : ∀ i j : Fin 9, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle)) :
    NoSatNineDBMTerminal.NineModel lam Real.pi where
  hlam := hleg.lam_pos
  hp := by linarith
  d := dirRep o e c
  hrange := fun _ _ _ => linRep_mem_Ico _
  htr := fun _ _ _ hij hjk => NoSatFiveGeometry.ordered_triangle o e he hleg hup hij hjk

/-- The bare arithmetic terminal is consumed on actual ordered points. -/
theorem ordered_nine_centres_angle_bound_impossible
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 9 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlow : 2*Real.pi/7 < lam)
    (hup : ∀ i j : Fin 9, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle)) : False :=
  NoSatNineDBMTerminal.nine_model_impossible (model o e he hleg hlow hup)

/-- Actual nine-point exclusion with only the original triangle-angle
legality and lambda>2*pi/7. The point order is constructed internally. -/
theorem nine_centres_angle_bound_impossible
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 9 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlow : 2*Real.pi/7 < lam) : False := by
  obtain ⟨sigma, hsigma, hup⟩ := ActualProjectionOrder.exists_ordered_config o e he hleg
  exact ordered_nine_centres_angle_bound_impossible o e he
    (hleg.restrict_injective sigma hsigma.1) hlow (fun i j hij => hup i j hij)

/-- Third-strip adapter. The floor hypothesis identifies the caller's
regime, but the geometric exclusion itself does not require it. -/
theorem nine_centres_low_impossible
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 9 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (_hn : Nat.floor (Real.pi/lam) = 3) (hlow : 2*Real.pi/7 < lam) : False :=
  nine_centres_angle_bound_impossible o e he hleg hlow

/-- The same actual exclusion bounds arbitrary configuration size. -/
theorem centres_low_card_le_eight {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlow : 2*Real.pi/7 < lam) : s ≤ 8 := by
  by_contra hh
  have hs : 9 ≤ s := by omega
  let pick : Fin 9 → Fin s := Fin.castLE hs
  have hpick : Function.Injective pick := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun a : Fin s => a.val) hij
  exact nine_centres_angle_bound_impossible o e he
    (hleg.restrict_injective pick hpick) hlow

#print axioms nine_centres_angle_bound_impossible
#print axioms nine_centres_low_impossible
#print axioms centres_low_card_le_eight
end Jsp404.NoSatNineGeometry
