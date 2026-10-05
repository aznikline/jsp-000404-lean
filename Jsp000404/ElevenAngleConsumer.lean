import Jsp000404.SmallAngleLower
import Jsp000404.NoSatElevenGeometry

/-! Exact original lower-bound consumers of the bare eleven-point angle
exclusion. The genuine finite maximum supplies the lambda margin, and the
first eleven entries of the original configuration supply distinct points. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404.ElevenAngleConsumer

/-- Taking the genuine finite maximum converts the actual geometric
exclusion to the exact 3*pi/4 lower bound, with no additional premise. -/
theorem eleven_index_lower
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (c : Fin 11 → Plane₂) (hinj : Function.Injective c) :
    ∃ i j k : Fin 11, i ≠ j ∧ k ≠ j ∧ i ≠ k ∧
      3*Real.pi/4 ≤ ∠ (c i) (c j) (c k) := by
  classical
  let T := {q : Fin 11 × Fin 11 × Fin 11 //
    q.1 ≠ q.2.1 ∧ q.2.2 ≠ q.2.1 ∧ q.1 ≠ q.2.2}
  let : Nonempty T := ⟨⟨(0,1,2), by decide, by decide, by decide⟩⟩
  let ang : T → ℝ := fun q => ∠ (c q.1.1) (c q.1.2.1) (c q.1.2.2)
  obtain ⟨q, hmax⟩ := Finite.exists_max ang
  by_contra h
  push Not at h
  have hlt : ang q < 3*Real.pi/4 := h _ _ _ q.2.1 q.2.2.1 q.2.2.2
  let lam := Real.pi-ang q
  have hlam : 0 < lam := by dsimp [lam]; linarith [Real.pi_pos]
  have hhigh : Real.pi/4 < lam := by dsimp [lam]; linarith
  have hleg : Section4Legality c lam := {
    lam_pos := hlam
    inj := hinj
    triAngle := fun i j k hij hjk hik => by
      have hh := hmax ⟨(i,j,k),hij,hjk.symm,hik⟩
      change ∠ (c i) (c j) (c k) ≤ ang q at hh
      dsimp [lam]
      linarith }
  exact NoSatElevenGeometry.eleven_centres_angle_bound_impossible o e he hleg hhigh

#print axioms eleven_index_lower
end Jsp404.ElevenAngleConsumer

namespace Jsp404

/-- Eleven actual distinct points in the original configuration force the
original lower bound at every N from eleven through sixteen. -/
theorem actual_eleven_angle_exclusion
    {N : ℕ} (hN11 : 11 ≤ N) (hN16 : N ≤ 16)
    (C : PtCfg) (hlen : C.pts.length = N) :
    ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
      p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN N ≤ ∠ p q r := by
  let c : Fin 11 → Plane₂ := fun i => C.pts.get ⟨i.val, by omega⟩
  have hc : Function.Injective c := by
    intro i j h
    have hi := C.nodup.get_inj_iff.mp h
    exact Fin.ext (congrArg (fun x : Fin C.pts.length => x.val) hi)
  let o : Orientation ℝ Plane₂ (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let e := c 1-c 0
  have he : e ≠ 0 := sub_ne_zero.mpr (hc.ne (by decide : (1 : Fin 11) ≠ 0))
  obtain ⟨i,j,k,hij,hkj,hik,ha⟩ := ElevenAngleConsumer.eleven_index_lower o e he c hc
  have hbeta : alphaN N = 3*Real.pi/4 := by
    interval_cases N <;> norm_num [alphaN, Nat.clog] <;> ring
  rw [← hbeta] at ha
  exact ⟨c i,c j,c k,List.get_mem _ _,List.get_mem _ _,List.get_mem _ _,
    hc.ne hij,hc.ne hkj,hc.ne hik,ha⟩

#print axioms actual_eleven_angle_exclusion
end Jsp404
