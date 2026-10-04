import Jsp000404.SmallAngleLower
import Jsp000404.Section4Legality

/-! Exact original lower-bound consumers for a bare nine-point angle
exclusion. The geometric exclusion is explicitly retained as a hypothesis
until its independently checked actual-point theorem is supplied. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404.NineAngleConsumer

def NineAngleExclusion : Prop :=
  ∀ (_o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂), e ≠ 0 →
    ∀ {lam : ℝ} {c : Fin 9 → Plane₂}, Section4Legality c lam →
      2*Real.pi/7 < lam → False

/-- Taking the genuine finite maximum angle converts the actual geometric
exclusion to the exact 5*pi/7 lower bound, with no floor hypothesis. -/
theorem nine_index_lower_of_exclusion (hex : NineAngleExclusion)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (c : Fin 9 → Plane₂) (hinj : Function.Injective c) :
    ∃ i j k : Fin 9, i ≠ j ∧ k ≠ j ∧ i ≠ k ∧
      5*Real.pi/7 ≤ ∠ (c i) (c j) (c k) := by
  classical
  let T := {q : Fin 9 × Fin 9 × Fin 9 //
    q.1 ≠ q.2.1 ∧ q.2.2 ≠ q.2.1 ∧ q.1 ≠ q.2.2}
  let : Nonempty T := ⟨⟨(0,1,2), by decide, by decide, by decide⟩⟩
  let ang : T → ℝ := fun q => ∠ (c q.1.1) (c q.1.2.1) (c q.1.2.2)
  obtain ⟨q, hmax⟩ := Finite.exists_max ang
  by_contra h
  push Not at h
  have hlt : ang q < 5*Real.pi/7 := h _ _ _ q.2.1 q.2.2.1 q.2.2.2
  let lam := Real.pi-ang q
  have hlam : 0 < lam := by dsimp [lam]; linarith [Real.pi_pos]
  have hlow : 2*Real.pi/7 < lam := by dsimp [lam]; linarith
  have hleg : Section4Legality c lam := {
    lam_pos := hlam
    inj := hinj
    triAngle := fun i j k hij hjk hik => by
      have hh := hmax ⟨(i,j,k),hij,hjk.symm,hik⟩
      change ∠ (c i) (c j) (c k) ≤ ang q at hh
      dsimp [lam]
      linarith }
  exact hex o e he hleg hlow

/-- The original problem's lower theorem at N=9 and N=10, conditional
only on the same explicit actual-point exclusion. -/
theorem sendov_lower_nine_ten_of_exclusion (hex : NineAngleExclusion)
    {N : ℕ} (hN9 : 9 ≤ N) (hN10 : N ≤ 10)
    (C : PtCfg) (hlen : C.pts.length = N) :
    ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
      p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN N ≤ ∠ p q r := by
  let c : Fin 9 → Plane₂ := fun i => C.pts.get ⟨i.val, by omega⟩
  have hc : Function.Injective c := by
    intro i j h
    have hi := C.nodup.get_inj_iff.mp h
    exact Fin.ext (congrArg (fun x : Fin C.pts.length => x.val) hi)
  let o : Orientation ℝ Plane₂ (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let e := c 1-c 0
  have he : e ≠ 0 := sub_ne_zero.mpr (hc.ne (by decide : (1 : Fin 9) ≠ 0))
  obtain ⟨i,j,k,hij,hkj,hik,ha⟩ := nine_index_lower_of_exclusion hex o e he c hc
  have hbeta : alphaN N = 5*Real.pi/7 := by
    interval_cases N <;> norm_num [alphaN, Nat.clog] <;> ring
  rw [← hbeta] at ha
  exact ⟨c i,c j,c k,List.get_mem _ _,List.get_mem _ _,List.get_mem _ _,
    hc.ne hij,hc.ne hkj,hc.ne hik,ha⟩

#print axioms nine_index_lower_of_exclusion
#print axioms sendov_lower_nine_ten_of_exclusion
end Jsp404.NineAngleConsumer
