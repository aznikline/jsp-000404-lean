import Jsp000404.ElevenAngleConsumer
import Jsp000404.NineAngleLower

/-! Exact unconditional original-problem lower bounds through sixteen
points. The bare actual eleven-point exclusion extends the checked initial
range, with the original definitions and quantifiers unchanged. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404

theorem sendov_lower_eleven_to_sixteen {N : ℕ} (hN11 : 11 ≤ N) (hN16 : N ≤ 16)
    (C : PtCfg) (hlen : C.pts.length = N) :
    ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
      p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN N ≤ ∠ p q r :=
  actual_eleven_angle_exclusion hN11 hN16 C hlen

theorem sendov_lower_le_sixteen {N : ℕ} (hN : 3 ≤ N) (hN16 : N ≤ 16)
    (C : PtCfg) (hlen : C.pts.length = N) :
    ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
      p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN N ≤ ∠ p q r := by
  by_cases hN10 : N ≤ 10
  · exact sendov_lower_le_ten hN hN10 C hlen
  · exact sendov_lower_eleven_to_sixteen (by omega) hN16 C hlen

/-- Equality of the original extremal quantity with the original formula
for every N from three through sixteen, without certificate hypotheses. -/
theorem sendov_alpha_eq_le_sixteen (N : ℕ) (hN : 3 ≤ N) (hN16 : N ≤ 16) :
    JSP404.alpha N = alphaN N := by
  classical
  apply le_antisymm (alpha_le_alphaN N hN)
  apply JSP404.le_alpha
  intro s hs
  let C : PtCfg := ⟨s.toList,s.nodup_toList,by simpa [hs] using hN⟩
  obtain ⟨p,q,r,hp,hq,hr,hpq,hrq,hpr,hang⟩ :=
    sendov_lower_le_sixteen hN hN16 C (by simpa [C] using hs)
  exact ⟨p,Finset.mem_toList.mp hp,q,Finset.mem_toList.mp hq,r,Finset.mem_toList.mp hr,
    hpq,hpr,hrq.symm,hang⟩

#print axioms sendov_lower_eleven_to_sixteen
#print axioms sendov_lower_le_sixteen
#print axioms sendov_alpha_eq_le_sixteen
end Jsp404
