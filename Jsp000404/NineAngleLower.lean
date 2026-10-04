import Jsp000404.NineAngleConsumer
import Jsp000404.NoSatNineGeometry

/-! Exact unconditional original-problem lower bounds through ten points.
The bare actual nine-point exclusion discharges the consumer's last
geometric premise. Original definitions and quantifiers are unchanged. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404

private theorem actual_nine_angle_exclusion : NineAngleConsumer.NineAngleExclusion := by
  intro o e he lam c hleg hlow
  exact NoSatNineGeometry.nine_centres_angle_bound_impossible o e he hleg hlow

theorem sendov_lower_nine_to_ten {N : ℕ} (hN9 : 9 ≤ N) (hN10 : N ≤ 10)
    (C : PtCfg) (hlen : C.pts.length = N) :
    ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
      p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN N ≤ ∠ p q r :=
  NineAngleConsumer.sendov_lower_nine_ten_of_exclusion
    actual_nine_angle_exclusion hN9 hN10 C hlen

theorem sendov_lower_le_ten {N : ℕ} (hN : 3 ≤ N) (hN10 : N ≤ 10)
    (C : PtCfg) (hlen : C.pts.length = N) :
    ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
      p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN N ≤ ∠ p q r := by
  by_cases hN8 : N ≤ 8
  · exact sendov_lower_le_eight hN hN8 C hlen
  · exact sendov_lower_nine_to_ten (by omega) hN10 C hlen

/-- Equality of the original extremal quantity with the original formula
for every N from three through ten, without certificate hypotheses. -/
theorem sendov_alpha_eq_le_ten (N : ℕ) (hN : 3 ≤ N) (hN10 : N ≤ 10) :
    JSP404.alpha N = alphaN N := by
  classical
  apply le_antisymm (alpha_le_alphaN N hN)
  apply JSP404.le_alpha
  intro s hs
  let C : PtCfg := ⟨s.toList,s.nodup_toList,by simpa [hs] using hN⟩
  obtain ⟨p,q,r,hp,hq,hr,hpq,hrq,hpr,hang⟩ :=
    sendov_lower_le_ten hN hN10 C (by simpa [C] using hs)
  exact ⟨p,Finset.mem_toList.mp hp,q,Finset.mem_toList.mp hq,r,Finset.mem_toList.mp hr,
    hpq,hpr,hrq.symm,hang⟩

#print axioms sendov_lower_nine_to_ten
#print axioms sendov_lower_le_ten
#print axioms sendov_alpha_eq_le_ten
end Jsp404
