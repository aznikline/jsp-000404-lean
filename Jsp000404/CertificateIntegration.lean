import Jsp000404.SmallStrip
import Jsp000404.Induction
import Jsp000404.SecondStripHigh

/-!
# From geometric certificates to the full Sendov theorem

The first two strips are now proved outright. For every later strip the only
input below is the geometric progress statement `CertExists`, quantified
uniformly in the chart, strip and regime. This is still an open hypothesis,
not an axiom or an established existence theorem.
-/

namespace Jsp404

/-- The remaining general geometric certificate claim. -/
def GeometricCertificates : Prop :=
  ∀ (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂), e ≠ 0 →
    ∀ (n : ℕ), 3 ≤ n → ∀ (lam : ℝ), 0 < lam → lam < Real.pi →
      Nat.floor (Real.pi / lam) = n → ∀ big : Bool,
        (big = false → Real.pi / lam - n < 1 / 2) →
        CertExists o e n big lam

/-- In the proved second strip the over-cap domain of `CertExists` is
empty. This discharges that boundary without any progress assumption. -/
private theorem second_strip_certificates
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 2)
    (big : Bool) (hbig : big = false → Real.pi / lam - 2 < 1/2) :
    CertExists o e 2 big lam := by
  intro t c ht hleg hover
  have hcap : potential lam (directionRows o e c) ≤ sendovCap 2 big := by
    cases big with
    | false =>
      simpa [sendovCap] using potential_le_four_of_second_strip_low o e he
        (by omega) hlam hn (hbig rfl) hleg
    | true =>
      simpa [sendovCap] using potential_le_five_of_second_strip o e he
        (by omega) hlam hn hleg
  exact False.elim ((not_lt_of_ge hcap) hover)

private lemma strip_index_pos {lam : ℝ} {n : ℕ}
    (hlam : 0 < lam) (hle : lam ≤ Real.pi)
    (hn : Nat.floor (Real.pi / lam) = n) : 1 ≤ n := by
  rw [← hn, Nat.one_le_floor_iff]
  exact (le_div_iff₀ hlam).mpr (by simpa using hle)

private lemma lam_lt_pi_of_second_strip {lam : ℝ} {n : ℕ}
    (hle : lam ≤ Real.pi) (hn : Nat.floor (Real.pi / lam) = n)
    (hn2 : 2 ≤ n) : lam < Real.pi := by
  by_contra h
  have he : lam = Real.pi := le_antisymm hle (not_lt.mp h)
  rw [he, div_self Real.pi_ne_zero] at hn
  norm_num at hn
  omega

/-- No small-strip or skeleton-adapter hypothesis is needed on this route. -/
theorem gadgetSelection_of_geometricCertificates (hcert : GeometricCertificates) :
    GadgetSelection where
  low := by
    intro V o e lam n he hle hlegal hfN hn hδ
    have hn1 := strip_index_pos hlegal.lam_pos hle hn
    by_cases heq : n = 1
    · rw [heq] at hn hδ ⊢
      simpa using first_strip_capacity_low V o e hlegal hfN hn
        (by simpa only [Nat.cast_one] using hδ)
    · have hn2 : 2 ≤ n := by omega
      have hlampi := lam_lt_pi_of_second_strip hle hn hn2
      have hc : CertExists o e n false lam := by
        by_cases hn3 : 3 ≤ n
        · exact hcert o e he n hn3 lam hlegal.lam_pos hlampi hn false (fun _ => hδ)
        · have heq2 : n = 2 := by omega
          rw [heq2] at hn hδ ⊢
          exact second_strip_certificates o e he hlegal.lam_pos hn false (fun _ => hδ)
      exact staircase_apply_low n _
        (staircase_of_cert V o e he n hn2 false hlegal.lam_pos hlampi hn
          (fun _ => hδ) hc hfN hlegal)
  high := by
    intro V o e lam n he hle hlegal hfN hn _hδ
    have hn1 := strip_index_pos hlegal.lam_pos hle hn
    by_cases heq : n = 1
    · rw [heq] at hn ⊢
      simpa using first_strip_capacity_high V o e hlegal hfN hn
    · have hn2 : 2 ≤ n := by omega
      have hlampi := lam_lt_pi_of_second_strip hle hn hn2
      have hbig : (true : Bool) = false → Real.pi / lam - n < 1 / 2 := by simp
      have hc : CertExists o e n true lam := by
        by_cases hn3 : 3 ≤ n
        · exact hcert o e he n hn3 lam hlegal.lam_pos hlampi hn true hbig
        · have heq2 : n = 2 := by omega
          rw [heq2] at hn hbig ⊢
          exact second_strip_certificates o e he hlegal.lam_pos hn true hbig
      exact staircase_apply_big n _
        (staircase_of_cert V o e he n hn2 true hlegal.lam_pos hlampi hn
          hbig hc hfN hlegal)

/-- Full classification, conditional only on the explicitly open certificate
existence claim. The upper bound and the n = 1,2 cases are proved. -/
theorem sendov_alpha_eq_of_geometricCertificates (hcert : GeometricCertificates)
    (N : ℕ) (hN : 3 ≤ N) : JSP404.alpha N = alphaN N :=
  sendov_alpha_eq_of_selection (gadgetSelection_of_geometricCertificates hcert) N hN

#print axioms gadgetSelection_of_geometricCertificates
#print axioms sendov_alpha_eq_of_geometricCertificates

end Jsp404
