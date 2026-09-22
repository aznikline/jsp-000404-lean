import Jsp000404.AcuteFanPacking
import Jsp000404.CircleSeparation
import Jsp000404.Statement
import Jsp000404.SmallStrip

/-! # Unconditional lower bounds through eight points -/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

/-- Below 120 degrees every center has an inward fan bisector. Packing
those bisectors on the full circle gives this ordinary-point lower bound. -/
theorem exists_angle_ge_of_circle_budget {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (hs : 3 ≤ s)
    (c : Fin s → Plane₂) (hinj : Function.Injective c)
    {beta : ℝ} (hbeta : beta ≤ 2*Real.pi/3)
    (hbudget : 2*Real.pi ≤ (s : ℝ)*(Real.pi-beta)) :
    ∃ i j k : Fin s, i ≠ j ∧ k ≠ j ∧ i ≠ k ∧ beta ≤ ∠ (c i) (c j) (c k) := by
  classical
  let T := {q : Fin s × Fin s × Fin s //
    q.1 ≠ q.2.1 ∧ q.2.2 ≠ q.2.1 ∧ q.1 ≠ q.2.2}
  let z : Fin s := ⟨0, by omega⟩
  let one : Fin s := ⟨1, by omega⟩
  let two : Fin s := ⟨2, by omega⟩
  have hz1 : z ≠ one := by intro h; have := congrArg Fin.val h; norm_num [z, one] at this
  have h21 : two ≠ one := by intro h; have := congrArg Fin.val h; norm_num [two, one] at this
  have hz2 : z ≠ two := by intro h; have := congrArg Fin.val h; norm_num [z, two] at this
  letI : Nonempty T := ⟨⟨(z, one, two), hz1, h21, hz2⟩⟩
  let ang : T → ℝ := fun q => ∠ (c q.1.1) (c q.1.2.1) (c q.1.2.2)
  obtain ⟨q, hmax⟩ := Finite.exists_max ang
  by_contra h
  push_neg at h
  have hlt : ang q < beta := h _ _ _ q.2.1 q.2.2.1 q.2.2.2
  have hnonneg : 0 ≤ ang q := EuclideanGeometry.angle_nonneg _ _ _
  have hsmall : 3*ang q < 2*Real.pi := by linarith
  have hcap (i j k : Fin s) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
      ∠ (c i) (c j) (c k) ≤ ang q := hmax ⟨(i,j,k), hij, hjk.symm, hik⟩
  obtain ⟨m, hm, hsep⟩ := exists_separated_inward_bisectors o (by omega)
    hinj hnonneg hsmall hcap
  have hc := circle_separation_bound o (by omega) m hm hsep
  have hspos : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hstrict : (s : ℝ) * (Real.pi-beta) < (s : ℝ)*(Real.pi-ang q) :=
    mul_lt_mul_of_pos_left (by linarith) hspos
  linarith

/-- The original problem's exact lower bounds for five through eight
points, without any certificate or capacity premise. -/
theorem sendov_lower_five_to_eight {N : ℕ} (hN5 : 5 ≤ N) (hN8 : N ≤ 8)
    (C : PtCfg) (hlen : C.pts.length = N) :
    ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
      p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN N ≤ ∠ p q r := by
  let c : Fin N → Plane₂ := fun i => C.pts.get ⟨i.val, by omega⟩
  have hc : Function.Injective c := by
    intro i j he
    have hget := C.nodup.get_inj_iff.mp he
    exact Fin.ext (congrArg (fun x : Fin C.pts.length => x.val) hget)
  let o : Orientation ℝ Plane₂ (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  have hbeta : alphaN N ≤ 2*Real.pi/3 := by
    interval_cases N <;> norm_num [alphaN, Nat.clog] <;> nlinarith [Real.pi_pos]
  have hbudget : 2*Real.pi ≤ (N : ℝ)*(Real.pi-alphaN N) := by
    interval_cases N <;> norm_num [alphaN, Nat.clog] <;> nlinarith [Real.pi_pos]
  obtain ⟨i,j,k,hij,hkj,hik,ha⟩ :=
    exists_angle_ge_of_circle_budget o (by omega) c hc hbeta hbudget
  exact ⟨c i,c j,c k,List.get_mem _ _,List.get_mem _ _,List.get_mem _ _,
    hc.ne hij,hc.ne hkj,hc.ne hik,ha⟩

/-- The unconditional lower theorem for the entire initial range. -/
theorem sendov_lower_le_eight {N : ℕ} (hN : 3 ≤ N) (hN8 : N ≤ 8)
    (C : PtCfg) (hlen : C.pts.length = N) :
    ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
      p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN N ≤ ∠ p q r := by
  rcases eq_or_ne N 3 with rfl | hN3
  · exact sendov_lower_three C hlen
  rcases eq_or_ne N 4 with rfl | hN4
  · exact sendov_lower_four C hlen
  exact sendov_lower_five_to_eight (by omega) hN8 C hlen

/-- Exact equality of the genuine extremal quantity with Sendov's
formula for every N from three through eight. -/
theorem sendov_alpha_eq_le_eight (N : ℕ) (hN : 3 ≤ N) (hN8 : N ≤ 8) :
    JSP404.alpha N = alphaN N := by
  classical
  apply le_antisymm (alpha_le_alphaN N hN)
  apply JSP404.le_alpha
  intro s hs
  let C : PtCfg := ⟨s.toList, s.nodup_toList, by simpa [hs] using hN⟩
  obtain ⟨p, q, r, hp, hq, hr, hpq, hrq, hpr, hang⟩ :=
    sendov_lower_le_eight hN hN8 C (by simpa [C] using hs)
  exact ⟨p, Finset.mem_toList.mp hp, q, Finset.mem_toList.mp hq,
    r, Finset.mem_toList.mp hr, hpq, hpr, hrq.symm, hang⟩

#print axioms exists_angle_ge_of_circle_budget
#print axioms sendov_lower_five_to_eight
#print axioms sendov_lower_le_eight
#print axioms sendov_alpha_eq_le_eight

end Jsp404
