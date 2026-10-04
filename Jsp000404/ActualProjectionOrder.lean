import Jsp000404.MixedStarExclusion
import Mathlib.Order.RelClasses

/-! A strict total order of actual centers by their directed half-plane
chords. No generic-reference or nonzero-projective-angle assumption is
needed: zero representatives are allowed. Actual legality excludes the
collinear middle-angle case in the transitivity proof. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404.ActualProjectionOrder

def Up {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) (a b : Fin s) : Prop :=
  o.oangle e (c b-c a) = (dirRep o e c a b : Real.Angle)

section Actual
variable (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {s : ℕ} {lam : ℝ} {c : Fin s → Plane₂} (hleg : Section4Legality c lam)

include he hleg

theorem up_or_up {a b : Fin s} (hab : a ≠ b) :
    Up o e c a b ∨ Up o e c b a := by
  rcases linRep_class (o.oangle e (c b-c a)) with h | h
  · exact Or.inl h.symm
  · right
    unfold Up
    rw [show c a-c b = -(c b-c a) by abel,
      o.oangle_neg_right he (sub_ne_zero.mpr (hleg.inj.ne hab.symm)),
      ← dirRep_comm o e c he (hleg.inj.ne hab)]
    exact h.symm

theorem up_not_both {a b : Fin s} (hab : a ≠ b) (h1 : Up o e c a b) :
    ¬ Up o e c b a := by
  intro h2
  unfold Up at h1 h2
  rw [show c a-c b = -(c b-c a) by abel,
    o.oangle_neg_right he (sub_ne_zero.mpr (hleg.inj.ne hab.symm)), h1,
    ← dirRep_comm o e c he (hleg.inj.ne hab)] at h2
  have h3 : ((Real.pi : ℝ) : Real.Angle) = 0 := by
    have := congrArg (fun t => t-(dirRep o e c a b : Real.Angle)) h2
    simpa using this
  exact Real.Angle.pi_ne_zero h3

/-- The cap at the middle vertex gives the separation of two forward
chord representatives. -/
theorem up_cap {a b d : Fin s} (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d)
    (h1 : Up o e c a b) (h2 : Up o e c b d) :
    lam ≤ |dirRep o e c b d-dirRep o e c a b| := by
  have hcap := hleg.triAngle a b d hab hbd had
  have hang := angle_eq_abs_of_half_plane_chart o he
    (sub_ne_zero.mpr (hleg.inj.ne hab.symm))
    (sub_ne_zero.mpr (hleg.inj.ne hbd.symm))
    (linRep_mem_Ico _) (linRep_mem_Ico _) h1 h2
  change InnerProductGeometry.angle (c a-c b) (c d-c b) ≤ Real.pi-lam at hcap
  rw [show c a-c b = -(c b-c a) by abel,
    InnerProductGeometry.angle_neg_left, hang] at hcap
  change lam ≤ |linRep (o.oangle e (c d-c b))-linRep (o.oangle e (c b-c a))|
  linarith

/-- Forward chords compose, and the composed representative lies strictly
between them. This is derived from actual vector addition and triangle cap. -/
theorem up_trans {a b d : Fin s} (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d)
    (h1 : Up o e c a b) (h2 : Up o e c b d) :
    Up o e c a d ∧
      ((dirRep o e c a b < dirRep o e c a d ∧
          dirRep o e c a d < dirRep o e c b d) ∨
        (dirRep o e c b d < dirRep o e c a d ∧
          dirRep o e c a d < dirRep o e c a b)) := by
  have hcap := up_cap o e he hleg hab hbd had h1 h2
  have hlam := hleg.lam_pos
  have m1 : dirRep o e c a b ∈ Set.Ico 0 Real.pi := linRep_mem_Ico _
  have m2 : dirRep o e c b d ∈ Set.Ico 0 Real.pi := linRep_mem_Ico _
  have hA : c b-c a ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hab.symm)
  have hB : c d-c b ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hbd.symm)
  have hsum : c d-c a = (c b-c a)+(c d-c b) := by abel
  have hfin : ∀ γ : ℝ, 0 ≤ γ → γ < Real.pi →
      o.oangle e (c d-c a) = (γ : Real.Angle) →
      Up o e c a d ∧ dirRep o e c a d = γ := by
    intro γ h0 hπ hγ
    have hd : dirRep o e c a d = γ := by
      show linRep (o.oangle e (c d-c a)) = γ
      rw [hγ, linRep_coe_eq_of_mem h0 hπ]
    exact ⟨by unfold Up; rw [hγ, hd], hd⟩
  rcases lt_or_gt_of_ne (show dirRep o e c a b ≠ dirRep o e c b d by
    intro h; rw [h, sub_self, abs_zero] at hcap; linarith) with hlt | hlt
  · obtain ⟨-, γ, hg1, hg2, hγ⟩ := oangle_add_between o he hA hB h1 h2 hlt
      (by linarith [m1.1, m2.2])
    rw [← hsum] at hγ
    obtain ⟨hup, hd⟩ := hfin γ (by linarith [m1.1]) (by linarith [m2.2]) hγ
    exact ⟨hup, Or.inl ⟨by rw [hd]; exact hg1, by rw [hd]; exact hg2⟩⟩
  · obtain ⟨-, γ, hg1, hg2, hγ⟩ := oangle_add_between o he hB hA h2 h1 hlt
      (by linarith [m2.1, m1.2])
    rw [add_comm, ← hsum] at hγ
    obtain ⟨hup, hd⟩ := hfin γ (by linarith [m2.1]) (by linarith [m1.2]) hγ
    exact ⟨hup, Or.inr ⟨by rw [hd]; exact hg1, by rw [hd]; exact hg2⟩⟩

theorem triangle_between {a b d : Fin s} (hab : a ≠ b) (hbd : b ≠ d)
    (had : a ≠ d) (h1 : Up o e c a b) (h2 : Up o e c b d) :
    (dirRep o e c a b < dirRep o e c a d ∧ dirRep o e c a d < dirRep o e c b d) ∨
      (dirRep o e c b d < dirRep o e c a d ∧ dirRep o e c a d < dirRep o e c a b) :=
  (up_trans o e he hleg hab hbd had h1 h2).2

/-- Every actual legal finite configuration can be bijectively indexed so
that all chords from lower to higher indices are forward in `[0,pi)`. -/
theorem exists_ordered_config :
    ∃ sigma : Fin s → Fin s, Function.Bijective sigma ∧
      ∀ i j : Fin s, i < j → Up o e c (sigma i) (sigma j) := by
  classical
  let r : ULift (Fin s) → ULift (Fin s) → Prop :=
    fun a b => a.down ≠ b.down ∧ Up o e c a.down b.down
  have : IsStrictTotalOrder (ULift (Fin s)) r := {
    irrefl := fun a h => h.1 rfl
    trichotomous := fun a b hnab hnba => by
      by_contra hab
      have hab' : a.down ≠ b.down := fun h => hab (ULift.down_injective h)
      rcases up_or_up o e he hleg hab' with h | h
      · exact hnab ⟨hab', h⟩
      · exact hnba ⟨hab'.symm, h⟩
    trans := fun a b d hab hbd => by
      have had : a.down ≠ d.down := by
        intro had
        exact up_not_both o e he hleg hab.1 hab.2 (had ▸ hbd.2)
      exact ⟨had, (up_trans o e he hleg hab.1 hbd.1 had hab.2 hbd.2).1⟩ }
  let ord : LinearOrder (ULift (Fin s)) := linearOrderOfSTO r
  let : LinearOrder (ULift (Fin s)) := ord
  let : Preorder (ULift (Fin s)) := ord.toPreorder
  let : LE (ULift (Fin s)) := ord.toLE
  let : LT (ULift (Fin s)) := ord.toLT
  let E : Fin s ≃o ULift.{0} (Fin s) :=
    Fintype.orderIsoFinOfCardEq (ULift.{0} (Fin s))
      (by simp : Fintype.card (ULift.{0} (Fin s)) = s)
  refine ⟨fun i => (E i).down, ?_, ?_⟩
  · refine ⟨ULift.down_injective.comp E.injective, ?_⟩
    intro a
    obtain ⟨i, hi⟩ := E.surjective (ULift.up a)
    exact ⟨i, congrArg ULift.down hi⟩
  intro i j hij
  have h := E.strictMono hij
  change r (E i) (E j) at h
  exact h.2

end Actual
#print axioms up_trans
#print axioms exists_ordered_config
end Jsp404.ActualProjectionOrder
