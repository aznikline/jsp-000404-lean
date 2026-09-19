import Jsp000404.SectorOS
import Jsp000404.SectorBound

/-!
# Sector-partition bound in the one-sided (wing) convention

The port of `card_le_two_pow_of_sector_cover` to `inSectorOS`: if every
generalized direction determined by two points of `Q` lies in one of `k`
one-sided double sectors `T(θᵢ, lam)`, and every generalized angle of `Q`
is at most `π - lam`, then `|Q| ≤ 2^k`. This is the counting engine of
Sendov's Lemma 3.7, where sectors come from consecutive wings of width
`2π/u` covering the gaps between center-line directions.
-/

open scoped EuclideanGeometry EuclideanSpace
open SimpleGraph

namespace Jsp404

/-- Shifting a direction by `π` swaps the two parts of `T(θ, lam)`. -/
lemma inSectorOS_add_pi {θ : Real.Angle} {lam : ℝ} {φ : Real.Angle} :
    inSectorOS θ lam (φ + Real.pi) ↔ inSectorOS θ lam φ := by
  unfold inSectorOS
  have h1 : φ + Real.pi - θ - Real.pi = φ - θ := by abel
  have h2 : φ + Real.pi - θ = φ - θ - Real.pi := by
    calc φ + Real.pi - θ = φ - θ + Real.pi := by abel
      _ = φ - θ + -Real.pi := by nth_rw 1 [pi_eq_neg_pi]
      _ = φ - θ - Real.pi := by rw [← sub_eq_add_neg]
  rw [h1, h2]
  exact or_comm

/-- A direction cannot lie in both parts of `T(θ, lam)` for `lam < π`. -/
lemma wing_both_parts_absurd {θ : Real.Angle} {lam : ℝ} (hlam : lam < Real.pi)
    {d : Real.Angle}
    (h1 : (d - θ).toReal ∈ Set.Ico 0 lam)
    (h2 : (d - θ - Real.pi).toReal ∈ Set.Ico 0 lam) : False := by
  obtain ⟨hx0, hxl⟩ := h1
  set x := (d - θ).toReal
  have hde : d - θ - Real.pi = ((x - Real.pi : ℝ) : Real.Angle) := by
    have hdt : d - θ = ((x : ℝ) : Real.Angle) := (Real.Angle.coe_toReal _).symm
    rw [hdt, ← Real.Angle.coe_sub]
  rw [hde, Real.Angle.toReal_coe] at h2
  by_cases hxp : x - Real.pi ≤ -Real.pi
  · -- then x = 0 and the representative is π
    have hx0' : x = 0 := by linarith [Real.pi_pos]
    have hto : toIocMod Real.two_pi_pos (-Real.pi) (x - Real.pi) = Real.pi := by
      rw [hx0']
      have : toIocMod Real.two_pi_pos (-Real.pi) (0 - Real.pi) =
          toIocMod Real.two_pi_pos (-Real.pi)
            (0 - Real.pi + (1 : ℤ) • (2 * Real.pi)) := by
        rw [toIocMod_add_zsmul]
      rw [show 0 - Real.pi + (1 : ℤ) • (2 * Real.pi) = Real.pi by
            simp; ring] at this
      rw [this, (toIocMod_eq_self Real.two_pi_pos).mpr
        (by constructor <;> linarith [Real.pi_pos])]
    rw [hto] at h2
    have := h2.2
    linarith [Real.pi_pos]
  · push Not at hxp
    have hmem : x - Real.pi ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
      constructor <;> linarith [Real.pi_pos]
    rw [(toIocMod_eq_self Real.two_pi_pos).mpr hmem] at h2
    have := h2.1
    linarith [Real.pi_pos]

/-- The wing-sector graph on `Q`: `p` and `q` are adjacent when their
generalized direction lies in `T(θ, lam)` (one-sided convention). -/
noncomputable def wingGraph (V : GCfg) (o : Orientation ℝ Plane₂ (Fin 2))
    (e : Plane₂) (he : e ≠ 0) (Q : Finset Plane₂) (θ : Real.Angle) (lam : ℝ) :
    SimpleGraph {p // p ∈ Q} where
  Adj p q := p ≠ q ∧ inSectorOS θ lam (o.oangle e (V.GD p.1 q.1))
  symm := ⟨fun {p q} h =>
    ⟨h.1.symm, by
      obtain ⟨hne, hT⟩ := h
      have hswap : V.GD q.1 p.1 = -V.GD p.1 q.1 := by
        unfold GCfg.GD
        rw [neg_sub]
      by_cases h0 : V.GD p.1 q.1 = 0
      · rw [hswap, h0, neg_zero, o.oangle_zero_right]
        rwa [h0, o.oangle_zero_right] at hT
      · rw [hswap, o.oangle_neg_right he h0, inSectorOS_add_pi]
        exact hT⟩⟩
  loopless := ⟨fun {v} h => h.1 rfl⟩

/-- Two consecutive edges of the wing graph lying in the same part of
`T(θ, lam)` force a generalized angle `> π - lam`. -/
lemma wingGraph_consec_angle (V : GCfg) {o : Orientation ℝ Plane₂ (Fin 2)}
    {e : Plane₂} (he : e ≠ 0) {Q : Finset Plane₂} (θ : Real.Angle)
    {lam : ℝ} (hlam : lam < Real.pi)
    (hGD : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → V.GD p q ≠ 0)
    {a b c : {p // p ∈ Q}}
    (hab : (wingGraph V o e he Q θ lam).Adj a b)
    (hbc : (wingGraph V o e he Q θ lam).Adj b c)
    (hsame : decide ((o.oangle e (V.GD a.1 b.1) - θ).toReal ∈ Set.Ico 0 lam) =
             decide ((o.oangle e (V.GD b.1 c.1) - θ).toReal ∈ Set.Ico 0 lam)) :
    V.GA a.1 b.1 c.1 > Real.pi - lam := by
  obtain ⟨hab_ne, hab_T⟩ := hab
  obtain ⟨hbc_ne, hbc_T⟩ := hbc
  have hab_ne' : (a : Plane₂) ≠ b := fun h => hab_ne (Subtype.ext h)
  have hbc_ne' : (b : Plane₂) ≠ c := fun h => hbc_ne (Subtype.ext h)
  have hpq : ((o.oangle e (V.GD a.1 b.1) - θ).toReal ∈ Set.Ico 0 lam) ↔
      ((o.oangle e (V.GD b.1 c.1) - θ).toReal ∈ Set.Ico 0 lam) := by
    cases hP : decide ((o.oangle e (V.GD a.1 b.1) - θ).toReal ∈ Set.Ico 0 lam) <;>
      cases hQ : decide ((o.oangle e (V.GD b.1 c.1) - θ).toReal ∈ Set.Ico 0 lam)
    · exact iff_of_false (of_decide_eq_false hP) (of_decide_eq_false hQ)
    · rw [hP, hQ] at hsame; nomatch hsame
    · rw [hP, hQ] at hsame; nomatch hsame
    · exact iff_of_true (of_decide_eq_true hP) (of_decide_eq_true hQ)
  have hsame' : ((o.oangle e (V.GD a.1 b.1) - θ).toReal ∈ Set.Ico 0 lam ∧
                 (o.oangle e (V.GD b.1 c.1) - θ).toReal ∈ Set.Ico 0 lam) ∨
                ((o.oangle e (V.GD a.1 b.1) - (θ + Real.pi)).toReal ∈ Set.Ico 0 lam ∧
                 (o.oangle e (V.GD b.1 c.1) - (θ + Real.pi)).toReal ∈ Set.Ico 0 lam) := by
    rcases hab_T with h1 | h1 <;> rcases hbc_T with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · exact False.elim (wing_both_parts_absurd hlam (hpq.mp h1) h2)
    · exact False.elim (wing_both_parts_absurd hlam (hpq.mpr h2) h1)
    · refine Or.inr ⟨?_, ?_⟩
      · have hre : o.oangle e (V.GD a.1 b.1) - (θ + Real.pi) =
            o.oangle e (V.GD a.1 b.1) - θ - Real.pi := sub_add_eq_sub_sub _ _ _
        rwa [hre]
      · have hre : o.oangle e (V.GD b.1 c.1) - (θ + Real.pi) =
            o.oangle e (V.GD b.1 c.1) - θ - Real.pi := sub_add_eq_sub_sub _ _ _
        rwa [hre]
  have hGDb : V.GD b.1 a.1 = -V.GD a.1 b.1 := by
    unfold GCfg.GD
    rw [neg_sub]
  have hbound : InnerProductGeometry.angle (-V.GD a.1 b.1) (V.GD b.1 c.1) >
      Real.pi - lam := by
    rcases hsame' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact angle_gt_of_same_wing he hlam
        (hGD a.1 a.2 b.1 b.2 hab_ne') (hGD b.1 b.2 c.1 c.2 hbc_ne') h1 h2
    · exact angle_gt_of_same_wing he hlam
        (hGD a.1 a.2 b.1 b.2 hab_ne') (hGD b.1 b.2 c.1 c.2 hbc_ne') h1 h2
  show InnerProductGeometry.angle (V.GD b.1 a.1) (V.GD b.1 c.1) > Real.pi - lam
  rw [hGDb]
  exact hbound

/-- **Sector-partition bound (wing convention).** If all generalized
directions determined by points of `Q` lie in `k` one-sided double sectors
`T(θᵢ, lam)`, and all generalized angles of `Q` are at most `π - lam`,
then `|Q| ≤ 2^k`. -/
theorem card_le_two_pow_of_wing_cover
    (V : GCfg) (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {k : ℕ} (θ : Fin k → Real.Angle) {lam : ℝ} (hlam : lam < Real.pi)
    (Q : Finset Plane₂)
    (hGD : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → V.GD p q ≠ 0)
    (hGA : ∀ p ∈ Q, ∀ q ∈ Q, ∀ r ∈ Q, p ≠ q → q ≠ r → p ≠ r →
      V.GA p q r ≤ Real.pi - lam)
    (hdir : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q →
      ∃ i, inSectorOS (θ i) lam (o.oangle e (V.GD p q))) :
    Q.card ≤ 2 ^ k := by
  classical
  have hcover : ∀ p q : {x // x ∈ Q}, p ≠ q →
      ∃ i, (wingGraph V o e he Q (θ i) lam).Adj p q := by
    intro p q hne
    have hne' : (p : Plane₂) ≠ q := fun h => hne (Subtype.ext h)
    obtain ⟨i, hi⟩ := hdir p.1 p.2 q.1 q.2 hne'
    exact ⟨i, hne, hi⟩
  have hcol : ∀ i, (wingGraph V o e he Q (θ i) lam).Colorable 2 := by
    intro i
    apply colorable_two_of_no_odd_closed_walk
    intro v W hWodd
    set L := W.length with hLdef
    have hLpos : 0 < L := by
      rcases Nat.eq_zero_or_pos L with h0 | h0
      · rw [h0] at hWodd; rcases hWodd with ⟨m, hm⟩; omega
      · exact h0
    set part : ℕ → Bool := fun t =>
      decide ((o.oangle e (V.GD (W.getVert t).1 (W.getVert (t + 1)).1) - θ i).toReal
        ∈ Set.Ico 0 lam) with hpart
    obtain ⟨k, hk, hpk⟩ := exists_consecutive_eq hWodd part
    have contra : ∀ a b c : {x // x ∈ Q},
        (wingGraph V o e he Q (θ i) lam).Adj a b →
        (wingGraph V o e he Q (θ i) lam).Adj b c →
        decide ((o.oangle e (V.GD a.1 b.1) - θ i).toReal ∈ Set.Ico 0 lam) =
        decide ((o.oangle e (V.GD b.1 c.1) - θ i).toReal ∈ Set.Ico 0 lam) →
        False := by
      intro a b c hab hbc hsame
      have hb_gt := wingGraph_consec_angle V he (θ i) hlam hGD hab hbc hsame
      have hab_ne' : (a : Plane₂) ≠ b := fun h => hab.1 (Subtype.ext h)
      have hbc_ne' : (b : Plane₂) ≠ c := fun h => hbc.1 (Subtype.ext h)
      rcases eq_or_ne (a : Plane₂) c with hac | hac
      · have hba : (b : Plane₂) ≠ a := fun h => hbc_ne' (h.trans hac)
        have hGA0 : V.GA a.1 b.1 c.1 = 0 := by
          show InnerProductGeometry.angle (V.GD b.1 a.1) (V.GD b.1 c.1) = 0
          rw [← hac]
          exact InnerProductGeometry.angle_self
            (hGD b.1 b.2 a.1 a.2 hba)
        linarith [Real.pi_pos]
      · linarith [hGA a.1 a.2 b.1 b.2 c.1 c.2 hab_ne' hbc_ne' hac]
    rcases Nat.lt_or_ge (k + 1) L with hlt | hge
    · have hmod : (k + 1) % L = k + 1 := Nat.mod_eq_of_lt hlt
      rw [hmod] at hpk
      simp only [hpart] at hpk
      exact contra _ _ _
        (W.adj_getVert_succ (show k < W.length by omega))
        (W.adj_getVert_succ (show k + 1 < W.length by omega)) hpk
    · have hk1 : k + 1 = L := by omega
      rw [hk1, Nat.mod_self] at hpk
      simp only [hpart] at hpk
      have hvl : W.getVert L = v := hLdef.symm ▸ W.getVert_length
      rw [hk1, hvl, W.getVert_zero] at hpk
      exact contra _ _ _
        (by have h := W.adj_getVert_succ (show k < W.length by omega)
            rw [hk1, hvl] at h; exact h)
        (by have h := W.adj_getVert_succ (show 0 < W.length by omega)
            rw [W.getVert_zero] at h; exact h) hpk
  let C : EvenCover {x // x ∈ Q} k :=
    ⟨fun i => wingGraph V o e he Q (θ i) lam, fun i => Classical.decRel _,
      hcover, hcol⟩
  have h := card_le_two_pow_of_evenCover C
  rwa [Fintype.card_coe] at h

end Jsp404
