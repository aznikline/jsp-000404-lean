import Jsp000404.Sector
import Jsp000404.EvenPartition

/-!
# Sendov Lemma 3.3 — the sector-partition bound

If every generalized direction determined by two points of `Q` lies inside
one of `k` double sectors `T(θᵢ, lam)`, and every generalized angle of `Q`
is at most `Real.pi - lam`, then `|Q| ≤ 2^k`.

The proof: the `k` graphs `Gᵢ` (edges = pairs whose generalized direction
lies in `T(θᵢ, lam)`) cover `Q`. Each `Gᵢ` has no odd closed walk — two
consecutive edges in the same part of the sector would force an angle
`> Real.pi - lam` by Lemma 3.2 — hence `Gᵢ` is 2-colorable, and the
Erdős–Szekeres lemma applies.
-/

open scoped EuclideanGeometry EuclideanSpace
open SimpleGraph

namespace Jsp404

/-- **Vector form of Lemma 3.2.** If the directions of `u₁`, `u₂` lie in the
same part of `T(θ, lam)`, then the angle between `-u₁` and `u₂` exceeds
`Real.pi - lam`. This is the form used for generalized angles, where
`GA(p,q,r) = angle (-GD(p,q)) (GD(q,r))`. -/
theorem lemma_3_2_vec {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
    (he : e ≠ 0) (θ : Real.Angle) {lam : ℝ} (hlpi : lam < Real.pi)
    {u₁ u₂ : Plane₂} (hu1 : u₁ ≠ 0) (hu2 : u₂ ≠ 0)
    (hsame : (angDist (o.oangle e u₁) θ < lam / 2 ∧ angDist (o.oangle e u₂) θ < lam / 2) ∨
             (angDist (o.oangle e u₁) (θ + Real.pi) < lam / 2 ∧
              angDist (o.oangle e u₂) (θ + Real.pi) < lam / 2)) :
    InnerProductGeometry.angle (-u₁) u₂ > Real.pi - lam := by
  have hu1' : -u₁ ≠ 0 := neg_ne_zero.mpr hu1
  have hangle : InnerProductGeometry.angle (-u₁) u₂ =
      |(o.oangle (-u₁) u₂).toReal| :=
    o.angle_eq_abs_oangle_toReal hu1' hu2
  have hsub : o.oangle (-u₁) u₂ = o.oangle e u₂ - o.oangle e (-u₁) :=
    (o.oangle_sub_left he hu1' hu2).symm
  have hflip : o.oangle e (-u₁) = o.oangle e u₁ + Real.pi :=
    o.oangle_neg_right he hu1
  rw [hangle, hsub, hflip]
  rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hdist : angDist (o.oangle e u₁ + Real.pi) (θ + Real.pi) < lam / 2 := by
      show |(o.oangle e u₁ + Real.pi - (θ + Real.pi)).toReal| < lam / 2
      have : o.oangle e u₁ + Real.pi - (θ + Real.pi) = o.oangle e u₁ - θ := by abel
      rw [this]; exact h1
    exact angDist_antipodal hlpi hdist h2
  · have hflip2 : o.oangle e u₁ + Real.pi - θ = o.oangle e u₁ - (θ + Real.pi) := by
      calc o.oangle e u₁ + Real.pi - θ = o.oangle e u₁ - θ + Real.pi := by abel
        _ = o.oangle e u₁ - θ + -Real.pi := by nth_rw 1 [pi_eq_neg_pi]
        _ = o.oangle e u₁ - θ - Real.pi := by rw [← sub_eq_add_neg]
        _ = o.oangle e u₁ - (θ + Real.pi) := by rw [sub_add_eq_sub_sub]
    have hdist : angDist (o.oangle e u₁ + Real.pi) θ < lam / 2 := by
      show |(o.oangle e u₁ + Real.pi - θ).toReal| < lam / 2
      rw [hflip2]; exact h1
    have := angDist_antipodal hlpi h2 hdist
    rw [show o.oangle e u₂ - (o.oangle e u₁ + Real.pi) =
        -((o.oangle e u₁ + Real.pi) - o.oangle e u₂) by abel, Real.Angle.abs_toReal_neg]
    exact this

/-- Shifting a direction by `Real.pi` swaps the parts of a double sector. -/
lemma inDoubleSector_add_pi {θ : Real.Angle} {lam : ℝ} {φ : Real.Angle} :
    inDoubleSector θ lam (φ + Real.pi) ↔ inDoubleSector θ lam φ := by
  unfold inDoubleSector angDist
  have h1 : φ + Real.pi - θ = φ - (θ + Real.pi) := by
    calc φ + Real.pi - θ = φ - θ + Real.pi := by abel
      _ = φ - θ + -Real.pi := by nth_rw 1 [pi_eq_neg_pi]
      _ = φ - θ - Real.pi := by rw [← sub_eq_add_neg]
      _ = φ - (θ + Real.pi) := by rw [sub_add_eq_sub_sub]
  have h2 : φ + Real.pi - (θ + Real.pi) = φ - θ := by abel
  rw [h1, h2]
  exact or_comm

/-- On a cyclic sequence of odd length, two consecutive entries coincide. -/
lemma exists_consecutive_eq {L : ℕ} (hL : Odd L) (f : ℕ → Bool) :
    ∃ k < L, f k = f ((k + 1) % L) := by
  by_contra hcon
  push_neg at hcon
  -- every step flips the value
  have key : ∀ n, n < L → f ((n + 1) % L) = !f (n % L) := by
    intro n hn
    have hne := hcon n hn
    rw [Nat.mod_eq_of_lt hn]
    rcases Bool.eq_false_or_eq_true (f n) with h' | h' <;>
      rcases Bool.eq_false_or_eq_true (f ((n + 1) % L)) with h'' | h'' <;>
      simp_all
  have step : ∀ m, m ≤ L → f (m % L) = if Even m then f 0 else !(f 0) := by
    intro m hm
    induction m with
    | zero => simp
    | succ n ih =>
      have hn : n < L := Nat.lt_of_succ_le hm
      rw [key n hn, ih (Nat.le_of_succ_le hm)]
      rcases Nat.even_or_odd n with he | ho
      · rw [if_pos he, if_neg (Nat.not_even_iff_odd.mpr (he.add_odd odd_one))]
      · rw [if_neg (Nat.not_even_iff_odd.mpr ho), if_pos (ho.add_odd odd_one)]
        rcases Bool.eq_false_or_eq_true (f 0) with h' | h' <;> simp [h']
  have hL' := step L le_rfl
  rw [Nat.mod_self, if_neg (Nat.not_even_iff_odd.mpr hL)] at hL'
  cases hf : f 0 <;> simp [hf] at hL'

/-- Shifting the direction by `π` moves between the two parts of `T(θ, lam)`. -/
lemma angDist_add_pi_left (φ θ : Real.Angle) :
    angDist (φ + Real.pi) θ = angDist φ (θ + Real.pi) := by
  unfold angDist
  rw [show φ + Real.pi - θ = φ - (θ + Real.pi) by
    calc φ + Real.pi - θ = φ - θ + Real.pi := by abel
      _ = φ - θ + -Real.pi := by nth_rw 1 [pi_eq_neg_pi]
      _ = φ - θ - Real.pi := by rw [← sub_eq_add_neg]
      _ = φ - (θ + Real.pi) := by rw [sub_add_eq_sub_sub]]

lemma angDist_add_pi_both (φ θ : Real.Angle) :
    angDist (φ + Real.pi) (θ + Real.pi) = angDist φ θ := by
  unfold angDist
  rw [show φ + Real.pi - (θ + Real.pi) = φ - θ by abel]

/-- A direction cannot lie in both parts of a double sector narrower than `π`. -/
lemma angDist_both_parts_absurd {φ θ : Real.Angle} {lam : ℝ} (hlam : lam < Real.pi)
    (h1 : angDist φ θ < lam / 2) (h2 : angDist φ (θ + Real.pi) < lam / 2) : False := by
  have h := angDist_antipodal hlam h2 h1
  simp only [sub_self, Real.Angle.toReal_zero, abs_zero] at h
  linarith [Real.pi_pos]

/-- The sector graph on `Q`: `p` and `q` are adjacent when their generalized
direction lies in the double sector `T(θ, lam)`. -/
noncomputable def sectorGraph (V : GCfg) (o : Orientation ℝ Plane₂ (Fin 2))
    (e : Plane₂) (he : e ≠ 0) (Q : Finset Plane₂) (θ : Real.Angle) (lam : ℝ) :
    SimpleGraph {p // p ∈ Q} where
  Adj p q := p ≠ q ∧ inDoubleSector θ lam (o.oangle e (V.GD p.1 q.1))
  symm := ⟨fun {p q} h =>
    ⟨h.1.symm, by
      obtain ⟨hne, hT⟩ := h
      have hswap : V.GD q.1 p.1 = -V.GD p.1 q.1 := by
        unfold GCfg.GD
        rw [neg_sub]
      by_cases h0 : V.GD p.1 q.1 = 0
      · rw [hswap, h0, neg_zero, o.oangle_zero_right]
        rwa [h0, o.oangle_zero_right] at hT
      · rw [hswap, o.oangle_neg_right he h0, inDoubleSector_add_pi]
        exact hT⟩⟩
  loopless := ⟨fun {v} h => h.1 rfl⟩

/-- Two consecutive edges of the sector graph lying in the same part of the
double sector force a generalized angle `> π - lam` (Lemma 3.2 in GA form). -/
lemma sectorGraph_consec_angle (V : GCfg) {o : Orientation ℝ Plane₂ (Fin 2)}
    {e : Plane₂} (he : e ≠ 0) {Q : Finset Plane₂} (θ : Real.Angle)
    {lam : ℝ} (hlam : lam < Real.pi)
    (hGD : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → V.GD p q ≠ 0)
    {a b c : {p // p ∈ Q}}
    (hab : (sectorGraph V o e he Q θ lam).Adj a b)
    (hbc : (sectorGraph V o e he Q θ lam).Adj b c)
    (hsame : decide (angDist (o.oangle e (V.GD a.1 b.1)) θ < lam / 2) =
             decide (angDist (o.oangle e (V.GD b.1 c.1)) θ < lam / 2)) :
    V.GA a.1 b.1 c.1 > Real.pi - lam := by
  obtain ⟨hab_ne, hab_T⟩ := hab
  obtain ⟨hbc_ne, hbc_T⟩ := hbc
  have hab_ne' : (a : Plane₂) ≠ b := fun h => hab_ne (Subtype.ext h)
  have hbc_ne' : (b : Plane₂) ≠ c := fun h => hbc_ne (Subtype.ext h)
  have hpq : (angDist (o.oangle e (V.GD a.1 b.1)) θ < lam / 2) ↔
      (angDist (o.oangle e (V.GD b.1 c.1)) θ < lam / 2) := by
    cases hP : decide (angDist (o.oangle e (V.GD a.1 b.1)) θ < lam / 2) <;>
      cases hQ : decide (angDist (o.oangle e (V.GD b.1 c.1)) θ < lam / 2)
    · exact iff_of_false (of_decide_eq_false hP) (of_decide_eq_false hQ)
    · rw [hP, hQ] at hsame; nomatch hsame
    · rw [hP, hQ] at hsame; nomatch hsame
    · exact iff_of_true (of_decide_eq_true hP) (of_decide_eq_true hQ)
  have hsame' : (angDist (o.oangle e (V.GD a.1 b.1)) θ < lam / 2 ∧
                 angDist (o.oangle e (V.GD b.1 c.1)) θ < lam / 2) ∨
                (angDist (o.oangle e (V.GD a.1 b.1)) (θ + Real.pi) < lam / 2 ∧
                 angDist (o.oangle e (V.GD b.1 c.1)) (θ + Real.pi) < lam / 2) := by
    rcases hab_T with h1 | h1 <;> rcases hbc_T with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · exact False.elim (angDist_both_parts_absurd hlam (hpq.mp h1) h2)
    · exact False.elim (angDist_both_parts_absurd hlam (hpq.mpr h2) h1)
    · exact Or.inr ⟨h1, h2⟩
  have hGDb : V.GD b.1 a.1 = -V.GD a.1 b.1 := by
    unfold GCfg.GD
    rw [neg_sub]
  have hbound := lemma_3_2_vec he θ hlam (hGD a.1 a.2 b.1 b.2 hab_ne')
    (hGD b.1 b.2 c.1 c.2 hbc_ne') hsame'
  show InnerProductGeometry.angle (V.GD b.1 a.1) (V.GD b.1 c.1) > Real.pi - lam
  rw [hGDb]
  exact hbound

/-- **Lemma 3.3 (Sendov).** If all generalized directions determined by points
of `Q` lie inside `k` double sectors `T(θᵢ, lam)`, and all generalized angles
of `Q` are at most `π - lam`, then `|Q| ≤ 2^k`. -/
theorem card_le_two_pow_of_sector_cover
    (V : GCfg) (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {k : ℕ} (θ : Fin k → Real.Angle) {lam : ℝ} (hlam : lam < Real.pi)
    (Q : Finset Plane₂)
    (hGD : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → V.GD p q ≠ 0)
    (hGA : ∀ p ∈ Q, ∀ q ∈ Q, ∀ r ∈ Q, p ≠ q → q ≠ r → p ≠ r →
      V.GA p q r ≤ Real.pi - lam)
    (hdir : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q →
      ∃ i, inDoubleSector (θ i) lam (o.oangle e (V.GD p q))) :
    Q.card ≤ 2 ^ k := by
  classical
  have hcover : ∀ p q : {x // x ∈ Q}, p ≠ q →
      ∃ i, (sectorGraph V o e he Q (θ i) lam).Adj p q := by
    intro p q hne
    have hne' : (p : Plane₂) ≠ q := fun h => hne (Subtype.ext h)
    obtain ⟨i, hi⟩ := hdir p.1 p.2 q.1 q.2 hne'
    exact ⟨i, hne, hi⟩
  have hcol : ∀ i, (sectorGraph V o e he Q (θ i) lam).Colorable 2 := by
    intro i
    apply colorable_two_of_no_odd_closed_walk
    intro v W hWodd
    set L := W.length with hLdef
    have hLpos : 0 < L := by
      rcases Nat.eq_zero_or_pos L with h0 | h0
      · rw [h0] at hWodd; rcases hWodd with ⟨m, hm⟩; omega
      · exact h0
    have hL1 : L ≠ 1 := by
      intro h1
      have hadj := W.adj_getVert_succ hLpos
      have hv1 : W.getVert 1 = v := by
        have hlen := W.getVert_length
        rwa [← hLdef, h1] at hlen
      rw [W.getVert_zero, hv1] at hadj
      exact hadj.1 rfl
    have hL3 : 3 ≤ L := by
      rcases hWodd with ⟨m, hm⟩
      omega
    set part : ℕ → Bool := fun t =>
      decide (angDist (o.oangle e (V.GD (W.getVert t).1 (W.getVert (t + 1)).1))
        (θ i) < lam / 2) with hpart
    obtain ⟨k, hk, hpk⟩ := exists_consecutive_eq hWodd part
    -- the contradiction obtained from a same-part consecutive pair
    have contra : ∀ a b c : {x // x ∈ Q},
        (sectorGraph V o e he Q (θ i) lam).Adj a b →
        (sectorGraph V o e he Q (θ i) lam).Adj b c →
        decide (angDist (o.oangle e (V.GD a.1 b.1)) (θ i) < lam / 2) =
        decide (angDist (o.oangle e (V.GD b.1 c.1)) (θ i) < lam / 2) →
        False := by
      intro a b c hab hbc hsame
      have hb_gt := sectorGraph_consec_angle V he (θ i) hlam hGD hab hbc hsame
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
    · -- interior: edges k, k+1 share vertex getVert (k+1)
      have hmod : (k + 1) % L = k + 1 := Nat.mod_eq_of_lt hlt
      rw [hmod] at hpk
      simp only [hpart] at hpk
      exact contra _ _ _
        (W.adj_getVert_succ (show k < W.length by omega))
        (W.adj_getVert_succ (show k + 1 < W.length by omega)) hpk
    · -- wraparound: edges k = L-1 and 0 share vertex v
      have hk1 : k + 1 = L := by omega
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
    ⟨fun i => sectorGraph V o e he Q (θ i) lam, fun i => Classical.decRel _,
      hcover, hcol⟩
  have h := card_le_two_pow_of_evenCover C
  rwa [Fintype.card_coe] at h
end Jsp404
