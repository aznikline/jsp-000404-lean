import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_63S11

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_14_M_LR_L_0_L_I_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_11_14_M_LR_L_0_L_I_x0_x0_x0 m hb0 hb1 hb4 h0 h1 h2
  · exact r1l7_20_11_14_M_LR_L_0_L_I_x0_x0_x1 m hb0 hb1 hb4 h0 h1 h2

theorem r1l7_20_11_14_M_LR_L_0_L_I_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  linarith only [h0, h1, hlam, hphi, ht01, u0ehi6, u1elo2]

theorem r1l7_20_11_14_M_LR_L_0_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_11_14_M_LR_L_0_L_I_x0_x0 m hb0 hb1 hb4 h0 h1
  · exact r1l7_20_11_14_M_LR_L_0_L_I_x0_x1 m hb0 hb1 hb4 h0 h1

theorem r1l7_20_11_14_M_LR_L_0_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo1]

theorem r1l7_20_11_14_M_LR_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_14_M_LR_L_0_L_I_x0 m hb0 hb1 hb4 h0
  · exact r1l7_20_11_14_M_LR_L_0_L_I_x1 m hb0 hb1 hb4 h0

theorem r1l7_20_12_13_15_M_LI_L_I_L_0_L_0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                              · linarith only [h0, h10, h15, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h15, h7, hc23, hlam, hphi, u3elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                              · linarith only [h0, h10, h18, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h18, h7, hc23, hlam, hphi, u3elo0]
                          · linarith only [h13, h7, hc13, hlam, hphi, u3elo0]
                        · linarith only [h0, h10, h12, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h11, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                      · linarith only [h0, h10, h24, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
                        · linarith only [h0, h10, h26, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h31 | h31
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h32 | h32
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h33 | h33
                                    · linarith only [h1, h28, h33, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h2, h29, h33, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · linarith only [h24, h29, h32, hlam]
                                · linarith only [h24, h29, h30, h31, hc45, hlam, hphi, u5elo3]
                              · linarith only [h10, h28, h29, h30, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                            · linarith only [h24, h29, h7, h9, hc12, hlam, hphi, ht23, u3elo0]
                          · linarith only [h28, h7, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h45 | h45
                            · linarith only [h2, h45, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                              · linarith only [h0, h41, h47, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h44, h47, hc23, hlam, hphi, u3elo1]
                          · linarith only [h44, h7, h9, hc13, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h0, h41, h43, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h41, h42, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h53 | h53
                      · linarith only [h0, h4, h41, h53, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h5, h53, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h7, h8, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h57 | h57
                · rcases m.htr 0 4 5 (by decide) (by decide) with h58 | h58
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                          · linarith only [h57, h62, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h64 | h64
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                              · linarith only [h57, h59, h65, h7, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h67 | h67
                                · linarith only [h0, h60, h65, h67, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h57, h67, h7, hc23, hlam, hphi, u3elo3]
                            · linarith only [h58, h62, h64, h7, hc13, hlam, hphi, u3elo3]
                        · linarith only [h57, h6, h61, h7, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h0, h5, h59, h60, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h4, h59, h7, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h57, h58, h7, hc35, hlam, hphi, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h75 | h75
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h78 | h78
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
                          · linarith only [h1, h57, h79, hc34, hlam, hphi, ht45, u5elo3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                              · linarith only [h1, h7, h76, h82, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h84 | h84
                                · linarith only [h1, h57, h76, h84, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h86 | h86
                                  · linarith only [h0, h77, h86, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h2, h81, h86, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h7, h75, h76, h79, h81, hc23, hlam, hphi, u3elo3]
                        · linarith only [h57, h6, h76, h78, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h5, h76, h77, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h4, h7, h76, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h93 | h93
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h94 | h94
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h95 | h95
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
                          · linarith only [h1, h7, h75, h96, hc34, hlam, hphi, ht45, u5elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h98 | h98
                            · linarith only [h2, h75, h98, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h100 | h100
                              · linarith only [h1, h100, h7, h93, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h102 | h102
                                · linarith only [h1, h102, h7, h75, h93, hc35, hlam, hphi, u5elo4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h104 | h104
                                  · linarith only [h104, h2, h75, h94, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h106 | h106
                                    · linarith only [h106, h7, h75, hc03, hlam, hphi, u3elo3]
                                    · linarith only [h1, h106, h7, h93, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h57, h6, h93, h95, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h5, h93, h94, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h4, h7, h93, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h4, h6, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h113 | h113
            · rcases m.htr 0 3 4 (by decide) (by decide) with h114 | h114
              · linarith only [h114, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h116 | h116
                · rcases m.htr 0 4 5 (by decide) (by decide) with h117 | h117
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h119 | h119
                      · linarith only [h0, h119, h5, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h121 | h121
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h122 | h122
                          · linarith only [h114, h122, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h124 | h124
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                              · linarith only [h0, h114, h116, h118, h125, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h0, h118, h125, h5, hc23, hlam, hphi, u3elo3]
                            · linarith only [h118, h119, h124, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h118, h121, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · linarith only [h118, h4, h5, hc12, hc24, hlam, hphi]
                  · linarith only [h117, h4, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h132 | h132
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h133 | h133
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h134 | h134
                      · linarith only [h0, h134, h5, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h136 | h136
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h137 | h137
                          · linarith only [h1, h116, h137, hc34, hlam, hphi, ht45, u5elo3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h139 | h139
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                              · linarith only [h0, h114, h133, h140, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · linarith only [h140, h4, h5, hc23, hlam, hphi, u3elo3]
                            · linarith only [h114, h132, h133, h134, h139, hc23, hlam, hphi, u3elo3]
                        · linarith only [h133, h136, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · linarith only [h133, h4, h5, hc12, hc24, hlam, hphi]
                  · linarith only [h132, h4, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h113, h4, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h148 | h148
          · rcases m.htr 0 2 5 (by decide) (by decide) with h149 | h149
            · rcases m.htr 0 3 4 (by decide) (by decide) with h150 | h150
              · rcases m.htr 0 3 5 (by decide) (by decide) with h151 | h151
                · rcases m.htr 0 4 5 (by decide) (by decide) with h152 | h152
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h153 | h153
                    · linarith only [h0, h153, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h155 | h155
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h156 | h156
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h157 | h157
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h160 | h160
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h161 | h161
                                  · linarith only [h0, h155, h161, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                  · linarith only [h158, h159, h161, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h160, h4, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h159, h4, hc02, hlam, hphi, ht23, u3elo3]
                            · linarith only [h148, h152, h158, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                          · linarith only [h150, h157, h4, hc13, hlam, hphi, u3elo2]
                        · linarith only [h149, h156, h4, hc12, hlam, hphi, ht23, u3elo2]
                      · linarith only [h148, h155, h4, hc12, hlam, hphi, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
                    · linarith only [h0, h170, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h172 | h172
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h173 | h173
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h174 | h174
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                            · linarith only [h152, h175, h2, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h179 | h179
                                  · linarith only [h152, h170, h172, h179, h2, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h181 | h181
                                    · linarith only [h148, h152, h177, h181, h3, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                    · rcases h0bigk with h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h0, h173, h177, h179, hc34, hlam, hphi, ht0b, ht45, ht5b, p183_1, u0elo0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h0, h173, h177, h179, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, p183_1, u0elo0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        rcases p183_3 (m.d 0 1) (by simp) with h187 | h187
                                        · rcases p183_3 (m.d 0 2) (by simp) with h188 | h188
                                          · linarith only [h0, h188, hlam]
                                          · linarith only [h148, h188, hlam]
                                        · linarith only [h187, h2, hlam]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        rcases p183_3 (m.d 0 1) (by simp) with h192 | h192
                                        · rcases p183_3 (m.d 0 2) (by simp) with h193 | h193
                                          · linarith only [h0, h193, hlam]
                                          · linarith only [h149, h193, hlam]
                                        · linarith only [h192, h3, hlam]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h0, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h4, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h4, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p183_1, u3elo2]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p183_1, u3elo2]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h1, hlam, p183_1]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h0, h173, h179, hc24, hlam, hphi, ht0b, ht45, ht5b, p183_1, u0elo2]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        rcases p183_3 (m.d 0 1) (by simp) with h205 | h205
                                        · rcases p183_3 (m.d 0 2) (by simp) with h206 | h206
                                          · linarith only [h206, h4, hlam]
                                          · linarith only [h148, h206, hlam]
                                        · linarith only [h2, h205, hlam]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        rcases p183_3 (m.d 0 1) (by simp) with h210 | h210
                                        · rcases p183_3 (m.d 0 2) (by simp) with h211 | h211
                                          · linarith only [h211, h4, hlam]
                                          · linarith only [h149, h211, hlam]
                                        · linarith only [h210, h3, hlam]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h2, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h148, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h150, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h152, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h3, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h149, hlam, p183_1]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h151, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h172, h177, h2, hc34, hlam, hphi, ht45, p183_1, u5elo0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [hlam, p183_0]
                                · linarith only [h178, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                              · linarith only [h177, h4, hc02, hlam, hphi, ht23, u3elo3]
                          · linarith only [h150, h152, h174, hc13, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h172, h173, hc24, hlam, hphi, ht45, u5elo2]
                      · linarith only [h148, h172, h4, hc12, hlam, hphi, ht23, u3elo2]
                · linarith only [h149, h151, h4, hc25, hlam, hphi, u5elo3]
              · linarith only [h148, h150, h4, hlam]
            · linarith only [h148, h149, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h233 | h233
            · rcases m.htr 0 3 4 (by decide) (by decide) with h234 | h234
              · rcases m.htr 0 3 5 (by decide) (by decide) with h235 | h235
                · rcases m.htr 0 4 5 (by decide) (by decide) with h236 | h236
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h237 | h237
                    · linarith only [h0, h233, h237, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h239 | h239
                      · linarith only [h148, h233, h237, h239, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h241 | h241
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h242 | h242
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h243 | h243
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h245 | h245
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h246 | h246
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h247 | h247
                                    · linarith only [h1, h242, h247, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h2, h243, h247, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · linarith only [h0, h1, h148, h241, h242, h243, h245, h246, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h148, h244, h245, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h0, h241, h244, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                            · linarith only [h236, h239, h241, h243, hc25, hlam, hphi, u5elo0]
                          · linarith only [h234, h242, h4, hc13, hlam, hphi, u3elo2]
                        · linarith only [h233, h241, h4, hc12, hlam, hphi, ht23, u3elo2]
                  · linarith only [h148, h233, h236, hc25, hlam, hphi, u5elo4]
                · linarith only [h233, h235, h4, hc25, hlam, hphi, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h258 | h258
                · rcases m.htr 0 4 5 (by decide) (by decide) with h259 | h259
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h260 | h260
                    · linarith only [h0, h234, h260, h4, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h262 | h262
                      · linarith only [h148, h260, h262, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h264 | h264
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h265 | h265
                          · linarith only [h1, h234, h265, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h267 | h267
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h268 | h268
                              · linarith only [h0, h234, h264, h268, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                              · linarith only [h0, h264, h268, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                            · linarith only [h234, h259, h265, h267, hc13, hlam, hphi, u3elo3]
                        · linarith only [h233, h264, h4, hc12, hlam, hphi, ht23, u3elo2]
                  · linarith only [h148, h233, h259, hc25, hlam, hphi, u5elo4]
                · linarith only [h233, h258, h4, hc25, hlam, hphi, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h275 | h275
              · rcases m.htr 0 3 5 (by decide) (by decide) with h276 | h276
                · rcases m.htr 0 4 5 (by decide) (by decide) with h277 | h277
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h278 | h278
                    · linarith only [h0, h233, h278, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h280 | h280
                      · linarith only [h148, h278, h280, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h282 | h282
                        · linarith only [h0, h233, h282, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h284 | h284
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h285 | h285
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h286 | h286
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h287 | h287
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h288 | h288
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h289 | h289
                                    · linarith only [h1, h284, h289, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h2, h285, h289, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · linarith only [h148, h2, h285, h288, hlam]
                                · linarith only [h148, h2, h285, h286, h287, hc45, hlam, hphi, u5elo3]
                              · linarith only [h0, h1, h284, h286, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h275, h277, h280, h285, h4, hc12, hlam, hphi, ht23, u3elo2]
                          · linarith only [h275, h284, h4, hc13, hlam, hphi, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h297 | h297
                    · linarith only [h0, h276, h297, h4, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h299 | h299
                      · linarith only [h0, h148, h277, h299, hc24, hlam, hphi, ht45, u5elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h301 | h301
                        · linarith only [h0, h148, h233, h277, h301, hc05, hlam, hphi, u5elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h303 | h303
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h304 | h304
                            · linarith only [h148, h2, h277, h304, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h306 | h306
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h307 | h307
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h308 | h308
                                  · linarith only [h0, h148, h277, h306, h308, hc12, hlam, hphi, ht23, u3elo2]
                                  · linarith only [h0, h148, h308, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                                · linarith only [h0, h307, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                              · linarith only [h0, h1, h303, h306, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h275, h303, h4, hc13, hlam, hphi, u3elo2]
                · linarith only [h275, h276, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h315 | h315
                · rcases m.htr 0 4 5 (by decide) (by decide) with h316 | h316
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h317 | h317
                    · linarith only [h0, h233, h317, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h319 | h319
                      · linarith only [h148, h317, h319, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h321 | h321
                        · linarith only [h0, h233, h321, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h323 | h323
                          · linarith only [h1, h275, h323, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h325 | h325
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h326 | h326
                              · linarith only [h233, h275, h315, h326, hc02, hlam, hphi, ht23, u3elo2]
                              · linarith only [h0, h326, h4, hc12, hlam, hphi, ht23, u3elo3]
                            · linarith only [h275, h316, h323, h325, hc13, hlam, hphi, u3elo3]
                  · linarith only [h275, h315, h316, hc35, hlam, hphi, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h331 | h331
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h332 | h332
                    · linarith only [h0, h332, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h334 | h334
                      · linarith only [h0, h148, h334, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h336 | h336
                        · linarith only [h0, h233, h336, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h338 | h338
                          · linarith only [h1, h315, h338, hc34, hlam, hphi, ht45, u5elo3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h340 | h340
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h341 | h341
                              · linarith only [h275, h341, hc03, hlam, hphi, u3elo2]
                              · linarith only [h0, h341, h4, hc12, hlam, hphi, ht23, u3elo3]
                            · linarith only [h275, h331, h334, h340, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h345 | h345
                    · linarith only [h0, h345, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h347 | h347
                      · linarith only [h0, h148, h347, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h349 | h349
                        · linarith only [h0, h233, h275, h3, h331, h349, h4, hc15, hlam, hphi, u5elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h351 | h351
                          · linarith only [h1, h275, h331, h351, hc34, hlam, hphi, ht45, u5elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h353 | h353
                            · linarith only [h0, h2, h275, h331, h353, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h355 | h355
                              · linarith only [h0, h275, h355, h4, hc12, hlam, hphi, ht23, u3elo2]
                              · linarith only [h0, h355, h4, hc12, hlam, hphi, ht23, u3elo3]
      · linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h359 | h359
      · rcases m.htr 0 2 3 (by decide) (by decide) with h360 | h360
        · rcases m.htr 0 2 4 (by decide) (by decide) with h361 | h361
          · linarith only [h0, h2, h361, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h363 | h363
            · rcases m.htr 0 3 4 (by decide) (by decide) with h364 | h364
              · linarith only [h1, h2, h364, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h366 | h366
                · rcases m.htr 0 4 5 (by decide) (by decide) with h367 | h367
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h368 | h368
                    · linarith only [h0, h2, h364, h368, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h2, h360, h364, h368, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1, h2, h367, hc13, hlam, hphi, ht34, ht45, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h372 | h372
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h373 | h373
                    · linarith only [h0, h2, h364, h373, hc23, hlam, hphi, u3elo3]
                    · linarith only [h360, h361, h373, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h2, h372, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h360, h363, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h378 | h378
          · linarith only [h0, h2, h360, h378, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h380 | h380
            · rcases m.htr 0 3 4 (by decide) (by decide) with h381 | h381
              · linarith only [h1, h2, h381, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h383 | h383
                · rcases m.htr 0 4 5 (by decide) (by decide) with h384 | h384
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h385 | h385
                    · linarith only [h0, h360, h381, h385, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h387 | h387
                      · linarith only [h1, h2, h378, h385, h387, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h389 | h389
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h390 | h390
                          · linarith only [h1, h2, h381, h390, hlam]
                          · linarith only [h1, h2, h385, h389, h390, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h360, h380, h381, h389, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1, h2, h384, hc13, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h360, h380, h383, hc25, hlam, hphi, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h396 | h396
              · linarith only [h1, h2, h396, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h398 | h398
                · rcases m.htr 0 4 5 (by decide) (by decide) with h399 | h399
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h400 | h400
                    · linarith only [h0, h360, h400, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h402 | h402
                      · linarith only [h0, h2, h360, h378, h402, hc01, hlam, hphi, ht12, ht23, u3elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h404 | h404
                        · linarith only [h1, h380, h400, h404, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h406 | h406
                          · linarith only [h1, h2, h396, h406, hlam]
                          · linarith only [h1, h2, h406, hc13, hlam, hphi, u3elo3]
                  · linarith only [h0, h2, h399, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h410 | h410
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h411 | h411
                    · linarith only [h0, h380, h411, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h413 | h413
                      · linarith only [h0, h360, h398, h413, hc24, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h415 | h415
                        · linarith only [h0, h360, h398, h415, hc25, hlam, hphi, u5elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h417 | h417
                          · linarith only [h1, h2, h396, h398, h417, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · linarith only [h1, h2, h411, h417, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1, h2, h410, hc13, hlam, hphi, ht34, ht45, u5elo4]
      · linarith only [h0, h359, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

end R2N4
