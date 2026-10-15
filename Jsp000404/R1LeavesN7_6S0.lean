import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6068000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1270 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1799 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1923 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1924 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1925 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1926 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1270 := hg1270
  have h1799 := hg1799
  linarith only [h0, h1926, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]

set_option maxHeartbeats 6068000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1270 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1799 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1923 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1924 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1925 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1926 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1928 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1270 := hg1270
  have h1799 := hg1799
  linarith only [h0, h1270, h1928, hlam]

set_option maxHeartbeats 6068000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1270 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1799 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1923 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1924 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1925 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1926 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1928 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1930 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1270 := hg1270
  have h1799 := hg1799
  linarith only [h0, h1799, h1930, hlam]

set_option maxHeartbeats 6068000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1270 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1799 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1923 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1924 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1925 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1926 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1928 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1930 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h1932 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1270 := hg1270
  have h1799 := hg1799
  rcases m.htr 1 4 5 (by decide) (by decide) with h1933 | h1933
  · rcases m.htr 2 3 4 (by decide) (by decide) with h1934 | h1934
    · rcases m.htr 2 3 5 (by decide) (by decide) with h1935 | h1935
      · rcases m.htr 2 4 5 (by decide) (by decide) with h1936 | h1936
        · rcases m.htr 3 4 5 (by decide) (by decide) with h1937 | h1937
          · linarith only [h1, h1932, h1937, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
          · linarith only [h1933, h1937, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
        · linarith only [h1270, h1933, h1936, h2, hlam]
      · linarith only [h1924, h1935, h4, hlam]
    · linarith only [h1923, h1934, h4, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h1943 | h1943
    · rcases m.htr 2 3 5 (by decide) (by decide) with h1944 | h1944
      · rcases m.htr 2 4 5 (by decide) (by decide) with h1945 | h1945
        · rcases m.htr 3 4 5 (by decide) (by decide) with h1946 | h1946
          · linarith only [h1932, h1933, h1946, hlam]
          · rcases h0bigk with h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [hlam, p1948_0]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              rcases p1948_3 (m.d 0 1) (by simp) with h1950 | h1950
              · rcases p1948_3 (m.d 0 2) (by simp) with h1951 | h1951
                · linarith only [h0, h1951, hlam]
                · rcases p1948_3 (m.d 0 3) (by simp) with h1953 | h1953
                  · linarith only [h1, h1953, hlam]
                  · linarith only [h1953, h4, hlam]
              · linarith only [h0, h1950, hlam]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [h1923, hc34, hlam, hphi, ht0b, ht45, ht5b, p1948_1, u0elo0]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [h1925, h1928, h1933, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1948_1, u0elo0]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [h1925, h1928, h1933, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1948_1, u0elo0]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [h0, hlam, p1948_0]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [hlam, p1948_0]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [h4, hlam, p1948_0]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [h1270, hlam, p1948_1]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [h1799, hlam, p1948_0]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [h1, hlam, p1948_1]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              rcases p1948_3 (m.d 0 1) (by simp) with h1966 | h1966
              · rcases p1948_3 (m.d 0 2) (by simp) with h1967 | h1967
                · linarith only [h1967, h4, hlam]
                · rcases p1948_3 (m.d 0 3) (by simp) with h1969 | h1969
                  · rcases p1948_3 (m.d 0 4) (by simp) with h1970 | h1970
                    · linarith only [h1923, h1970, hlam]
                    · linarith only [h1270, h1970, hlam]
                  · linarith only [h1969, h4, hlam]
              · linarith only [h0, h1966, hlam]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [hlam, p1948_0]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [h1925, h1928, h1933, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1948_1, u0elo2]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [h1, h1925, h1928, h1933, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1948_1, u0elo0]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [h2, hlam, p1948_0]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              rcases p1948_3 (m.d 0 1) (by simp) with h1979 | h1979
              · rcases p1948_3 (m.d 0 2) (by simp) with h1980 | h1980
                · linarith only [h1270, h1980, hlam]
                · rcases p1948_3 (m.d 0 3) (by simp) with h1982 | h1982
                  · rcases p1948_3 (m.d 0 4) (by simp) with h1983 | h1983
                    · rcases p1948_3 (m.d 0 5) (by simp) with h1984 | h1984
                      · linarith only [h1925, h1984, hlam]
                      · linarith only [h1799, h1984, hlam]
                    · linarith only [h1270, h1983, hlam]
                  · linarith only [h1982, h4, hlam]
              · linarith only [h0, h1979, hlam]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [h1923, hlam, p1948_0]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [hlam, p1948_0]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [h1925, h1928, h1933, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1948_1, u0elo3]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [h3, hlam, p1948_0]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              rcases p1948_3 (m.d 0 1) (by simp) with h1994 | h1994
              · rcases p1948_3 (m.d 0 2) (by simp) with h1995 | h1995
                · linarith only [h1799, h1995, hlam]
                · rcases p1948_3 (m.d 0 3) (by simp) with h1997 | h1997
                  · rcases p1948_3 (m.d 0 4) (by simp) with h1998 | h1998
                    · rcases p1948_3 (m.d 0 5) (by simp) with h1999 | h1999
                      · rcases h0emin with h2000 | h2000 | h2000 | h2000 | h2000
                        · rcases h2bigk with h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [hlam, p2001_0]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1948_1, p2001_1, u0elo4]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [h4, hlam, p2001_0]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [h1270, hlam, p2001_0]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [h1799, hlam, p2001_0]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [h0, hlam, p2001_0]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [hlam, p2001_0]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [h1926, hlam, p2001_0]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [h1928, hlam, p2001_0]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [h1930, hlam, p2001_0]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            rcases p2001_3 (m.d 0 2) (by simp) with h2012 | h2012
                            · linarith only [h2012, hlam, p2001_0]
                            · rcases p2001_3 (m.d 1 2) (by simp) with h2014 | h2014
                              · linarith only [h1926, h2014, hlam]
                              · rcases p2001_3 (m.d 2 3) (by simp) with h2016 | h2016
                                · rcases p2001_3 (m.d 2 4) (by simp) with h2017 | h2017
                                  · linarith only [h1943, h2017, hlam]
                                  · linarith only [h1270, h2017, hlam]
                                · linarith only [h2016, hlam, p2001_0]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            rcases p2001_3 (m.d 0 2) (by simp) with h2021 | h2021
                            · linarith only [h2021, h4, hlam]
                            · linarith only [h0, h2021, hlam]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [hlam, p2001_0]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [h1270, h1925, hc02, hc23, hlam, hphi, p1948_1, p2001_1]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [h0, h1799, hc12, hc23, hlam, hphi, p1948_1, p2001_1]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            rcases p2001_3 (m.d 0 2) (by simp) with h2027 | h2027
                            · linarith only [h2027, hlam, p2001_0]
                            · rcases p2001_3 (m.d 1 2) (by simp) with h2029 | h2029
                              · linarith only [h1928, h2029, hlam]
                              · rcases p2001_3 (m.d 2 3) (by simp) with h2031 | h2031
                                · rcases p2001_3 (m.d 2 4) (by simp) with h2032 | h2032
                                  · rcases p2001_3 (m.d 2 5) (by simp) with h2033 | h2033
                                    · linarith only [h1945, h2033, hlam]
                                    · linarith only [h1799, h2033, hlam]
                                  · linarith only [h2032, hlam, p2001_0]
                                · linarith only [h2031, h4, hlam]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            rcases p2001_3 (m.d 0 2) (by simp) with h2038 | h2038
                            · linarith only [h1270, h2038, hlam]
                            · linarith only [h0, h2038, hlam]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [h1943, hlam, p2001_1]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [hlam, p2001_0]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [h0, h1799, hc12, hc24, hlam, hphi, p1948_1, p2001_1]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            rcases p2001_3 (m.d 0 2) (by simp) with h2044 | h2044
                            · linarith only [h2044, hlam, p2001_0]
                            · rcases p2001_3 (m.d 1 2) (by simp) with h2046 | h2046
                              · linarith only [h1930, h2046, hlam]
                              · rcases p2001_3 (m.d 2 3) (by simp) with h2048 | h2048
                                · rcases p2001_3 (m.d 2 4) (by simp) with h2049 | h2049
                                  · rcases p2001_3 (m.d 2 5) (by simp) with h2050 | h2050
                                    · rcases h4bigk with h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c | h2051c
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [hlam, p2051_0]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        rcases p2051_3 (m.d 0 4) (by simp) with h2053 | h2053
                                        · rcases p2051_3 (m.d 1 4) (by simp) with h2054 | h2054
                                          · linarith only [h2, h2054, hlam]
                                          · rcases p2051_3 (m.d 2 4) (by simp) with h2056 | h2056
                                            · rcases p2051_3 (m.d 3 4) (by simp) with h2057 | h2057
                                              · linarith only [h1923, h2057, hlam]
                                              · rcases p2051_3 (m.d 4 5) (by simp) with h2059 | h2059
                                                · linarith only [h1925, h2059, hlam]
                                                · linarith only [h1933, h2059, hlam]
                                            · linarith only [h1928, h2056, hlam]
                                        · linarith only [h2, h2053, hlam]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [h1270, hlam, p2051_0]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        rcases p2051_3 (m.d 0 4) (by simp) with h2065 | h2065
                                        · rcases p2051_3 (m.d 1 4) (by simp) with h2066 | h2066
                                          · linarith only [h2, h2066, hlam]
                                          · linarith only [h1932, h2066, hlam]
                                        · linarith only [h1923, h2065, hlam]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [h1928, h1933, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2051_1, u0elo3]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [h2, hlam, p2051_1]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [hlam, p2051_0]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [h1928, hlam, p2051_0]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [h1933, hc34, hc45, hlam, hphi, p2051_1]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [h1933, hlam, p2051_0]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [h0, h1925, h1943, hc12, hc23, hlam, hphi, p1948_1, p2051_1]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        rcases p2051_3 (m.d 0 4) (by simp) with h2077 | h2077
                                        · linarith only [h1270, h2077, hlam]
                                        · linarith only [h2, h2077, hlam]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [hlam, p2051_0]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        rcases p2051_3 (m.d 0 4) (by simp) with h2081 | h2081
                                        · linarith only [h1270, h2081, hlam]
                                        · linarith only [h1923, h2081, hlam]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [h1928, h1933, hc12, hc24, hlam, hphi, p2051_1]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [h1923, hlam, p2051_1]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [h1932, hlam, p2051_0]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [h1943, hlam, p2051_0]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [hlam, p2051_0]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [h1946, hlam, p2051_0]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [h1925, hlam, p2051_0]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [h1925, hc14, hlam, hphi, ht0b, ht45, ht5b, p2051_1, u0elo3]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [h1945, hlam, p2051_0]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [h1, h1923, h1925, hc34, hlam, hphi, ht0b, ht45, ht5b, p2051_1, u0elo0]
                                      · have p2051_0 := h2051c.1
                                        have p2051_1 := h2051c.2.1
                                        have p2051_2 := h2051c.2.2.1
                                        have p2051_3 := h2051c.2.2.2
                                        linarith only [hlam, p2051_0]
                                    · linarith only [h2050, hlam, p2001_0]
                                  · linarith only [h1270, h2049, hlam]
                                · linarith only [h2048, h4, hlam]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            rcases p2001_3 (m.d 0 2) (by simp) with h2098 | h2098
                            · linarith only [h1799, h2098, hlam]
                            · linarith only [h0, h2098, hlam]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [h1944, hlam, p2001_1]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [h1945, hlam, p2001_0]
                          · have p2001_0 := h2001c.1
                            have p2001_1 := h2001c.2.1
                            have p2001_2 := h2001c.2.2.1
                            have p2001_3 := h2001c.2.2.2
                            linarith only [hlam, p2001_0]
                        · linarith only [h2000, hlam, p1948_1, u0elo4]
                        · rcases h2bigk with h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [hlam, p2105_0]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [h1, h1923, h1925, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1948_1, p2105_1, u0elo0]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [h4, hlam, p2105_0]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [h1270, hlam, p2105_0]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [h1799, hlam, p2105_0]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [h0, hlam, p2105_0]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [hlam, p2105_0]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [h1926, hlam, p2105_0]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [h1928, hlam, p2105_0]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [h1930, hlam, p2105_0]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            rcases p2105_3 (m.d 0 2) (by simp) with h2116 | h2116
                            · linarith only [h2116, hlam, p2105_0]
                            · rcases p2105_3 (m.d 1 2) (by simp) with h2118 | h2118
                              · linarith only [h1926, h2118, hlam]
                              · rcases p2105_3 (m.d 2 3) (by simp) with h2120 | h2120
                                · rcases p2105_3 (m.d 2 4) (by simp) with h2121 | h2121
                                  · linarith only [h1943, h2121, hlam]
                                  · linarith only [h1270, h2121, hlam]
                                · linarith only [h2120, hlam, p2105_0]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            rcases p2105_3 (m.d 0 2) (by simp) with h2125 | h2125
                            · linarith only [h2125, h4, hlam]
                            · linarith only [h0, h2125, hlam]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [hlam, p2105_0]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [h1270, hc02, hc23, hlam, hphi, p2105_1]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [h0, h1799, hc12, hc23, hlam, hphi, p2105_1]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            rcases p2105_3 (m.d 0 2) (by simp) with h2131 | h2131
                            · linarith only [h2131, hlam, p2105_0]
                            · rcases p2105_3 (m.d 1 2) (by simp) with h2133 | h2133
                              · linarith only [h1928, h2133, hlam]
                              · rcases p2105_3 (m.d 2 3) (by simp) with h2135 | h2135
                                · rcases p2105_3 (m.d 2 4) (by simp) with h2136 | h2136
                                  · rcases p2105_3 (m.d 2 5) (by simp) with h2137 | h2137
                                    · linarith only [h1945, h2137, hlam]
                                    · linarith only [h1799, h2137, hlam]
                                  · linarith only [h2136, hlam, p2105_0]
                                · linarith only [h2135, h4, hlam]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            rcases p2105_3 (m.d 0 2) (by simp) with h2142 | h2142
                            · linarith only [h1270, h2142, hlam]
                            · linarith only [h0, h2142, hlam]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [h1943, hlam, p2105_1]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [hlam, p2105_0]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [h0, h1799, hc12, hc24, hlam, hphi, p1948_1, p2105_1]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            rcases p2105_3 (m.d 0 2) (by simp) with h2148 | h2148
                            · linarith only [h2148, hlam, p2105_0]
                            · rcases p2105_3 (m.d 1 2) (by simp) with h2150 | h2150
                              · linarith only [h1930, h2150, hlam]
                              · rcases p2105_3 (m.d 2 3) (by simp) with h2152 | h2152
                                · rcases p2105_3 (m.d 2 4) (by simp) with h2153 | h2153
                                  · rcases p2105_3 (m.d 2 5) (by simp) with h2154 | h2154
                                    · rcases h4bigk with h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [hlam, p2155_0]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        rcases p2155_3 (m.d 0 4) (by simp) with h2157 | h2157
                                        · rcases p2155_3 (m.d 1 4) (by simp) with h2158 | h2158
                                          · linarith only [h2, h2158, hlam]
                                          · rcases p2155_3 (m.d 2 4) (by simp) with h2160 | h2160
                                            · rcases p2155_3 (m.d 3 4) (by simp) with h2161 | h2161
                                              · linarith only [h1923, h2161, hlam]
                                              · rcases p2155_3 (m.d 4 5) (by simp) with h2163 | h2163
                                                · linarith only [h1925, h2163, hlam]
                                                · linarith only [h1933, h2163, hlam]
                                            · linarith only [h1928, h2160, hlam]
                                        · linarith only [h2, h2157, hlam]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [h1270, hlam, p2155_0]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        rcases p2155_3 (m.d 0 4) (by simp) with h2169 | h2169
                                        · rcases p2155_3 (m.d 1 4) (by simp) with h2170 | h2170
                                          · linarith only [h2, h2170, hlam]
                                          · linarith only [h1932, h2170, hlam]
                                        · linarith only [h1923, h2169, hlam]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [h1, h1923, h1928, h1933, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2155_1, u0elo0]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [h2, hlam, p2155_1]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [hlam, p2155_0]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [h1928, hlam, p2155_0]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [h2, hc34, hlam, hphi, ht0b, ht45, ht5b, p2155_1, u0elo0]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [h1933, hlam, p2155_0]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [h0, h1925, h1943, hc12, hc23, hlam, hphi, p1948_1, p2155_1]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        rcases p2155_3 (m.d 0 4) (by simp) with h2181 | h2181
                                        · linarith only [h1270, h2181, hlam]
                                        · linarith only [h2, h2181, hlam]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [hlam, p2155_0]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        rcases p2155_3 (m.d 0 4) (by simp) with h2185 | h2185
                                        · linarith only [h1270, h2185, hlam]
                                        · linarith only [h1923, h2185, hlam]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [h1928, h1933, hc12, hc24, hlam, hphi, p2155_1]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [h1923, hlam, p2155_1]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [h1932, hlam, p2155_0]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [h1943, hlam, p2155_0]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [hlam, p2155_0]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [h1946, hlam, p2155_0]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [h1925, hlam, p2155_0]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [h1925, h1928, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2155_1, u0elo3]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [h1945, hlam, p2155_0]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [h1, h1923, h1925, hc34, hlam, hphi, ht0b, ht45, ht5b, p2155_1, u0elo0]
                                      · have p2155_0 := h2155c.1
                                        have p2155_1 := h2155c.2.1
                                        have p2155_2 := h2155c.2.2.1
                                        have p2155_3 := h2155c.2.2.2
                                        linarith only [hlam, p2155_0]
                                    · linarith only [h2154, hlam, p2105_0]
                                  · linarith only [h1270, h2153, hlam]
                                · linarith only [h2152, h4, hlam]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            rcases p2105_3 (m.d 0 2) (by simp) with h2202 | h2202
                            · linarith only [h1799, h2202, hlam]
                            · linarith only [h0, h2202, hlam]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [h1944, hlam, p2105_1]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [h1945, hlam, p2105_0]
                          · have p2105_0 := h2105c.1
                            have p2105_1 := h2105c.2.1
                            have p2105_2 := h2105c.2.2.1
                            have p2105_3 := h2105c.2.2.2
                            linarith only [hlam, p2105_0]
                        · rcases h2bigk with h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1948_1, p2208_1, u0elo4]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h4, hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h1270, hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h1799, hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h0, hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h1926, hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h1928, hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h1930, hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            rcases p2208_3 (m.d 0 2) (by simp) with h2219 | h2219
                            · linarith only [h2219, hlam, p2208_0]
                            · rcases p2208_3 (m.d 1 2) (by simp) with h2221 | h2221
                              · linarith only [h1926, h2221, hlam]
                              · rcases p2208_3 (m.d 2 3) (by simp) with h2223 | h2223
                                · rcases p2208_3 (m.d 2 4) (by simp) with h2224 | h2224
                                  · linarith only [h1943, h2224, hlam]
                                  · linarith only [h1270, h2224, hlam]
                                · linarith only [h2223, hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            rcases p2208_3 (m.d 0 2) (by simp) with h2228 | h2228
                            · linarith only [h2228, h4, hlam]
                            · linarith only [h0, h2228, hlam]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h1270, hc02, hc23, hlam, hphi, p2208_1]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h0, h1799, hc12, hc23, hlam, hphi, p2208_1]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            rcases p2208_3 (m.d 0 2) (by simp) with h2234 | h2234
                            · linarith only [h2234, hlam, p2208_0]
                            · rcases p2208_3 (m.d 1 2) (by simp) with h2236 | h2236
                              · linarith only [h1928, h2236, hlam]
                              · rcases p2208_3 (m.d 2 3) (by simp) with h2238 | h2238
                                · rcases p2208_3 (m.d 2 4) (by simp) with h2239 | h2239
                                  · rcases p2208_3 (m.d 2 5) (by simp) with h2240 | h2240
                                    · linarith only [h1945, h2240, hlam]
                                    · linarith only [h1799, h2240, hlam]
                                  · linarith only [h2239, hlam, p2208_0]
                                · linarith only [h2238, h4, hlam]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            rcases p2208_3 (m.d 0 2) (by simp) with h2245 | h2245
                            · linarith only [h1270, h2245, hlam]
                            · linarith only [h0, h2245, hlam]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h1943, hlam, p2208_1]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h0, h1799, hc12, hc24, hlam, hphi, p1948_1, p2208_1]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            rcases p2208_3 (m.d 0 2) (by simp) with h2251 | h2251
                            · linarith only [h2251, hlam, p2208_0]
                            · rcases p2208_3 (m.d 1 2) (by simp) with h2253 | h2253
                              · linarith only [h1930, h2253, hlam]
                              · rcases p2208_3 (m.d 2 3) (by simp) with h2255 | h2255
                                · rcases p2208_3 (m.d 2 4) (by simp) with h2256 | h2256
                                  · rcases p2208_3 (m.d 2 5) (by simp) with h2257 | h2257
                                    · rcases h4bigk with h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [hlam, p2258_0]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        rcases p2258_3 (m.d 0 4) (by simp) with h2260 | h2260
                                        · rcases p2258_3 (m.d 1 4) (by simp) with h2261 | h2261
                                          · linarith only [h2, h2261, hlam]
                                          · rcases p2258_3 (m.d 2 4) (by simp) with h2263 | h2263
                                            · rcases p2258_3 (m.d 3 4) (by simp) with h2264 | h2264
                                              · linarith only [h1923, h2264, hlam]
                                              · rcases p2258_3 (m.d 4 5) (by simp) with h2266 | h2266
                                                · linarith only [h1925, h2266, hlam]
                                                · linarith only [h1933, h2266, hlam]
                                            · linarith only [h1928, h2263, hlam]
                                        · linarith only [h2, h2260, hlam]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [h1270, hlam, p2258_0]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        rcases p2258_3 (m.d 0 4) (by simp) with h2272 | h2272
                                        · rcases p2258_3 (m.d 1 4) (by simp) with h2273 | h2273
                                          · linarith only [h2, h2273, hlam]
                                          · linarith only [h1932, h2273, hlam]
                                        · linarith only [h1923, h2272, hlam]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [h1, h1923, h1928, h1933, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2258_1, u0elo0]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [h2, hlam, p2258_1]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [hlam, p2258_0]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [h1928, hlam, p2258_0]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [h2, hc34, hlam, hphi, ht0b, ht45, ht5b, p2258_1, u0elo0]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [h1933, hlam, p2258_0]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [h1943, h2000, hc23, hlam, ht01, ht12, p2258_1]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        rcases p2258_3 (m.d 0 4) (by simp) with h2284 | h2284
                                        · linarith only [h1270, h2284, hlam]
                                        · linarith only [h2, h2284, hlam]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [hlam, p2258_0]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        rcases p2258_3 (m.d 0 4) (by simp) with h2288 | h2288
                                        · linarith only [h1270, h2288, hlam]
                                        · linarith only [h1923, h2288, hlam]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [h1928, h1933, hc12, hc24, hlam, hphi, p2258_1]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [h1923, hlam, p2258_1]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [h1932, hlam, p2258_0]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [h1943, hlam, p2258_0]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [hlam, p2258_0]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [h1946, hlam, p2258_0]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [h1925, hlam, p2258_0]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [h1, h1923, h1925, h1928, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2258_1, u0elo0]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [h1945, hlam, p2258_0]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [h1, h1923, h1925, hc34, hlam, hphi, ht0b, ht45, ht5b, p2258_1, u0elo0]
                                      · have p2258_0 := h2258c.1
                                        have p2258_1 := h2258c.2.1
                                        have p2258_2 := h2258c.2.2.1
                                        have p2258_3 := h2258c.2.2.2
                                        linarith only [hlam, p2258_0]
                                    · linarith only [h2257, hlam, p2208_0]
                                  · linarith only [h1270, h2256, hlam]
                                · linarith only [h2255, h4, hlam]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            rcases p2208_3 (m.d 0 2) (by simp) with h2305 | h2305
                            · linarith only [h1799, h2305, hlam]
                            · linarith only [h0, h2305, hlam]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h1944, hlam, p2208_1]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h1945, hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [hlam, p2208_0]
                        · rcases h2bigk with h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [hlam, p2311_0]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [h1, h1923, h1925, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1948_1, p2311_1, u0elo0]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [h4, hlam, p2311_0]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [h1270, hlam, p2311_0]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [h1799, hlam, p2311_0]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [h0, hlam, p2311_0]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [hlam, p2311_0]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [h1926, hlam, p2311_0]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [h1928, hlam, p2311_0]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [h1930, hlam, p2311_0]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            rcases p2311_3 (m.d 0 2) (by simp) with h2322 | h2322
                            · linarith only [h2322, hlam, p2311_0]
                            · rcases p2311_3 (m.d 1 2) (by simp) with h2324 | h2324
                              · linarith only [h1926, h2324, hlam]
                              · rcases p2311_3 (m.d 2 3) (by simp) with h2326 | h2326
                                · rcases p2311_3 (m.d 2 4) (by simp) with h2327 | h2327
                                  · linarith only [h1943, h2327, hlam]
                                  · linarith only [h1270, h2327, hlam]
                                · linarith only [h2326, hlam, p2311_0]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            rcases p2311_3 (m.d 0 2) (by simp) with h2331 | h2331
                            · linarith only [h2331, h4, hlam]
                            · linarith only [h0, h2331, hlam]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [hlam, p2311_0]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [h1270, hc02, hc23, hlam, hphi, p2311_1]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [h1799, h2000, hc23, hlam, ht01, ht12, p2311_1]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            rcases p2311_3 (m.d 0 2) (by simp) with h2337 | h2337
                            · linarith only [h2337, hlam, p2311_0]
                            · rcases p2311_3 (m.d 1 2) (by simp) with h2339 | h2339
                              · linarith only [h1928, h2339, hlam]
                              · rcases p2311_3 (m.d 2 3) (by simp) with h2341 | h2341
                                · rcases p2311_3 (m.d 2 4) (by simp) with h2342 | h2342
                                  · rcases p2311_3 (m.d 2 5) (by simp) with h2343 | h2343
                                    · linarith only [h1945, h2343, hlam]
                                    · linarith only [h1799, h2343, hlam]
                                  · linarith only [h2342, hlam, p2311_0]
                                · linarith only [h2341, h4, hlam]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            rcases p2311_3 (m.d 0 2) (by simp) with h2348 | h2348
                            · linarith only [h1270, h2348, hlam]
                            · linarith only [h0, h2348, hlam]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [h1943, hlam, p2311_1]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [hlam, p2311_0]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [h0, h1799, hc12, hc24, hlam, hphi, p1948_1, p2311_1]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            rcases p2311_3 (m.d 0 2) (by simp) with h2354 | h2354
                            · linarith only [h2354, hlam, p2311_0]
                            · rcases p2311_3 (m.d 1 2) (by simp) with h2356 | h2356
                              · linarith only [h1930, h2356, hlam]
                              · rcases p2311_3 (m.d 2 3) (by simp) with h2358 | h2358
                                · rcases p2311_3 (m.d 2 4) (by simp) with h2359 | h2359
                                  · rcases p2311_3 (m.d 2 5) (by simp) with h2360 | h2360
                                    · rcases h4bigk with h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [hlam, p2361_0]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        rcases p2361_3 (m.d 0 4) (by simp) with h2363 | h2363
                                        · rcases p2361_3 (m.d 1 4) (by simp) with h2364 | h2364
                                          · linarith only [h2, h2364, hlam]
                                          · rcases p2361_3 (m.d 2 4) (by simp) with h2366 | h2366
                                            · rcases p2361_3 (m.d 3 4) (by simp) with h2367 | h2367
                                              · linarith only [h1923, h2367, hlam]
                                              · rcases p2361_3 (m.d 4 5) (by simp) with h2369 | h2369
                                                · linarith only [h1925, h2369, hlam]
                                                · linarith only [h1933, h2369, hlam]
                                            · linarith only [h1928, h2366, hlam]
                                        · linarith only [h2, h2363, hlam]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [h1270, hlam, p2361_0]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        rcases p2361_3 (m.d 0 4) (by simp) with h2375 | h2375
                                        · rcases p2361_3 (m.d 1 4) (by simp) with h2376 | h2376
                                          · linarith only [h2, h2376, hlam]
                                          · linarith only [h1932, h2376, hlam]
                                        · linarith only [h1923, h2375, hlam]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [h1, h1923, h1928, h1933, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2361_1, u0elo0]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [h2, hlam, p2361_1]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [hlam, p2361_0]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [h1928, hlam, p2361_0]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [h1933, hc34, hc45, hlam, hphi, p2361_1]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [h1933, hlam, p2361_0]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [h1925, h1943, hc02, hc23, hlam, hphi, p1948_1, p2361_1]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        rcases p2361_3 (m.d 0 4) (by simp) with h2387 | h2387
                                        · linarith only [h1270, h2387, hlam]
                                        · linarith only [h2, h2387, hlam]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [hlam, p2361_0]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        rcases p2361_3 (m.d 0 4) (by simp) with h2391 | h2391
                                        · linarith only [h1270, h2391, hlam]
                                        · linarith only [h1923, h2391, hlam]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [h1928, h1933, hc12, hc24, hlam, hphi, p2361_1]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [h1923, hlam, p2361_1]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [h1932, hlam, p2361_0]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [h1943, hlam, p2361_0]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [hlam, p2361_0]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [h1946, hlam, p2361_0]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [h1925, hlam, p2361_0]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [h1, h1923, h1925, hc14, hlam, hphi, ht0b, ht45, ht5b, p2361_1, u0elo0]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [h1945, hlam, p2361_0]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [h1, h1923, h1925, hc34, hlam, hphi, ht0b, ht45, ht5b, p2361_1, u0elo0]
                                      · have p2361_0 := h2361c.1
                                        have p2361_1 := h2361c.2.1
                                        have p2361_2 := h2361c.2.2.1
                                        have p2361_3 := h2361c.2.2.2
                                        linarith only [hlam, p2361_0]
                                    · linarith only [h2360, hlam, p2311_0]
                                  · linarith only [h1270, h2359, hlam]
                                · linarith only [h2358, h4, hlam]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            rcases p2311_3 (m.d 0 2) (by simp) with h2408 | h2408
                            · linarith only [h1799, h2408, hlam]
                            · linarith only [h0, h2408, hlam]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [h1944, hlam, p2311_1]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [h1945, hlam, p2311_0]
                          · have p2311_0 := h2311c.1
                            have p2311_1 := h2311c.2.1
                            have p2311_2 := h2311c.2.2.1
                            have p2311_3 := h2311c.2.2.2
                            linarith only [hlam, p2311_0]
                      · linarith only [h1799, h1999, hlam]
                    · linarith only [h1270, h1998, hlam]
                  · linarith only [h1997, h4, hlam]
              · linarith only [h0, h1994, hlam]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [h1924, hlam, p1948_0]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [h1925, hlam, p1948_1]
            · have p1948_0 := h1948c.1
              have p1948_1 := h1948c.2.1
              have p1948_2 := h1948c.2.2.1
              have p1948_3 := h1948c.2.2.2
              linarith only [hlam, p1948_0]
        · linarith only [h0, h1, h1270, h1923, h1925, h1945, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
      · linarith only [h1923, h1925, h1928, h1933, h1944, h4, hc12, hc35, hlam, hphi, ht23]
    · linarith only [h1923, h1925, h1928, h1933, h1943, h4, hc12, hc34, hlam, hphi, ht23]

end R2N4
