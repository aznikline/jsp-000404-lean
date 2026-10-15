import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S0
import Jsp000404.R1LeavesN7_6S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6068000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0_x1_x1 (m : N7Model)
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
  rcases m.htr 1 2 5 (by decide) (by decide) with h1930 | h1930
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0_x1_x1_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg1270 hg1799 h1923 h1924 h1925 h1926 h1928 h1930
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0_x1_x1_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg1270 hg1799 h1923 h1924 h1925 h1926 h1928 h1930

set_option maxHeartbeats 6068000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0_x1 (m : N7Model)
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h1928 | h1928
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0_x1_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg1270 hg1799 h1923 h1924 h1925 h1926 h1928
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0_x1_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg1270 hg1799 h1923 h1924 h1925 h1926 h1928

set_option maxHeartbeats 6068000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0 (m : N7Model)
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h1926 | h1926
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg1270 hg1799 h1923 h1924 h1925 h1926
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg1270 hg1799 h1923 h1924 h1925 h1926

set_option maxHeartbeats 6068000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x1 (m : N7Model)
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
    (h1925 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h3180 | h3180
  · linarith only [h0, h1923, h3180, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h3182 | h3182
    · linarith only [h0, h1270, h3182, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h3184 | h3184
      · linarith only [h0, h1799, h3184, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3186 | h3186
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3187 | h3187
          · linarith only [h1925, h2, h3187, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3189 | h3189
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3190 | h3190
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3191 | h3191
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3192 | h3192
                  · linarith only [h1, h1925, h3186, h3192, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · rcases h0bigk with h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c | h3194c
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [hlam, p3194_0]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      rcases p3194_3 (m.d 0 1) (by simp) with h3196 | h3196
                      · rcases p3194_3 (m.d 0 2) (by simp) with h3197 | h3197
                        · linarith only [h0, h3197, hlam]
                        · rcases p3194_3 (m.d 0 3) (by simp) with h3199 | h3199
                          · linarith only [h1, h3199, hlam]
                          · linarith only [h3199, h4, hlam]
                      · linarith only [h0, h3196, hlam]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [h1923, hc34, hlam, hphi, ht0b, ht45, ht5b, p3194_1, u0elo0]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      rcases p3194_3 (m.d 0 1) (by simp) with h3204 | h3204
                      · rcases p3194_3 (m.d 0 2) (by simp) with h3205 | h3205
                        · linarith only [h0, h3205, hlam]
                        · rcases p3194_3 (m.d 0 3) (by simp) with h3207 | h3207
                          · linarith only [h1, h3207, hlam]
                          · linarith only [h1923, h3207, hlam]
                      · linarith only [h2, h3204, hlam]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      rcases p3194_3 (m.d 0 1) (by simp) with h3211 | h3211
                      · rcases p3194_3 (m.d 0 2) (by simp) with h3212 | h3212
                        · linarith only [h0, h3212, hlam]
                        · rcases p3194_3 (m.d 0 3) (by simp) with h3214 | h3214
                          · linarith only [h1, h3214, hlam]
                          · linarith only [h1924, h3214, hlam]
                      · linarith only [h3, h3211, hlam]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [h0, hlam, p3194_0]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [hlam, p3194_0]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [h4, hlam, p3194_0]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [h1270, hlam, p3194_1]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [h1799, hlam, p3194_0]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [h1, hlam, p3194_1]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      rcases p3194_3 (m.d 0 1) (by simp) with h3224 | h3224
                      · rcases p3194_3 (m.d 0 2) (by simp) with h3225 | h3225
                        · linarith only [h3225, h4, hlam]
                        · rcases p3194_3 (m.d 0 3) (by simp) with h3227 | h3227
                          · rcases p3194_3 (m.d 0 4) (by simp) with h3228 | h3228
                            · linarith only [h1923, h3228, hlam]
                            · linarith only [h1270, h3228, hlam]
                          · linarith only [h3227, h4, hlam]
                      · linarith only [h0, h3224, hlam]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [hlam, p3194_0]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      rcases p3194_3 (m.d 0 1) (by simp) with h3234 | h3234
                      · rcases p3194_3 (m.d 0 2) (by simp) with h3235 | h3235
                        · linarith only [h3235, h4, hlam]
                        · rcases p3194_3 (m.d 0 3) (by simp) with h3237 | h3237
                          · rcases p3194_3 (m.d 0 4) (by simp) with h3238 | h3238
                            · linarith only [h1923, h3238, hlam]
                            · rcases p3194_3 (m.d 0 5) (by simp) with h3240 | h3240
                              · linarith only [h1924, h3240, hlam]
                              · linarith only [h1925, h3240, hlam]
                          · linarith only [h1923, h3237, hlam]
                      · linarith only [h2, h3234, hlam]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      rcases p3194_3 (m.d 0 1) (by simp) with h3245 | h3245
                      · rcases p3194_3 (m.d 0 2) (by simp) with h3246 | h3246
                        · linarith only [h3246, h4, hlam]
                        · rcases p3194_3 (m.d 0 3) (by simp) with h3248 | h3248
                          · rcases p3194_3 (m.d 0 4) (by simp) with h3249 | h3249
                            · linarith only [h1923, h3249, hlam]
                            · rcases p3194_3 (m.d 0 5) (by simp) with h3251 | h3251
                              · linarith only [h1924, h3251, hlam]
                              · rcases h0emin with h3253 | h3253 | h3253 | h3253 | h3253
                                · rcases h2bigk with h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [hlam, p3254_0]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [h4, hc12, hc23, hlam, hphi, p3254_1]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [h4, hlam, p3254_0]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [h1270, hlam, p3254_0]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [h1799, hlam, p3254_0]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [h0, hlam, p3254_0]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [hlam, p3254_0]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [h3180, hlam, p3254_0]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [h3182, hlam, p3254_0]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [h3184, hlam, p3254_0]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    rcases p3254_3 (m.d 0 2) (by simp) with h3265 | h3265
                                    · linarith only [h3265, hlam, p3254_0]
                                    · rcases p3254_3 (m.d 1 2) (by simp) with h3267 | h3267
                                      · linarith only [h3180, h3267, hlam]
                                      · rcases p3254_3 (m.d 2 3) (by simp) with h3269 | h3269
                                        · rcases p3254_3 (m.d 2 4) (by simp) with h3270 | h3270
                                          · linarith only [h3189, h3270, hlam]
                                          · linarith only [h1270, h3270, hlam]
                                        · linarith only [h3269, hlam, p3254_0]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    rcases p3254_3 (m.d 0 2) (by simp) with h3274 | h3274
                                    · linarith only [h3274, h4, hlam]
                                    · linarith only [h0, h3274, hlam]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [hlam, p3254_0]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [h1925, h2, h3182, h3191, hc12, hc23, hlam, hphi, p3254_1]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [h1925, h2, h3182, h3191, hc12, hc23, hlam, hphi, p3254_1]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    rcases p3254_3 (m.d 0 2) (by simp) with h3280 | h3280
                                    · linarith only [h3280, hlam, p3254_0]
                                    · rcases p3254_3 (m.d 1 2) (by simp) with h3282 | h3282
                                      · linarith only [h3182, h3282, hlam]
                                      · rcases p3254_3 (m.d 2 3) (by simp) with h3284 | h3284
                                        · rcases p3254_3 (m.d 2 4) (by simp) with h3285 | h3285
                                          · rcases p3254_3 (m.d 2 5) (by simp) with h3286 | h3286
                                            · linarith only [h3191, h3286, hlam]
                                            · linarith only [h1799, h3286, hlam]
                                          · linarith only [h3285, hlam, p3254_0]
                                        · linarith only [h3284, h4, hlam]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    rcases p3254_3 (m.d 0 2) (by simp) with h3291 | h3291
                                    · linarith only [h1270, h3291, hlam]
                                    · linarith only [h0, h3291, hlam]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [h3189, hlam, p3254_1]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [hlam, p3254_0]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [h1925, h2, h3182, h3191, hc12, hc24, hlam, hphi, p3254_1]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    rcases p3254_3 (m.d 0 2) (by simp) with h3297 | h3297
                                    · linarith only [h3297, hlam, p3254_0]
                                    · rcases p3254_3 (m.d 1 2) (by simp) with h3299 | h3299
                                      · linarith only [h3184, h3299, hlam]
                                      · rcases p3254_3 (m.d 2 3) (by simp) with h3301 | h3301
                                        · rcases p3254_3 (m.d 2 4) (by simp) with h3302 | h3302
                                          · rcases p3254_3 (m.d 2 5) (by simp) with h3303 | h3303
                                            · rcases h4bigk with h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c | h3304c
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [hlam, p3304_0]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [h1925, h3182, hc12, hc45, hlam, hphi, ht23, ht34, p3304_1]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [h1270, hlam, p3304_0]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [h1925, hc34, hc45, hlam, hphi, p3304_1]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [h1925, hlam, p3304_0]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [h2, hlam, p3304_1]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [hlam, p3304_0]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [h3182, hlam, p3304_0]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [h2, hc34, hlam, hphi, ht0b, ht45, ht5b, p3304_1, u0elo0]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [h3187, hlam, p3304_0]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                rcases p3304_3 (m.d 0 4) (by simp) with h3315 | h3315
                                                · linarith only [h1270, h3315, hlam]
                                                · rcases p3304_3 (m.d 1 4) (by simp) with h3317 | h3317
                                                  · linarith only [h3182, h3317, hlam]
                                                  · rcases p3304_3 (m.d 2 4) (by simp) with h3319 | h3319
                                                    · rcases p3304_3 (m.d 3 4) (by simp) with h3320 | h3320
                                                      · linarith only [h3189, h3320, hlam]
                                                      · rcases p3304_3 (m.d 4 5) (by simp) with h3322 | h3322
                                                        · linarith only [h3191, h3322, hlam]
                                                        · linarith only [h1925, h3322, hlam]
                                                    · linarith only [h1270, h3319, hlam]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                rcases p3304_3 (m.d 0 4) (by simp) with h3326 | h3326
                                                · linarith only [h1270, h3326, hlam]
                                                · linarith only [h2, h3326, hlam]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [hlam, p3304_0]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                rcases p3304_3 (m.d 0 4) (by simp) with h3330 | h3330
                                                · linarith only [h1270, h3330, hlam]
                                                · linarith only [h1923, h3330, hlam]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [h0, h1270, h1925, h3189, hc12, hc23, hlam, hphi, p3304_1]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [h1923, hlam, p3304_1]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [h3186, hlam, p3304_0]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [h3189, hlam, p3304_0]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [hlam, p3304_0]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [h3192, hlam, p3304_0]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [h0, h1270, h3189, h3191, hc12, hc23, hlam, hphi, p3304_1]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [h3182, h3189, h3191, hc12, hc23, hlam, hphi, p3304_1]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [h3191, hlam, p3304_0]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                rcases p3304_3 (m.d 0 4) (by simp) with h3342 | h3342
                                                · linarith only [h1925, h3342, hlam]
                                                · linarith only [h1923, h3342, hlam]
                                              · have p3304_0 := h3304c.1
                                                have p3304_1 := h3304c.2.1
                                                have p3304_2 := h3304c.2.2.1
                                                have p3304_3 := h3304c.2.2.2
                                                linarith only [hlam, p3304_0]
                                            · linarith only [h3303, hlam, p3254_0]
                                          · linarith only [h1270, h3302, hlam]
                                        · linarith only [h3301, h4, hlam]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    rcases p3254_3 (m.d 0 2) (by simp) with h3349 | h3349
                                    · linarith only [h1799, h3349, hlam]
                                    · linarith only [h0, h3349, hlam]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [h3190, hlam, p3254_1]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [h3191, hlam, p3254_0]
                                  · have p3254_0 := h3254c.1
                                    have p3254_1 := h3254c.2.1
                                    have p3254_2 := h3254c.2.2.1
                                    have p3254_3 := h3254c.2.2.2
                                    linarith only [hlam, p3254_0]
                                · linarith only [h1, h1270, h1925, h3253, hlam, p3194_1, u0elo0]
                                · rcases h2bigk with h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h1, h1270, h1925, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3194_1, p3356_1, u0elo0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h4, hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h1270, hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h1799, hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h0, hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3180, hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3182, hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3184, hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    rcases p3356_3 (m.d 0 2) (by simp) with h3367 | h3367
                                    · linarith only [h3367, hlam, p3356_0]
                                    · rcases p3356_3 (m.d 1 2) (by simp) with h3369 | h3369
                                      · linarith only [h3180, h3369, hlam]
                                      · rcases p3356_3 (m.d 2 3) (by simp) with h3371 | h3371
                                        · rcases p3356_3 (m.d 2 4) (by simp) with h3372 | h3372
                                          · linarith only [h3189, h3372, hlam]
                                          · linarith only [h1270, h3372, hlam]
                                        · linarith only [h3371, hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    rcases p3356_3 (m.d 0 2) (by simp) with h3376 | h3376
                                    · linarith only [h3376, h4, hlam]
                                    · linarith only [h0, h3376, hlam]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h1270, hc02, hc23, hlam, hphi, p3356_1]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h0, h1799, hc12, hc23, hlam, hphi, p3356_1]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    rcases p3356_3 (m.d 0 2) (by simp) with h3382 | h3382
                                    · linarith only [h3382, hlam, p3356_0]
                                    · rcases p3356_3 (m.d 1 2) (by simp) with h3384 | h3384
                                      · linarith only [h3182, h3384, hlam]
                                      · rcases p3356_3 (m.d 2 3) (by simp) with h3386 | h3386
                                        · rcases p3356_3 (m.d 2 4) (by simp) with h3387 | h3387
                                          · rcases p3356_3 (m.d 2 5) (by simp) with h3388 | h3388
                                            · linarith only [h3191, h3388, hlam]
                                            · linarith only [h1799, h3388, hlam]
                                          · linarith only [h3387, hlam, p3356_0]
                                        · linarith only [h3386, h4, hlam]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    rcases p3356_3 (m.d 0 2) (by simp) with h3393 | h3393
                                    · linarith only [h1270, h3393, hlam]
                                    · linarith only [h0, h3393, hlam]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3189, hlam, p3356_1]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h1925, h2, h3182, h3191, hc12, hc24, hlam, hphi, p3356_1]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    rcases p3356_3 (m.d 0 2) (by simp) with h3399 | h3399
                                    · linarith only [h3399, hlam, p3356_0]
                                    · rcases p3356_3 (m.d 1 2) (by simp) with h3401 | h3401
                                      · linarith only [h3184, h3401, hlam]
                                      · rcases p3356_3 (m.d 2 3) (by simp) with h3403 | h3403
                                        · rcases p3356_3 (m.d 2 4) (by simp) with h3404 | h3404
                                          · rcases p3356_3 (m.d 2 5) (by simp) with h3405 | h3405
                                            · rcases h4bigk with h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c | h3406c
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [hlam, p3406_0]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [h1925, h3182, hc12, hc45, hlam, hphi, ht23, ht34, p3406_1]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [h1270, hlam, p3406_0]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [h1925, hc34, hc45, hlam, hphi, p3406_1]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [h1925, hlam, p3406_0]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [h2, hlam, p3406_1]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [hlam, p3406_0]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [h3182, hlam, p3406_0]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [h2, hc34, hlam, hphi, ht0b, ht45, ht5b, p3406_1, u0elo0]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [h3187, hlam, p3406_0]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                rcases p3406_3 (m.d 0 4) (by simp) with h3417 | h3417
                                                · linarith only [h1270, h3417, hlam]
                                                · rcases p3406_3 (m.d 1 4) (by simp) with h3419 | h3419
                                                  · linarith only [h3182, h3419, hlam]
                                                  · rcases p3406_3 (m.d 2 4) (by simp) with h3421 | h3421
                                                    · rcases p3406_3 (m.d 3 4) (by simp) with h3422 | h3422
                                                      · linarith only [h3189, h3422, hlam]
                                                      · rcases p3406_3 (m.d 4 5) (by simp) with h3424 | h3424
                                                        · linarith only [h3191, h3424, hlam]
                                                        · linarith only [h1925, h3424, hlam]
                                                    · linarith only [h1270, h3421, hlam]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                rcases p3406_3 (m.d 0 4) (by simp) with h3428 | h3428
                                                · linarith only [h1270, h3428, hlam]
                                                · linarith only [h2, h3428, hlam]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [hlam, p3406_0]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                rcases p3406_3 (m.d 0 4) (by simp) with h3432 | h3432
                                                · linarith only [h1270, h3432, hlam]
                                                · linarith only [h1923, h3432, hlam]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [h0, h1270, h1925, h3189, hc12, hc23, hlam, hphi, p3406_1]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [h1923, hlam, p3406_1]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [h3186, hlam, p3406_0]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [h3189, hlam, p3406_0]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [hlam, p3406_0]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [h3192, hlam, p3406_0]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [h0, h1270, h3189, h3191, hc12, hc23, hlam, hphi, p3406_1]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [h3182, h3189, h3191, hc12, hc23, hlam, hphi, p3406_1]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [h3191, hlam, p3406_0]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                rcases p3406_3 (m.d 0 4) (by simp) with h3444 | h3444
                                                · linarith only [h1925, h3444, hlam]
                                                · linarith only [h1923, h3444, hlam]
                                              · have p3406_0 := h3406c.1
                                                have p3406_1 := h3406c.2.1
                                                have p3406_2 := h3406c.2.2.1
                                                have p3406_3 := h3406c.2.2.2
                                                linarith only [hlam, p3406_0]
                                            · linarith only [h3405, hlam, p3356_0]
                                          · linarith only [h1270, h3404, hlam]
                                        · linarith only [h3403, h4, hlam]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    rcases p3356_3 (m.d 0 2) (by simp) with h3451 | h3451
                                    · linarith only [h1799, h3451, hlam]
                                    · linarith only [h0, h3451, hlam]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3190, hlam, p3356_1]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3191, hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [hlam, p3356_0]
                                · linarith only [h1, h1925, h3253, hlam, p3194_1, u0elo0]
                                · linarith only [h1, h3253, hlam, p3194_1, u0elo0]
                          · linarith only [h1924, h3248, hlam]
                      · linarith only [h3, h3245, hlam]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [h2, hlam, p3194_0]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [h0, h1925, h3189, h3191, hc12, hc23, hlam, hphi, p3194_1]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [h1923, hlam, p3194_0]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [hlam, p3194_0]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [h1925, hlam, p3194_0]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [h3, hlam, p3194_0]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [h0, h1925, h3189, h3191, hc12, hc23, hlam, hphi, p3194_1]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [h1924, hlam, p3194_0]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [h1925, h2, h3182, h3189, h3191, hc12, hc23, hlam, hphi, p3194_1]
                    · have p3194_0 := h3194c.1
                      have p3194_1 := h3194c.2.1
                      have p3194_2 := h3194c.2.2.1
                      have p3194_3 := h3194c.2.2.2
                      linarith only [hlam, p3194_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3471 | h3471
                  · linarith only [h1, h3186, h3191, h3471, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases h0bigk with h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c | h3473c
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      linarith only [hlam, p3473_0]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      rcases p3473_3 (m.d 0 1) (by simp) with h3475 | h3475
                      · rcases p3473_3 (m.d 0 2) (by simp) with h3476 | h3476
                        · linarith only [h0, h3476, hlam]
                        · rcases p3473_3 (m.d 0 3) (by simp) with h3478 | h3478
                          · linarith only [h1, h3478, hlam]
                          · linarith only [h3478, h4, hlam]
                      · linarith only [h0, h3475, hlam]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      linarith only [h1924, hc35, hlam, hphi, ht0b, ht5b, p3473_1, u0elo0]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      rcases p3473_3 (m.d 0 1) (by simp) with h3483 | h3483
                      · rcases p3473_3 (m.d 0 2) (by simp) with h3484 | h3484
                        · linarith only [h0, h3484, hlam]
                        · rcases p3473_3 (m.d 0 3) (by simp) with h3486 | h3486
                          · linarith only [h1, h3486, hlam]
                          · linarith only [h1923, h3486, hlam]
                      · linarith only [h2, h3483, hlam]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      rcases p3473_3 (m.d 0 1) (by simp) with h3490 | h3490
                      · rcases p3473_3 (m.d 0 2) (by simp) with h3491 | h3491
                        · linarith only [h0, h3491, hlam]
                        · rcases p3473_3 (m.d 0 3) (by simp) with h3493 | h3493
                          · linarith only [h1, h3493, hlam]
                          · linarith only [h1924, h3493, hlam]
                      · linarith only [h3, h3490, hlam]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      linarith only [h0, hlam, p3473_0]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      linarith only [hlam, p3473_0]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      linarith only [h4, hlam, p3473_0]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      linarith only [h1270, hlam, p3473_1]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      linarith only [h1799, hlam, p3473_0]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      linarith only [h1, hlam, p3473_1]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      rcases p3473_3 (m.d 0 1) (by simp) with h3503 | h3503
                      · rcases p3473_3 (m.d 0 2) (by simp) with h3504 | h3504
                        · linarith only [h3504, h4, hlam]
                        · rcases p3473_3 (m.d 0 3) (by simp) with h3506 | h3506
                          · rcases p3473_3 (m.d 0 4) (by simp) with h3507 | h3507
                            · linarith only [h1923, h3507, hlam]
                            · linarith only [h1270, h3507, hlam]
                          · linarith only [h3506, h4, hlam]
                      · linarith only [h0, h3503, hlam]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      linarith only [hlam, p3473_0]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      rcases p3473_3 (m.d 0 1) (by simp) with h3513 | h3513
                      · rcases p3473_3 (m.d 0 2) (by simp) with h3514 | h3514
                        · linarith only [h3514, h4, hlam]
                        · rcases p3473_3 (m.d 0 3) (by simp) with h3516 | h3516
                          · rcases p3473_3 (m.d 0 4) (by simp) with h3517 | h3517
                            · linarith only [h1923, h3517, hlam]
                            · rcases p3473_3 (m.d 0 5) (by simp) with h3519 | h3519
                              · linarith only [h1924, h3519, hlam]
                              · linarith only [h1925, h3519, hlam]
                          · linarith only [h1923, h3516, hlam]
                      · linarith only [h2, h3513, hlam]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      rcases p3473_3 (m.d 0 1) (by simp) with h3524 | h3524
                      · rcases p3473_3 (m.d 0 2) (by simp) with h3525 | h3525
                        · linarith only [h3525, h4, hlam]
                        · rcases p3473_3 (m.d 0 3) (by simp) with h3527 | h3527
                          · rcases p3473_3 (m.d 0 4) (by simp) with h3528 | h3528
                            · linarith only [h1923, h3528, hlam]
                            · rcases p3473_3 (m.d 0 5) (by simp) with h3530 | h3530
                              · linarith only [h1924, h3530, hlam]
                              · rcases h0emin with h3532 | h3532 | h3532 | h3532 | h3532
                                · rcases h2bigk with h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c | h3533c
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [hlam, p3533_0]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [h1270, hc12, hc24, hlam, hphi, p3533_1]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [h4, hlam, p3533_0]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [h1270, hlam, p3533_0]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [h1799, hlam, p3533_0]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [h0, hlam, p3533_0]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [hlam, p3533_0]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [h3180, hlam, p3533_0]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [h3182, hlam, p3533_0]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [h3184, hlam, p3533_0]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    rcases p3533_3 (m.d 0 2) (by simp) with h3544 | h3544
                                    · linarith only [h3544, hlam, p3533_0]
                                    · rcases p3533_3 (m.d 1 2) (by simp) with h3546 | h3546
                                      · linarith only [h3180, h3546, hlam]
                                      · rcases p3533_3 (m.d 2 3) (by simp) with h3548 | h3548
                                        · rcases p3533_3 (m.d 2 4) (by simp) with h3549 | h3549
                                          · linarith only [h3189, h3549, hlam]
                                          · linarith only [h1270, h3549, hlam]
                                        · linarith only [h3548, hlam, p3533_0]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    rcases p3533_3 (m.d 0 2) (by simp) with h3553 | h3553
                                    · linarith only [h3553, h4, hlam]
                                    · linarith only [h0, h3553, hlam]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [hlam, p3533_0]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [h1270, hc02, hc23, hlam, hphi, p3533_1]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [h0, h1799, hc12, hc23, hlam, hphi, p3533_1]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [h0, h3191, hc12, hc45, hlam, hphi, ht23, ht34, p3533_1]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [h3191, hc12, hc45, hlam, hphi, ht23, ht34, p3533_1]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [h3189, hlam, p3533_1]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [hlam, p3533_0]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [h3191, hlam, p3533_1]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    rcases p3533_3 (m.d 0 2) (by simp) with h3564 | h3564
                                    · linarith only [h3564, hlam, p3533_0]
                                    · rcases p3533_3 (m.d 1 2) (by simp) with h3566 | h3566
                                      · linarith only [h3184, h3566, hlam]
                                      · rcases p3533_3 (m.d 2 3) (by simp) with h3568 | h3568
                                        · rcases p3533_3 (m.d 2 4) (by simp) with h3569 | h3569
                                          · linarith only [h3191, h3569, hlam]
                                          · linarith only [h1270, h3569, hlam]
                                        · linarith only [h3568, h4, hlam]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    rcases p3533_3 (m.d 0 2) (by simp) with h3573 | h3573
                                    · linarith only [h1799, h3573, hlam]
                                    · linarith only [h0, h3573, hlam]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [h3190, hlam, p3533_1]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [h0, h1270, hc12, hc25, hlam, hphi, p3533_1]
                                  · have p3533_0 := h3533c.1
                                    have p3533_1 := h3533c.2.1
                                    have p3533_2 := h3533c.2.2.1
                                    have p3533_3 := h3533c.2.2.2
                                    linarith only [hlam, p3533_0]
                                · linarith only [h1, h1799, h3532, hlam, p3473_1, u0elo0]
                                · rcases h2bigk with h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [hlam, p3580_0]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [h1, h1270, h1925, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3473_1, p3580_1, u0elo0]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [h4, hlam, p3580_0]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [h1270, hlam, p3580_0]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [h1799, hlam, p3580_0]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [h0, hlam, p3580_0]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [hlam, p3580_0]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [h3180, hlam, p3580_0]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [h3182, hlam, p3580_0]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [h3184, hlam, p3580_0]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    rcases p3580_3 (m.d 0 2) (by simp) with h3591 | h3591
                                    · linarith only [h3591, hlam, p3580_0]
                                    · rcases p3580_3 (m.d 1 2) (by simp) with h3593 | h3593
                                      · linarith only [h3180, h3593, hlam]
                                      · rcases p3580_3 (m.d 2 3) (by simp) with h3595 | h3595
                                        · rcases p3580_3 (m.d 2 4) (by simp) with h3596 | h3596
                                          · linarith only [h3189, h3596, hlam]
                                          · linarith only [h1270, h3596, hlam]
                                        · linarith only [h3595, hlam, p3580_0]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    rcases p3580_3 (m.d 0 2) (by simp) with h3600 | h3600
                                    · linarith only [h3600, h4, hlam]
                                    · linarith only [h0, h3600, hlam]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [hlam, p3580_0]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [h1270, hc02, hc23, hlam, hphi, p3580_1]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [h0, h1799, hc12, hc23, hlam, hphi, p3580_1]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [h0, h3191, hc12, hc45, hlam, hphi, ht23, ht34, p3580_1]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [h3191, hc12, hc45, hlam, hphi, ht23, ht34, p3580_1]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [h3189, hlam, p3580_1]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [hlam, p3580_0]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [h3191, hlam, p3580_1]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    rcases p3580_3 (m.d 0 2) (by simp) with h3611 | h3611
                                    · linarith only [h3611, hlam, p3580_0]
                                    · rcases p3580_3 (m.d 1 2) (by simp) with h3613 | h3613
                                      · linarith only [h3184, h3613, hlam]
                                      · rcases p3580_3 (m.d 2 3) (by simp) with h3615 | h3615
                                        · rcases p3580_3 (m.d 2 4) (by simp) with h3616 | h3616
                                          · linarith only [h3191, h3616, hlam]
                                          · linarith only [h1270, h3616, hlam]
                                        · linarith only [h3615, h4, hlam]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    rcases p3580_3 (m.d 0 2) (by simp) with h3620 | h3620
                                    · linarith only [h1799, h3620, hlam]
                                    · linarith only [h0, h3620, hlam]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [h3190, hlam, p3580_1]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [h0, h1270, hc12, hc25, hlam, hphi, p3580_1]
                                  · have p3580_0 := h3580c.1
                                    have p3580_1 := h3580c.2.1
                                    have p3580_2 := h3580c.2.2.1
                                    have p3580_3 := h3580c.2.2.2
                                    linarith only [hlam, p3580_0]
                                · linarith only [h1, h1925, h3532, hlam, p3473_1, u0elo0]
                                · linarith only [h1, h3532, hlam, p3473_1, u0elo0]
                          · linarith only [h1924, h3527, hlam]
                      · linarith only [h3, h3524, hlam]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      linarith only [h2, hlam, p3473_0]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      linarith only [h0, h1925, hc12, hc45, hlam, hphi, ht23, ht34, p3473_1]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      linarith only [h1923, hlam, p3473_0]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      linarith only [hlam, p3473_0]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      linarith only [h1925, hlam, p3473_0]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      linarith only [h3, hlam, p3473_0]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      rcases p3473_3 (m.d 0 1) (by simp) with h3636 | h3636
                      · rcases p3473_3 (m.d 0 2) (by simp) with h3637 | h3637
                        · linarith only [h1799, h3637, hlam]
                        · rcases p3473_3 (m.d 0 3) (by simp) with h3639 | h3639
                          · rcases p3473_3 (m.d 0 4) (by simp) with h3640 | h3640
                            · linarith only [h1925, h3640, hlam]
                            · linarith only [h1270, h3640, hlam]
                          · linarith only [h3639, h4, hlam]
                      · linarith only [h0, h3636, hlam]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      linarith only [h1924, hlam, p3473_0]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      rcases p3473_3 (m.d 0 1) (by simp) with h3646 | h3646
                      · rcases p3473_3 (m.d 0 2) (by simp) with h3647 | h3647
                        · linarith only [h1799, h3647, hlam]
                        · rcases p3473_3 (m.d 0 3) (by simp) with h3649 | h3649
                          · rcases p3473_3 (m.d 0 4) (by simp) with h3650 | h3650
                            · linarith only [h1925, h3650, hlam]
                            · rcases p3473_3 (m.d 0 5) (by simp) with h3652 | h3652
                              · rcases h0emin with h3653 | h3653 | h3653 | h3653 | h3653
                                · rcases h2bigk with h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h4, hc12, hc23, hlam, hphi, p3654_1]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h4, hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h1270, hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h1799, hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h0, hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h3180, hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h3182, hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h3184, hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    rcases p3654_3 (m.d 0 2) (by simp) with h3665 | h3665
                                    · linarith only [h3665, hlam, p3654_0]
                                    · rcases p3654_3 (m.d 1 2) (by simp) with h3667 | h3667
                                      · linarith only [h3180, h3667, hlam]
                                      · rcases p3654_3 (m.d 2 3) (by simp) with h3669 | h3669
                                        · rcases p3654_3 (m.d 2 4) (by simp) with h3670 | h3670
                                          · linarith only [h3189, h3670, hlam]
                                          · linarith only [h1270, h3670, hlam]
                                        · linarith only [h3669, hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    rcases p3654_3 (m.d 0 2) (by simp) with h3674 | h3674
                                    · linarith only [h3674, h4, hlam]
                                    · linarith only [h0, h3674, hlam]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h1270, hc02, hc23, hlam, hphi, p3654_1]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h0, h1799, hc12, hc23, hlam, hphi, p3654_1]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h0, h3191, hc12, hc45, hlam, hphi, ht23, ht34, p3654_1]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h3191, hc12, hc45, hlam, hphi, ht23, ht34, p3654_1]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h3189, hlam, p3654_1]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h3191, hlam, p3654_1]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    rcases p3654_3 (m.d 0 2) (by simp) with h3685 | h3685
                                    · linarith only [h3685, hlam, p3654_0]
                                    · rcases p3654_3 (m.d 1 2) (by simp) with h3687 | h3687
                                      · linarith only [h3184, h3687, hlam]
                                      · rcases p3654_3 (m.d 2 3) (by simp) with h3689 | h3689
                                        · rcases p3654_3 (m.d 2 4) (by simp) with h3690 | h3690
                                          · linarith only [h3191, h3690, hlam]
                                          · linarith only [h1270, h3690, hlam]
                                        · linarith only [h3689, h4, hlam]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    rcases p3654_3 (m.d 0 2) (by simp) with h3694 | h3694
                                    · linarith only [h1799, h3694, hlam]
                                    · linarith only [h0, h3694, hlam]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h3190, hlam, p3654_1]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h0, h1270, hc12, hc25, hlam, hphi, p3654_1]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [hlam, p3654_0]
                                · linarith only [h1270, h3653, hlam, p3473_1, u0elo4]
                                · rcases h2bigk with h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c | h3701c
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [hlam, p3701_0]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [h1, h1270, h1924, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3473_1, p3701_1, u0elo0]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [h4, hlam, p3701_0]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [h1270, hlam, p3701_0]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [h1799, hlam, p3701_0]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [h0, hlam, p3701_0]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [hlam, p3701_0]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [h3180, hlam, p3701_0]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [h3182, hlam, p3701_0]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [h3184, hlam, p3701_0]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    rcases p3701_3 (m.d 0 2) (by simp) with h3712 | h3712
                                    · linarith only [h3712, hlam, p3701_0]
                                    · rcases p3701_3 (m.d 1 2) (by simp) with h3714 | h3714
                                      · linarith only [h3180, h3714, hlam]
                                      · rcases p3701_3 (m.d 2 3) (by simp) with h3716 | h3716
                                        · rcases p3701_3 (m.d 2 4) (by simp) with h3717 | h3717
                                          · linarith only [h3189, h3717, hlam]
                                          · linarith only [h1270, h3717, hlam]
                                        · linarith only [h3716, hlam, p3701_0]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    rcases p3701_3 (m.d 0 2) (by simp) with h3721 | h3721
                                    · linarith only [h3721, h4, hlam]
                                    · linarith only [h0, h3721, hlam]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [hlam, p3701_0]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [h1270, hc02, hc23, hlam, hphi, p3701_1]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [h0, h1799, hc12, hc23, hlam, hphi, p3701_1]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [h0, h3191, hc12, hc45, hlam, hphi, ht23, ht34, p3701_1]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [h3191, hc12, hc45, hlam, hphi, ht23, ht34, p3701_1]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [h3189, hlam, p3701_1]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [hlam, p3701_0]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [h3191, hlam, p3701_1]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    rcases p3701_3 (m.d 0 2) (by simp) with h3732 | h3732
                                    · linarith only [h3732, hlam, p3701_0]
                                    · rcases p3701_3 (m.d 1 2) (by simp) with h3734 | h3734
                                      · linarith only [h3184, h3734, hlam]
                                      · rcases p3701_3 (m.d 2 3) (by simp) with h3736 | h3736
                                        · rcases p3701_3 (m.d 2 4) (by simp) with h3737 | h3737
                                          · linarith only [h3191, h3737, hlam]
                                          · linarith only [h1270, h3737, hlam]
                                        · linarith only [h3736, h4, hlam]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    rcases p3701_3 (m.d 0 2) (by simp) with h3741 | h3741
                                    · linarith only [h1799, h3741, hlam]
                                    · linarith only [h0, h3741, hlam]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [h3190, hlam, p3701_1]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [h0, h1270, hc12, hc25, hlam, hphi, p3701_1]
                                  · have p3701_0 := h3701c.1
                                    have p3701_1 := h3701c.2.1
                                    have p3701_2 := h3701c.2.2.1
                                    have p3701_3 := h3701c.2.2.2
                                    linarith only [hlam, p3701_0]
                                · linarith only [h1, h1924, h3653, hlam, p3473_1, u0elo0]
                                · rcases h2bigk with h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [hlam, p3748_0]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [h1270, hc12, hc24, hlam, hphi, p3748_1]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [h4, hlam, p3748_0]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [h1270, hlam, p3748_0]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [h1799, hlam, p3748_0]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [h0, hlam, p3748_0]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [hlam, p3748_0]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [h3180, hlam, p3748_0]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [h3182, hlam, p3748_0]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [h3184, hlam, p3748_0]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    rcases p3748_3 (m.d 0 2) (by simp) with h3759 | h3759
                                    · linarith only [h3759, hlam, p3748_0]
                                    · rcases p3748_3 (m.d 1 2) (by simp) with h3761 | h3761
                                      · linarith only [h3180, h3761, hlam]
                                      · rcases p3748_3 (m.d 2 3) (by simp) with h3763 | h3763
                                        · rcases p3748_3 (m.d 2 4) (by simp) with h3764 | h3764
                                          · linarith only [h3189, h3764, hlam]
                                          · linarith only [h1270, h3764, hlam]
                                        · linarith only [h3763, hlam, p3748_0]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    rcases p3748_3 (m.d 0 2) (by simp) with h3768 | h3768
                                    · linarith only [h3768, h4, hlam]
                                    · linarith only [h0, h3768, hlam]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [hlam, p3748_0]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [h1270, hc02, hc23, hlam, hphi, p3748_1]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [h0, h1799, hc12, hc23, hlam, hphi, p3748_1]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [h0, h3191, hc12, hc45, hlam, hphi, ht23, ht34, p3748_1]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [h3191, hc12, hc45, hlam, hphi, ht23, ht34, p3748_1]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [h3189, hlam, p3748_1]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [hlam, p3748_0]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [h3191, hlam, p3748_1]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    rcases p3748_3 (m.d 0 2) (by simp) with h3779 | h3779
                                    · linarith only [h3779, hlam, p3748_0]
                                    · rcases p3748_3 (m.d 1 2) (by simp) with h3781 | h3781
                                      · linarith only [h3184, h3781, hlam]
                                      · rcases p3748_3 (m.d 2 3) (by simp) with h3783 | h3783
                                        · rcases p3748_3 (m.d 2 4) (by simp) with h3784 | h3784
                                          · linarith only [h3191, h3784, hlam]
                                          · linarith only [h1270, h3784, hlam]
                                        · linarith only [h3783, h4, hlam]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    rcases p3748_3 (m.d 0 2) (by simp) with h3788 | h3788
                                    · linarith only [h1799, h3788, hlam]
                                    · linarith only [h0, h3788, hlam]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [h3190, hlam, p3748_1]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [h0, h1270, hc12, hc25, hlam, hphi, p3748_1]
                                  · have p3748_0 := h3748c.1
                                    have p3748_1 := h3748c.2.1
                                    have p3748_2 := h3748c.2.2.1
                                    have p3748_3 := h3748c.2.2.2
                                    linarith only [hlam, p3748_0]
                              · linarith only [h1925, h3652, hlam]
                          · linarith only [h1923, h3649, hlam]
                      · linarith only [h2, h3646, hlam]
                    · have p3473_0 := h3473c.1
                      have p3473_1 := h3473c.2.1
                      have p3473_2 := h3473c.2.2.1
                      have p3473_3 := h3473c.2.2.2
                      linarith only [hlam, p3473_0]
              · linarith only [h1924, h3190, h4, hlam]
            · linarith only [h1923, h3189, h4, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3800 | h3800
          · linarith only [h1923, h1925, h2, h3180, h3186, h3800, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3802 | h3802
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3803 | h3803
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3804 | h3804
                · linarith only [h1923, h1925, h3180, h3186, h3804, hc12, hc24, hlam, hphi]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3806 | h3806
                  · linarith only [h1923, h3804, h3806, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · rcases h0bigk with h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c | h3808c
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [hlam, p3808_0]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      rcases p3808_3 (m.d 0 1) (by simp) with h3810 | h3810
                      · rcases p3808_3 (m.d 0 2) (by simp) with h3811 | h3811
                        · linarith only [h0, h3811, hlam]
                        · rcases p3808_3 (m.d 0 3) (by simp) with h3813 | h3813
                          · linarith only [h1, h3813, hlam]
                          · linarith only [h3813, h4, hlam]
                      · linarith only [h0, h3810, hlam]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [h1924, h3180, h3186, h3806, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3808_1, u0elo0]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [h1923, h3180, h3186, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3808_1, u0elo0]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [h1924, h3180, h3186, h3806, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3808_1, u0elo0]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [h0, hlam, p3808_0]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [hlam, p3808_0]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [h4, hlam, p3808_0]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [h1270, hlam, p3808_1]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [h1799, hlam, p3808_0]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [h1, hlam, p3808_1]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      rcases p3808_3 (m.d 0 1) (by simp) with h3826 | h3826
                      · rcases p3808_3 (m.d 0 2) (by simp) with h3827 | h3827
                        · linarith only [h3827, h4, hlam]
                        · rcases p3808_3 (m.d 0 3) (by simp) with h3829 | h3829
                          · rcases p3808_3 (m.d 0 4) (by simp) with h3830 | h3830
                            · linarith only [h1923, h3830, hlam]
                            · linarith only [h1270, h3830, hlam]
                          · linarith only [h3829, h4, hlam]
                      · linarith only [h0, h3826, hlam]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [hlam, p3808_0]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [h1923, h3180, h3186, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3808_1, u0elo2]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [h1, h1924, h3180, h3186, h3806, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3808_1, u0elo0]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [h2, hlam, p3808_0]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [h0, h1270, h3804, hc12, hc45, hlam, hphi, ht23, ht34, p3808_1]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [h1923, hlam, p3808_0]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [hlam, p3808_0]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [h1925, hlam, p3808_0]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [h3, hlam, p3808_0]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      rcases p3808_3 (m.d 0 1) (by simp) with h3844 | h3844
                      · rcases p3808_3 (m.d 0 2) (by simp) with h3845 | h3845
                        · linarith only [h1799, h3845, hlam]
                        · rcases p3808_3 (m.d 0 3) (by simp) with h3847 | h3847
                          · rcases p3808_3 (m.d 0 4) (by simp) with h3848 | h3848
                            · linarith only [h1925, h3848, hlam]
                            · linarith only [h1270, h3848, hlam]
                          · linarith only [h3847, h4, hlam]
                      · linarith only [h0, h3844, hlam]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [h1924, hlam, p3808_0]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [h1923, h3180, h3186, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3808_1, u0elo4]
                    · have p3808_0 := h3808c.1
                      have p3808_1 := h3808c.2.1
                      have p3808_2 := h3808c.2.2.1
                      have p3808_3 := h3808c.2.2.2
                      linarith only [hlam, p3808_0]
              · linarith only [h1923, h3180, h3186, h3803, h4, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h1923, h3802, h4, hlam]

set_option maxHeartbeats 6068000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0 (m : N7Model)
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h1925 | h1925
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg1270 hg1799 h1923 h1924 h1925
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg1270 hg1799 h1923 h1924 h1925

end R2N4
