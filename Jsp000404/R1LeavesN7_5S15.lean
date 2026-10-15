import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7119 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7120 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  linarith only [h0, h6314, h7120, hlam]

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7119 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 1 2 4 (by decide) (by decide) with h7120 | h7120
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h7119 h7120
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h7119 h7120

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7119 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  linarith only [h0, h6313, h7119, hlam]

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 1 2 3 (by decide) (by decide) with h7119 | h7119
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h7119
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h7119

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8208 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8209 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  linarith only [h6310, h6316, h8209, hlam]

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8208 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8209 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8211 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  linarith only [h6310, h6900, h8211, hlam]

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8208 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8209 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8211 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h8213 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  linarith only [h0, h6311, h6316, h7118, h8213, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8208 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8209 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8211 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h8213 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h8215 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  linarith only [h6310, h6316, h8206, h8215, hlam]

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8208 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8209 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8211 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h8213 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h8215 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h8217 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  linarith only [h6310, h6900, h8206, h8217, hlam]

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8208 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8209 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8211 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h8213 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h8215 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h8217 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h8219 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  linarith only [h6310, h6314, h6316, h7118, h8206, h8219, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8208 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8209 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8211 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h8213 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h8215 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h8217 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h8219 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h8221 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases h0bigk with h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c | h8222c
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [hlam, p8222_0]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [h0, hlam, p8222_1]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    rcases p8222_3 (m.d 0 1) (by simp) with h8225 | h8225
    · rcases p8222_3 (m.d 0 2) (by simp) with h8226 | h8226
      · rcases p8222_3 (m.d 0 3) (by simp) with h8227 | h8227
        · linarith only [h6310, h8227, hlam]
        · rcases p8222_3 (m.d 0 4) (by simp) with h8229 | h8229
          · linarith only [h6311, h8229, hlam]
          · linarith only [h6316, h8229, hlam]
      · linarith only [h6313, h8226, hlam]
    · linarith only [h6310, h8225, hlam]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    rcases p8222_3 (m.d 0 1) (by simp) with h8234 | h8234
    · rcases p8222_3 (m.d 0 2) (by simp) with h8235 | h8235
      · rcases p8222_3 (m.d 0 3) (by simp) with h8236 | h8236
        · linarith only [h6310, h8236, hlam]
        · rcases p8222_3 (m.d 0 4) (by simp) with h8238 | h8238
          · linarith only [h6311, h8238, hlam]
          · rcases p8222_3 (m.d 0 5) (by simp) with h8240 | h8240
            · linarith only [h6312, h8240, hlam]
            · linarith only [h7118, h8240, hlam]
      · linarith only [h6314, h8235, hlam]
    · linarith only [h6311, h8234, hlam]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    rcases p8222_3 (m.d 0 1) (by simp) with h8245 | h8245
    · rcases p8222_3 (m.d 0 2) (by simp) with h8246 | h8246
      · rcases p8222_3 (m.d 0 3) (by simp) with h8247 | h8247
        · linarith only [h6310, h8247, hlam]
        · rcases p8222_3 (m.d 0 4) (by simp) with h8249 | h8249
          · linarith only [h6311, h8249, hlam]
          · rcases p8222_3 (m.d 0 5) (by simp) with h8251 | h8251
            · linarith only [h6312, h8251, hlam]
            · rcases h0emin with h8253 | h8253 | h8253 | h8253 | h8253
              · rcases h1bigk with h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [hlam, p8254_0]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [h0, hlam, p8254_0]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  rcases p8254_3 (m.d 0 1) (by simp) with h8257 | h8257
                  · rcases p8254_3 (m.d 1 2) (by simp) with h8258 | h8258
                    · rcases p8254_3 (m.d 1 3) (by simp) with h8259 | h8259
                      · linarith only [h8259, hlam, p8254_0]
                      · rcases p8254_3 (m.d 1 4) (by simp) with h8261 | h8261
                        · linarith only [h6311, h8261, hlam]
                        · linarith only [h8209, h8261, hlam]
                    · linarith only [h8206, h8258, hlam]
                  · linarith only [h8257, hlam, p8254_0]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  rcases p8254_3 (m.d 0 1) (by simp) with h8266 | h8266
                  · rcases p8254_3 (m.d 1 2) (by simp) with h8267 | h8267
                    · rcases p8254_3 (m.d 1 3) (by simp) with h8268 | h8268
                      · linarith only [h6310, h8268, hlam]
                      · rcases p8254_3 (m.d 1 4) (by simp) with h8270 | h8270
                        · linarith only [h8270, hlam, p8254_0]
                        · rcases p8254_3 (m.d 1 5) (by simp) with h8272 | h8272
                          · linarith only [h6312, h8272, hlam]
                          · linarith only [h8213, h8272, hlam]
                    · linarith only [h8207, h8267, hlam]
                  · linarith only [h8266, hlam, p8254_0]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  rcases p8254_3 (m.d 0 1) (by simp) with h8277 | h8277
                  · rcases p8254_3 (m.d 1 2) (by simp) with h8278 | h8278
                    · rcases p8254_3 (m.d 1 3) (by simp) with h8279 | h8279
                      · linarith only [h6310, h8279, hlam]
                      · rcases p8254_3 (m.d 1 4) (by simp) with h8281 | h8281
                        · linarith only [h6311, h8281, hlam]
                        · rcases p8254_3 (m.d 1 5) (by simp) with h8283 | h8283
                          · linarith only [h8283, hlam, p8254_0]
                          · rcases h3bigk with h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c | h8285c
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [hlam, p8285_0]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [h6316, h7118, h8206, h8221, hc23, hc34, hlam, hphi, p8285_1]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [h6316, h7118, h8221, hc23, hc34, hlam, hphi, p8285_1]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [h6316, hlam, p8285_0]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [h6900, hlam, p8285_0]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [h6310, hlam, p8285_0]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [hlam, p8285_0]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [h0, h6310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8285_1]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [h8209, hlam, p8285_0]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [h8211, hlam, p8285_0]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [h6313, hlam, p8285_0]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [h8206, hlam, p8285_0]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [hlam, p8285_0]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [h8215, hlam, p8285_0]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [h8217, hlam, p8285_0]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              rcases p8285_3 (m.d 0 3) (by simp) with h8301 | h8301
                              · linarith only [h8301, hlam, p8285_0]
                              · rcases p8285_3 (m.d 1 3) (by simp) with h8303 | h8303
                                · linarith only [h8209, h8303, hlam]
                                · rcases p8285_3 (m.d 2 3) (by simp) with h8305 | h8305
                                  · linarith only [h8215, h8305, hlam]
                                  · rcases p8285_3 (m.d 3 4) (by simp) with h8307 | h8307
                                    · rcases p8285_3 (m.d 3 5) (by simp) with h8308 | h8308
                                      · linarith only [h8221, h8308, hlam]
                                      · linarith only [h6900, h8308, hlam]
                                    · linarith only [h8307, hlam, p8285_0]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              rcases p8285_3 (m.d 0 3) (by simp) with h8312 | h8312
                              · linarith only [h6316, h8312, hlam]
                              · linarith only [h6310, h8312, hlam]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              rcases p8285_3 (m.d 0 3) (by simp) with h8315 | h8315
                              · linarith only [h6316, h8315, hlam]
                              · linarith only [h6313, h8315, hlam]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [hlam, p8285_0]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [h6900, hc03, hc34, hlam, hphi, p8285_1]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              rcases p8285_3 (m.d 0 3) (by simp) with h8320 | h8320
                              · linarith only [h8320, hlam, p8285_0]
                              · rcases p8285_3 (m.d 1 3) (by simp) with h8322 | h8322
                                · linarith only [h8211, h8322, hlam]
                                · rcases p8285_3 (m.d 2 3) (by simp) with h8324 | h8324
                                  · linarith only [h8217, h8324, hlam]
                                  · rcases p8285_3 (m.d 3 4) (by simp) with h8326 | h8326
                                    · rcases p8285_3 (m.d 3 5) (by simp) with h8327 | h8327
                                      · rcases h4bigk with h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c | h8328c
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [hlam, p8328_0]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [h0, h7118, h8207, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8222_1, p8328_1]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [h0, h7118, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8222_1, p8328_1]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [h6316, hlam, p8328_0]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [h7118, hlam, p8328_0]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [h6311, hlam, p8328_1]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [hlam, p8328_0]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [h0, h6311, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8328_1]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [h8209, hlam, p8328_1]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [h8213, hlam, p8328_0]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [h6314, hlam, p8328_1]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [h8207, hlam, p8328_1]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [hlam, p8328_0]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [h8215, hlam, p8328_1]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [h8219, hlam, p8328_0]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          rcases p8328_3 (m.d 0 4) (by simp) with h8344 | h8344
                                          · linarith only [h6316, h8344, hlam]
                                          · rcases p8328_3 (m.d 1 4) (by simp) with h8346 | h8346
                                            · linarith only [h8209, h8346, hlam]
                                            · rcases p8328_3 (m.d 2 4) (by simp) with h8348 | h8348
                                              · linarith only [h8215, h8348, hlam]
                                              · rcases p8328_3 (m.d 3 4) (by simp) with h8350 | h8350
                                                · rcases p8328_3 (m.d 4 5) (by simp) with h8351 | h8351
                                                  · linarith only [h8221, h8351, hlam]
                                                  · linarith only [h7118, h8351, hlam]
                                                · linarith only [h6316, h8350, hlam]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          rcases p8328_3 (m.d 0 4) (by simp) with h8355 | h8355
                                          · linarith only [h6316, h8355, hlam]
                                          · linarith only [h6311, h8355, hlam]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          rcases p8328_3 (m.d 0 4) (by simp) with h8358 | h8358
                                          · linarith only [h6316, h8358, hlam]
                                          · linarith only [h6314, h8358, hlam]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [hlam, p8328_0]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [h6314, h7118, h8215, hc23, hc34, hlam, hphi, p8328_1]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [h6310, h6316, h8206, h8221, hc23, hc34, hlam, hphi, p8328_1]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [h8207, h8215, h8221, hc23, hc34, hlam, hphi, p8328_1]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [h8215, h8221, hc23, hc34, hlam, hphi, p8328_1]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [h8221, hlam, p8328_0]
                                        · have p8328_0 := h8328c.1
                                          have p8328_1 := h8328c.2.1
                                          have p8328_2 := h8328c.2.2.1
                                          have p8328_3 := h8328c.2.2.2
                                          linarith only [hlam, p8328_0]
                                      · linarith only [h8327, hlam, p8285_0]
                                    · linarith only [h6316, h8326, hlam]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              rcases p8285_3 (m.d 0 3) (by simp) with h8370 | h8370
                              · linarith only [h6900, h8370, hlam]
                              · linarith only [h6310, h8370, hlam]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              rcases p8285_3 (m.d 0 3) (by simp) with h8373 | h8373
                              · linarith only [h6900, h8373, hlam]
                              · linarith only [h6313, h8373, hlam]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [h8221, hlam, p8285_0]
                            · have p8285_0 := h8285c.1
                              have p8285_1 := h8285c.2.1
                              have p8285_2 := h8285c.2.2.1
                              have p8285_3 := h8285c.2.2.2
                              linarith only [hlam, p8285_0]
                    · linarith only [h8208, h8278, hlam]
                  · linarith only [h8277, hlam, p8254_0]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [h6310, h6316, h7118, h8206, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8222_1, p8254_1]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [hlam, p8254_0]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [h0, h6310, h6316, h7118, hlam, p8222_1, p8254_2]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [h0, h6311, h7118, hlam, p8222_1, p8254_2]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [h0, h6312, hlam, p8222_1, p8254_2]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [h6310, hlam, p8254_0]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [h8206, hlam, p8254_1]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [hlam, p8254_0]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [h8209, hlam, p8254_1]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [h8211, hlam, p8254_1]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [h6311, hlam, p8254_0]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [h8207, hlam, p8254_1]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [h6311, h7118, h8206, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8222_1, p8254_1, u0elo0]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [hlam, p8254_0]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [h8213, hlam, p8254_1]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [h6312, hlam, p8254_0]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [h8208, hlam, p8254_1]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [h0, h6312, h8206, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8222_1, p8254_1]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [h0, h6312, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p8222_1, p8254_1]
                · have p8254_0 := h8254c.1
                  have p8254_1 := h8254c.2.1
                  have p8254_2 := h8254c.2.2.1
                  have p8254_3 := h8254c.2.2.2
                  linarith only [hlam, p8254_0]
              · rcases h1bigk with h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [hlam, p8400_0]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [h0, hlam, p8400_0]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  rcases p8400_3 (m.d 0 1) (by simp) with h8403 | h8403
                  · rcases p8400_3 (m.d 1 2) (by simp) with h8404 | h8404
                    · rcases p8400_3 (m.d 1 3) (by simp) with h8405 | h8405
                      · linarith only [h8405, hlam, p8400_0]
                      · rcases p8400_3 (m.d 1 4) (by simp) with h8407 | h8407
                        · linarith only [h6311, h8407, hlam]
                        · linarith only [h8209, h8407, hlam]
                    · linarith only [h8206, h8404, hlam]
                  · linarith only [h8403, hlam, p8400_0]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  rcases p8400_3 (m.d 0 1) (by simp) with h8412 | h8412
                  · rcases p8400_3 (m.d 1 2) (by simp) with h8413 | h8413
                    · rcases p8400_3 (m.d 1 3) (by simp) with h8414 | h8414
                      · linarith only [h6310, h8414, hlam]
                      · rcases p8400_3 (m.d 1 4) (by simp) with h8416 | h8416
                        · linarith only [h8416, hlam, p8400_0]
                        · rcases p8400_3 (m.d 1 5) (by simp) with h8418 | h8418
                          · linarith only [h6312, h8418, hlam]
                          · linarith only [h8213, h8418, hlam]
                    · linarith only [h8207, h8413, hlam]
                  · linarith only [h8412, hlam, p8400_0]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  rcases p8400_3 (m.d 0 1) (by simp) with h8423 | h8423
                  · rcases p8400_3 (m.d 1 2) (by simp) with h8424 | h8424
                    · rcases p8400_3 (m.d 1 3) (by simp) with h8425 | h8425
                      · linarith only [h6310, h8425, hlam]
                      · rcases p8400_3 (m.d 1 4) (by simp) with h8427 | h8427
                        · linarith only [h6311, h8427, hlam]
                        · rcases p8400_3 (m.d 1 5) (by simp) with h8429 | h8429
                          · linarith only [h8429, hlam, p8400_0]
                          · rcases h3bigk with h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c | h8431c
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [hlam, p8431_0]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [h6316, h8206, hc23, hc34, hlam, hphi, p8431_1]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [h6316, hc23, hc34, hlam, hphi, p8431_1]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [h6316, hlam, p8431_0]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [h6900, hlam, p8431_0]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [h6310, hlam, p8431_0]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [hlam, p8431_0]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [h0, h6310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8431_1]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [h8209, hlam, p8431_0]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [h8211, hlam, p8431_0]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [h6313, hlam, p8431_0]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [h8206, hlam, p8431_0]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [hlam, p8431_0]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [h8215, hlam, p8431_0]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [h8217, hlam, p8431_0]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              rcases p8431_3 (m.d 0 3) (by simp) with h8447 | h8447
                              · linarith only [h8447, hlam, p8431_0]
                              · rcases p8431_3 (m.d 1 3) (by simp) with h8449 | h8449
                                · linarith only [h8209, h8449, hlam]
                                · rcases p8431_3 (m.d 2 3) (by simp) with h8451 | h8451
                                  · linarith only [h8215, h8451, hlam]
                                  · rcases p8431_3 (m.d 3 4) (by simp) with h8453 | h8453
                                    · rcases p8431_3 (m.d 3 5) (by simp) with h8454 | h8454
                                      · linarith only [h8221, h8454, hlam]
                                      · linarith only [h6900, h8454, hlam]
                                    · linarith only [h8453, hlam, p8431_0]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              rcases p8431_3 (m.d 0 3) (by simp) with h8458 | h8458
                              · linarith only [h6316, h8458, hlam]
                              · linarith only [h6310, h8458, hlam]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              rcases p8431_3 (m.d 0 3) (by simp) with h8461 | h8461
                              · linarith only [h6316, h8461, hlam]
                              · linarith only [h6313, h8461, hlam]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [hlam, p8431_0]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [h6900, hc03, hc34, hlam, hphi, p8431_1]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              rcases p8431_3 (m.d 0 3) (by simp) with h8466 | h8466
                              · linarith only [h8466, hlam, p8431_0]
                              · rcases p8431_3 (m.d 1 3) (by simp) with h8468 | h8468
                                · linarith only [h8211, h8468, hlam]
                                · rcases p8431_3 (m.d 2 3) (by simp) with h8470 | h8470
                                  · linarith only [h8217, h8470, hlam]
                                  · rcases p8431_3 (m.d 3 4) (by simp) with h8472 | h8472
                                    · rcases p8431_3 (m.d 3 5) (by simp) with h8473 | h8473
                                      · rcases h4bigk with h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c | h8474c
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [hlam, p8474_0]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [h0, h7118, h8206, h8209, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8222_1, p8474_1]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [h0, h7118, h8215, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8222_1, p8474_1]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [h6316, hlam, p8474_0]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [h7118, hlam, p8474_0]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [h6311, hlam, p8474_1]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [hlam, p8474_0]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [h0, h6311, h8215, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8474_1]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [h8209, hlam, p8474_1]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [h8213, hlam, p8474_0]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [h6314, hlam, p8474_1]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [h8207, hlam, p8474_1]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [hlam, p8474_0]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [h8215, hlam, p8474_1]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [h8219, hlam, p8474_0]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          rcases p8474_3 (m.d 0 4) (by simp) with h8490 | h8490
                                          · linarith only [h6316, h8490, hlam]
                                          · rcases p8474_3 (m.d 1 4) (by simp) with h8492 | h8492
                                            · linarith only [h8209, h8492, hlam]
                                            · rcases p8474_3 (m.d 2 4) (by simp) with h8494 | h8494
                                              · linarith only [h8215, h8494, hlam]
                                              · rcases p8474_3 (m.d 3 4) (by simp) with h8496 | h8496
                                                · rcases p8474_3 (m.d 4 5) (by simp) with h8497 | h8497
                                                  · linarith only [h8221, h8497, hlam]
                                                  · linarith only [h7118, h8497, hlam]
                                                · linarith only [h6316, h8496, hlam]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          rcases p8474_3 (m.d 0 4) (by simp) with h8501 | h8501
                                          · linarith only [h6316, h8501, hlam]
                                          · linarith only [h6311, h8501, hlam]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          rcases p8474_3 (m.d 0 4) (by simp) with h8504 | h8504
                                          · linarith only [h6316, h8504, hlam]
                                          · linarith only [h6314, h8504, hlam]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [hlam, p8474_0]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [h6314, h7118, h8215, hc23, hc34, hlam, hphi, p8474_1]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [h6310, h6316, h8206, h8221, hc23, hc34, hlam, hphi, p8474_1]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [h8207, h8215, h8221, hc23, hc34, hlam, hphi, p8474_1]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [h8215, h8221, hc23, hc34, hlam, hphi, p8474_1]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [h8221, hlam, p8474_0]
                                        · have p8474_0 := h8474c.1
                                          have p8474_1 := h8474c.2.1
                                          have p8474_2 := h8474c.2.2.1
                                          have p8474_3 := h8474c.2.2.2
                                          linarith only [hlam, p8474_0]
                                      · linarith only [h8473, hlam, p8431_0]
                                    · linarith only [h6316, h8472, hlam]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              rcases p8431_3 (m.d 0 3) (by simp) with h8516 | h8516
                              · linarith only [h6900, h8516, hlam]
                              · linarith only [h6310, h8516, hlam]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              rcases p8431_3 (m.d 0 3) (by simp) with h8519 | h8519
                              · linarith only [h6900, h8519, hlam]
                              · linarith only [h6313, h8519, hlam]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [h8221, hlam, p8431_0]
                            · have p8431_0 := h8431c.1
                              have p8431_1 := h8431c.2.1
                              have p8431_2 := h8431c.2.2.1
                              have p8431_3 := h8431c.2.2.2
                              linarith only [hlam, p8431_0]
                    · linarith only [h8208, h8424, hlam]
                  · linarith only [h8423, hlam, p8400_0]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [h6310, h6316, h7118, h8206, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8222_1, p8400_1]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [hlam, p8400_0]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [h0, h6310, h6316, h7118, hlam, p8222_1, p8400_2]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [h0, h6311, h7118, hlam, p8222_1, p8400_2]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [h0, h6312, hlam, p8222_1, p8400_2]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [h6310, hlam, p8400_0]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [h8206, hlam, p8400_1]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [hlam, p8400_0]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [h8209, hlam, p8400_1]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [h8211, hlam, p8400_1]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [h6311, hlam, p8400_0]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [h8207, hlam, p8400_1]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [h6311, h7118, h8206, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8222_1, p8400_1, u0elo0]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [hlam, p8400_0]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [h8213, hlam, p8400_1]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [h6312, hlam, p8400_0]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [h8208, hlam, p8400_1]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [h0, h6312, h8206, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8222_1, p8400_1]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [h0, h6312, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p8222_1, p8400_1]
                · have p8400_0 := h8400c.1
                  have p8400_1 := h8400c.2.1
                  have p8400_2 := h8400c.2.2.1
                  have p8400_3 := h8400c.2.2.2
                  linarith only [hlam, p8400_0]
              · linarith only [h0, h6316, h7118, h8253, hc12, hlam, ht01, p8222_1]
              · linarith only [h0, h7118, h8253, hc12, hlam, ht01, p8222_1]
              · linarith only [h0, h8253, hc12, hlam, ht01, p8222_1]
      · linarith only [h6315, h8246, hlam]
    · linarith only [h6312, h8245, hlam]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [h6310, h8206, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8222_1, u0elo1]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [hlam, p8222_0]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    rcases p8222_3 (m.d 0 1) (by simp) with h8553 | h8553
    · linarith only [h0, h8553, hlam]
    · linarith only [h6310, h8553, hlam]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    rcases p8222_3 (m.d 0 1) (by simp) with h8556 | h8556
    · linarith only [h0, h8556, hlam]
    · linarith only [h6311, h8556, hlam]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    rcases p8222_3 (m.d 0 1) (by simp) with h8559 | h8559
    · linarith only [h0, h8559, hlam]
    · linarith only [h6312, h8559, hlam]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [h6310, hlam, p8222_1]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [h6313, hlam, p8222_1]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [hlam, p8222_0]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [h6316, hlam, p8222_1]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [h6900, hlam, p8222_1]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [h6311, hlam, p8222_0]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [h6314, hlam, p8222_0]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [h6310, h7118, h8206, h8221, hc23, hc34, hlam, hphi, p8222_1]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [hlam, p8222_0]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [h7118, hlam, p8222_0]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [h6312, hlam, p8222_0]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [h6315, hlam, p8222_1]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [h6310, h7118, h8206, h8221, hc23, hc34, hlam, hphi, p8222_1]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [h6311, h7118, h8207, h8215, h8221, hc23, hc34, hlam, hphi, p8222_1]
  · have p8222_0 := h8222c.1
    have p8222_1 := h8222c.2.1
    have p8222_2 := h8222c.2.2.1
    have p8222_3 := h8222c.2.2.2
    linarith only [hlam, p8222_0]

end R2N4
