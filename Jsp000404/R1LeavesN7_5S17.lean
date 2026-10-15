import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S12
import Jsp000404.R1LeavesN7_5S13
import Jsp000404.R1LeavesN7_5S15
import Jsp000404.R1LeavesN7_5S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0 (m : N7Model)
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h8207 | h8207
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x1 (m : N7Model)
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
    (h8206 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  linarith only [h0, h6313, h8206, hlam]

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1 (m : N7Model)
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h8206 | h8206
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1 (m : N7Model)
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h7118 | h7118
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1 (m : N7Model)
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h6900 | h6900
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13 (m : N7Model)
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
  rcases m.htr 0 3 4 (by decide) (by decide) with h6316 | h6316
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316

set_option maxHeartbeats 5620000 in
set_option maxHeartbeats 5620000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s12 (m : N7Model)
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h6315 | h6315
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13 m hb0 hb1 hb3 hb4 h0 h6310 h6311 h6312 h6313 h6314 h6315
  · linarith only [h0, h6312, h6315, hlam]

set_option maxHeartbeats 5624000 in
set_option maxHeartbeats 5624000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s11 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h6314 | h6314
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s12 m hb0 hb1 hb3 hb4 h0 h6310 h6311 h6312 h6313 h6314
  · linarith only [h0, h6311, h6314, hlam]

set_option maxHeartbeats 5628000 in
set_option maxHeartbeats 5628000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s10 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h6313 | h6313
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s11 m hb0 hb1 hb3 hb4 h0 h6310 h6311 h6312 h6313
  · linarith only [h0, h6310, h6313, hlam]

set_option maxHeartbeats 5952000 in
set_option maxHeartbeats 5952000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s9 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h6312 | h6312
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s10 m hb0 hb1 hb3 hb4 h0 h6310 h6311 h6312
  · rcases m.htr 0 2 3 (by decide) (by decide) with h9127 | h9127
    · rcases m.htr 0 2 4 (by decide) (by decide) with h9128 | h9128
      · rcases m.htr 0 2 5 (by decide) (by decide) with h9129 | h9129
        · rcases m.htr 0 3 4 (by decide) (by decide) with h9130 | h9130
          · rcases m.htr 0 3 5 (by decide) (by decide) with h9131 | h9131
            · linarith only [h6310, h6312, h9131, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9133 | h9133
              · linarith only [h6310, h6312, h9130, h9133, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9135 | h9135
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9136 | h9136
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9137 | h9137
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h9138 | h9138
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h9139 | h9139
                        · linarith only [h6310, h9131, h9139, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9141 | h9141
                          · linarith only [h6311, h6312, h9133, h9141, hlam]
                          · linarith only [h6310, h6312, h9138, h9141, hc34, hc45, hlam, hphi]
                      · linarith only [h9130, h9131, h9135, h9138, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h9129, h9137, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h9128, h9136, hlam]
                · linarith only [h0, h9127, h9135, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h9148 | h9148
            · linarith only [h6311, h6312, h9130, h9148, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9150 | h9150
              · linarith only [h6311, h6312, h9150, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9152 | h9152
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9153 | h9153
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9154 | h9154
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h9155 | h9155
                      · linarith only [h6310, h9130, h9155, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h9157 | h9157
                        · linarith only [h6310, h6312, h9148, h9157, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9159 | h9159
                          · linarith only [h6311, h9130, h9150, h9159, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h9161 | h9161
                            · linarith only [h6310, h9130, h9152, h9161, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h9163 | h9163
                              · linarith only [h6310, h9148, h9152, h9163, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h9165 | h9165
                                · linarith only [h6310, h6312, h9128, h9152, h9159, h9165, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h9167 | h9167
                                  · linarith only [h6311, h6312, h9152, h9155, h9159, h9167, hc23, hc34, hlam, hphi]
                                  · rcases h0bigk with h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c | h9169c
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [hlam, p9169_0]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [h0, hlam, p9169_1]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [h6312, h9157, hc03, hc35, hlam, hphi, p9169_1]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [h6312, h9157, h9167, hc04, hc45, hlam, hphi, p9169_1]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [h6312, hlam, p9169_1]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [h6310, h9152, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9169_1, u0elo1]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [hlam, p9169_0]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      rcases p9169_3 (m.d 0 1) (by simp) with h9177 | h9177
                                      · linarith only [h0, h9177, hlam]
                                      · linarith only [h6310, h9177, hlam]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      rcases p9169_3 (m.d 0 1) (by simp) with h9180 | h9180
                                      · linarith only [h0, h9180, hlam]
                                      · linarith only [h6311, h9180, hlam]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [h6311, h6312, h9152, h9155, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9169_1, u0elo1]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [h6310, hlam, p9169_1]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [h9127, hlam, p9169_1]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [hlam, p9169_0]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [h9130, hlam, p9169_1]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [h9148, hlam, p9169_1]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [h6311, hlam, p9169_0]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [h9128, hlam, p9169_0]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [h6310, h6311, h6312, h9152, h9157, h9167, hc23, hc45, hlam, hphi, ht34, p9169_1]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [hlam, p9169_0]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [h9150, hlam, p9169_0]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [h6310, h9152, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9169_1, u0elo4]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [h9129, hlam, p9169_1]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      rcases p9169_3 (m.d 0 1) (by simp) with h9196 | h9196
                                      · linarith only [h6312, h9196, hlam]
                                      · linarith only [h6310, h9196, hlam]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      rcases p9169_3 (m.d 0 1) (by simp) with h9199 | h9199
                                      · linarith only [h6312, h9199, hlam]
                                      · linarith only [h6311, h9199, hlam]
                                    · have p9169_0 := h9169c.1
                                      have p9169_1 := h9169c.2.1
                                      have p9169_2 := h9169c.2.2.1
                                      have p9169_3 := h9169c.2.2.2
                                      linarith only [hlam, p9169_0]
                    · linarith only [h0, h9129, h9154, hlam]
                  · linarith only [h0, h9128, h9153, hlam]
                · linarith only [h0, h9127, h9152, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h9206 | h9206
          · rcases m.htr 0 3 5 (by decide) (by decide) with h9207 | h9207
            · linarith only [h0, h6310, h9129, h9207, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9209 | h9209
              · linarith only [h0, h6310, h9129, h9206, h9209, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9211 | h9211
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9212 | h9212
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9213 | h9213
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h9214 | h9214
                      · linarith only [h0, h6310, h9129, h9213, h9214, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h6310, h9129, h9206, h9211, h9213, h9214, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h9217 | h9217
                      · linarith only [h0, h6310, h9213, h9217, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h6310, h9206, h9211, h9213, h9217, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h0, h9128, h9212, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h9127, h9211, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h9222 | h9222
            · linarith only [h6311, h6312, h9206, h9222, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9224 | h9224
              · linarith only [h0, h6311, h9129, h9224, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9226 | h9226
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9227 | h9227
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9228 | h9228
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h9229 | h9229
                      · linarith only [h0, h6310, h9129, h9206, h9228, h9229, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h9231 | h9231
                        · linarith only [h0, h6310, h9129, h9222, h9231, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9233 | h9233
                          · linarith only [h0, h6311, h9129, h9206, h9224, h9228, h9233, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h9235 | h9235
                            · linarith only [h6310, h9206, h9226, h9235, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h9237 | h9237
                              · linarith only [h0, h6310, h6311, h9129, h9226, h9228, h9231, h9237, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h9239 | h9239
                                · linarith only [h0, h6311, h9129, h9227, h9228, h9233, h9239, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h9241 | h9241
                                  · linarith only [h0, h6311, h9129, h9226, h9228, h9229, h9233, h9241, hc23, hc34, hlam, hphi]
                                  · rcases h0bigk with h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c | h9243c
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [hlam, p9243_0]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h0, hlam, p9243_1]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h0, h6310, h9129, h9226, h9228, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9243_1]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h0, h6310, h9129, h9206, h9226, h9228, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9243_1]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h6312, hlam, p9243_1]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h9129, h9228, hc01, hc12, hlam, hphi, p9243_1]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [hlam, p9243_0]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h6310, h9129, h9226, h9228, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9243_1]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h6310, h9129, h9206, h9226, h9228, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9243_1]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h9129, hlam, p9243_0]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h6310, hlam, p9243_1]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h9127, hlam, p9243_1]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [hlam, p9243_0]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h9206, hlam, p9243_1]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h9222, hlam, p9243_1]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h6311, hlam, p9243_0]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h9128, hlam, p9243_0]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h0, h6310, h6311, h9129, h9226, h9228, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9243_1]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [hlam, p9243_0]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h9224, hlam, p9243_0]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h6310, h9226, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9243_1, u0elo4]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [h0, h6311, h9129, h9226, h9228, h9229, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9243_1]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      rcases p9243_3 (m.d 0 1) (by simp) with h9266 | h9266
                                      · linarith only [h6312, h9266, hlam]
                                      · linarith only [h6310, h9266, hlam]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      rcases p9243_3 (m.d 0 1) (by simp) with h9269 | h9269
                                      · linarith only [h6312, h9269, hlam]
                                      · linarith only [h6311, h9269, hlam]
                                    · have p9243_0 := h9243c.1
                                      have p9243_1 := h9243c.2.1
                                      have p9243_2 := h9243c.2.2.1
                                      have p9243_3 := h9243c.2.2.2
                                      linarith only [hlam, p9243_0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h9273 | h9273
                      · linarith only [h0, h6310, h9228, h9273, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h9275 | h9275
                        · linarith only [h0, h6311, h9228, h9273, h9275, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9277 | h9277
                          · linarith only [h0, h6311, h9228, h9277, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h9279 | h9279
                            · linarith only [h0, h6311, h9206, h9226, h9228, h9273, h9279, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h9281 | h9281
                              · linarith only [h0, h6310, h6312, h9226, h9228, h9275, h9281, hc05, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h0, h6311, h9226, h9228, h9273, h9281, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h9128, h9227, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h9127, h9226, hlam]
      · linarith only [h0, h6311, h9128, hlam]
    · linarith only [h0, h6310, h9127, hlam]

end R2N4
