import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S11
import Jsp000404.R1LeavesN7_5S18
import Jsp000404.R1LeavesN7_5S28
import Jsp000404.R1LeavesN7_5S29

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 14334000 in
set_option maxHeartbeats 14334000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h9935 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h9936 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h9937 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h9938 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h9939 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h9940 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9941 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  rcases m.htr 0 4 5 (by decide) (by decide) with h9942 | h9942
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 h9935 h9936 h9937 h9938 h9939 h9940 h9941 h9942
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 h9935 h9936 h9937 h9938 h9939 h9940 h9941 h9942

set_option maxHeartbeats 14334000 in
set_option maxHeartbeats 14334000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h9935 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h9936 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h9937 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h9938 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h9939 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h9940 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9941 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  linarith only [h6310, h9936, h9941, hlam]

set_option maxHeartbeats 14334000 in
set_option maxHeartbeats 14334000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h9935 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h9936 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h9937 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h9938 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h9939 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h9940 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  rcases m.htr 0 3 5 (by decide) (by decide) with h9941 | h9941
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 h9935 h9936 h9937 h9938 h9939 h9940 h9941
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 h9935 h9936 h9937 h9938 h9939 h9940 h9941

set_option maxHeartbeats 14334000 in
set_option maxHeartbeats 14334000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h9935 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h9936 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h9937 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h9938 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h9939 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h9940 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  linarith only [h6310, h9935, h9940, hlam]

set_option maxHeartbeats 14334000 in
set_option maxHeartbeats 14334000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h9935 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h9936 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h9937 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h9938 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h9939 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  rcases m.htr 0 3 4 (by decide) (by decide) with h9940 | h9940
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 h9935 h9936 h9937 h9938 h9939 h9940
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 h9935 h9936 h9937 h9938 h9939 h9940

set_option maxHeartbeats 14334000 in
set_option maxHeartbeats 14334000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h9935 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h9936 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h9937 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h9938 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h9939 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  linarith only [h6310, h9936, h9937, h9939, hlam]

set_option maxHeartbeats 14334000 in
set_option maxHeartbeats 14334000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h9935 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h9936 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h9937 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h9938 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  rcases m.htr 0 2 5 (by decide) (by decide) with h9939 | h9939
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 h9935 h9936 h9937 h9938 h9939
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 h9935 h9936 h9937 h9938 h9939

set_option maxHeartbeats 14334000 in
set_option maxHeartbeats 14334000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h9935 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h9936 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h9937 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h9938 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  linarith only [h6310, h9935, h9937, h9938, hlam]

set_option maxHeartbeats 14334000 in
set_option maxHeartbeats 14334000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h9935 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h9936 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h9937 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  rcases m.htr 0 2 4 (by decide) (by decide) with h9938 | h9938
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 h9935 h9936 h9937 h9938
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 h9935 h9936 h9937 h9938

set_option maxHeartbeats 14334000 in
set_option maxHeartbeats 14334000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h9935 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h9936 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h9937 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  rcases m.htr 0 2 4 (by decide) (by decide) with h10761 | h10761
  · rcases m.htr 0 2 5 (by decide) (by decide) with h10762 | h10762
    · rcases m.htr 0 3 4 (by decide) (by decide) with h10763 | h10763
      · rcases m.htr 0 3 5 (by decide) (by decide) with h10764 | h10764
        · rcases m.htr 0 4 5 (by decide) (by decide) with h10765 | h10765
          · rcases m.htr 1 2 3 (by decide) (by decide) with h10766 | h10766
            · rcases m.htr 1 2 4 (by decide) (by decide) with h10767 | h10767
              · rcases m.htr 1 2 5 (by decide) (by decide) with h10768 | h10768
                · rcases m.htr 1 3 4 (by decide) (by decide) with h10769 | h10769
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h10770 | h10770
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10771 | h10771
                      · linarith only [h0, h10766, h10771, h9935, h9937, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h10765, h10766, h10771, h9935, h9937, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h10764, h10770, h6310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h10763, h10766, h10769, h9937, hlam]
                · linarith only [h0, h10766, h10767, h10768, h9935, h9937, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h0, h10766, h10767, h9935, h9937, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h10778 | h10778
              · rcases m.htr 1 2 5 (by decide) (by decide) with h10779 | h10779
                · rcases m.htr 1 3 4 (by decide) (by decide) with h10780 | h10780
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h10781 | h10781
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10782 | h10782
                      · linarith only [h0, h10766, h10782, h9935, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h10765, h10766, h10782, h9935, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h10764, h10781, h6310, hlam]
                  · linarith only [h10763, h10780, h6310, hlam]
                · linarith only [h0, h10762, h10779, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h10761, h10778, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h10789 | h10789
            · rcases m.htr 1 2 4 (by decide) (by decide) with h10790 | h10790
              · rcases m.htr 1 2 5 (by decide) (by decide) with h10791 | h10791
                · rcases m.htr 1 3 4 (by decide) (by decide) with h10792 | h10792
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h10793 | h10793
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10794 | h10794
                      · linarith only [h10765, h10794, h9935, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h10796 | h10796
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h10797 | h10797
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h10798 | h10798
                            · linarith only [h10765, h10790, h10798, h9935, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h10800 | h10800
                              · linarith only [h10765, h10790, h10796, h10800, h9935, hlam]
                              · rcases h0bigk with h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c | h10802c
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [hlam, p10802_0]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h0, hlam, p10802_1]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h6310, hlam, p10802_0]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h0, h10789, h10790, h10796, h9935, h9937, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10802_1]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h0, h10789, h9937, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10802_1]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h10789, h9937, hc01, hc12, hlam, hphi, p10802_1]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [hlam, p10802_0]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h9937, hlam, p10802_0]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h10789, h10790, h10796, h9935, h9937, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10802_1]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h10789, h10790, h10794, h10796, h9936, h9937, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10802_1]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h10789, h10790, h10794, h10796, h9936, h9937, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10802_1]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h0, h10789, h10790, h10794, h10796, h9936, h9937, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10802_1]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [hlam, p10802_0]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  rcases p10802_3 (m.d 0 1) (by simp) with h10816 | h10816
                                  · linarith only [h10816, h6310, hlam]
                                  · linarith only [h10816, h9935, hlam]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  rcases p10802_3 (m.d 0 1) (by simp) with h10819 | h10819
                                  · linarith only [h10819, h6310, hlam]
                                  · linarith only [h10819, h9936, hlam]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h9935, hlam, p10802_0]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h10761, hlam, p10802_0]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h10763, hlam, p10802_0]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [hlam, p10802_0]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h10765, hlam, p10802_0]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h9936, hlam, p10802_0]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h10762, hlam, p10802_1]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h10764, hlam, p10802_0]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [h0, h10789, h10790, h10796, h9935, h9936, h9937, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10802_1]
                                · have p10802_0 := h10802c.1
                                  have p10802_1 := h10802c.2.1
                                  have p10802_2 := h10802c.2.2.1
                                  have p10802_3 := h10802c.2.2.2
                                  linarith only [hlam, p10802_0]
                          · linarith only [h10764, h10797, h9937, hlam]
                        · linarith only [h10763, h10796, h9937, hlam]
                    · linarith only [h10764, h10793, h6310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h10763, h10789, h10792, h9937, hlam]
                · linarith only [h0, h10762, h10790, h10791, h9935, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · linarith only [h10789, h10790, h9937, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h10838 | h10838
              · rcases m.htr 1 2 5 (by decide) (by decide) with h10839 | h10839
                · rcases m.htr 1 3 4 (by decide) (by decide) with h10840 | h10840
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h10841 | h10841
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10842 | h10842
                      · linarith only [h10765, h10842, h9935, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h10844 | h10844
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h10845 | h10845
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h10846 | h10846
                            · linarith only [h0, h10765, h10789, h10838, h10846, h9935, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h10848 | h10848
                              · linarith only [h10765, h10838, h10844, h10848, h9935, hlam]
                              · rcases h0bigk with h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c | h10850c
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [hlam, p10850_0]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [h0, hlam, p10850_1]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [h6310, hlam, p10850_0]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [h0, h10789, h10838, h10844, h9935, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10850_1]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [h0, h10789, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10850_1]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [h0, h10789, hc01, hc23, hlam, hphi, ht12, p10850_1]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [hlam, p10850_0]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [h9937, hlam, p10850_0]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  rcases p10850_3 (m.d 0 1) (by simp) with h10859 | h10859
                                  · linarith only [h0, h10859, hlam]
                                  · linarith only [h10859, h9935, hlam]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  rcases p10850_3 (m.d 0 1) (by simp) with h10862 | h10862
                                  · linarith only [h0, h10862, hlam]
                                  · linarith only [h10862, h9936, hlam]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [h10839, h10844, h10846, h9936, hc34, hlam, hphi, ht0b, ht45, ht5b, p10850_1, u0elo2]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [h0, h10839, h10844, h10846, h9936, hc34, hlam, hphi, ht0b, ht45, ht5b, p10850_1, u0elo2]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [hlam, p10850_0]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  rcases p10850_3 (m.d 0 1) (by simp) with h10868 | h10868
                                  · linarith only [h10868, h6310, hlam]
                                  · linarith only [h10868, h9935, hlam]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  rcases p10850_3 (m.d 0 1) (by simp) with h10871 | h10871
                                  · linarith only [h10871, h6310, hlam]
                                  · linarith only [h10871, h9936, hlam]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [h9935, hlam, p10850_0]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [h10761, hlam, p10850_0]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [h10763, hlam, p10850_0]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [hlam, p10850_0]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [h10765, hlam, p10850_0]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [h9936, hlam, p10850_0]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [h10762, hlam, p10850_1]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [h10764, hlam, p10850_0]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [h0, h10789, h10838, h10844, h9935, h9936, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10850_1]
                                · have p10850_0 := h10850c.1
                                  have p10850_1 := h10850c.2.1
                                  have p10850_2 := h10850c.2.2.1
                                  have p10850_3 := h10850c.2.2.2
                                  linarith only [hlam, p10850_0]
                          · linarith only [h0, h10789, h10845, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h10789, h10838, h10842, h10844, h9936, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h10764, h10841, h6310, hlam]
                  · linarith only [h10763, h10840, h6310, h9936, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
                · linarith only [h0, h10762, h10838, h10839, h9935, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · linarith only [h0, h10761, h10838, hlam]
        · linarith only [h10764, h6310, h9936, hlam]
      · linarith only [h0, h10763, h9935, h9937, hlam]
    · linarith only [h0, h10762, h9936, hlam]
  · linarith only [h0, h10761, h9935, hlam]

set_option maxHeartbeats 14334000 in
set_option maxHeartbeats 14334000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h9935 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h9936 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  rcases m.htr 0 2 3 (by decide) (by decide) with h9937 | h9937
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 h9935 h9936 h9937
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 h9935 h9936 h9937

set_option maxHeartbeats 14334000 in
set_option maxHeartbeats 14334000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h9935 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h9936 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  rcases m.htr 0 2 3 (by decide) (by decide) with h10894 | h10894
  · rcases m.htr 0 2 4 (by decide) (by decide) with h10895 | h10895
    · rcases m.htr 0 2 5 (by decide) (by decide) with h10896 | h10896
      · rcases m.htr 0 3 4 (by decide) (by decide) with h10897 | h10897
        · rcases m.htr 0 3 5 (by decide) (by decide) with h10898 | h10898
          · rcases m.htr 0 4 5 (by decide) (by decide) with h10899 | h10899
            · linarith only [h10899, h9935, h9936, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10901 | h10901
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10902 | h10902
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10903 | h10903
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10904 | h10904
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10905 | h10905
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h10906 | h10906
                        · linarith only [h10899, h10906, h9935, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h10908 | h10908
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h10909 | h10909
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h10910 | h10910
                              · linarith only [h10902, h10906, h10910, h9935, h9936, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h10912 | h10912
                                · linarith only [h10902, h10906, h10908, h10912, h9935, h9936, hlam]
                                · rcases h0bigk with h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c | h10914c
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [hlam, p10914_0]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [h0, hlam, p10914_1]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [h6310, hlam, p10914_0]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [h10906, h9936, hc04, hc45, hlam, hphi, p10914_1]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [h9936, hlam, p10914_1]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [h10902, h10908, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p10914_1, u0elo1]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [hlam, p10914_0]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [h10902, h10908, h6310, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p10914_1, u0elo1]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    rcases p10914_3 (m.d 0 1) (by simp) with h10923 | h10923
                                    · linarith only [h0, h10923, hlam]
                                    · linarith only [h10923, h9935, hlam]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [h10902, h10908, h9935, h9936, hc34, hlam, hphi, ht0b, ht45, ht5b, p10914_1, u0elo1]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [h10894, h10902, h10908, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p10914_1, u0elo1]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [h10894, hlam, p10914_1]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [hlam, p10914_0]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    rcases p10914_3 (m.d 0 1) (by simp) with h10930 | h10930
                                    · linarith only [h10930, h6310, hlam]
                                    · linarith only [h10930, h9935, hlam]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [h10894, h10902, h10908, h9935, h9936, hc34, hlam, hphi, ht0b, ht45, ht5b, p10914_1, u0elo1]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [h9935, hlam, p10914_0]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [h10895, hlam, p10914_0]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [h10897, hlam, p10914_0]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [hlam, p10914_0]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [h10899, hlam, p10914_0]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [h10902, h10908, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p10914_1, u0elo4]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [h10896, hlam, p10914_1]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [h10898, hlam, p10914_0]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    rcases p10914_3 (m.d 0 1) (by simp) with h10942 | h10942
                                    · linarith only [h10942, h9936, hlam]
                                    · linarith only [h10942, h9935, hlam]
                                  · have p10914_0 := h10914c.1
                                    have p10914_1 := h10914c.2.1
                                    have p10914_2 := h10914c.2.2.1
                                    have p10914_3 := h10914c.2.2.2
                                    linarith only [hlam, p10914_0]
                            · linarith only [h10894, h10898, h10908, h10909, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h10904, h10906, h10908, h9935, h9936, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h10894, h10898, h10905, h6310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h10897, h10904, h6310, hlam]
                  · linarith only [h0, h10896, h10903, hlam]
                · linarith only [h0, h10895, h10902, hlam]
              · linarith only [h0, h10894, h10901, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h10953 | h10953
            · linarith only [h10898, h10953, h6310, h9935, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10955 | h10955
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10956 | h10956
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10957 | h10957
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10958 | h10958
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10959 | h10959
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h10960 | h10960
                        · linarith only [h10953, h10960, h9935, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h10962 | h10962
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h10963 | h10963
                            · linarith only [h10894, h10898, h10963, h6310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h10965 | h10965
                              · linarith only [h10898, h10956, h10959, h10960, h10965, h6310, h9935, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h10967 | h10967
                                · linarith only [h10898, h10956, h10959, h10960, h10962, h10967, h6310, h9935, hlam]
                                · rcases h0bigk with h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [hlam, p10969_0]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h0, hlam, p10969_1]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h6310, hlam, p10969_0]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h10898, h10955, h10956, h10959, h10962, h6310, h9935, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10969_1]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h9936, hlam, p10969_1]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h10956, h10962, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p10969_1, u0elo1]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [hlam, p10969_0]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h10956, h10962, h6310, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p10969_1, u0elo1]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    rcases p10969_3 (m.d 0 1) (by simp) with h10978 | h10978
                                    · linarith only [h0, h10978, hlam]
                                    · linarith only [h10978, h9935, hlam]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h10898, h10956, h10962, h6310, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p10969_1, u0elo1]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h10956, h10962, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p10969_1, u0elo2]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h10894, hlam, p10969_1]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [hlam, p10969_0]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h10898, h10955, h10956, h10959, h10962, h9935, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10969_1]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h10898, hlam, p10969_1]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h9935, hlam, p10969_0]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h10895, hlam, p10969_0]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h10897, hlam, p10969_0]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [hlam, p10969_0]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h10953, hlam, p10969_0]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h10896, h10956, h10962, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p10969_1, u0elo1]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h10896, hlam, p10969_1]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [h10898, h10955, h10956, h10959, h10962, h6310, h9935, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10969_1]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    rcases p10969_3 (m.d 0 1) (by simp) with h10995 | h10995
                                    · linarith only [h10995, h9936, hlam]
                                    · linarith only [h10995, h9935, hlam]
                                  · have p10969_0 := h10969c.1
                                    have p10969_1 := h10969c.2.1
                                    have p10969_2 := h10969c.2.2.1
                                    have p10969_3 := h10969c.2.2.2
                                    linarith only [hlam, p10969_0]
                          · linarith only [h10897, h10898, h10955, h10959, h10962, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11000 | h11000
                        · linarith only [h10959, h11000, h6310, h9935, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11002 | h11002
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11003 | h11003
                            · linarith only [h10956, h10959, h11002, h11003, h6310, h9935, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11005 | h11005
                              · linarith only [h10956, h10959, h11000, h11005, h6310, h9935, h9936, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h11007 | h11007
                                · linarith only [h10956, h10959, h11000, h11002, h11007, h6310, h9935, hlam]
                                · linarith only [h10956, h10959, h11002, h11007, h6310, h9935, hc34, hc45, hlam, hphi]
                          · linarith only [h10897, h10959, h11002, h6310, hc23, hc35, hlam, hphi]
                    · linarith only [h10897, h10956, h10958, h6310, h9935, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h10896, h10956, h10957, h9935, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h0, h10895, h10956, hlam]
              · linarith only [h0, h10894, h10955, hlam]
        · linarith only [h10897, h6310, h9935, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h11016 | h11016
        · rcases m.htr 0 3 5 (by decide) (by decide) with h11017 | h11017
          · linarith only [h10894, h10896, h11017, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h11019 | h11019
            · linarith only [h10894, h10896, h11019, h6310, h9935, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h11021 | h11021
              · rcases m.htr 1 2 4 (by decide) (by decide) with h11022 | h11022
                · rcases m.htr 1 2 5 (by decide) (by decide) with h11023 | h11023
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h11024 | h11024
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h11025 | h11025
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11026 | h11026
                        · linarith only [h10894, h10896, h11019, h11023, h11026, h6310, h9935, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11028 | h11028
                          · linarith only [h10894, h10896, h11023, h11028, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h10894, h10896, h11016, h11023, h11028, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11031 | h11031
                        · linarith only [h10894, h10896, h11023, h11031, h6310, h9935, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11033 | h11033
                          · linarith only [h10894, h10896, h11023, h11033, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h10894, h10896, h11016, h11023, h11033, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h11016, h11022, h11024, h6310, h9935, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h11037 | h11037
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h11038 | h11038
                      · linarith only [h11017, h11021, h11022, h11023, h11038, h6310, h9935, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11040 | h11040
                        · linarith only [h0, h11023, h11040, h9935, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11042 | h11042
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11043 | h11043
                            · linarith only [h10894, h11038, h11043, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11045 | h11045
                              · linarith only [h0, h11022, h11023, h11040, h11043, h11045, h9935, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h0, h11022, h11023, h11042, h11045, h9935, hc34, hc45, hlam, hphi]
                          · linarith only [h11016, h11038, h11042, h6310, hc23, hc35, hlam, hphi]
                    · linarith only [h11016, h11037, h6310, h9935, hlam]
                · linarith only [h0, h10895, h11022, hlam]
              · linarith only [h0, h10894, h11021, hlam]
        · linarith only [h11016, h6310, h9935, hlam]
    · linarith only [h0, h10895, h9935, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h11054 | h11054
    · rcases m.htr 0 2 5 (by decide) (by decide) with h11055 | h11055
      · rcases m.htr 0 3 4 (by decide) (by decide) with h11056 | h11056
        · rcases m.htr 0 3 5 (by decide) (by decide) with h11057 | h11057
          · rcases m.htr 0 4 5 (by decide) (by decide) with h11058 | h11058
            · linarith only [h11058, h9935, h9936, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h11060 | h11060
              · rcases m.htr 1 2 4 (by decide) (by decide) with h11061 | h11061
                · rcases m.htr 1 2 5 (by decide) (by decide) with h11062 | h11062
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h11063 | h11063
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h11064 | h11064
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11065 | h11065
                        · linarith only [h11058, h11065, h9935, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11067 | h11067
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11068 | h11068
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11069 | h11069
                              · linarith only [h11061, h11065, h11069, h9935, h9936, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h11071 | h11071
                                · linarith only [h11061, h11065, h11067, h11071, h9935, h9936, hlam]
                                · rcases h0bigk with h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c | h11073c
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [hlam, p11073_0]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h0, hlam, p11073_1]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h6310, hlam, p11073_0]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h10894, h11055, h11060, h9936, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p11073_1]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h9936, hlam, p11073_1]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h10894, h11060, hc01, hc12, hlam, hphi, p11073_1]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [hlam, p11073_0]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h10894, hlam, p11073_0]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h10894, h11060, h11061, h11067, h9935, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11073_1]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h10894, h11060, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p11073_1]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h11061, h11067, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p11073_1, u0elo2]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h0, h10894, h11060, h11061, h11067, h9935, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11073_1]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [hlam, p11073_0]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    rcases p11073_3 (m.d 0 1) (by simp) with h11087 | h11087
                                    · linarith only [h11087, h6310, hlam]
                                    · linarith only [h11087, h9935, hlam]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h10894, h11060, h11061, h11067, h9935, h9936, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11073_1]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h9935, hlam, p11073_0]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h11054, hlam, p11073_0]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h11056, hlam, p11073_0]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [hlam, p11073_0]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h11058, hlam, p11073_0]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h11055, h11061, h11067, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p11073_1, u0elo1]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h11055, hlam, p11073_1]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h11057, hlam, p11073_0]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [h10894, h11055, h11060, h11061, h11067, h9935, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11073_1]
                                  · have p11073_0 := h11073c.1
                                    have p11073_1 := h11073c.2.1
                                    have p11073_2 := h11073c.2.2.1
                                    have p11073_3 := h11073c.2.2.2
                                    linarith only [hlam, p11073_0]
                            · linarith only [h10894, h11057, h11068, hlam]
                          · linarith only [h10894, h11056, h11067, hlam]
                      · linarith only [h10894, h11055, h11057, h11060, h11064, hlam]
                    · linarith only [h10894, h11056, h11060, h11063, hlam]
                  · linarith only [h10894, h11055, h11062, hc12, hc23, hlam, hphi]
                · linarith only [h10894, h11060, h11061, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h11107 | h11107
                · rcases m.htr 1 2 5 (by decide) (by decide) with h11108 | h11108
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h11109 | h11109
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h11110 | h11110
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11111 | h11111
                        · linarith only [h11060, h11108, h11111, h9935, h9936, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11113 | h11113
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11114 | h11114
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11115 | h11115
                              · linarith only [h11107, h11111, h11115, h9935, h9936, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h11117 | h11117
                                · linarith only [h11107, h11111, h11113, h11117, h9935, h9936, hlam]
                                · rcases h0bigk with h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [hlam, p11119_0]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [h0, hlam, p11119_1]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [h6310, hlam, p11119_0]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [h11107, h11111, h11113, h9935, h9936, hc34, hc45, hlam, hphi, p11119_1]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [h9936, hlam, p11119_1]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [h0, h11060, hc01, hc23, hlam, hphi, ht12, p11119_1]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [hlam, p11119_0]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [h10894, hlam, p11119_0]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    rcases p11119_3 (m.d 0 1) (by simp) with h11128 | h11128
                                    · linarith only [h0, h11128, hlam]
                                    · linarith only [h11128, h9935, hlam]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [h0, h11060, h11107, h11113, h9935, h9936, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11119_1]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [h11107, h11113, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p11119_1, u0elo2]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [h0, h11107, h11113, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p11119_1, u0elo2]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [hlam, p11119_0]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    rcases p11119_3 (m.d 0 1) (by simp) with h11135 | h11135
                                    · linarith only [h11135, h6310, hlam]
                                    · linarith only [h11135, h9935, hlam]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [h11107, h11113, h9935, h9936, hc34, hlam, hphi, ht0b, ht45, ht5b, p11119_1, u0elo2]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [h9935, hlam, p11119_0]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [h11054, hlam, p11119_0]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [h11056, hlam, p11119_0]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [hlam, p11119_0]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [h11058, hlam, p11119_0]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [h11107, h11113, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p11119_1, u0elo4]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [h11055, hlam, p11119_1]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [h11057, hlam, p11119_0]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    rcases p11119_3 (m.d 0 1) (by simp) with h11147 | h11147
                                    · linarith only [h11147, h9936, hlam]
                                    · linarith only [h11147, h9935, hlam]
                                  · have p11119_0 := h11119c.1
                                    have p11119_1 := h11119c.2.1
                                    have p11119_2 := h11119c.2.2.1
                                    have p11119_3 := h11119c.2.2.2
                                    linarith only [hlam, p11119_0]
                            · linarith only [h0, h11060, h11107, h11113, h11114, h9935, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h11060, h11113, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h11057, h11110, h6310, hlam]
                    · linarith only [h11056, h11109, h6310, hlam]
                  · linarith only [h0, h11055, h11108, hlam]
                · linarith only [h0, h11054, h11107, hlam]
          · linarith only [h10894, h11055, h11057, hlam]
        · linarith only [h0, h10894, h11056, h9935, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h11159 | h11159
        · rcases m.htr 0 3 5 (by decide) (by decide) with h11160 | h11160
          · rcases m.htr 0 4 5 (by decide) (by decide) with h11161 | h11161
            · linarith only [h0, h11055, h11161, h9935, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h11163 | h11163
              · rcases m.htr 1 2 4 (by decide) (by decide) with h11164 | h11164
                · rcases m.htr 1 2 5 (by decide) (by decide) with h11165 | h11165
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h11166 | h11166
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h11167 | h11167
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11168 | h11168
                        · linarith only [h11161, h11168, h9935, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11170 | h11170
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11171 | h11171
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11172 | h11172
                              · linarith only [h0, h11055, h11164, h11165, h11168, h11172, h9935, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h11174 | h11174
                                · linarith only [h0, h11055, h11164, h11165, h11168, h11170, h11174, h9935, hlam]
                                · rcases h0bigk with h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c | h11176c
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [hlam, p11176_0]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h0, hlam, p11176_1]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h6310, hlam, p11176_0]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h0, h11055, h11163, h11171, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p11176_1]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h9936, hlam, p11176_1]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h11055, h11163, h11171, hc01, hc12, hlam, hphi, p11176_1]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [hlam, p11176_0]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h10894, hlam, p11176_0]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h11055, h11163, h11164, h11170, h11171, h9935, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11176_1]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h11055, hlam, p11176_0]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h11164, h11170, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p11176_1, u0elo2]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h0, h10894, h11163, h11164, h11170, h9935, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11176_1]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [hlam, p11176_0]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    rcases p11176_3 (m.d 0 1) (by simp) with h11190 | h11190
                                    · linarith only [h11190, h6310, hlam]
                                    · linarith only [h11190, h9935, hlam]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h0, h10894, h11055, h11163, h11164, h11170, h9935, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11176_1]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h9935, hlam, p11176_0]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h11054, hlam, p11176_0]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h11159, hlam, p11176_0]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [hlam, p11176_0]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h11161, hlam, p11176_0]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h11164, h11170, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p11176_1, u0elo4]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h0, h11055, h11163, h11164, h11170, h11171, h9935, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11176_1]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [h11160, hlam, p11176_0]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    rcases p11176_3 (m.d 0 1) (by simp) with h11202 | h11202
                                    · linarith only [h11202, h9936, hlam]
                                    · linarith only [h11202, h9935, hlam]
                                  · have p11176_0 := h11176c.1
                                    have p11176_1 := h11176c.2.1
                                    have p11176_2 := h11176c.2.2.1
                                    have p11176_3 := h11176c.2.2.2
                                    linarith only [hlam, p11176_0]
                            · linarith only [h10894, h11160, h11171, hlam]
                          · linarith only [h0, h10894, h11159, h11164, h11170, h9935, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h10894, h11160, h11163, h11167, hlam]
                    · linarith only [h10894, h11159, h11163, h11166, hlam]
                  · linarith only [h0, h10894, h11163, h11165, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h10894, h11163, h11164, h9935, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h11212 | h11212
                · rcases m.htr 1 2 5 (by decide) (by decide) with h11213 | h11213
                  · linarith only [h0, h11055, h11163, h11212, h11213, h9935, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h11215 | h11215
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h11216 | h11216
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11217 | h11217
                        · linarith only [h0, h11163, h11217, h9935, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11219 | h11219
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11220 | h11220
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11221 | h11221
                              · linarith only [h0, h11054, h11213, h11217, h11220, h11221, h9936, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h11212, h11213, h11219, h11221, h9935, hc34, hc45, hlam, hphi]
                            · linarith only [h10894, h11160, h11220, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h0, h11163, h11219, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h11160, h11212, h11216, h6310, h9935, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h11159, h11215, h6310, hlam]
                · linarith only [h0, h11054, h11212, h9935, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h11229 | h11229
            · linarith only [h11160, h11229, h6310, h9935, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h11231 | h11231
              · rcases m.htr 1 2 4 (by decide) (by decide) with h11232 | h11232
                · rcases m.htr 1 2 5 (by decide) (by decide) with h11233 | h11233
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h11234 | h11234
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h11235 | h11235
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11236 | h11236
                        · linarith only [h11229, h11236, h9935, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11238 | h11238
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11239 | h11239
                            · linarith only [h0, h10894, h11160, h11231, h11239, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h10894, h11232, h11235, h11236, h11238, h11239, h9935, hc34, hc45, hlam, hphi]
                          · linarith only [h0, h10894, h11159, h11232, h11238, h9935, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11243 | h11243
                        · linarith only [h11235, h11243, h6310, h9935, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11245 | h11245
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11246 | h11246
                            · linarith only [h11231, h11235, h11246, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11248 | h11248
                              · linarith only [h0, h10894, h11231, h11232, h11235, h11243, h11248, h9935, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h11250 | h11250
                                · linarith only [h0, h10894, h11232, h11233, h11243, h11245, h11246, h11250, h9935, hlam]
                                · linarith only [h0, h10894, h11231, h11235, h11250, h9935, hc14, hc45, hlam, hphi]
                          · linarith only [h0, h10894, h11159, h11232, h11245, h9935, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h11159, h11232, h11234, h6310, h9935, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h10894, h11231, h11232, h11233, h9935, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h10894, h11231, h11232, h9935, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h11257 | h11257
                · rcases m.htr 1 2 5 (by decide) (by decide) with h11258 | h11258
                  · linarith only [h0, h11055, h11231, h11257, h11258, h9935, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h11260 | h11260
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h11261 | h11261
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11262 | h11262
                        · linarith only [h0, h11231, h11262, h9935, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11264 | h11264
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11265 | h11265
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11266 | h11266
                              · linarith only [h0, h10894, h11160, h11231, h11257, h11258, h11261, h11262, h11266, h9935, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h11257, h11258, h11264, h11266, h9935, hc34, hc45, hlam, hphi]
                            · linarith only [h11231, h11261, h11265, hlam]
                          · linarith only [h0, h10894, h11160, h11231, h11257, h11261, h11264, h9935, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11271 | h11271
                        · linarith only [h0, h11231, h11261, h11271, h9935, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11273 | h11273
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11274 | h11274
                            · linarith only [h0, h11231, h11257, h11261, h11273, h11274, h9935, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h11231, h11257, h11273, h11274, h9935, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h11231, h11257, h11273, h9935, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h11159, h11231, h11260, h9935, hlam]
                · linarith only [h0, h11054, h11257, hlam]
        · linarith only [h11159, h6310, h9935, hlam]
    · linarith only [h0, h11054, h9935, hlam]

set_option maxHeartbeats 14334000 in
set_option maxHeartbeats 14334000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h9935 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  rcases m.htr 0 1 5 (by decide) (by decide) with h9936 | h9936
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 h9935 h9936
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 h9935 h9936

set_option maxHeartbeats 14334000 in
set_option maxHeartbeats 14334000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s15 m hb0 hb1 hb3 hb4 h0 h6310 h9935

set_option maxHeartbeats 14334000 in
set_option maxHeartbeats 14334000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  rcases m.htr 0 1 4 (by decide) (by decide) with h9935 | h9935
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 h9935
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 h9935

set_option maxHeartbeats 21584000 in
set_option maxHeartbeats 21584000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s7 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h6310 | h6310
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s8 m hb0 hb1 hb3 hb4 h0 h6310
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14 m hb0 hb1 hb3 hb4 h0 h6310

set_option maxHeartbeats 34204000 in
set_option maxHeartbeats 34204000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s7 m hb0 hb1 hb3 hb4 h0

end R2N4
