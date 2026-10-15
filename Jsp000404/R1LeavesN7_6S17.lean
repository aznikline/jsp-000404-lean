import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S12
import Jsp000404.R1LeavesN7_6S13
import Jsp000404.R1LeavesN7_6S14
import Jsp000404.R1LeavesN7_6S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 0 4 5 (by decide) (by decide) with h7593 | h7593
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 0 3 5 (by decide) (by decide) with h7373 | h7373
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 0 3 4 (by decide) (by decide) with h6799 | h6799
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  linarith only [h0, h6795, h6798, hlam]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 0 2 5 (by decide) (by decide) with h6798 | h6798
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  linarith only [h0, h6794, h6797, hlam]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 0 2 4 (by decide) (by decide) with h6797 | h6797
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  linarith only [h0, h6793, h6796, hlam]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 0 2 3 (by decide) (by decide) with h6796 | h6796
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 0 2 3 (by decide) (by decide) with h9280 | h9280
  · rcases m.htr 0 2 4 (by decide) (by decide) with h9281 | h9281
    · rcases m.htr 0 2 5 (by decide) (by decide) with h9282 | h9282
      · rcases m.htr 0 3 4 (by decide) (by decide) with h9283 | h9283
        · rcases m.htr 0 3 5 (by decide) (by decide) with h9284 | h9284
          · linarith only [h6793, h6795, h9284, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h9286 | h9286
            · linarith only [h6793, h6795, h9283, h9286, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9288 | h9288
              · rcases m.htr 1 2 4 (by decide) (by decide) with h9289 | h9289
                · rcases m.htr 1 2 5 (by decide) (by decide) with h9290 | h9290
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9291 | h9291
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h9292 | h9292
                      · linarith only [h6793, h9286, h9291, h9292, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h6793, h6795, h9291, h9292, hc34, hc45, hlam, hphi]
                    · linarith only [h9283, h9284, h9288, h9291, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h9282, h9290, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h9281, h9289, hlam]
              · linarith only [h0, h9280, h9288, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h9299 | h9299
          · linarith only [h6794, h6795, h9283, h9299, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h9301 | h9301
            · linarith only [h6794, h6795, h9301, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9303 | h9303
              · rcases m.htr 1 2 4 (by decide) (by decide) with h9304 | h9304
                · rcases m.htr 1 2 5 (by decide) (by decide) with h9305 | h9305
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9306 | h9306
                    · linarith only [h6793, h9283, h9306, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h9308 | h9308
                      · linarith only [h6794, h6795, h9282, h9301, h9308, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h9310 | h9310
                        · linarith only [h6793, h9283, h9303, h9310, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h9312 | h9312
                          · linarith only [h6793, h6795, h9299, h9303, h9312, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h9314 | h9314
                            · linarith only [h6795, h9281, h9308, h9314, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h9316 | h9316
                              · linarith only [h6794, h6795, h9303, h9306, h9308, h9316, hc23, hc34, hlam, hphi]
                              · rcases h0bigk with h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c | h9318c
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [hlam, p9318_0]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [h0, hlam, p9318_1]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [h6793, h6795, h9303, h9308, hc23, hc45, hlam, hphi, ht34, p9318_1]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [h6793, h6795, h9283, h9303, h9308, hc23, hc45, hlam, hphi, ht34, p9318_1]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [h6795, hlam, p9318_1]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [h6793, h9303, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9318_1, u0elo1]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [hlam, p9318_0]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  rcases p9318_3 (m.d 0 1) (by simp) with h9326 | h9326
                                  · linarith only [h0, h9326, hlam]
                                  · linarith only [h6793, h9326, hlam]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  rcases p9318_3 (m.d 0 1) (by simp) with h9329 | h9329
                                  · linarith only [h0, h9329, hlam]
                                  · linarith only [h6794, h9329, hlam]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [h6794, h6795, h9303, h9306, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9318_1, u0elo1]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [h6793, hlam, p9318_1]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [h9280, hlam, p9318_1]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [hlam, p9318_0]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [h9283, hlam, p9318_1]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [h9299, hlam, p9318_1]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [h6794, hlam, p9318_0]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [h9281, hlam, p9318_0]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [h6793, h9283, h9303, h9316, hc23, hc45, hlam, hphi, ht34, p9318_1]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [hlam, p9318_0]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [h9301, hlam, p9318_0]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [h6793, h9303, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9318_1, u0elo4]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [h9282, hlam, p9318_1]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  rcases p9318_3 (m.d 0 1) (by simp) with h9345 | h9345
                                  · linarith only [h6795, h9345, hlam]
                                  · linarith only [h6793, h9345, hlam]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  rcases p9318_3 (m.d 0 1) (by simp) with h9348 | h9348
                                  · linarith only [h6795, h9348, hlam]
                                  · linarith only [h6794, h9348, hlam]
                                · have p9318_0 := h9318c.1
                                  have p9318_1 := h9318c.2.1
                                  have p9318_2 := h9318c.2.2.1
                                  have p9318_3 := h9318c.2.2.2
                                  linarith only [hlam, p9318_0]
                  · linarith only [h0, h9282, h9305, hlam]
                · linarith only [h0, h9281, h9304, hlam]
              · linarith only [h0, h6793, h9280, h9303, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h9355 | h9355
        · rcases m.htr 0 3 5 (by decide) (by decide) with h9356 | h9356
          · linarith only [h0, h6793, h9282, h9356, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h9358 | h9358
            · linarith only [h0, h6793, h9282, h9355, h9358, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9360 | h9360
              · rcases m.htr 1 2 4 (by decide) (by decide) with h9361 | h9361
                · rcases m.htr 1 2 5 (by decide) (by decide) with h9362 | h9362
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9363 | h9363
                    · linarith only [h0, h6793, h9282, h9362, h9363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h6793, h9282, h9355, h9360, h9362, h9363, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9366 | h9366
                    · linarith only [h0, h6793, h9362, h9366, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h6793, h9355, h9360, h9362, h9366, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h0, h9281, h9361, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h9280, h9360, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h9371 | h9371
          · linarith only [h6794, h6795, h9355, h9371, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h9373 | h9373
            · linarith only [h0, h6794, h9282, h9373, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9375 | h9375
              · rcases m.htr 1 2 4 (by decide) (by decide) with h9376 | h9376
                · rcases m.htr 1 2 5 (by decide) (by decide) with h9377 | h9377
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9378 | h9378
                    · linarith only [h6793, h9355, h9378, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h9380 | h9380
                      · linarith only [h0, h6794, h9282, h9373, h9377, h9380, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h9382 | h9382
                        · linarith only [h6793, h9355, h9375, h9382, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h9384 | h9384
                          · linarith only [h0, h6793, h9282, h9371, h9375, h9384, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h9386 | h9386
                            · linarith only [h9281, h9282, h9377, h9380, h9386, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h9388 | h9388
                              · linarith only [h0, h6794, h9282, h9375, h9377, h9378, h9380, h9388, hc23, hc34, hlam, hphi]
                              · rcases h0bigk with h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c | h9390c
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [hlam, p9390_0]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h0, hlam, p9390_1]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h0, h6793, h9282, h9375, h9384, hc23, hc35, hlam, hphi, p9390_1]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h0, h6793, h9282, h9355, h9375, h9377, h9380, hc23, hc45, hlam, hphi, ht34, p9390_1]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h6795, hlam, p9390_1]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h9282, h9377, h9380, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9390_1]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [hlam, p9390_0]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h6793, h9282, h9375, h9377, h9380, hc23, hc45, hlam, hphi, ht34, p9390_1]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h6793, h9282, h9355, h9375, h9377, h9380, hc23, hc45, hlam, hphi, ht34, p9390_1]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h9282, hlam, p9390_0]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h6793, hlam, p9390_1]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h9280, hlam, p9390_1]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [hlam, p9390_0]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h9355, hlam, p9390_1]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h9371, hlam, p9390_1]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h6794, hlam, p9390_0]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h9281, hlam, p9390_0]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h0, h6793, h6794, h9282, h9375, h9377, h9380, hc23, hc45, hlam, hphi, ht34, p9390_1]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [hlam, p9390_0]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h9373, hlam, p9390_0]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h6793, h9375, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9390_1, u0elo4]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [h0, h6794, h9282, h9375, h9377, h9378, h9380, hc23, hc45, hlam, hphi, ht34, p9390_1]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  rcases p9390_3 (m.d 0 1) (by simp) with h9413 | h9413
                                  · linarith only [h6795, h9413, hlam]
                                  · linarith only [h6793, h9413, hlam]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  rcases p9390_3 (m.d 0 1) (by simp) with h9416 | h9416
                                  · linarith only [h6795, h9416, hlam]
                                  · linarith only [h6794, h9416, hlam]
                                · have p9390_0 := h9390c.1
                                  have p9390_1 := h9390c.2.1
                                  have p9390_2 := h9390c.2.2.1
                                  have p9390_3 := h9390c.2.2.2
                                  linarith only [hlam, p9390_0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9420 | h9420
                    · linarith only [h0, h6793, h9377, h9420, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h9422 | h9422
                      · linarith only [h0, h6794, h9377, h9422, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h9424 | h9424
                        · linarith only [h6793, h9355, h9375, h9424, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h9426 | h9426
                          · linarith only [h0, h6794, h9375, h9377, h9420, h9426, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h6794, h9375, h9377, h9420, h9426, hc23, hc35, hlam, hphi]
                · linarith only [h0, h6793, h9281, h9375, h9376, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h9280, h9375, hlam]
    · linarith only [h0, h6794, h9281, hlam]
  · linarith only [h0, h6793, h9280, hlam]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 0 1 5 (by decide) (by decide) with h6795 | h6795
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795

end R2N4
