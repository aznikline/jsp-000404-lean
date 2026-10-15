import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_22S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4340 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4341 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4342 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h4343 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  linarith only [h3609, h4337, h4343, hlam]

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4340 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4341 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4342 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 1 3 4 (by decide) (by decide) with h4343 | h4343
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338 h4339 h4340 h4341 h4342 h4343
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338 h4339 h4340 h4341 h4342 h4343

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4340 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4341 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4342 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  linarith only [h3609, h4340, h4342, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4340 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4341 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 1 2 5 (by decide) (by decide) with h4342 | h4342
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338 h4339 h4340 h4341 h4342
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338 h4339 h4340 h4341 h4342

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4340 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4341 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  linarith only [h0, h4335, h4341, hlam]

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4340 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 1 2 4 (by decide) (by decide) with h4341 | h4341
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338 h4339 h4340 h4341
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338 h4339 h4340 h4341

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  linarith only [h0, h4334, h4340, hlam]

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 1 2 3 (by decide) (by decide) with h4340 | h4340
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338 h4339 h4340
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338 h4339 h4340

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  linarith only [h4339, hc04, hlam, hphi, ht45, u5elo4]

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 0 4 5 (by decide) (by decide) with h4339 | h4339
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338 h4339
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338 h4339

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  linarith only [h4113, h4337, h4338, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 0 3 5 (by decide) (by decide) with h4338 | h4338
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 0 3 5 (by decide) (by decide) with h5792 | h5792
  · rcases m.htr 0 4 5 (by decide) (by decide) with h5793 | h5793
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5794 | h5794
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5795 | h5795
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5796 | h5796
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5797 | h5797
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5798 | h5798
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5799 | h5799
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5800 | h5800
                  · linarith only [h3609, h4333, h4334, h4337, h5796, h5800, hc02, hc25, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5802 | h5802
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5803 | h5803
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5804 | h5804
                        · rcases h0bigk with h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [hlam, p5805_0]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [h0, hlam, p5805_1]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [h3609, hlam, p5805_0]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [h4113, hlam, p5805_1]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [h3609, h4337, h5797, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p5805_1]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            rcases p5805_3 (m.d 0 1) (by simp) with h5811 | h5811
                            · linarith only [h0, h5811, hlam]
                            · rcases p5805_3 (m.d 0 2) (by simp) with h5813 | h5813
                              · rcases p5805_3 (m.d 0 3) (by simp) with h5814 | h5814
                                · linarith only [h4334, h5814, hlam]
                                · linarith only [h3609, h5814, hlam]
                              · linarith only [h0, h5813, hlam]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [hlam, p5805_0]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            rcases p5805_3 (m.d 0 1) (by simp) with h5819 | h5819
                            · linarith only [h0, h5819, hlam]
                            · rcases p5805_3 (m.d 0 2) (by simp) with h5821 | h5821
                              · rcases p5805_3 (m.d 0 3) (by simp) with h5822 | h5822
                                · linarith only [h4334, h5822, hlam]
                                · rcases p5805_3 (m.d 0 4) (by simp) with h5824 | h5824
                                  · linarith only [h4335, h5824, hlam]
                                  · linarith only [h4337, h5824, hlam]
                              · linarith only [h4334, h5821, hlam]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            rcases p5805_3 (m.d 0 1) (by simp) with h5828 | h5828
                            · linarith only [h0, h5828, hlam]
                            · rcases p5805_3 (m.d 0 2) (by simp) with h5830 | h5830
                              · rcases p5805_3 (m.d 0 3) (by simp) with h5831 | h5831
                                · linarith only [h4334, h5831, hlam]
                                · rcases p5805_3 (m.d 0 4) (by simp) with h5833 | h5833
                                  · linarith only [h4335, h5833, hlam]
                                  · rcases p5805_3 (m.d 0 5) (by simp) with h5835 | h5835
                                    · linarith only [h4336, h5835, hlam]
                                    · rcases h0emin with h5837 | h5837 | h5837 | h5837 | h5837
                                      · linarith only [h0, h3609, h4337, h5837, hc12, hlam, ht01, p5805_1]
                                      · rcases h2bigk with h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [hlam, p5839_0]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [h0, hlam, p5839_1]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          rcases p5839_3 (m.d 0 2) (by simp) with h5842 | h5842
                                          · rcases p5839_3 (m.d 1 2) (by simp) with h5843 | h5843
                                            · rcases p5839_3 (m.d 2 3) (by simp) with h5844 | h5844
                                              · linarith only [h5844, hlam, p5839_0]
                                              · rcases p5839_3 (m.d 2 4) (by simp) with h5846 | h5846
                                                · linarith only [h4335, h5846, hlam]
                                                · linarith only [h5800, h5846, hlam]
                                            · linarith only [h5794, h5843, hlam]
                                          · linarith only [h5842, hlam, p5839_0]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          rcases p5839_3 (m.d 0 2) (by simp) with h5851 | h5851
                                          · rcases p5839_3 (m.d 1 2) (by simp) with h5852 | h5852
                                            · rcases p5839_3 (m.d 2 3) (by simp) with h5853 | h5853
                                              · linarith only [h4334, h5853, hlam]
                                              · rcases p5839_3 (m.d 2 4) (by simp) with h5855 | h5855
                                                · linarith only [h5855, hlam, p5839_0]
                                                · rcases p5839_3 (m.d 2 5) (by simp) with h5857 | h5857
                                                  · linarith only [h4336, h5857, hlam]
                                                  · rcases h3bigk with h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c | h5859c
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [hlam, p5859_0]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [h3609, hlam, p5859_1]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [h0, h4337, h5802, h5804, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5805_1, p5859_1]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [h4337, hlam, p5859_0]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [h0, h4337, h5804, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5805_1, p5859_1]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      rcases p5859_3 (m.d 0 3) (by simp) with h5865 | h5865
                                                      · linarith only [h3609, h5865, hlam]
                                                      · rcases p5859_3 (m.d 1 3) (by simp) with h5867 | h5867
                                                        · rcases p5859_3 (m.d 2 3) (by simp) with h5868 | h5868
                                                          · linarith only [h5794, h5868, hlam]
                                                          · rcases p5859_3 (m.d 3 4) (by simp) with h5870 | h5870
                                                            · linarith only [h5797, h5870, hlam]
                                                            · linarith only [h4337, h5870, hlam]
                                                        · linarith only [h3609, h5867, hlam]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [hlam, p5859_0]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      rcases p5859_3 (m.d 0 3) (by simp) with h5875 | h5875
                                                      · linarith only [h3609, h5875, hlam]
                                                      · linarith only [h4334, h5875, hlam]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [h3609, h4333, h4337, h5794, h5796, h5802, h5804, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5859_1]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [h3609, h4333, h4337, h5796, h5797, h5802, hlam, p5859_2]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [h4334, hlam, p5859_0]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [h5794, hlam, p5859_0]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [hlam, p5859_0]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [h5800, hlam, p5859_0]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [h0, h5800, h5804, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5839_1, p5859_1]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [h3609, h4333, h5796, h5797, h5802, h5804, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p5859_1]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [h5797, hlam, p5859_0]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [h5794, h5797, h5802, h5804, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5859_1]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [hlam, p5859_0]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      rcases p5859_3 (m.d 0 3) (by simp) with h5889 | h5889
                                                      · linarith only [h4337, h5889, hlam]
                                                      · linarith only [h5792, h5889, hlam]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [h5792, hlam, p5859_0]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [h5798, hlam, p5859_0]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [h5802, hlam, p5859_0]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [h5804, hlam, p5859_0]
                                                    · have p5859_0 := h5859c.1
                                                      have p5859_1 := h5859c.2.1
                                                      have p5859_2 := h5859c.2.2.1
                                                      have p5859_3 := h5859c.2.2.2
                                                      linarith only [hlam, p5859_0]
                                            · linarith only [h5795, h5852, hlam]
                                          · linarith only [h5851, hlam, p5839_0]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [h4113, h4333, h5796, hlam, p5805_1, p5839_2]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [h5837, hc12, hlam, ht01, p5839_1]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [hlam, p5839_0]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          rcases p5839_3 (m.d 0 2) (by simp) with h5902 | h5902
                                          · linarith only [h0, h5902, hlam]
                                          · linarith only [h4334, h5902, hlam]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          rcases p5839_3 (m.d 0 2) (by simp) with h5905 | h5905
                                          · linarith only [h0, h5905, hlam]
                                          · linarith only [h4335, h5905, hlam]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [h0, h3609, h4333, h4337, h5796, hlam, p5805_1, p5839_2]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [h4334, hlam, p5839_0]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [h5794, hlam, p5839_0]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [hlam, p5839_0]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [h5800, hlam, p5839_0]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [h4334, h4337, h5802, h5804, hc02, hc45, hlam, hphi, ht0b, ht5b, p5805_1, p5839_1]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [h4335, hlam, p5839_0]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [h5795, hlam, p5839_0]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [h0, h4335, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5805_1, p5839_1]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [hlam, p5839_0]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [h0, h4335, h5802, h5804, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5805_1, p5839_1]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [h4336, hlam, p5839_0]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [h5796, hlam, p5839_0]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [h5802, hlam, p5839_1]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [h5803, hlam, p5839_0]
                                        · have p5839_0 := h5839c.1
                                          have p5839_1 := h5839c.2.1
                                          have p5839_2 := h5839c.2.2.1
                                          have p5839_3 := h5839c.2.2.2
                                          linarith only [hlam, p5839_0]
                                      · linarith only [h0, h4337, h5837, hc12, hlam, ht01, p5805_1]
                                      · linarith only [h0, h5837, hc12, hlam, ht01, p5805_1]
                                      · linarith only [h5837, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                              · linarith only [h4335, h5830, hlam]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            rcases p5805_3 (m.d 0 1) (by simp) with h5928 | h5928
                            · linarith only [h0, h5928, hlam]
                            · linarith only [h4333, h5928, hlam]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [h4333, h4337, h5794, h5796, h5797, h5802, h5804, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5805_1]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [h4334, hlam, p5805_1]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [hlam, p5805_0]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [h4337, hlam, p5805_1]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [h4337, h5794, h5797, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p5805_1]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [h4333, h4337, h5794, h5796, h5797, h5802, h5804, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5805_1]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [h4335, hlam, p5805_0]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [h3609, h4333, h4337, h5794, h5796, h5797, h5802, h5804, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5805_1]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [hlam, p5805_0]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            rcases p5805_3 (m.d 0 1) (by simp) with h5940 | h5940
                            · linarith only [h4113, h5940, hlam]
                            · linarith only [h4333, h5940, hlam]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [h4333, hlam, p5805_0]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [h4336, hlam, p5805_1]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [h5792, hlam, p5805_0]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [h5793, hlam, p5805_1]
                          · have p5805_0 := h5805c.1
                            have p5805_1 := h5805c.2.1
                            have p5805_2 := h5805c.2.2.1
                            have p5805_3 := h5805c.2.2.2
                            linarith only [hlam, p5805_0]
                        · linarith only [h4335, h4337, h5804, hc24, hlam, hphi, ht45, u5elo4]
                      · linarith only [h3609, h4333, h4337, h5794, h5797, h5799, h5800, h5803, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h5802, hc23, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h3609, h4337, h5797, h5799, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · linarith only [h3609, h4337, h5797, h5798, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5953 | h5953
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5954 | h5954
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5955 | h5955
                  · linarith only [h3609, h4333, h5796, h5797, h5955, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5957 | h5957
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5958 | h5958
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5959 | h5959
                        · rcases h0bigk with h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h0, hlam, p5960_1]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h3609, hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h4113, hlam, p5960_1]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h3609, h4333, h5796, h5797, h5957, h5959, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5960_1]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            rcases p5960_3 (m.d 0 1) (by simp) with h5966 | h5966
                            · linarith only [h0, h5966, hlam]
                            · rcases p5960_3 (m.d 0 2) (by simp) with h5968 | h5968
                              · rcases p5960_3 (m.d 0 3) (by simp) with h5969 | h5969
                                · linarith only [h4334, h5969, hlam]
                                · linarith only [h3609, h5969, hlam]
                              · linarith only [h0, h5968, hlam]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            rcases p5960_3 (m.d 0 1) (by simp) with h5974 | h5974
                            · linarith only [h0, h5974, hlam]
                            · rcases p5960_3 (m.d 0 2) (by simp) with h5976 | h5976
                              · rcases p5960_3 (m.d 0 3) (by simp) with h5977 | h5977
                                · linarith only [h4334, h5977, hlam]
                                · rcases p5960_3 (m.d 0 4) (by simp) with h5979 | h5979
                                  · linarith only [h4335, h5979, hlam]
                                  · linarith only [h4337, h5979, hlam]
                              · linarith only [h4334, h5976, hlam]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            rcases p5960_3 (m.d 0 1) (by simp) with h5983 | h5983
                            · linarith only [h0, h5983, hlam]
                            · rcases p5960_3 (m.d 0 2) (by simp) with h5985 | h5985
                              · rcases p5960_3 (m.d 0 3) (by simp) with h5986 | h5986
                                · linarith only [h4334, h5986, hlam]
                                · rcases p5960_3 (m.d 0 4) (by simp) with h5988 | h5988
                                  · linarith only [h4335, h5988, hlam]
                                  · rcases p5960_3 (m.d 0 5) (by simp) with h5990 | h5990
                                    · linarith only [h4336, h5990, hlam]
                                    · rcases h0emin with h5992 | h5992 | h5992 | h5992 | h5992
                                      · linarith only [h0, h3609, h4337, h5992, hc12, hlam, ht01, p5960_1]
                                      · rcases h2bigk with h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [hlam, p5994_0]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [h0, hlam, p5994_1]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          rcases p5994_3 (m.d 0 2) (by simp) with h5997 | h5997
                                          · rcases p5994_3 (m.d 1 2) (by simp) with h5998 | h5998
                                            · rcases p5994_3 (m.d 2 3) (by simp) with h5999 | h5999
                                              · linarith only [h5999, hlam, p5994_0]
                                              · rcases p5994_3 (m.d 2 4) (by simp) with h6001 | h6001
                                                · linarith only [h4335, h6001, hlam]
                                                · linarith only [h5955, h6001, hlam]
                                            · linarith only [h5794, h5998, hlam]
                                          · linarith only [h5997, hlam, p5994_0]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          rcases p5994_3 (m.d 0 2) (by simp) with h6006 | h6006
                                          · rcases p5994_3 (m.d 1 2) (by simp) with h6007 | h6007
                                            · rcases p5994_3 (m.d 2 3) (by simp) with h6008 | h6008
                                              · linarith only [h4334, h6008, hlam]
                                              · rcases p5994_3 (m.d 2 4) (by simp) with h6010 | h6010
                                                · linarith only [h6010, hlam, p5994_0]
                                                · rcases p5994_3 (m.d 2 5) (by simp) with h6012 | h6012
                                                  · linarith only [h4336, h6012, hlam]
                                                  · rcases h3bigk with h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c | h6014c
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [hlam, p6014_0]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [h3609, hlam, p6014_1]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [h0, h4337, h5957, h5959, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5960_1, p6014_1]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [h4337, hlam, p6014_0]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [h0, h4337, h5959, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5960_1, p6014_1]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [h3609, h5797, hc01, hc34, hlam, hphi, ht12, ht23, p6014_1]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [hlam, p6014_0]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [h5797, h5957, h5959, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6014_1]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [h5797, hlam, p6014_0]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      rcases p6014_3 (m.d 0 3) (by simp) with h6024 | h6024
                                                      · linarith only [h3609, h6024, hlam]
                                                      · linarith only [h5792, h6024, hlam]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [h4334, hlam, p6014_0]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [h5794, hlam, p6014_0]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [hlam, p6014_0]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [h5955, hlam, p6014_0]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [h0, h5955, h5959, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5994_1, p6014_1]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      rcases p6014_3 (m.d 0 3) (by simp) with h6032 | h6032
                                                      · linarith only [h6032, hlam, p6014_0]
                                                      · rcases p6014_3 (m.d 1 3) (by simp) with h6034 | h6034
                                                        · linarith only [h5797, h6034, hlam]
                                                        · linarith only [h3609, h6034, hlam]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [h3609, h4333, h5796, h5957, h5959, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6014_1]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      rcases p6014_3 (m.d 0 3) (by simp) with h6038 | h6038
                                                      · linarith only [h4337, h6038, hlam]
                                                      · linarith only [h4334, h6038, hlam]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [hlam, p6014_0]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [h3609, h4333, h5796, h5797, h5957, hlam, p6014_2]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [h5792, hlam, p6014_0]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [h5953, hlam, p6014_0]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [h5957, hlam, p6014_0]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [h5959, hlam, p6014_0]
                                                    · have p6014_0 := h6014c.1
                                                      have p6014_1 := h6014c.2.1
                                                      have p6014_2 := h6014c.2.2.1
                                                      have p6014_3 := h6014c.2.2.2
                                                      linarith only [hlam, p6014_0]
                                            · linarith only [h5795, h6007, hlam]
                                          · linarith only [h6006, hlam, p5994_0]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [h4113, h4333, h5796, hlam, p5960_1, p5994_2]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [h5992, hc12, hlam, ht01, p5994_1]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [hlam, p5994_0]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          rcases p5994_3 (m.d 0 2) (by simp) with h6053 | h6053
                                          · linarith only [h0, h6053, hlam]
                                          · linarith only [h4334, h6053, hlam]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          rcases p5994_3 (m.d 0 2) (by simp) with h6056 | h6056
                                          · linarith only [h0, h6056, hlam]
                                          · linarith only [h4335, h6056, hlam]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [h0, h3609, h4333, h4337, h5796, hlam, p5960_1, p5994_2]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [h4334, hlam, p5994_0]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [h5794, hlam, p5994_0]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [hlam, p5994_0]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [h5955, hlam, p5994_0]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [h4335, h5955, h5957, h5959, hc02, hc45, hlam, hphi, ht0b, ht5b, p5960_1, p5994_1]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [h4335, hlam, p5994_0]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [h5795, hlam, p5994_0]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [h0, h4335, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5960_1, p5994_1]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [hlam, p5994_0]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [h0, h4335, h5957, h5959, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5960_1, p5994_1]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [h4336, hlam, p5994_0]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [h5796, hlam, p5994_0]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [h5957, hlam, p5994_1]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [h5958, hlam, p5994_0]
                                        · have p5994_0 := h5994c.1
                                          have p5994_1 := h5994c.2.1
                                          have p5994_2 := h5994c.2.2.1
                                          have p5994_3 := h5994c.2.2.2
                                          linarith only [hlam, p5994_0]
                                      · linarith only [h3609, h5797, h5992, hc34, hlam, ht01, ht12, ht23]
                                      · linarith only [h0, h5992, hc12, hlam, ht01, p5960_1]
                                      · linarith only [h5992, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                              · linarith only [h4335, h5985, hlam]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            rcases p5960_3 (m.d 0 1) (by simp) with h6079 | h6079
                            · linarith only [h0, h6079, hlam]
                            · linarith only [h4333, h6079, hlam]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h3609, h4333, h5796, h5797, h5957, h5959, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5960_1]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h4334, hlam, p5960_1]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h4337, hlam, p5960_1]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            rcases p5960_3 (m.d 0 1) (by simp) with h6086 | h6086
                            · linarith only [h3609, h6086, hlam]
                            · linarith only [h4333, h6086, hlam]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            rcases p5960_3 (m.d 0 1) (by simp) with h6089 | h6089
                            · linarith only [h4113, h6089, hlam]
                            · rcases p5960_3 (m.d 0 2) (by simp) with h6091 | h6091
                              · rcases p5960_3 (m.d 0 3) (by simp) with h6092 | h6092
                                · linarith only [h4337, h6092, hlam]
                                · linarith only [h3609, h6092, hlam]
                              · linarith only [h0, h6091, hlam]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h4335, hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            rcases p5960_3 (m.d 0 1) (by simp) with h6097 | h6097
                            · linarith only [h4113, h6097, hlam]
                            · rcases p5960_3 (m.d 0 2) (by simp) with h6099 | h6099
                              · rcases p5960_3 (m.d 0 3) (by simp) with h6100 | h6100
                                · linarith only [h4337, h6100, hlam]
                                · rcases p5960_3 (m.d 0 4) (by simp) with h6102 | h6102
                                  · rcases p5960_3 (m.d 0 5) (by simp) with h6103 | h6103
                                    · linarith only [h5793, h6103, hlam]
                                    · rcases h0emin with h6105 | h6105 | h6105 | h6105 | h6105
                                      · linarith only [h0, h6105, hc12, hlam, ht01]
                                      · rcases h2bigk with h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [hlam, p6107_0]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [h0, hlam, p6107_1]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          rcases p6107_3 (m.d 0 2) (by simp) with h6110 | h6110
                                          · rcases p6107_3 (m.d 1 2) (by simp) with h6111 | h6111
                                            · rcases p6107_3 (m.d 2 3) (by simp) with h6112 | h6112
                                              · linarith only [h6112, hlam, p6107_0]
                                              · rcases p6107_3 (m.d 2 4) (by simp) with h6114 | h6114
                                                · linarith only [h4335, h6114, hlam]
                                                · linarith only [h5955, h6114, hlam]
                                            · linarith only [h5794, h6111, hlam]
                                          · linarith only [h6110, hlam, p6107_0]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          rcases p6107_3 (m.d 0 2) (by simp) with h6119 | h6119
                                          · rcases p6107_3 (m.d 1 2) (by simp) with h6120 | h6120
                                            · rcases p6107_3 (m.d 2 3) (by simp) with h6121 | h6121
                                              · linarith only [h4334, h6121, hlam]
                                              · rcases p6107_3 (m.d 2 4) (by simp) with h6123 | h6123
                                                · linarith only [h6123, hlam, p6107_0]
                                                · rcases p6107_3 (m.d 2 5) (by simp) with h6125 | h6125
                                                  · linarith only [h4336, h6125, hlam]
                                                  · rcases h3bigk with h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c | h6127c
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [hlam, p6127_0]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [h3609, hlam, p6127_1]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [h4113, h5797, h5957, h5959, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5960_1, p6127_1]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [h4337, hlam, p6127_0]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [h4113, h5797, h5959, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5960_1, p6127_1]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [h3609, h5797, hc01, hc34, hlam, hphi, ht12, ht23, p6127_1]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [hlam, p6127_0]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [h5797, h5957, h5959, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6127_1]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [h5797, hlam, p6127_0]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      rcases p6127_3 (m.d 0 3) (by simp) with h6137 | h6137
                                                      · linarith only [h3609, h6137, hlam]
                                                      · linarith only [h5792, h6137, hlam]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [h4334, hlam, p6127_0]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [h5794, hlam, p6127_0]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [hlam, p6127_0]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [h5955, hlam, p6127_0]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [h4113, h4334, h5797, h5959, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5960_1, p6127_1]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      rcases p6127_3 (m.d 0 3) (by simp) with h6145 | h6145
                                                      · linarith only [h6145, hlam, p6127_0]
                                                      · rcases p6127_3 (m.d 1 3) (by simp) with h6147 | h6147
                                                        · linarith only [h5797, h6147, hlam]
                                                        · linarith only [h3609, h6147, hlam]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [h3609, h4333, h5796, h5957, h5959, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6127_1]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      rcases p6127_3 (m.d 0 3) (by simp) with h6151 | h6151
                                                      · linarith only [h4337, h6151, hlam]
                                                      · linarith only [h4334, h6151, hlam]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [hlam, p6127_0]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [h3609, h4113, h4333, h5796, h5797, h5957, hlam, p5960_1, p6127_2]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [h5792, hlam, p6127_0]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [h5953, hlam, p6127_0]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [h5957, hlam, p6127_0]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [h5959, hlam, p6127_0]
                                                    · have p6127_0 := h6127c.1
                                                      have p6127_1 := h6127c.2.1
                                                      have p6127_2 := h6127c.2.2.1
                                                      have p6127_3 := h6127c.2.2.2
                                                      linarith only [hlam, p6127_0]
                                            · linarith only [h5795, h6120, hlam]
                                          · linarith only [h6119, hlam, p6107_0]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [h3609, h4333, h4335, h5796, hlam, p5960_1, p6107_2]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [h6105, hc12, hlam, ht01, p6107_1]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [hlam, p6107_0]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          rcases p6107_3 (m.d 0 2) (by simp) with h6166 | h6166
                                          · linarith only [h0, h6166, hlam]
                                          · linarith only [h4334, h6166, hlam]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          rcases p6107_3 (m.d 0 2) (by simp) with h6169 | h6169
                                          · linarith only [h0, h6169, hlam]
                                          · linarith only [h4335, h6169, hlam]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [h0, h3609, h4333, h4335, h5796, hlam, p5960_1, p6107_2]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [h4334, hlam, p6107_0]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [h5794, hlam, p6107_0]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [hlam, p6107_0]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [h5955, hlam, p6107_0]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [h4334, h4335, h5957, h5959, hc02, hc45, hlam, hphi, ht0b, ht5b, p5960_1, p6107_1]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [h4335, hlam, p6107_0]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [h5795, hlam, p6107_0]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [h0, h4335, h5957, h5959, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6107_1]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [hlam, p6107_0]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          rcases p6107_3 (m.d 0 2) (by simp) with h6182 | h6182
                                          · rcases p6107_3 (m.d 1 2) (by simp) with h6183 | h6183
                                            · rcases p6107_3 (m.d 2 3) (by simp) with h6184 | h6184
                                              · linarith only [h5955, h6184, hlam]
                                              · linarith only [h5957, h6184, hlam]
                                            · linarith only [h5796, h6183, hlam]
                                          · linarith only [h4336, h6182, hlam]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [h4336, hlam, p6107_0]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [h5796, hlam, p6107_0]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [h5957, hlam, p6107_1]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [h5958, hlam, p6107_0]
                                        · have p6107_0 := h6107c.1
                                          have p6107_1 := h6107c.2.1
                                          have p6107_2 := h6107c.2.2.1
                                          have p6107_3 := h6107c.2.2.2
                                          linarith only [hlam, p6107_0]
                                      · linarith only [h4113, h5797, h6105, hc34, hlam, ht01, ht12, ht23, p5960_1]
                                      · rcases h2bigk with h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [hlam, p6195_0]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [h0, hlam, p6195_1]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          rcases p6195_3 (m.d 0 2) (by simp) with h6198 | h6198
                                          · rcases p6195_3 (m.d 1 2) (by simp) with h6199 | h6199
                                            · rcases p6195_3 (m.d 2 3) (by simp) with h6200 | h6200
                                              · linarith only [h6200, hlam, p6195_0]
                                              · rcases p6195_3 (m.d 2 4) (by simp) with h6202 | h6202
                                                · linarith only [h4335, h6202, hlam]
                                                · linarith only [h5955, h6202, hlam]
                                            · linarith only [h5794, h6199, hlam]
                                          · linarith only [h6198, hlam, p6195_0]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          rcases p6195_3 (m.d 0 2) (by simp) with h6207 | h6207
                                          · rcases p6195_3 (m.d 1 2) (by simp) with h6208 | h6208
                                            · rcases p6195_3 (m.d 2 3) (by simp) with h6209 | h6209
                                              · linarith only [h4334, h6209, hlam]
                                              · rcases p6195_3 (m.d 2 4) (by simp) with h6211 | h6211
                                                · linarith only [h6211, hlam, p6195_0]
                                                · rcases p6195_3 (m.d 2 5) (by simp) with h6213 | h6213
                                                  · linarith only [h4336, h6213, hlam]
                                                  · rcases h3bigk with h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [hlam, p6215_0]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [h3609, hlam, p6215_1]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [h4113, h5797, h5957, h5959, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5960_1, p6215_1]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [h4337, hlam, p6215_0]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [h4113, h5797, h5959, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5960_1, p6215_1]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [h3609, h5797, hc01, hc34, hlam, hphi, ht12, ht23, p6215_1]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [hlam, p6215_0]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [h5797, h5957, h5959, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6215_1]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [h5797, hlam, p6215_0]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      rcases p6215_3 (m.d 0 3) (by simp) with h6225 | h6225
                                                      · linarith only [h3609, h6225, hlam]
                                                      · linarith only [h5792, h6225, hlam]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [h4334, hlam, p6215_0]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [h5794, hlam, p6215_0]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [hlam, p6215_0]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [h5955, hlam, p6215_0]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [h4113, h4334, h5797, h5959, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5960_1, p6215_1]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      rcases p6215_3 (m.d 0 3) (by simp) with h6233 | h6233
                                                      · linarith only [h6233, hlam, p6215_0]
                                                      · rcases p6215_3 (m.d 1 3) (by simp) with h6235 | h6235
                                                        · linarith only [h5797, h6235, hlam]
                                                        · linarith only [h3609, h6235, hlam]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [h3609, h4333, h5796, h5957, h5959, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6215_1]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      rcases p6215_3 (m.d 0 3) (by simp) with h6239 | h6239
                                                      · linarith only [h4337, h6239, hlam]
                                                      · linarith only [h4334, h6239, hlam]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [hlam, p6215_0]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [h3609, h4113, h4333, h5796, h5797, h5957, hlam, p5960_1, p6215_2]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [h5792, hlam, p6215_0]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [h5953, hlam, p6215_0]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [h5957, hlam, p6215_0]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [h5959, hlam, p6215_0]
                                                    · have p6215_0 := h6215c.1
                                                      have p6215_1 := h6215c.2.1
                                                      have p6215_2 := h6215c.2.2.1
                                                      have p6215_3 := h6215c.2.2.2
                                                      linarith only [hlam, p6215_0]
                                            · linarith only [h5795, h6208, hlam]
                                          · linarith only [h6207, hlam, p6195_0]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [h3609, h4333, h4335, h5796, hlam, p5960_1, p6195_2]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [h3609, h4333, h4335, h5796, h5957, h5959, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5960_1, p6195_1]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [hlam, p6195_0]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          rcases p6195_3 (m.d 0 2) (by simp) with h6254 | h6254
                                          · linarith only [h0, h6254, hlam]
                                          · linarith only [h4334, h6254, hlam]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          rcases p6195_3 (m.d 0 2) (by simp) with h6257 | h6257
                                          · linarith only [h0, h6257, hlam]
                                          · linarith only [h4335, h6257, hlam]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [h0, h3609, h4333, h4335, h5796, hlam, p5960_1, p6195_2]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [h4334, hlam, p6195_0]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [h5794, hlam, p6195_0]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [hlam, p6195_0]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [h5955, hlam, p6195_0]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [h4113, h4334, h5797, h5957, h5959, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5960_1, p6195_1]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [h4335, hlam, p6195_0]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [h5795, hlam, p6195_0]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [h0, h4335, h5957, h5959, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6195_1]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [hlam, p6195_0]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          rcases p6195_3 (m.d 0 2) (by simp) with h6270 | h6270
                                          · rcases p6195_3 (m.d 1 2) (by simp) with h6271 | h6271
                                            · rcases p6195_3 (m.d 2 3) (by simp) with h6272 | h6272
                                              · linarith only [h5955, h6272, hlam]
                                              · linarith only [h5957, h6272, hlam]
                                            · linarith only [h5796, h6271, hlam]
                                          · linarith only [h4336, h6270, hlam]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [h4336, hlam, p6195_0]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [h5796, hlam, p6195_0]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [h5957, hlam, p6195_1]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [h5958, hlam, p6195_0]
                                        · have p6195_0 := h6195c.1
                                          have p6195_1 := h6195c.2.1
                                          have p6195_2 := h6195c.2.2.1
                                          have p6195_3 := h6195c.2.2.2
                                          linarith only [hlam, p6195_0]
                                      · linarith only [h6105, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                  · linarith only [h4337, h6102, hlam]
                              · linarith only [h4334, h6099, hlam]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            rcases p5960_3 (m.d 0 1) (by simp) with h6286 | h6286
                            · linarith only [h4113, h6286, hlam]
                            · linarith only [h4333, h6286, hlam]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h4333, hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h4336, hlam, p5960_1]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h5792, hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h5793, hlam, p5960_1]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [hlam, p5960_0]
                        · linarith only [h3609, h5797, h5959, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h3609, h4333, h5797, h5954, h5958, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h5957, hc23, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h4113, h5954, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h3609, h5953, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · linarith only [h0, h5796, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h4335, h5795, hlam]
      · linarith only [h0, h4334, h5794, hlam]
    · linarith only [h3609, h4333, h4337, h5793, hc15, hlam, hphi, u5elo4]
  · linarith only [h3609, h4333, h5792, hc15, hlam, hphi, u5elo3]

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 0 3 4 (by decide) (by decide) with h4337 | h4337
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  linarith only [h4336, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]

end R2N4
