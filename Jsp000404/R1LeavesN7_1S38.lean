import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h26153c : ((m.d 0 1) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 1) ∧ (m.d 0 2) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 2) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have p26153_0 := h26153c.1
  have p26153_1 := h26153c.2.1
  have p26153_2 := h26153c.2.2.1
  have p26153_3 := h26153c.2.2.2
  linarith only [h0, hlam, p26153_1]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x2 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h26153c : ((m.d 0 1) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 1) ∧ (m.d 0 3) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 3) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have p26153_0 := h26153c.1
  have p26153_1 := h26153c.2.1
  have p26153_2 := h26153c.2.2.1
  have p26153_3 := h26153c.2.2.2
  linarith only [h15532, hlam, p26153_0]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x3 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h26153c : ((m.d 0 1) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 1) ∧ (m.d 0 4) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 4) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have p26153_0 := h26153c.1
  have p26153_1 := h26153c.2.1
  have p26153_2 := h26153c.2.2.1
  have p26153_3 := h26153c.2.2.2
  linarith only [h18443, hlam, p26153_1]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x4 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h26153c : ((m.d 0 1) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 1) ∧ (m.d 0 5) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 5) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have p26153_0 := h26153c.1
  have p26153_1 := h26153c.2.1
  have p26153_2 := h26153c.2.2.1
  have p26153_3 := h26153c.2.2.2
  linarith only [h20697, hlam, p26153_1]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x5 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h26153c : ((m.d 0 2) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 2) ∧ (m.d 0 1) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 1) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have p26153_0 := h26153c.1
  have p26153_1 := h26153c.2.1
  have p26153_2 := h26153c.2.2.1
  have p26153_3 := h26153c.2.2.2
  rcases p26153_3 (m.d 0 1) (by simp) with h26159 | h26159
  · linarith only [h0, h26159, hlam]
  · rcases p26153_3 (m.d 0 2) (by simp) with h26161 | h26161
    · rcases p26153_3 (m.d 0 3) (by simp) with h26162 | h26162
      · linarith only [h22350, h26162, hlam]
      · linarith only [h15532, h26162, hlam]
    · linarith only [h0, h26161, hlam]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x6 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h26153c : ((m.d 0 2) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 2) ∧ (m.d 0 2) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 2) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have p26153_0 := h26153c.1
  have p26153_1 := h26153c.2.1
  have p26153_2 := h26153c.2.2.1
  have p26153_3 := h26153c.2.2.2
  linarith only [hlam, p26153_0]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x7 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h26153c : ((m.d 0 2) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 2) ∧ (m.d 0 3) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 3) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have p26153_0 := h26153c.1
  have p26153_1 := h26153c.2.1
  have p26153_2 := h26153c.2.2.1
  have p26153_3 := h26153c.2.2.2
  rcases p26153_3 (m.d 0 1) (by simp) with h26167 | h26167
  · linarith only [h0, h26167, hlam]
  · rcases p26153_3 (m.d 0 2) (by simp) with h26169 | h26169
    · rcases p26153_3 (m.d 0 3) (by simp) with h26170 | h26170
      · linarith only [h22350, h26170, hlam]
      · rcases p26153_3 (m.d 0 4) (by simp) with h26172 | h26172
        · linarith only [h22351, h26172, hlam]
        · rcases p26153_3 (m.d 0 5) (by simp) with h26174 | h26174
          · linarith only [h22352, h26174, hlam]
          · rcases h2bigk with h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c | h26176c
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [hlam, p26176_0]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [h0, hlam, p26176_1]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              rcases p26176_3 (m.d 0 2) (by simp) with h26179 | h26179
              · rcases p26176_3 (m.d 1 2) (by simp) with h26180 | h26180
                · rcases p26176_3 (m.d 2 3) (by simp) with h26181 | h26181
                  · linarith only [h26181, hlam, p26176_0]
                  · rcases p26176_3 (m.d 2 4) (by simp) with h26183 | h26183
                    · linarith only [h22351, h26183, hlam]
                    · rcases p26176_3 (m.d 2 5) (by simp) with h26185 | h26185
                      · linarith only [h22352, h26185, hlam]
                      · rcases h3bigk with h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c | h26187c
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [hlam, p26187_0]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [h15532, hlam, p26187_1]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [h0, h26148, h26151, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26153_1, p26187_1]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26153_1, p26187_1]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [h0, h26151, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26153_1, p26187_1]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          rcases p26187_3 (m.d 0 3) (by simp) with h26193 | h26193
                          · linarith only [h15532, h26193, hlam]
                          · rcases p26187_3 (m.d 1 3) (by simp) with h26195 | h26195
                            · rcases p26187_3 (m.d 2 3) (by simp) with h26196 | h26196
                              · linarith only [h25422, h26196, hlam]
                              · rcases p26187_3 (m.d 3 4) (by simp) with h26198 | h26198
                                · linarith only [h25425, h26198, hlam]
                                · rcases p26187_3 (m.d 3 5) (by simp) with h26200 | h26200
                                  · linarith only [h25426, h26200, hlam]
                                  · rcases h5bigk with h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c | h26202c
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [hlam, p26202_0]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h20697, hlam, p26202_1]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h0, h22354, h26149, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p26153_1, p26202_1]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h0, h22354, h26151, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26153_1, p26202_1]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h22355, hlam, p26202_1]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h18443, h22355, hc01, hc15, hlam, hphi, p26202_1]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [hlam, p26202_0]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h25427, h26149, hc24, hc45, hlam, hphi, p26202_1]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h25427, h26151, hc34, hc45, hlam, hphi, p26202_1]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h25427, hlam, p26202_1]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h22352, hlam, p26202_1]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h25424, hlam, p26202_1]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [hlam, p26202_0]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h0, h22352, h26151, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26202_1]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h26149, hlam, p26202_1]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h22354, hlam, p26202_0]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h25426, hlam, p26202_0]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h26148, hlam, p26202_0]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [hlam, p26202_0]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h26151, hlam, p26202_1]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h20697, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p26202_1]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h20697, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p26202_1]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h26148, h26151, hc34, hc45, hlam, hphi, p26202_1]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [h26151, hc34, hc45, hlam, hphi, p26202_1]
                                    · have p26202_0 := h26202c.1
                                      have p26202_1 := h26202c.2.1
                                      have p26202_2 := h26202c.2.2.1
                                      have p26202_3 := h26202c.2.2.2
                                      linarith only [hlam, p26202_0]
                            · linarith only [h15532, h26195, hlam]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [hlam, p26187_0]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          rcases p26187_3 (m.d 0 3) (by simp) with h26230 | h26230
                          · linarith only [h15532, h26230, hlam]
                          · linarith only [h22350, h26230, hlam]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          rcases p26187_3 (m.d 0 3) (by simp) with h26233 | h26233
                          · linarith only [h15532, h26233, hlam]
                          · linarith only [h22353, h26233, hlam]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          rcases p26187_3 (m.d 0 3) (by simp) with h26236 | h26236
                          · linarith only [h15532, h26236, hlam]
                          · linarith only [h22354, h26236, hlam]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [h22350, hlam, p26187_0]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [h25422, hlam, p26187_0]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [hlam, p26187_0]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [h0, h22350, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26153_1, p26187_1]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [h0, h22350, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p26153_1, p26187_1]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [h22353, hlam, p26187_0]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [h25425, hlam, p26187_0]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [h26147, hlam, p26187_0]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [hlam, p26187_0]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [h26151, hlam, p26187_1]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [h22354, hlam, p26187_0]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [h25426, hlam, p26187_0]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [h26148, hlam, p26187_0]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [h0, h22354, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26153_1, p26187_1]
                        · have p26187_0 := h26187c.1
                          have p26187_1 := h26187c.2.1
                          have p26187_2 := h26187c.2.2.1
                          have p26187_3 := h26187c.2.2.2
                          linarith only [hlam, p26187_0]
                · linarith only [h25422, h26180, hlam]
              · linarith only [h26179, hlam, p26176_0]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              rcases p26176_3 (m.d 0 2) (by simp) with h26256 | h26256
              · rcases p26176_3 (m.d 1 2) (by simp) with h26257 | h26257
                · rcases p26176_3 (m.d 2 3) (by simp) with h26258 | h26258
                  · linarith only [h22350, h26258, hlam]
                  · linarith only [h26147, h26258, hlam]
                · linarith only [h25423, h26257, hlam]
              · linarith only [h26256, hlam, p26176_0]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              rcases p26176_3 (m.d 0 2) (by simp) with h26263 | h26263
              · rcases p26176_3 (m.d 1 2) (by simp) with h26264 | h26264
                · rcases p26176_3 (m.d 2 3) (by simp) with h26265 | h26265
                  · linarith only [h22350, h26265, hlam]
                  · linarith only [h26148, h26265, hlam]
                · linarith only [h25424, h26264, hlam]
              · linarith only [h26263, hlam, p26176_0]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26153_1, p26176_1]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [hlam, p26176_0]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              rcases p26176_3 (m.d 0 2) (by simp) with h26272 | h26272
              · linarith only [h0, h26272, hlam]
              · linarith only [h22350, h26272, hlam]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              rcases p26176_3 (m.d 0 2) (by simp) with h26275 | h26275
              · linarith only [h0, h26275, hlam]
              · linarith only [h22351, h26275, hlam]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              rcases p26176_3 (m.d 0 2) (by simp) with h26278 | h26278
              · linarith only [h0, h26278, hlam]
              · linarith only [h22352, h26278, hlam]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [h22350, hlam, p26176_0]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [h25422, hlam, p26176_0]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [hlam, p26176_0]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [h22350, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p26153_1, p26176_1]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [h0, h22350, h26147, h26149, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26153_1, p26176_1]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [h22351, hlam, p26176_0]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [h25423, hlam, p26176_0]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [h26147, hlam, p26176_1]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [hlam, p26176_0]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [h26149, hlam, p26176_1]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [h22352, hlam, p26176_0]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [h25424, hlam, p26176_0]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [h26148, hlam, p26176_1]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [h0, h22352, h22354, h26147, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26153_1, p26176_1]
            · have p26176_0 := h26176c.1
              have p26176_1 := h26176c.2.1
              have p26176_2 := h26176c.2.2.1
              have p26176_3 := h26176c.2.2.2
              linarith only [hlam, p26176_0]
    · linarith only [h22350, h26169, hlam]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x8 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h26153c : ((m.d 0 2) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 2) ∧ (m.d 0 4) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 4) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have p26153_0 := h26153c.1
  have p26153_1 := h26153c.2.1
  have p26153_2 := h26153c.2.2.1
  have p26153_3 := h26153c.2.2.2
  rcases p26153_3 (m.d 0 1) (by simp) with h26297 | h26297
  · linarith only [h0, h26297, hlam]
  · rcases p26153_3 (m.d 0 2) (by simp) with h26299 | h26299
    · rcases p26153_3 (m.d 0 3) (by simp) with h26300 | h26300
      · linarith only [h22350, h26300, hlam]
      · linarith only [h22353, h26300, hlam]
    · linarith only [h22351, h26299, hlam]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x9 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h26153c : ((m.d 0 2) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 2) ∧ (m.d 0 5) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 5) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have p26153_0 := h26153c.1
  have p26153_1 := h26153c.2.1
  have p26153_2 := h26153c.2.2.1
  have p26153_3 := h26153c.2.2.2
  rcases p26153_3 (m.d 0 1) (by simp) with h26304 | h26304
  · linarith only [h0, h26304, hlam]
  · rcases p26153_3 (m.d 0 2) (by simp) with h26306 | h26306
    · rcases p26153_3 (m.d 0 3) (by simp) with h26307 | h26307
      · linarith only [h22350, h26307, hlam]
      · linarith only [h22354, h26307, hlam]
    · linarith only [h22352, h26306, hlam]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x10 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h26153c : ((m.d 0 3) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 3) ∧ (m.d 0 1) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 1) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have p26153_0 := h26153c.1
  have p26153_1 := h26153c.2.1
  have p26153_2 := h26153c.2.2.1
  have p26153_3 := h26153c.2.2.2
  rcases p26153_3 (m.d 0 1) (by simp) with h26311 | h26311
  · linarith only [h15532, h26311, hlam]
  · rcases p26153_3 (m.d 0 2) (by simp) with h26313 | h26313
    · rcases p26153_3 (m.d 0 3) (by simp) with h26314 | h26314
      · rcases p26153_3 (m.d 0 4) (by simp) with h26315 | h26315
        · linarith only [h22353, h26315, hlam]
        · linarith only [h18443, h26315, hlam]
      · linarith only [h15532, h26314, hlam]
    · linarith only [h0, h26313, hlam]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x11 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h26153c : ((m.d 0 3) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 3) ∧ (m.d 0 2) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 2) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have p26153_0 := h26153c.1
  have p26153_1 := h26153c.2.1
  have p26153_2 := h26153c.2.2.1
  have p26153_3 := h26153c.2.2.2
  linarith only [h22350, hlam, p26153_1]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x12 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h26153c : ((m.d 0 3) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 3) ∧ (m.d 0 3) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 3) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have p26153_0 := h26153c.1
  have p26153_1 := h26153c.2.1
  have p26153_2 := h26153c.2.2.1
  have p26153_3 := h26153c.2.2.2
  linarith only [hlam, p26153_0]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x13 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h26153c : ((m.d 0 3) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 3) ∧ (m.d 0 4) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 4) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have p26153_0 := h26153c.1
  have p26153_1 := h26153c.2.1
  have p26153_2 := h26153c.2.2.1
  have p26153_3 := h26153c.2.2.2
  rcases p26153_3 (m.d 0 1) (by simp) with h26322 | h26322
  · linarith only [h15532, h26322, hlam]
  · rcases p26153_3 (m.d 0 2) (by simp) with h26324 | h26324
    · rcases p26153_3 (m.d 0 3) (by simp) with h26325 | h26325
      · rcases p26153_3 (m.d 0 4) (by simp) with h26326 | h26326
        · linarith only [h22353, h26326, hlam]
        · rcases p26153_3 (m.d 0 5) (by simp) with h26328 | h26328
          · linarith only [h22354, h26328, hlam]
          · linarith only [h22355, h26328, hlam]
      · linarith only [h22353, h26325, hlam]
    · linarith only [h22351, h26324, hlam]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x14 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h26153c : ((m.d 0 3) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 3) ∧ (m.d 0 5) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 5) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have p26153_0 := h26153c.1
  have p26153_1 := h26153c.2.1
  have p26153_2 := h26153c.2.2.1
  have p26153_3 := h26153c.2.2.2
  rcases p26153_3 (m.d 0 1) (by simp) with h26333 | h26333
  · linarith only [h15532, h26333, hlam]
  · rcases p26153_3 (m.d 0 2) (by simp) with h26335 | h26335
    · rcases p26153_3 (m.d 0 3) (by simp) with h26336 | h26336
      · rcases p26153_3 (m.d 0 4) (by simp) with h26337 | h26337
        · linarith only [h22353, h26337, hlam]
        · rcases p26153_3 (m.d 0 5) (by simp) with h26339 | h26339
          · linarith only [h22354, h26339, hlam]
          · rcases h2bigk with h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c | h26341c
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              linarith only [hlam, p26341_0]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              linarith only [h0, hlam, p26341_1]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              rcases p26341_3 (m.d 0 2) (by simp) with h26344 | h26344
              · rcases p26341_3 (m.d 1 2) (by simp) with h26345 | h26345
                · rcases p26341_3 (m.d 2 3) (by simp) with h26346 | h26346
                  · linarith only [h26346, hlam, p26341_0]
                  · rcases p26341_3 (m.d 2 4) (by simp) with h26348 | h26348
                    · linarith only [h22351, h26348, hlam]
                    · rcases p26341_3 (m.d 2 5) (by simp) with h26350 | h26350
                      · linarith only [h22352, h26350, hlam]
                      · rcases h3bigk with h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c | h26352c
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [hlam, p26352_0]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [h15532, hlam, p26352_1]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          rcases p26352_3 (m.d 0 3) (by simp) with h26355 | h26355
                          · rcases p26352_3 (m.d 1 3) (by simp) with h26356 | h26356
                            · rcases p26352_3 (m.d 2 3) (by simp) with h26357 | h26357
                              · linarith only [h22350, h26357, hlam]
                              · rcases p26352_3 (m.d 3 4) (by simp) with h26359 | h26359
                                · linarith only [h22353, h26359, hlam]
                                · rcases p26352_3 (m.d 3 5) (by simp) with h26361 | h26361
                                  · linarith only [h22354, h26361, hlam]
                                  · rcases h5bigk with h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c | h26363c
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [hlam, p26363_0]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h20697, hlam, p26363_1]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h0, h22350, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p26153_1, p26363_1]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h0, h22350, h26151, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26153_1, p26363_1]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h22355, hlam, p26363_1]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h20697, hc01, hc15, hlam, hphi, p26363_1]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [hlam, p26363_0]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h25427, h26148, h26151, hc34, hc45, hlam, hphi, p26363_1]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h25427, h26151, hc34, hc45, hlam, hphi, p26363_1]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h25427, hlam, p26363_1]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h22352, hlam, p26363_1]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h25424, hlam, p26363_1]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [hlam, p26363_0]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h0, h22352, h26151, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26363_1]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h26149, hlam, p26363_1]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h22354, hlam, p26363_0]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h25426, hlam, p26363_0]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h26148, hlam, p26363_0]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [hlam, p26363_0]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h26151, hlam, p26363_1]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h18443, h22355, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p26363_1]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h20697, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p26363_1]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h26148, h26151, hc34, hc45, hlam, hphi, p26363_1]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [h26151, hc34, hc45, hlam, hphi, p26363_1]
                                    · have p26363_0 := h26363c.1
                                      have p26363_1 := h26363c.2.1
                                      have p26363_2 := h26363c.2.2.1
                                      have p26363_3 := h26363c.2.2.2
                                      linarith only [hlam, p26363_0]
                            · linarith only [h25422, h26356, hlam]
                          · linarith only [h22350, h26355, hlam]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          rcases p26352_3 (m.d 0 3) (by simp) with h26391 | h26391
                          · rcases p26352_3 (m.d 1 3) (by simp) with h26392 | h26392
                            · rcases p26352_3 (m.d 2 3) (by simp) with h26393 | h26393
                              · linarith only [h22350, h26393, hlam]
                              · linarith only [h26147, h26393, hlam]
                            · linarith only [h25425, h26392, hlam]
                          · linarith only [h26391, hlam, p26352_0]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          rcases p26352_3 (m.d 0 3) (by simp) with h26398 | h26398
                          · rcases p26352_3 (m.d 1 3) (by simp) with h26399 | h26399
                            · rcases p26352_3 (m.d 2 3) (by simp) with h26400 | h26400
                              · linarith only [h22350, h26400, hlam]
                              · linarith only [h26148, h26400, hlam]
                            · linarith only [h25426, h26399, hlam]
                          · linarith only [h26398, hlam, p26352_0]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [h18443, h22355, hc01, hc13, hlam, hphi, p26153_1, p26352_1]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [hlam, p26352_0]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          rcases p26352_3 (m.d 0 3) (by simp) with h26407 | h26407
                          · linarith only [h15532, h26407, hlam]
                          · linarith only [h22350, h26407, hlam]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          rcases p26352_3 (m.d 0 3) (by simp) with h26410 | h26410
                          · linarith only [h15532, h26410, hlam]
                          · linarith only [h22353, h26410, hlam]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          rcases p26352_3 (m.d 0 3) (by simp) with h26413 | h26413
                          · linarith only [h15532, h26413, hlam]
                          · linarith only [h22354, h26413, hlam]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [h22350, hlam, p26352_0]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [h25422, hlam, p26352_0]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [hlam, p26352_0]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26341_1, p26352_1]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p26341_1, p26352_1]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [h22353, hlam, p26352_0]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [h25425, hlam, p26352_0]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [h26147, hlam, p26352_0]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [hlam, p26352_0]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [h26151, hlam, p26352_1]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [h22354, hlam, p26352_0]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [h25426, hlam, p26352_0]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [h26148, hlam, p26352_0]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [h22354, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p26153_1, p26352_1]
                        · have p26352_0 := h26352c.1
                          have p26352_1 := h26352c.2.1
                          have p26352_2 := h26352c.2.2.1
                          have p26352_3 := h26352c.2.2.2
                          linarith only [hlam, p26352_0]
                · linarith only [h25422, h26345, hlam]
              · linarith only [h26344, hlam, p26341_0]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              rcases p26341_3 (m.d 0 2) (by simp) with h26433 | h26433
              · rcases p26341_3 (m.d 1 2) (by simp) with h26434 | h26434
                · rcases p26341_3 (m.d 2 3) (by simp) with h26435 | h26435
                  · linarith only [h22350, h26435, hlam]
                  · linarith only [h26147, h26435, hlam]
                · linarith only [h25423, h26434, hlam]
              · linarith only [h26433, hlam, p26341_0]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              rcases p26341_3 (m.d 0 2) (by simp) with h26440 | h26440
              · rcases p26341_3 (m.d 1 2) (by simp) with h26441 | h26441
                · rcases p26341_3 (m.d 2 3) (by simp) with h26442 | h26442
                  · linarith only [h22350, h26442, hlam]
                  · linarith only [h26148, h26442, hlam]
                · linarith only [h25424, h26441, hlam]
              · linarith only [h26440, hlam, p26341_0]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              linarith only [h22350, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p26153_1, p26341_1]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              linarith only [hlam, p26341_0]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              rcases p26341_3 (m.d 0 2) (by simp) with h26449 | h26449
              · linarith only [h0, h26449, hlam]
              · linarith only [h22350, h26449, hlam]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              rcases p26341_3 (m.d 0 2) (by simp) with h26452 | h26452
              · linarith only [h0, h26452, hlam]
              · linarith only [h22351, h26452, hlam]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              rcases p26341_3 (m.d 0 2) (by simp) with h26455 | h26455
              · linarith only [h0, h26455, hlam]
              · linarith only [h22352, h26455, hlam]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              linarith only [h22350, hlam, p26341_0]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              linarith only [h25422, hlam, p26341_0]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              linarith only [hlam, p26341_0]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              rcases p26341_3 (m.d 0 2) (by simp) with h26461 | h26461
              · rcases p26341_3 (m.d 1 2) (by simp) with h26462 | h26462
                · rcases p26341_3 (m.d 2 3) (by simp) with h26463 | h26463
                  · rcases p26341_3 (m.d 2 4) (by simp) with h26464 | h26464
                    · linarith only [h26147, h26464, hlam]
                    · rcases p26341_3 (m.d 2 5) (by simp) with h26466 | h26466
                      · linarith only [h26148, h26466, hlam]
                      · linarith only [h26149, h26466, hlam]
                  · linarith only [h26147, h26463, hlam]
                · linarith only [h25423, h26462, hlam]
              · linarith only [h22351, h26461, hlam]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              rcases p26341_3 (m.d 0 2) (by simp) with h26472 | h26472
              · rcases p26341_3 (m.d 1 2) (by simp) with h26473 | h26473
                · rcases p26341_3 (m.d 2 3) (by simp) with h26474 | h26474
                  · rcases p26341_3 (m.d 2 4) (by simp) with h26475 | h26475
                    · linarith only [h26147, h26475, hlam]
                    · rcases p26341_3 (m.d 2 5) (by simp) with h26477 | h26477
                      · linarith only [h26148, h26477, hlam]
                      · rcases h3bigk with h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c | h26479c
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [hlam, p26479_0]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [h15532, hlam, p26479_1]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [h26147, h26149, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p26341_1, p26479_1]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          rcases p26479_3 (m.d 0 3) (by simp) with h26483 | h26483
                          · rcases p26479_3 (m.d 1 3) (by simp) with h26484 | h26484
                            · rcases p26479_3 (m.d 2 3) (by simp) with h26485 | h26485
                              · linarith only [h22350, h26485, hlam]
                              · linarith only [h26147, h26485, hlam]
                            · linarith only [h25425, h26484, hlam]
                          · linarith only [h26483, hlam, p26479_0]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          rcases p26479_3 (m.d 0 3) (by simp) with h26490 | h26490
                          · rcases p26479_3 (m.d 1 3) (by simp) with h26491 | h26491
                            · rcases p26479_3 (m.d 2 3) (by simp) with h26492 | h26492
                              · linarith only [h22350, h26492, hlam]
                              · linarith only [h26148, h26492, hlam]
                            · linarith only [h25426, h26491, hlam]
                          · linarith only [h26490, hlam, p26479_0]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [h22350, h25422, h26147, h26149, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26341_1, p26479_1]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [hlam, p26479_0]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [h25422, h26147, h26149, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26341_1, p26479_1]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          rcases p26479_3 (m.d 0 3) (by simp) with h26500 | h26500
                          · linarith only [h15532, h26500, hlam]
                          · linarith only [h22353, h26500, hlam]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          rcases p26479_3 (m.d 0 3) (by simp) with h26503 | h26503
                          · linarith only [h15532, h26503, hlam]
                          · linarith only [h22354, h26503, hlam]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [h22350, hlam, p26479_0]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [h25422, hlam, p26479_0]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [hlam, p26479_0]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          rcases p26479_3 (m.d 0 3) (by simp) with h26509 | h26509
                          · rcases p26479_3 (m.d 1 3) (by simp) with h26510 | h26510
                            · rcases p26479_3 (m.d 2 3) (by simp) with h26511 | h26511
                              · rcases p26479_3 (m.d 3 4) (by simp) with h26512 | h26512
                                · linarith only [h26512, hlam, p26479_0]
                                · rcases p26479_3 (m.d 3 5) (by simp) with h26514 | h26514
                                  · linarith only [h26148, h26514, hlam]
                                  · linarith only [h26151, h26514, hlam]
                              · linarith only [h26511, hlam, p26479_0]
                            · linarith only [h25425, h26510, hlam]
                          · linarith only [h22353, h26509, hlam]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          rcases p26479_3 (m.d 0 3) (by simp) with h26520 | h26520
                          · rcases p26479_3 (m.d 1 3) (by simp) with h26521 | h26521
                            · rcases p26479_3 (m.d 2 3) (by simp) with h26522 | h26522
                              · rcases p26479_3 (m.d 3 4) (by simp) with h26523 | h26523
                                · linarith only [h26147, h26523, hlam]
                                · rcases p26479_3 (m.d 3 5) (by simp) with h26525 | h26525
                                  · linarith only [h26525, hlam, p26479_0]
                                  · rcases h5bigk with h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c | h26527c
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [hlam, p26527_0]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h20697, hlam, p26527_1]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h26147, h26149, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p26153_1, p26527_1]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h0, h22350, h26151, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26153_1, p26527_1]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h22355, hlam, p26527_1]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h18443, h22355, hc01, hc15, hlam, hphi, p26527_1]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [hlam, p26527_0]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h25427, h26147, h26149, hc34, hc45, hlam, hphi, p26527_1]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h25427, h26151, hc34, hc45, hlam, hphi, p26527_1]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h25427, hlam, p26527_1]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h22352, hlam, p26527_1]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h25424, hlam, p26527_1]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [hlam, p26527_0]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h26151, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p26341_1, p26527_1]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h26149, hlam, p26527_1]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h22354, hlam, p26527_0]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h25426, hlam, p26527_0]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h26148, hlam, p26527_0]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [hlam, p26527_0]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h26151, hlam, p26527_1]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h18443, h22355, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p26527_1]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h20697, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p26527_1]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h26148, h26151, hc34, hc45, hlam, hphi, p26527_1]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [h26151, hc34, hc45, hlam, hphi, p26527_1]
                                    · have p26527_0 := h26527c.1
                                      have p26527_1 := h26527c.2.1
                                      have p26527_2 := h26527c.2.2.1
                                      have p26527_3 := h26527c.2.2.2
                                      linarith only [hlam, p26527_0]
                              · linarith only [h26522, hlam, p26479_0]
                            · linarith only [h25426, h26521, hlam]
                          · linarith only [h22354, h26520, hlam]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [h22353, hlam, p26479_0]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [h25425, hlam, p26479_0]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [h26147, hlam, p26479_0]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [hlam, p26479_0]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [h26151, hlam, p26479_1]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [h22354, hlam, p26479_0]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [h25426, hlam, p26479_0]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [h26148, hlam, p26479_0]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [h0, h22350, h26148, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26341_1, p26479_1]
                        · have p26479_0 := h26479c.1
                          have p26479_1 := h26479c.2.1
                          have p26479_2 := h26479c.2.2.1
                          have p26479_3 := h26479c.2.2.2
                          linarith only [hlam, p26479_0]
                  · linarith only [h26148, h26474, hlam]
                · linarith only [h25424, h26473, hlam]
              · linarith only [h22352, h26472, hlam]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              linarith only [h22351, hlam, p26341_0]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              linarith only [h25423, hlam, p26341_0]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              linarith only [h26147, hlam, p26341_1]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              linarith only [hlam, p26341_0]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              linarith only [h26149, hlam, p26341_1]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              linarith only [h22352, hlam, p26341_0]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              linarith only [h25424, hlam, p26341_0]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              linarith only [h26148, hlam, p26341_1]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              linarith only [h0, h22350, h22352, h26147, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26153_1, p26341_1]
            · have p26341_0 := h26341c.1
              have p26341_1 := h26341c.2.1
              have p26341_2 := h26341c.2.2.1
              have p26341_3 := h26341c.2.2.2
              linarith only [hlam, p26341_0]
      · linarith only [h22354, h26336, hlam]
    · linarith only [h22352, h26335, hlam]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x15 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h26153c : ((m.d 0 4) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 4) ∧ (m.d 0 1) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 1) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have p26153_0 := h26153c.1
  have p26153_1 := h26153c.2.1
  have p26153_2 := h26153c.2.2.1
  have p26153_3 := h26153c.2.2.2
  linarith only [h22355, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p26153_1]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x16 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26148 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26149 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h26151 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h26153c : ((m.d 0 4) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 4) ∧ (m.d 0 2) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 2) ≤ z)))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have p26153_0 := h26153c.1
  have p26153_1 := h26153c.2.1
  have p26153_2 := h26153c.2.2.1
  have p26153_3 := h26153c.2.2.2
  linarith only [h22351, hlam, p26153_0]

end R2N4
