import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S37
import Jsp000404.R1LeavesN7_1S38

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x17 (m : N7Model)
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
    (h26153c : ((m.d 0 4) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 4) ∧ (m.d 0 3) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 3) ≤ z)))
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
  linarith only [h22353, hlam, p26153_0]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x18 (m : N7Model)
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
    (h26153c : ((m.d 0 4) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 4) ∧ (m.d 0 4) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 4) ≤ z)))
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
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x19 (m : N7Model)
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
    (h26153c : ((m.d 0 4) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 4) ∧ (m.d 0 5) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 5) ≤ z)))
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
  linarith only [h22355, hlam, p26153_0]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x20 (m : N7Model)
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
    (h26153c : ((m.d 0 5) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 5) ∧ (m.d 0 1) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 1) ≤ z)))
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
  rcases p26153_3 (m.d 0 1) (by simp) with h26586 | h26586
  · linarith only [h20697, h26586, hlam]
  · rcases p26153_3 (m.d 0 2) (by simp) with h26588 | h26588
    · rcases p26153_3 (m.d 0 3) (by simp) with h26589 | h26589
      · rcases p26153_3 (m.d 0 4) (by simp) with h26590 | h26590
        · linarith only [h22355, h26590, hlam]
        · linarith only [h18443, h26590, hlam]
      · linarith only [h15532, h26589, hlam]
    · linarith only [h0, h26588, hlam]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x21 (m : N7Model)
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
    (h26153c : ((m.d 0 5) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 5) ∧ (m.d 0 2) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 2) ≤ z)))
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
  linarith only [h22352, hlam, p26153_1]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x22 (m : N7Model)
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
    (h26153c : ((m.d 0 5) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 5) ∧ (m.d 0 3) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 3) ≤ z)))
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
  linarith only [h22354, hlam, p26153_0]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x23 (m : N7Model)
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
    (h26153c : ((m.d 0 5) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 5) ∧ (m.d 0 4) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 4) ≤ z)))
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
  rcases p26153_3 (m.d 0 1) (by simp) with h26597 | h26597
  · linarith only [h20697, h26597, hlam]
  · rcases p26153_3 (m.d 0 2) (by simp) with h26599 | h26599
    · rcases p26153_3 (m.d 0 3) (by simp) with h26600 | h26600
      · rcases p26153_3 (m.d 0 4) (by simp) with h26601 | h26601
        · linarith only [h22355, h26601, hlam]
        · rcases p26153_3 (m.d 0 5) (by simp) with h26603 | h26603
          · rcases h2bigk with h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c | h26604c
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              linarith only [hlam, p26604_0]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              linarith only [h0, hlam, p26604_1]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              rcases p26604_3 (m.d 0 2) (by simp) with h26607 | h26607
              · rcases p26604_3 (m.d 1 2) (by simp) with h26608 | h26608
                · rcases p26604_3 (m.d 2 3) (by simp) with h26609 | h26609
                  · linarith only [h26609, hlam, p26604_0]
                  · rcases p26604_3 (m.d 2 4) (by simp) with h26611 | h26611
                    · linarith only [h22351, h26611, hlam]
                    · rcases p26604_3 (m.d 2 5) (by simp) with h26613 | h26613
                      · linarith only [h22352, h26613, hlam]
                      · rcases h3bigk with h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c | h26615c
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [hlam, p26615_0]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [h15532, hlam, p26615_1]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          rcases p26615_3 (m.d 0 3) (by simp) with h26618 | h26618
                          · rcases p26615_3 (m.d 1 3) (by simp) with h26619 | h26619
                            · rcases p26615_3 (m.d 2 3) (by simp) with h26620 | h26620
                              · linarith only [h22350, h26620, hlam]
                              · rcases p26615_3 (m.d 3 4) (by simp) with h26622 | h26622
                                · linarith only [h22353, h26622, hlam]
                                · rcases p26615_3 (m.d 3 5) (by simp) with h26624 | h26624
                                  · linarith only [h22354, h26624, hlam]
                                  · rcases h5bigk with h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c | h26626c
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [hlam, p26626_0]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h20697, hlam, p26626_1]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h22355, h26148, h26151, hc34, hc45, hlam, hphi, p26626_1]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h22355, h26151, hc34, hc45, hlam, hphi, p26626_1]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h22355, hlam, p26626_1]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h20697, hc01, hc15, hlam, hphi, p26626_1]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [hlam, p26626_0]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h25427, h26148, h26151, hc34, hc45, hlam, hphi, p26626_1]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h25427, h26151, hc34, hc45, hlam, hphi, p26626_1]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h25427, hlam, p26626_1]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h22352, hlam, p26626_1]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h25424, hlam, p26626_1]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [hlam, p26626_0]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h22352, h26151, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p26626_1]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h26149, hlam, p26626_1]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h22354, hlam, p26626_0]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h25426, hlam, p26626_0]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h26148, hlam, p26626_0]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [hlam, p26626_0]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h26151, hlam, p26626_1]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h18443, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p26153_1, p26626_1]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h18443, h20697, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p26153_1, p26626_1]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h26148, h26151, hc34, hc45, hlam, hphi, p26626_1]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [h26151, hc34, hc45, hlam, hphi, p26626_1]
                                    · have p26626_0 := h26626c.1
                                      have p26626_1 := h26626c.2.1
                                      have p26626_2 := h26626c.2.2.1
                                      have p26626_3 := h26626c.2.2.2
                                      linarith only [hlam, p26626_0]
                            · linarith only [h25422, h26619, hlam]
                          · linarith only [h22350, h26618, hlam]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          rcases p26615_3 (m.d 0 3) (by simp) with h26654 | h26654
                          · rcases p26615_3 (m.d 1 3) (by simp) with h26655 | h26655
                            · rcases p26615_3 (m.d 2 3) (by simp) with h26656 | h26656
                              · linarith only [h22350, h26656, hlam]
                              · linarith only [h26147, h26656, hlam]
                            · linarith only [h25425, h26655, hlam]
                          · linarith only [h26654, hlam, p26615_0]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          rcases p26615_3 (m.d 0 3) (by simp) with h26661 | h26661
                          · rcases p26615_3 (m.d 1 3) (by simp) with h26662 | h26662
                            · rcases p26615_3 (m.d 2 3) (by simp) with h26663 | h26663
                              · linarith only [h22350, h26663, hlam]
                              · linarith only [h26148, h26663, hlam]
                            · linarith only [h25426, h26662, hlam]
                          · linarith only [h26661, hlam, p26615_0]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [h18443, h22354, hc01, hc13, hlam, hphi, p26153_1, p26615_1]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [hlam, p26615_0]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          rcases p26615_3 (m.d 0 3) (by simp) with h26670 | h26670
                          · linarith only [h15532, h26670, hlam]
                          · linarith only [h22350, h26670, hlam]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          rcases p26615_3 (m.d 0 3) (by simp) with h26673 | h26673
                          · linarith only [h15532, h26673, hlam]
                          · linarith only [h22353, h26673, hlam]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          rcases p26615_3 (m.d 0 3) (by simp) with h26676 | h26676
                          · linarith only [h15532, h26676, hlam]
                          · linarith only [h22354, h26676, hlam]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [h22350, hlam, p26615_0]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [h25422, hlam, p26615_0]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [hlam, p26615_0]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26604_1, p26615_1]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p26604_1, p26615_1]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [h22353, hlam, p26615_0]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [h25425, hlam, p26615_0]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [h26147, hlam, p26615_0]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [hlam, p26615_0]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [h26151, hlam, p26615_1]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [h22354, hlam, p26615_0]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [h25426, hlam, p26615_0]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [h26148, hlam, p26615_0]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [h0, h18443, h20697, h25427, h26148, hc01, hc12, hc34, hc45, hlam, hphi, p26153_1, p26604_1, p26615_1]
                        · have p26615_0 := h26615c.1
                          have p26615_1 := h26615c.2.1
                          have p26615_2 := h26615c.2.2.1
                          have p26615_3 := h26615c.2.2.2
                          linarith only [hlam, p26615_0]
                · linarith only [h25422, h26608, hlam]
              · linarith only [h26607, hlam, p26604_0]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              rcases p26604_3 (m.d 0 2) (by simp) with h26696 | h26696
              · rcases p26604_3 (m.d 1 2) (by simp) with h26697 | h26697
                · rcases p26604_3 (m.d 2 3) (by simp) with h26698 | h26698
                  · linarith only [h22350, h26698, hlam]
                  · linarith only [h26147, h26698, hlam]
                · linarith only [h25423, h26697, hlam]
              · linarith only [h26696, hlam, p26604_0]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              rcases p26604_3 (m.d 0 2) (by simp) with h26703 | h26703
              · rcases p26604_3 (m.d 1 2) (by simp) with h26704 | h26704
                · rcases p26604_3 (m.d 2 3) (by simp) with h26705 | h26705
                  · linarith only [h22350, h26705, hlam]
                  · linarith only [h26148, h26705, hlam]
                · linarith only [h25424, h26704, hlam]
              · linarith only [h26703, hlam, p26604_0]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              linarith only [h18443, h22352, hc01, hc12, hlam, hphi, p26153_1, p26604_1]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              linarith only [hlam, p26604_0]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              rcases p26604_3 (m.d 0 2) (by simp) with h26712 | h26712
              · linarith only [h0, h26712, hlam]
              · linarith only [h22350, h26712, hlam]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              rcases p26604_3 (m.d 0 2) (by simp) with h26715 | h26715
              · linarith only [h0, h26715, hlam]
              · linarith only [h22351, h26715, hlam]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              rcases p26604_3 (m.d 0 2) (by simp) with h26718 | h26718
              · linarith only [h0, h26718, hlam]
              · linarith only [h22352, h26718, hlam]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              linarith only [h22350, hlam, p26604_0]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              linarith only [h25422, hlam, p26604_0]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              linarith only [hlam, p26604_0]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              rcases p26604_3 (m.d 0 2) (by simp) with h26724 | h26724
              · rcases p26604_3 (m.d 1 2) (by simp) with h26725 | h26725
                · rcases p26604_3 (m.d 2 3) (by simp) with h26726 | h26726
                  · rcases p26604_3 (m.d 2 4) (by simp) with h26727 | h26727
                    · linarith only [h26147, h26727, hlam]
                    · rcases p26604_3 (m.d 2 5) (by simp) with h26729 | h26729
                      · linarith only [h26148, h26729, hlam]
                      · linarith only [h26149, h26729, hlam]
                  · linarith only [h26147, h26726, hlam]
                · linarith only [h25423, h26725, hlam]
              · linarith only [h22351, h26724, hlam]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              rcases p26604_3 (m.d 0 2) (by simp) with h26735 | h26735
              · rcases p26604_3 (m.d 1 2) (by simp) with h26736 | h26736
                · rcases p26604_3 (m.d 2 3) (by simp) with h26737 | h26737
                  · rcases p26604_3 (m.d 2 4) (by simp) with h26738 | h26738
                    · linarith only [h26147, h26738, hlam]
                    · rcases p26604_3 (m.d 2 5) (by simp) with h26740 | h26740
                      · linarith only [h26148, h26740, hlam]
                      · rcases h3bigk with h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c | h26742c
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [hlam, p26742_0]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [h15532, hlam, p26742_1]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [h15532, h26149, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p26604_1, p26742_1]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          rcases p26742_3 (m.d 0 3) (by simp) with h26746 | h26746
                          · rcases p26742_3 (m.d 1 3) (by simp) with h26747 | h26747
                            · rcases p26742_3 (m.d 2 3) (by simp) with h26748 | h26748
                              · linarith only [h22350, h26748, hlam]
                              · linarith only [h26147, h26748, hlam]
                            · linarith only [h25425, h26747, hlam]
                          · linarith only [h26746, hlam, p26742_0]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          rcases p26742_3 (m.d 0 3) (by simp) with h26753 | h26753
                          · rcases p26742_3 (m.d 1 3) (by simp) with h26754 | h26754
                            · rcases p26742_3 (m.d 2 3) (by simp) with h26755 | h26755
                              · linarith only [h22350, h26755, hlam]
                              · linarith only [h26148, h26755, hlam]
                            · linarith only [h25426, h26754, hlam]
                          · linarith only [h26753, hlam, p26742_0]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [h18443, h20697, h22350, h25422, h25427, h26147, h26149, hc01, hc12, hc34, hc45, hlam, hphi, p26153_1, p26604_1, p26742_1]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [hlam, p26742_0]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [h18443, h20697, h25422, h25427, h26147, h26149, hc01, hc12, hc34, hc45, hlam, hphi, p26153_1, p26604_1, p26742_1]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          rcases p26742_3 (m.d 0 3) (by simp) with h26763 | h26763
                          · linarith only [h15532, h26763, hlam]
                          · linarith only [h22353, h26763, hlam]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          rcases p26742_3 (m.d 0 3) (by simp) with h26766 | h26766
                          · linarith only [h15532, h26766, hlam]
                          · linarith only [h22354, h26766, hlam]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [h22350, hlam, p26742_0]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [h25422, hlam, p26742_0]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [hlam, p26742_0]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          rcases p26742_3 (m.d 0 3) (by simp) with h26772 | h26772
                          · rcases p26742_3 (m.d 1 3) (by simp) with h26773 | h26773
                            · rcases p26742_3 (m.d 2 3) (by simp) with h26774 | h26774
                              · rcases p26742_3 (m.d 3 4) (by simp) with h26775 | h26775
                                · linarith only [h26775, hlam, p26742_0]
                                · rcases p26742_3 (m.d 3 5) (by simp) with h26777 | h26777
                                  · linarith only [h26148, h26777, hlam]
                                  · linarith only [h26151, h26777, hlam]
                              · linarith only [h26774, hlam, p26742_0]
                            · linarith only [h25425, h26773, hlam]
                          · linarith only [h22353, h26772, hlam]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          rcases p26742_3 (m.d 0 3) (by simp) with h26783 | h26783
                          · rcases p26742_3 (m.d 1 3) (by simp) with h26784 | h26784
                            · rcases p26742_3 (m.d 2 3) (by simp) with h26785 | h26785
                              · rcases p26742_3 (m.d 3 4) (by simp) with h26786 | h26786
                                · linarith only [h26147, h26786, hlam]
                                · rcases p26742_3 (m.d 3 5) (by simp) with h26788 | h26788
                                  · linarith only [h26788, hlam, p26742_0]
                                  · rcases h5bigk with h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c | h26790c
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [hlam, p26790_0]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h20697, hlam, p26790_1]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h20697, h25427, h26147, h26149, hc34, hc45, hlam, hphi, p26790_1]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h20697, h25427, h26151, hc34, hc45, hlam, hphi, p26790_1]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h22355, hlam, p26790_1]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h18443, h25427, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p26153_1, p26790_1]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [hlam, p26790_0]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h25427, h26147, h26149, hc34, hc45, hlam, hphi, p26790_1]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h25427, h26151, hc34, hc45, hlam, hphi, p26790_1]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h25427, hlam, p26790_1]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h22352, hlam, p26790_1]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h25424, hlam, p26790_1]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [hlam, p26790_0]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h0, h22350, h26151, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26604_1, p26790_1]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h26149, hlam, p26790_1]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h22354, hlam, p26790_0]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h25426, hlam, p26790_0]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h26148, hlam, p26790_0]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [hlam, p26790_0]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h26151, hlam, p26790_1]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h18443, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p26153_1, p26790_1]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h18443, h20697, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p26153_1, p26790_1]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h26147, h26149, hc34, hc45, hlam, hphi, p26790_1]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [h26151, hc34, hc45, hlam, hphi, p26790_1]
                                    · have p26790_0 := h26790c.1
                                      have p26790_1 := h26790c.2.1
                                      have p26790_2 := h26790c.2.2.1
                                      have p26790_3 := h26790c.2.2.2
                                      linarith only [hlam, p26790_0]
                              · linarith only [h26785, hlam, p26742_0]
                            · linarith only [h25426, h26784, hlam]
                          · linarith only [h22354, h26783, hlam]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [h22353, hlam, p26742_0]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [h25425, hlam, p26742_0]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [h26147, hlam, p26742_0]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [hlam, p26742_0]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [h26151, hlam, p26742_1]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [h22354, hlam, p26742_0]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [h25426, hlam, p26742_0]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [h26148, hlam, p26742_0]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [h0, h22350, h26148, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26742_1]
                        · have p26742_0 := h26742c.1
                          have p26742_1 := h26742c.2.1
                          have p26742_2 := h26742c.2.2.1
                          have p26742_3 := h26742c.2.2.2
                          linarith only [hlam, p26742_0]
                  · linarith only [h26148, h26737, hlam]
                · linarith only [h25424, h26736, hlam]
              · linarith only [h22352, h26735, hlam]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              linarith only [h22351, hlam, p26604_0]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              linarith only [h25423, hlam, p26604_0]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              linarith only [h26147, hlam, p26604_1]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              linarith only [hlam, p26604_0]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              linarith only [h26149, hlam, p26604_1]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              linarith only [h22352, hlam, p26604_0]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              linarith only [h25424, hlam, p26604_0]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              linarith only [h26148, hlam, p26604_1]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              rcases p26604_3 (m.d 0 2) (by simp) with h26840 | h26840
              · rcases p26604_3 (m.d 1 2) (by simp) with h26841 | h26841
                · rcases p26604_3 (m.d 2 3) (by simp) with h26842 | h26842
                  · rcases p26604_3 (m.d 2 4) (by simp) with h26843 | h26843
                    · linarith only [h26149, h26843, hlam]
                    · rcases p26604_3 (m.d 2 5) (by simp) with h26845 | h26845
                      · rcases h3bigk with h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c | h26846c
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [hlam, p26846_0]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [h15532, hlam, p26846_1]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [h0, h18443, h20697, h22350, h25427, h26147, h26148, hc01, hc12, hc34, hc45, hlam, hphi, p26153_1, p26604_1, p26846_1]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          rcases p26846_3 (m.d 0 3) (by simp) with h26850 | h26850
                          · rcases p26846_3 (m.d 1 3) (by simp) with h26851 | h26851
                            · rcases p26846_3 (m.d 2 3) (by simp) with h26852 | h26852
                              · linarith only [h22350, h26852, hlam]
                              · linarith only [h26147, h26852, hlam]
                            · linarith only [h25425, h26851, hlam]
                          · linarith only [h26850, hlam, p26846_0]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          rcases p26846_3 (m.d 0 3) (by simp) with h26857 | h26857
                          · rcases p26846_3 (m.d 1 3) (by simp) with h26858 | h26858
                            · rcases p26846_3 (m.d 2 3) (by simp) with h26859 | h26859
                              · linarith only [h22350, h26859, hlam]
                              · linarith only [h26148, h26859, hlam]
                            · linarith only [h25426, h26858, hlam]
                          · linarith only [h26857, hlam, p26846_0]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [h18443, h20697, h22350, h25422, h25427, h26147, h26148, hc01, hc12, hc34, hc45, hlam, hphi, p26153_1, p26604_1, p26846_1]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [hlam, p26846_0]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [h18443, h20697, h25422, h25427, h26147, h26148, hc01, hc12, hc34, hc45, hlam, hphi, p26153_1, p26604_1, p26846_1]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          rcases p26846_3 (m.d 0 3) (by simp) with h26867 | h26867
                          · linarith only [h15532, h26867, hlam]
                          · linarith only [h22353, h26867, hlam]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          rcases p26846_3 (m.d 0 3) (by simp) with h26870 | h26870
                          · linarith only [h15532, h26870, hlam]
                          · linarith only [h22354, h26870, hlam]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [h22350, hlam, p26846_0]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [h25422, hlam, p26846_0]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [hlam, p26846_0]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          rcases p26846_3 (m.d 0 3) (by simp) with h26876 | h26876
                          · rcases p26846_3 (m.d 1 3) (by simp) with h26877 | h26877
                            · rcases p26846_3 (m.d 2 3) (by simp) with h26878 | h26878
                              · rcases p26846_3 (m.d 3 4) (by simp) with h26879 | h26879
                                · linarith only [h26879, hlam, p26846_0]
                                · rcases p26846_3 (m.d 3 5) (by simp) with h26881 | h26881
                                  · linarith only [h26148, h26881, hlam]
                                  · linarith only [h26151, h26881, hlam]
                              · linarith only [h26878, hlam, p26846_0]
                            · linarith only [h25425, h26877, hlam]
                          · linarith only [h22353, h26876, hlam]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          rcases p26846_3 (m.d 0 3) (by simp) with h26887 | h26887
                          · rcases p26846_3 (m.d 1 3) (by simp) with h26888 | h26888
                            · rcases p26846_3 (m.d 2 3) (by simp) with h26889 | h26889
                              · rcases p26846_3 (m.d 3 4) (by simp) with h26890 | h26890
                                · linarith only [h26147, h26890, hlam]
                                · rcases p26846_3 (m.d 3 5) (by simp) with h26892 | h26892
                                  · linarith only [h26892, hlam, p26846_0]
                                  · rcases h5bigk with h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c | h26894c
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [hlam, p26894_0]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h20697, hlam, p26894_1]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h20697, h25427, h26147, hc34, hc45, hlam, hphi, p26604_1, p26894_1]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h20697, h25427, h26151, hc34, hc45, hlam, hphi, p26894_1]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h22355, hlam, p26894_1]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h18443, h25427, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p26153_1, p26894_1]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [hlam, p26894_0]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h25427, h26147, hc34, hc45, hlam, hphi, p26604_1, p26894_1]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h25427, h26151, hc34, hc45, hlam, hphi, p26894_1]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h25427, hlam, p26894_1]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h22352, hlam, p26894_1]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h25424, hlam, p26894_1]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [hlam, p26894_0]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h0, h22350, h26148, h26151, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26894_1]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h26149, hlam, p26894_1]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h22354, hlam, p26894_0]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h25426, hlam, p26894_0]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h26148, hlam, p26894_0]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [hlam, p26894_0]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h26151, hlam, p26894_1]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h18443, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p26153_1, p26894_1]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h18443, h20697, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p26153_1, p26894_1]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h26147, hc34, hc45, hlam, hphi, p26604_1, p26894_1]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [h26151, hc34, hc45, hlam, hphi, p26894_1]
                                    · have p26894_0 := h26894c.1
                                      have p26894_1 := h26894c.2.1
                                      have p26894_2 := h26894c.2.2.1
                                      have p26894_3 := h26894c.2.2.2
                                      linarith only [hlam, p26894_0]
                              · linarith only [h26889, hlam, p26846_0]
                            · linarith only [h25426, h26888, hlam]
                          · linarith only [h22354, h26887, hlam]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [h22353, hlam, p26846_0]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [h25425, hlam, p26846_0]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [h26147, hlam, p26846_0]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [hlam, p26846_0]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [h26151, hlam, p26846_1]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [h22354, hlam, p26846_0]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [h25426, hlam, p26846_0]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [h26148, hlam, p26846_0]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [h0, h22350, h26148, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26846_1]
                        · have p26846_0 := h26846c.1
                          have p26846_1 := h26846c.2.1
                          have p26846_2 := h26846c.2.2.1
                          have p26846_3 := h26846c.2.2.2
                          linarith only [hlam, p26846_0]
                      · linarith only [h26149, h26845, hlam]
                  · linarith only [h26147, h26842, hlam]
                · linarith only [h25423, h26841, hlam]
              · linarith only [h22351, h26840, hlam]
            · have p26604_0 := h26604c.1
              have p26604_1 := h26604c.2.1
              have p26604_2 := h26604c.2.2.1
              have p26604_3 := h26604c.2.2.2
              linarith only [hlam, p26604_0]
          · linarith only [h22355, h26603, hlam]
      · linarith only [h22353, h26600, hlam]
    · linarith only [h22351, h26599, hlam]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x24 (m : N7Model)
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
    (h26153c : ((m.d 0 5) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 5) ∧ (m.d 0 5) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 5) ≤ z)))
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
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1 (m : N7Model)
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
  rcases h0bigk with h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c | h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x2 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x3 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x4 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x5 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x6 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x7 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x8 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x9 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x10 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x11 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x12 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x13 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x14 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x15 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x16 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x17 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x18 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x19 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x20 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x21 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x22 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x23 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x24 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151 h26153c

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1 (m : N7Model)
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
  rcases m.htr 3 4 5 (by decide) (by decide) with h26151 | h26151
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149 h26151

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0 (m : N7Model)
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
  rcases m.htr 2 4 5 (by decide) (by decide) with h26149 | h26149
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148 h26149

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x1 (m : N7Model)
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
    (h26148 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  rcases m.htr 2 4 5 (by decide) (by decide) with h26942 | h26942
  · linarith only [h0, h20697, h22351, h25427, h26942, hc01, hc12, hlam, hphi]
  · rcases m.htr 3 4 5 (by decide) (by decide) with h26944 | h26944
    · linarith only [h18443, h22354, h25427, h26147, h26148, h26944, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
    · rcases h0bigk with h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c | h26946c
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [hlam, p26946_0]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [h0, hlam, p26946_1]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [h15532, hlam, p26946_0]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [h18443, hlam, p26946_1]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [h20697, hlam, p26946_1]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        rcases p26946_3 (m.d 0 1) (by simp) with h26952 | h26952
        · linarith only [h0, h26952, hlam]
        · rcases p26946_3 (m.d 0 2) (by simp) with h26954 | h26954
          · rcases p26946_3 (m.d 0 3) (by simp) with h26955 | h26955
            · linarith only [h22350, h26955, hlam]
            · linarith only [h15532, h26955, hlam]
          · linarith only [h0, h26954, hlam]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [hlam, p26946_0]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [h0, h22354, h26148, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26946_1]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        rcases p26946_3 (m.d 0 1) (by simp) with h26961 | h26961
        · linarith only [h0, h26961, hlam]
        · rcases p26946_3 (m.d 0 2) (by simp) with h26963 | h26963
          · rcases p26946_3 (m.d 0 3) (by simp) with h26964 | h26964
            · linarith only [h22350, h26964, hlam]
            · linarith only [h22353, h26964, hlam]
          · linarith only [h22351, h26963, hlam]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [h0, h22354, h26147, h26148, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26946_1]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        rcases p26946_3 (m.d 0 1) (by simp) with h26969 | h26969
        · linarith only [h15532, h26969, hlam]
        · rcases p26946_3 (m.d 0 2) (by simp) with h26971 | h26971
          · rcases p26946_3 (m.d 0 3) (by simp) with h26972 | h26972
            · rcases p26946_3 (m.d 0 4) (by simp) with h26973 | h26973
              · linarith only [h22353, h26973, hlam]
              · linarith only [h18443, h26973, hlam]
            · linarith only [h15532, h26972, hlam]
          · linarith only [h0, h26971, hlam]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [h22350, hlam, p26946_1]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [hlam, p26946_0]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        rcases p26946_3 (m.d 0 1) (by simp) with h26980 | h26980
        · linarith only [h15532, h26980, hlam]
        · rcases p26946_3 (m.d 0 2) (by simp) with h26982 | h26982
          · rcases p26946_3 (m.d 0 3) (by simp) with h26983 | h26983
            · rcases p26946_3 (m.d 0 4) (by simp) with h26984 | h26984
              · linarith only [h22353, h26984, hlam]
              · rcases p26946_3 (m.d 0 5) (by simp) with h26986 | h26986
                · linarith only [h22354, h26986, hlam]
                · linarith only [h22355, h26986, hlam]
            · linarith only [h22353, h26983, hlam]
          · linarith only [h22351, h26982, hlam]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [h15532, h22354, h25422, h26147, h26148, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26946_1]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [h18443, h25427, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p26946_1]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [h22351, hlam, p26946_0]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [h22353, hlam, p26946_0]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [hlam, p26946_0]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [h22355, hlam, p26946_0]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        rcases p26946_3 (m.d 0 1) (by simp) with h26997 | h26997
        · linarith only [h20697, h26997, hlam]
        · rcases p26946_3 (m.d 0 2) (by simp) with h26999 | h26999
          · rcases p26946_3 (m.d 0 3) (by simp) with h27000 | h27000
            · rcases p26946_3 (m.d 0 4) (by simp) with h27001 | h27001
              · linarith only [h22355, h27001, hlam]
              · linarith only [h18443, h27001, hlam]
            · linarith only [h15532, h27000, hlam]
          · linarith only [h0, h26999, hlam]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [h22352, hlam, p26946_1]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [h22354, hlam, p26946_0]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        rcases p26946_3 (m.d 0 1) (by simp) with h27008 | h27008
        · linarith only [h20697, h27008, hlam]
        · rcases p26946_3 (m.d 0 2) (by simp) with h27010 | h27010
          · rcases p26946_3 (m.d 0 3) (by simp) with h27011 | h27011
            · rcases p26946_3 (m.d 0 4) (by simp) with h27012 | h27012
              · linarith only [h22355, h27012, hlam]
              · rcases p26946_3 (m.d 0 5) (by simp) with h27014 | h27014
                · rcases h2bigk with h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c | h27015c
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [hlam, p27015_0]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [h0, hlam, p27015_1]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    rcases p27015_3 (m.d 0 2) (by simp) with h27018 | h27018
                    · rcases p27015_3 (m.d 1 2) (by simp) with h27019 | h27019
                      · rcases p27015_3 (m.d 2 3) (by simp) with h27020 | h27020
                        · linarith only [h27020, hlam, p27015_0]
                        · rcases p27015_3 (m.d 2 4) (by simp) with h27022 | h27022
                          · linarith only [h22351, h27022, hlam]
                          · rcases p27015_3 (m.d 2 5) (by simp) with h27024 | h27024
                            · linarith only [h22352, h27024, hlam]
                            · linarith only [h26148, h27024, hlam]
                      · linarith only [h25422, h27019, hlam]
                    · linarith only [h27018, hlam, p27015_0]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    rcases p27015_3 (m.d 0 2) (by simp) with h27029 | h27029
                    · rcases p27015_3 (m.d 1 2) (by simp) with h27030 | h27030
                      · rcases p27015_3 (m.d 2 3) (by simp) with h27031 | h27031
                        · linarith only [h22350, h27031, hlam]
                        · linarith only [h26147, h27031, hlam]
                      · linarith only [h25423, h27030, hlam]
                    · linarith only [h27029, hlam, p27015_0]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    rcases p27015_3 (m.d 0 2) (by simp) with h27036 | h27036
                    · rcases p27015_3 (m.d 1 2) (by simp) with h27037 | h27037
                      · rcases p27015_3 (m.d 2 3) (by simp) with h27038 | h27038
                        · linarith only [h22350, h27038, hlam]
                        · rcases p27015_3 (m.d 2 4) (by simp) with h27040 | h27040
                          · linarith only [h22351, h27040, hlam]
                          · rcases p27015_3 (m.d 2 5) (by simp) with h27042 | h27042
                            · linarith only [h27042, hlam, p27015_0]
                            · rcases h3bigk with h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c | h27044c
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [hlam, p27044_0]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [h15532, hlam, p27044_1]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                rcases p27044_3 (m.d 0 3) (by simp) with h27047 | h27047
                                · rcases p27044_3 (m.d 1 3) (by simp) with h27048 | h27048
                                  · rcases p27044_3 (m.d 2 3) (by simp) with h27049 | h27049
                                    · linarith only [h22350, h27049, hlam]
                                    · rcases p27044_3 (m.d 3 4) (by simp) with h27051 | h27051
                                      · linarith only [h22353, h27051, hlam]
                                      · rcases p27044_3 (m.d 3 5) (by simp) with h27053 | h27053
                                        · linarith only [h22354, h27053, hlam]
                                        · linarith only [h26148, h27053, hlam]
                                  · linarith only [h25422, h27048, hlam]
                                · linarith only [h22350, h27047, hlam]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [h22354, h26147, h26148, hlam, p27044_2]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [h26147, h26148, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p27044_1]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [h22354, h25422, h26147, h26148, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p27044_1]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [hlam, p27044_0]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                rcases p27044_3 (m.d 0 3) (by simp) with h27062 | h27062
                                · linarith only [h15532, h27062, hlam]
                                · linarith only [h22350, h27062, hlam]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [h15532, h22354, h26147, h26148, hlam, p27044_2]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [h18443, h20697, h25427, h26147, h26148, hc01, hc13, hc34, hc45, hlam, hphi, p26946_1, p27044_1]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [h22350, hlam, p27044_0]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [h25422, hlam, p27044_0]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [hlam, p27044_0]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [h22354, h26148, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p27044_1]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [h26148, hlam, p27044_0]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [h22353, hlam, p27044_0]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [h25425, hlam, p27044_0]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [h26147, hlam, p27044_0]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [hlam, p27044_0]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [h26944, hlam, p27044_1]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [h22354, hlam, p27044_0]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [h25426, hlam, p27044_0]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [h0, h18443, h20697, h22350, h22354, h25427, h26147, hc01, hc12, hc34, hc45, hlam, hphi, p26946_1, p27044_1]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                rcases p27044_3 (m.d 0 3) (by simp) with h27080 | h27080
                                · rcases p27044_3 (m.d 1 3) (by simp) with h27081 | h27081
                                  · rcases p27044_3 (m.d 2 3) (by simp) with h27082 | h27082
                                    · linarith only [h26148, h27082, hlam]
                                    · linarith only [h26147, h27082, hlam]
                                  · linarith only [h25425, h27081, hlam]
                                · linarith only [h22353, h27080, hlam]
                              · have p27044_0 := h27044c.1
                                have p27044_1 := h27044c.2.1
                                have p27044_2 := h27044c.2.2.1
                                have p27044_3 := h27044c.2.2.2
                                linarith only [hlam, p27044_0]
                      · linarith only [h25424, h27037, hlam]
                    · linarith only [h27036, hlam, p27015_0]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [h18443, h20697, h22350, h25427, h26147, hc01, hc12, hc34, hc45, hlam, hphi, p26946_1, p27015_1]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [hlam, p27015_0]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    rcases p27015_3 (m.d 0 2) (by simp) with h27092 | h27092
                    · linarith only [h0, h27092, hlam]
                    · linarith only [h22350, h27092, hlam]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    rcases p27015_3 (m.d 0 2) (by simp) with h27095 | h27095
                    · linarith only [h0, h27095, hlam]
                    · linarith only [h22351, h27095, hlam]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    rcases p27015_3 (m.d 0 2) (by simp) with h27098 | h27098
                    · linarith only [h0, h27098, hlam]
                    · linarith only [h22352, h27098, hlam]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [h22350, hlam, p27015_0]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [h25422, hlam, p27015_0]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [hlam, p27015_0]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [h22350, h22354, h26148, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p27015_1]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [h26148, hlam, p27015_0]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [h22351, hlam, p27015_0]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [h25423, hlam, p27015_0]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [h26147, hlam, p27015_1]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [hlam, p27015_0]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [h26942, hlam, p27015_1]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [h22352, hlam, p27015_0]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [h25424, hlam, p27015_0]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [h0, h18443, h20697, h22352, h25427, h26147, hc01, hc12, hc34, hc45, hlam, hphi, p26946_1, p27015_1]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    rcases p27015_3 (m.d 0 2) (by simp) with h27114 | h27114
                    · rcases p27015_3 (m.d 1 2) (by simp) with h27115 | h27115
                      · rcases p27015_3 (m.d 2 3) (by simp) with h27116 | h27116
                        · linarith only [h26148, h27116, hlam]
                        · linarith only [h26147, h27116, hlam]
                      · linarith only [h25423, h27115, hlam]
                    · linarith only [h22351, h27114, hlam]
                  · have p27015_0 := h27015c.1
                    have p27015_1 := h27015c.2.1
                    have p27015_2 := h27015c.2.2.1
                    have p27015_3 := h27015c.2.2.2
                    linarith only [hlam, p27015_0]
                · linarith only [h22355, h27014, hlam]
            · linarith only [h22353, h27011, hlam]
          · linarith only [h22351, h27010, hlam]
      · have p26946_0 := h26946c.1
        have p26946_1 := h26946c.2.1
        have p26946_2 := h26946c.2.2.1
        have p26946_3 := h26946c.2.2.2
        linarith only [hlam, p26946_0]

end R2N4
