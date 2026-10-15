import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x11 (m : N7Model)
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
    (hg22355 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg22356 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg22357 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg22358 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg22359 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg22360 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg22361 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h24025 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h24026c : ((m.d 0 3) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 3) ∧ (m.d 0 2) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 2) ≤ z)))
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
  have h22355 := hg22355
  have h22356 := hg22356
  have h22357 := hg22357
  have h22358 := hg22358
  have h22359 := hg22359
  have h22360 := hg22360
  have h22361 := hg22361
  have p24026_0 := h24026c.1
  have p24026_1 := h24026c.2.1
  have p24026_2 := h24026c.2.2.1
  have p24026_3 := h24026c.2.2.2
  linarith only [h22350, hlam, p24026_1]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x12 (m : N7Model)
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
    (hg22355 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg22356 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg22357 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg22358 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg22359 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg22360 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg22361 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h24025 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h24026c : ((m.d 0 3) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 3) ∧ (m.d 0 3) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 3) ≤ z)))
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
  have h22355 := hg22355
  have h22356 := hg22356
  have h22357 := hg22357
  have h22358 := hg22358
  have h22359 := hg22359
  have h22360 := hg22360
  have h22361 := hg22361
  have p24026_0 := h24026c.1
  have p24026_1 := h24026c.2.1
  have p24026_2 := h24026c.2.2.1
  have p24026_3 := h24026c.2.2.2
  linarith only [hlam, p24026_0]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x13 (m : N7Model)
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
    (hg22355 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg22356 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg22357 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg22358 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg22359 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg22360 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg22361 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h24025 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h24026c : ((m.d 0 3) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 3) ∧ (m.d 0 4) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 4) ≤ z)))
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
  have h22355 := hg22355
  have h22356 := hg22356
  have h22357 := hg22357
  have h22358 := hg22358
  have h22359 := hg22359
  have h22360 := hg22360
  have h22361 := hg22361
  have p24026_0 := h24026c.1
  have p24026_1 := h24026c.2.1
  have p24026_2 := h24026c.2.2.1
  have p24026_3 := h24026c.2.2.2
  rcases p24026_3 (m.d 0 1) (by simp) with h24066 | h24066
  · linarith only [h15532, h24066, hlam]
  · rcases p24026_3 (m.d 0 2) (by simp) with h24068 | h24068
    · rcases p24026_3 (m.d 0 3) (by simp) with h24069 | h24069
      · rcases p24026_3 (m.d 0 4) (by simp) with h24070 | h24070
        · linarith only [h22353, h24070, hlam]
        · rcases p24026_3 (m.d 0 5) (by simp) with h24072 | h24072
          · linarith only [h22354, h24072, hlam]
          · rcases h2bigk with h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c | h24074c
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [hlam, p24074_0]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [h0, hlam, p24074_1]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [h22350, h22353, h23731, h24025, hlam, p24026_1, p24074_2]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              rcases p24074_3 (m.d 0 2) (by simp) with h24078 | h24078
              · rcases p24074_3 (m.d 1 2) (by simp) with h24079 | h24079
                · rcases p24074_3 (m.d 2 3) (by simp) with h24080 | h24080
                  · linarith only [h22350, h24080, hlam]
                  · rcases p24074_3 (m.d 2 4) (by simp) with h24082 | h24082
                    · linarith only [h24082, hlam, p24074_0]
                    · rcases p24074_3 (m.d 2 5) (by simp) with h24084 | h24084
                      · linarith only [h22352, h24084, hlam]
                      · rcases h3bigk with h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c | h24086c
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [hlam, p24086_0]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [h15532, hlam, p24086_1]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [h22353, h23731, h24025, hlam, p24026_1, p24086_2]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          rcases p24086_3 (m.d 0 3) (by simp) with h24090 | h24090
                          · rcases p24086_3 (m.d 1 3) (by simp) with h24091 | h24091
                            · rcases p24086_3 (m.d 2 3) (by simp) with h24092 | h24092
                              · linarith only [h22350, h24092, hlam]
                              · rcases p24086_3 (m.d 3 4) (by simp) with h24094 | h24094
                                · linarith only [h24094, hlam, p24086_0]
                                · rcases p24086_3 (m.d 3 5) (by simp) with h24096 | h24096
                                  · linarith only [h22354, h24096, hlam]
                                  · rcases h5bigk with h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c | h24098c
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [hlam, p24098_0]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h20697, hlam, p24098_1]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h22350, h22355, h23731, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24026_1, p24098_1]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h0, h22350, h22355, h23731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24026_1, p24098_1]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h0, h22350, h22355, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24026_1, p24098_1]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h20697, h22356, h22359, h22361, hc01, hc12, hlam, hphi, p24098_1]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [hlam, p24098_0]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      rcases p24098_3 (m.d 0 5) (by simp) with h24106 | h24106
                                      · linarith only [h20697, h24106, hlam]
                                      · linarith only [h22352, h24106, hlam]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h22356, h22359, h22361, h23731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24098_1]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      rcases p24098_3 (m.d 0 5) (by simp) with h24110 | h24110
                                      · linarith only [h20697, h24110, hlam]
                                      · linarith only [h22355, h24110, hlam]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h22352, hlam, p24098_1]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h22358, hlam, p24098_1]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [hlam, p24098_0]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h23731, hlam, p24098_1]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h0, h22352, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24098_1]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h22354, hlam, p24098_0]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h22360, hlam, p24098_0]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h0, h22350, h24025, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p24086_1, p24098_1]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [hlam, p24098_0]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h0, h22350, h22353, h24025, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24026_1, p24098_1]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h22355, hlam, p24098_0]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h22361, hlam, p24098_0]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h24024, hlam, p24098_0]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [h24025, hlam, p24098_0]
                                    · have p24098_0 := h24098c.1
                                      have p24098_1 := h24098c.2.1
                                      have p24098_2 := h24098c.2.2.1
                                      have p24098_3 := h24098c.2.2.2
                                      linarith only [hlam, p24098_0]
                            · linarith only [h22359, h24091, hlam]
                          · linarith only [h24090, hlam, p24086_0]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          rcases p24086_3 (m.d 0 3) (by simp) with h24130 | h24130
                          · rcases p24086_3 (m.d 1 3) (by simp) with h24131 | h24131
                            · rcases p24086_3 (m.d 2 3) (by simp) with h24132 | h24132
                              · linarith only [h22350, h24132, hlam]
                              · rcases p24086_3 (m.d 3 4) (by simp) with h24134 | h24134
                                · linarith only [h22353, h24134, hlam]
                                · linarith only [h24025, h24134, hlam]
                            · linarith only [h22360, h24131, hlam]
                          · linarith only [h24130, hlam, p24086_0]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [h22356, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p24026_1, p24086_1]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [hlam, p24086_0]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [h15532, h22353, h22362, hlam, p24026_1, p24086_2]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          rcases p24086_3 (m.d 0 3) (by simp) with h24142 | h24142
                          · linarith only [h15532, h24142, hlam]
                          · linarith only [h22353, h24142, hlam]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          rcases p24086_3 (m.d 0 3) (by simp) with h24145 | h24145
                          · linarith only [h15532, h24145, hlam]
                          · linarith only [h22354, h24145, hlam]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [h22350, hlam, p24086_0]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [h22356, hlam, p24086_0]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [hlam, p24086_0]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [h22362, hlam, p24086_0]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [h23731, hlam, p24086_0]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [h22353, hlam, p24086_0]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [h22359, hlam, p24086_0]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [h0, h22350, h22353, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24026_1, p24086_1]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [hlam, p24086_0]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [h0, h22350, h22353, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p24026_1, p24086_1]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [h22354, hlam, p24086_0]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [h22360, hlam, p24086_0]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [h0, h22350, h22354, h22355, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24026_1, p24086_1]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [h24025, hlam, p24086_0]
                        · have p24086_0 := h24086c.1
                          have p24086_1 := h24086c.2.1
                          have p24086_2 := h24086c.2.2.1
                          have p24086_3 := h24086c.2.2.2
                          linarith only [hlam, p24086_0]
                · linarith only [h22357, h24079, hlam]
              · linarith only [h24078, hlam, p24074_0]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              rcases p24074_3 (m.d 0 2) (by simp) with h24165 | h24165
              · rcases p24074_3 (m.d 1 2) (by simp) with h24166 | h24166
                · rcases p24074_3 (m.d 2 3) (by simp) with h24167 | h24167
                  · linarith only [h22350, h24167, hlam]
                  · rcases p24074_3 (m.d 2 4) (by simp) with h24169 | h24169
                    · linarith only [h22351, h24169, hlam]
                    · linarith only [h24024, h24169, hlam]
                · linarith only [h22358, h24166, hlam]
              · linarith only [h24165, hlam, p24074_0]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [h22350, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p24026_1, p24074_1]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [hlam, p24074_0]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [h0, h22350, h22353, h22362, hlam, p24026_1, p24074_2]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              rcases p24074_3 (m.d 0 2) (by simp) with h24177 | h24177
              · linarith only [h0, h24177, hlam]
              · linarith only [h22351, h24177, hlam]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              rcases p24074_3 (m.d 0 2) (by simp) with h24180 | h24180
              · linarith only [h0, h24180, hlam]
              · linarith only [h22352, h24180, hlam]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [h22350, hlam, p24074_0]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [h22356, hlam, p24074_0]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [hlam, p24074_0]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [h22362, hlam, p24074_0]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [h23731, hlam, p24074_0]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [h22351, hlam, p24074_0]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [h22357, hlam, p24074_0]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [h22350, h22353, h22362, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24026_1, p24074_1]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [hlam, p24074_0]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [h0, h22350, h22353, h22362, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p24026_1, p24074_1]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [h22352, hlam, p24074_0]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [h22358, hlam, p24074_0]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [h0, h22350, h22352, h22355, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24026_1, p24074_1]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [h24024, hlam, p24074_0]
            · have p24074_0 := h24074c.1
              have p24074_1 := h24074c.2.1
              have p24074_2 := h24074c.2.2.1
              have p24074_3 := h24074c.2.2.2
              linarith only [hlam, p24074_0]
      · linarith only [h22353, h24069, hlam]
    · linarith only [h22351, h24068, hlam]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x14 (m : N7Model)
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
    (hg22355 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg22356 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg22357 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg22358 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg22359 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg22360 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg22361 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h24025 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h24026c : ((m.d 0 3) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 3) ∧ (m.d 0 5) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 5) ≤ z)))
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
  have h22355 := hg22355
  have h22356 := hg22356
  have h22357 := hg22357
  have h22358 := hg22358
  have h22359 := hg22359
  have h22360 := hg22360
  have h22361 := hg22361
  have p24026_0 := h24026c.1
  have p24026_1 := h24026c.2.1
  have p24026_2 := h24026c.2.2.1
  have p24026_3 := h24026c.2.2.2
  rcases p24026_3 (m.d 0 1) (by simp) with h24200 | h24200
  · linarith only [h15532, h24200, hlam]
  · rcases p24026_3 (m.d 0 2) (by simp) with h24202 | h24202
    · rcases p24026_3 (m.d 0 3) (by simp) with h24203 | h24203
      · rcases p24026_3 (m.d 0 4) (by simp) with h24204 | h24204
        · linarith only [h22353, h24204, hlam]
        · linarith only [h22355, h24204, hlam]
      · linarith only [h22354, h24203, hlam]
    · linarith only [h22352, h24202, hlam]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x15 (m : N7Model)
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
    (hg22355 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg22356 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg22357 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg22358 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg22359 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg22360 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg22361 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h24025 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h24026c : ((m.d 0 4) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 4) ∧ (m.d 0 1) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 1) ≤ z)))
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
  have h22355 := hg22355
  have h22356 := hg22356
  have h22357 := hg22357
  have h22358 := hg22358
  have h22359 := hg22359
  have h22360 := hg22360
  have h22361 := hg22361
  have p24026_0 := h24026c.1
  have p24026_1 := h24026c.2.1
  have p24026_2 := h24026c.2.2.1
  have p24026_3 := h24026c.2.2.2
  rcases p24026_3 (m.d 0 1) (by simp) with h24209 | h24209
  · linarith only [h18443, h24209, hlam]
  · rcases p24026_3 (m.d 0 2) (by simp) with h24211 | h24211
    · rcases p24026_3 (m.d 0 3) (by simp) with h24212 | h24212
      · rcases p24026_3 (m.d 0 4) (by simp) with h24213 | h24213
        · rcases p24026_3 (m.d 0 5) (by simp) with h24214 | h24214
          · linarith only [h22355, h24214, hlam]
          · linarith only [h20697, h24214, hlam]
        · linarith only [h18443, h24213, hlam]
      · linarith only [h15532, h24212, hlam]
    · linarith only [h0, h24211, hlam]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x16 (m : N7Model)
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
    (hg22355 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg22356 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg22357 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg22358 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg22359 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg22360 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg22361 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h24025 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h24026c : ((m.d 0 4) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 4) ∧ (m.d 0 2) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 2) ≤ z)))
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
  have h22355 := hg22355
  have h22356 := hg22356
  have h22357 := hg22357
  have h22358 := hg22358
  have h22359 := hg22359
  have h22360 := hg22360
  have h22361 := hg22361
  have p24026_0 := h24026c.1
  have p24026_1 := h24026c.2.1
  have p24026_2 := h24026c.2.2.1
  have p24026_3 := h24026c.2.2.2
  linarith only [h22351, hlam, p24026_0]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x17 (m : N7Model)
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
    (hg22355 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg22356 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg22357 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg22358 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg22359 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg22360 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg22361 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h24025 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h24026c : ((m.d 0 4) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 4) ∧ (m.d 0 3) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 3) ≤ z)))
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
  have h22355 := hg22355
  have h22356 := hg22356
  have h22357 := hg22357
  have h22358 := hg22358
  have h22359 := hg22359
  have h22360 := hg22360
  have h22361 := hg22361
  have p24026_0 := h24026c.1
  have p24026_1 := h24026c.2.1
  have p24026_2 := h24026c.2.2.1
  have p24026_3 := h24026c.2.2.2
  linarith only [h22353, hlam, p24026_0]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x18 (m : N7Model)
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
    (hg22355 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg22356 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg22357 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg22358 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg22359 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg22360 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg22361 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h24025 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h24026c : ((m.d 0 4) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 4) ∧ (m.d 0 4) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 4) ≤ z)))
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
  have h22355 := hg22355
  have h22356 := hg22356
  have h22357 := hg22357
  have h22358 := hg22358
  have h22359 := hg22359
  have h22360 := hg22360
  have h22361 := hg22361
  have p24026_0 := h24026c.1
  have p24026_1 := h24026c.2.1
  have p24026_2 := h24026c.2.2.1
  have p24026_3 := h24026c.2.2.2
  linarith only [hlam, p24026_0]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x19 (m : N7Model)
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
    (hg22355 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg22356 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg22357 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg22358 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg22359 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg22360 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg22361 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h24025 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h24026c : ((m.d 0 4) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 4) ∧ (m.d 0 5) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 5) ≤ z)))
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
  have h22355 := hg22355
  have h22356 := hg22356
  have h22357 := hg22357
  have h22358 := hg22358
  have h22359 := hg22359
  have h22360 := hg22360
  have h22361 := hg22361
  have p24026_0 := h24026c.1
  have p24026_1 := h24026c.2.1
  have p24026_2 := h24026c.2.2.1
  have p24026_3 := h24026c.2.2.2
  rcases p24026_3 (m.d 0 1) (by simp) with h24223 | h24223
  · linarith only [h18443, h24223, hlam]
  · rcases p24026_3 (m.d 0 2) (by simp) with h24225 | h24225
    · rcases p24026_3 (m.d 0 3) (by simp) with h24226 | h24226
      · rcases p24026_3 (m.d 0 4) (by simp) with h24227 | h24227
        · rcases p24026_3 (m.d 0 5) (by simp) with h24228 | h24228
          · linarith only [h22355, h24228, hlam]
          · rcases h2bigk with h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c | h24230c
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [hlam, p24230_0]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [h0, hlam, p24230_1]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [h22351, h22354, h23731, hlam, p24026_1, p24230_2]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              rcases p24230_3 (m.d 0 2) (by simp) with h24234 | h24234
              · rcases p24230_3 (m.d 1 2) (by simp) with h24235 | h24235
                · rcases p24230_3 (m.d 2 3) (by simp) with h24236 | h24236
                  · linarith only [h22350, h24236, hlam]
                  · rcases p24230_3 (m.d 2 4) (by simp) with h24238 | h24238
                    · linarith only [h24238, hlam, p24230_0]
                    · rcases p24230_3 (m.d 2 5) (by simp) with h24240 | h24240
                      · linarith only [h22352, h24240, hlam]
                      · rcases h3bigk with h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c | h24242c
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [hlam, p24242_0]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [h15532, hlam, p24242_1]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [h22353, h22354, h23731, hlam, p24026_1, p24242_2]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          rcases p24242_3 (m.d 0 3) (by simp) with h24246 | h24246
                          · rcases p24242_3 (m.d 1 3) (by simp) with h24247 | h24247
                            · rcases p24242_3 (m.d 2 3) (by simp) with h24248 | h24248
                              · linarith only [h22350, h24248, hlam]
                              · rcases p24242_3 (m.d 3 4) (by simp) with h24250 | h24250
                                · linarith only [h24250, hlam, p24242_0]
                                · rcases p24242_3 (m.d 3 5) (by simp) with h24252 | h24252
                                  · linarith only [h22354, h24252, hlam]
                                  · rcases h5bigk with h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c | h24254c
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [hlam, p24254_0]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h20697, hlam, p24254_1]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h0, h22350, h22353, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p24026_1, p24254_1]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h0, h22350, h22353, h23731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24026_1, p24254_1]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h0, h22350, h22353, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24026_1, p24254_1]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h20697, h22359, h22361, hc01, hc13, hlam, hphi, p24254_1]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [hlam, p24254_0]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      rcases p24254_3 (m.d 0 5) (by simp) with h24262 | h24262
                                      · linarith only [h20697, h24262, hlam]
                                      · linarith only [h22352, h24262, hlam]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h22356, h22359, h22361, h23731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24254_1]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      rcases p24254_3 (m.d 0 5) (by simp) with h24266 | h24266
                                      · linarith only [h20697, h24266, hlam]
                                      · linarith only [h22355, h24266, hlam]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h22352, hlam, p24254_1]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h22358, hlam, p24254_1]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [hlam, p24254_0]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h23731, hlam, p24254_1]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h0, h22352, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24254_1]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h22354, hlam, p24254_0]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h22360, hlam, p24254_0]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h0, h22350, h22354, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p24254_1]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [hlam, p24254_0]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h0, h22350, h22353, h22354, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24026_1, p24254_1]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h22355, hlam, p24254_0]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h22361, hlam, p24254_0]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h24024, hlam, p24254_0]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [h24025, hlam, p24254_0]
                                    · have p24254_0 := h24254c.1
                                      have p24254_1 := h24254c.2.1
                                      have p24254_2 := h24254c.2.2.1
                                      have p24254_3 := h24254c.2.2.2
                                      linarith only [hlam, p24254_0]
                            · linarith only [h22359, h24247, hlam]
                          · linarith only [h24246, hlam, p24242_0]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          rcases p24242_3 (m.d 0 3) (by simp) with h24286 | h24286
                          · rcases p24242_3 (m.d 1 3) (by simp) with h24287 | h24287
                            · rcases p24242_3 (m.d 2 3) (by simp) with h24288 | h24288
                              · linarith only [h22350, h24288, hlam]
                              · rcases p24242_3 (m.d 3 4) (by simp) with h24290 | h24290
                                · linarith only [h22353, h24290, hlam]
                                · linarith only [h24025, h24290, hlam]
                            · linarith only [h22360, h24287, hlam]
                          · linarith only [h24286, hlam, p24242_0]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [h22353, h22356, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p24026_1, p24242_1]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [hlam, p24242_0]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [h15532, h22353, h22354, h23731, hlam, p24026_1, p24242_2]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          rcases p24242_3 (m.d 0 3) (by simp) with h24298 | h24298
                          · linarith only [h15532, h24298, hlam]
                          · linarith only [h22353, h24298, hlam]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          rcases p24242_3 (m.d 0 3) (by simp) with h24301 | h24301
                          · linarith only [h15532, h24301, hlam]
                          · linarith only [h22354, h24301, hlam]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [h22350, hlam, p24242_0]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [h22356, hlam, p24242_0]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [hlam, p24242_0]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [h22362, hlam, p24242_0]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [h23731, hlam, p24242_0]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [h22353, hlam, p24242_0]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [h22359, hlam, p24242_0]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          rcases p24242_3 (m.d 0 3) (by simp) with h24311 | h24311
                          · rcases p24242_3 (m.d 1 3) (by simp) with h24312 | h24312
                            · rcases p24242_3 (m.d 2 3) (by simp) with h24313 | h24313
                              · linarith only [h24313, hlam, p24242_0]
                              · rcases p24242_3 (m.d 3 4) (by simp) with h24315 | h24315
                                · rcases p24242_3 (m.d 3 5) (by simp) with h24316 | h24316
                                  · linarith only [h24025, h24316, hlam]
                                  · linarith only [h23731, h24316, hlam]
                                · linarith only [h24315, hlam, p24242_0]
                            · linarith only [h22356, h24312, hlam]
                          · linarith only [h22350, h24311, hlam]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [hlam, p24242_0]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [h23731, hc23, hc34, hlam, hphi, p24242_1]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [h22354, hlam, p24242_0]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [h22360, hlam, p24242_0]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [h0, h22350, h22353, h22354, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24026_1, p24242_1]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [h24025, hlam, p24242_0]
                        · have p24242_0 := h24242c.1
                          have p24242_1 := h24242c.2.1
                          have p24242_2 := h24242c.2.2.1
                          have p24242_3 := h24242c.2.2.2
                          linarith only [hlam, p24242_0]
                · linarith only [h22357, h24235, hlam]
              · linarith only [h24234, hlam, p24230_0]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              rcases p24230_3 (m.d 0 2) (by simp) with h24331 | h24331
              · rcases p24230_3 (m.d 1 2) (by simp) with h24332 | h24332
                · rcases p24230_3 (m.d 2 3) (by simp) with h24333 | h24333
                  · linarith only [h22350, h24333, hlam]
                  · rcases p24230_3 (m.d 2 4) (by simp) with h24335 | h24335
                    · linarith only [h22351, h24335, hlam]
                    · linarith only [h24024, h24335, hlam]
                · linarith only [h22358, h24332, hlam]
              · linarith only [h24331, hlam, p24230_0]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [h22350, h22353, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p24026_1, p24230_1]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [hlam, p24230_0]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [h0, h22350, h22353, h22354, h23731, hlam, p24026_1, p24230_2]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              rcases p24230_3 (m.d 0 2) (by simp) with h24343 | h24343
              · linarith only [h0, h24343, hlam]
              · linarith only [h22351, h24343, hlam]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              rcases p24230_3 (m.d 0 2) (by simp) with h24346 | h24346
              · linarith only [h0, h24346, hlam]
              · linarith only [h22352, h24346, hlam]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [h22350, hlam, p24230_0]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [h22356, hlam, p24230_0]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [hlam, p24230_0]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [h22362, hlam, p24230_0]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [h23731, hlam, p24230_0]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [h22351, hlam, p24230_0]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [h22357, hlam, p24230_0]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              rcases p24230_3 (m.d 0 2) (by simp) with h24356 | h24356
              · rcases p24230_3 (m.d 1 2) (by simp) with h24357 | h24357
                · rcases p24230_3 (m.d 2 3) (by simp) with h24358 | h24358
                  · linarith only [h22362, h24358, hlam]
                  · rcases p24230_3 (m.d 2 4) (by simp) with h24360 | h24360
                    · rcases p24230_3 (m.d 2 5) (by simp) with h24361 | h24361
                      · linarith only [h24024, h24361, hlam]
                      · linarith only [h23731, h24361, hlam]
                    · linarith only [h22362, h24360, hlam]
                · linarith only [h22356, h24357, hlam]
              · linarith only [h22350, h24356, hlam]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [hlam, p24230_0]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              rcases p24230_3 (m.d 0 2) (by simp) with h24368 | h24368
              · rcases p24230_3 (m.d 1 2) (by simp) with h24369 | h24369
                · rcases p24230_3 (m.d 2 3) (by simp) with h24370 | h24370
                  · linarith only [h22362, h24370, hlam]
                  · rcases p24230_3 (m.d 2 4) (by simp) with h24372 | h24372
                    · rcases p24230_3 (m.d 2 5) (by simp) with h24373 | h24373
                      · linarith only [h24024, h24373, hlam]
                      · rcases h3bigk with h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c | h24375c
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [hlam, p24375_0]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [h15532, hlam, p24375_1]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [h22353, h22354, h23731, hlam, p24026_1, p24375_2]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [h22350, h22362, h23731, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24230_1, p24375_1]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          rcases p24375_3 (m.d 0 3) (by simp) with h24380 | h24380
                          · rcases p24375_3 (m.d 1 3) (by simp) with h24381 | h24381
                            · rcases p24375_3 (m.d 2 3) (by simp) with h24382 | h24382
                              · linarith only [h22350, h24382, hlam]
                              · rcases p24375_3 (m.d 3 4) (by simp) with h24384 | h24384
                                · linarith only [h22353, h24384, hlam]
                                · linarith only [h24025, h24384, hlam]
                            · linarith only [h22360, h24381, hlam]
                          · linarith only [h24380, hlam, p24375_0]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [h20697, h22353, hc01, hc13, hlam, hphi, p24026_1, p24375_1]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [hlam, p24375_0]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [h15532, h22353, h22362, h23731, hlam, p24230_1, p24375_2]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [h22362, h23731, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24230_1, p24375_1]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          rcases p24375_3 (m.d 0 3) (by simp) with h24393 | h24393
                          · linarith only [h15532, h24393, hlam]
                          · linarith only [h22354, h24393, hlam]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [h22350, hlam, p24375_0]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [h22356, hlam, p24375_0]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [hlam, p24375_0]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [h22362, hlam, p24375_0]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [h23731, hlam, p24375_0]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [h22353, hlam, p24375_0]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [h22359, hlam, p24375_0]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          rcases p24375_3 (m.d 0 3) (by simp) with h24403 | h24403
                          · rcases p24375_3 (m.d 1 3) (by simp) with h24404 | h24404
                            · rcases p24375_3 (m.d 2 3) (by simp) with h24405 | h24405
                              · linarith only [h24405, hlam, p24375_0]
                              · rcases p24375_3 (m.d 3 4) (by simp) with h24407 | h24407
                                · rcases p24375_3 (m.d 3 5) (by simp) with h24408 | h24408
                                  · linarith only [h24025, h24408, hlam]
                                  · linarith only [h23731, h24408, hlam]
                                · linarith only [h24407, hlam, p24375_0]
                            · linarith only [h22356, h24404, hlam]
                          · linarith only [h22350, h24403, hlam]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [hlam, p24375_0]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [h22353, h23731, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24375_1]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [h22354, hlam, p24375_0]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [h22360, hlam, p24375_0]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [h22354, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24026_1, p24375_1]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [h24025, hlam, p24375_0]
                        · have p24375_0 := h24375c.1
                          have p24375_1 := h24375c.2.1
                          have p24375_2 := h24375c.2.2.1
                          have p24375_3 := h24375c.2.2.2
                          linarith only [hlam, p24375_0]
                    · linarith only [h24024, h24372, hlam]
                · linarith only [h22358, h24369, hlam]
              · linarith only [h22352, h24368, hlam]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [h22352, hlam, p24230_0]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [h22358, hlam, p24230_0]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [h18443, h22352, h22356, h22359, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24026_1, p24230_1]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [h24024, hlam, p24230_0]
            · have p24230_0 := h24230c.1
              have p24230_1 := h24230c.2.1
              have p24230_2 := h24230c.2.2.1
              have p24230_3 := h24230c.2.2.2
              linarith only [hlam, p24230_0]
        · linarith only [h22355, h24227, hlam]
      · linarith only [h22354, h24226, hlam]
    · linarith only [h22352, h24225, hlam]

end R2N4
