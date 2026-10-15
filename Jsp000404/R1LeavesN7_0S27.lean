import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S24
import Jsp000404.R1LeavesN7_0S26

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14161 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14162 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h14163 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 1 3 5 (by decide) (by decide) with h14165 | h14165
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0_x0_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h14161 h14162 h14163 h14165
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0_x0_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h14161 h14162 h14163 h14165

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14161 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14162 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 1 3 4 (by decide) (by decide) with h14163 | h14163
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h14161 h14162 h14163
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h14161 h14162 h14163

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14161 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14162 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 1 3 4 (by decide) (by decide) with h15381 | h15381
  · linarith only [h1, h15381, h7, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h15383 | h15383
    · linarith only [h1, h13284, h15383, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h15385 | h15385
      · linarith only [h14161, h14162, h15385, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h15387 | h15387
        · linarith only [h14159, h14160, h14162, h15381, h15385, h15387, h6, h7, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h15389 | h15389
          · linarith only [h0, h14161, h14162, h15387, h15389, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h15391 | h15391
            · linarith only [h14161, h14162, h15385, h15391, hlam]
            · linarith only [h14159, h14161, h14162, h15387, h15391, h7, hc23, hc34, hlam, hphi]

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14161 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 1 2 5 (by decide) (by decide) with h14162 | h14162
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h14161 h14162
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h14161 h14162

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14161 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 1 2 5 (by decide) (by decide) with h15394 | h15394
  · rcases m.htr 1 3 4 (by decide) (by decide) with h15395 | h15395
    · linarith only [h1, h13284, h14161, h15395, h5, h7, hc12, hc35, hlam, hphi, ht23]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h15397 | h15397
      · linarith only [h0, h13284, h14160, h14161, h15397, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h15399 | h15399
        · rcases m.htr 2 3 4 (by decide) (by decide) with h15400 | h15400
          · linarith only [h14160, h14161, h15400, h5, h7, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h15402 | h15402
            · linarith only [h1, h13284, h14160, h15402, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h15404 | h15404
              · rcases m.htr 3 4 5 (by decide) (by decide) with h15405 | h15405
                · rcases h1bigk with h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c | h15406c
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [hlam, p15406_0]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    rcases p15406_3 (m.d 0 1) (by simp) with h15408 | h15408
                    · rcases p15406_3 (m.d 1 2) (by simp) with h15409 | h15409
                      · linarith only [h15409, hlam, p15406_0]
                      · rcases p15406_3 (m.d 1 3) (by simp) with h15411 | h15411
                        · linarith only [h1, h15411, hlam]
                        · rcases p15406_3 (m.d 1 4) (by simp) with h15413 | h15413
                          · linarith only [h15413, h2, hlam]
                          · linarith only [h14161, h15413, hlam]
                    · linarith only [h15408, hlam, p15406_0]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    rcases p15406_3 (m.d 0 1) (by simp) with h15417 | h15417
                    · rcases p15406_3 (m.d 1 2) (by simp) with h15418 | h15418
                      · linarith only [h0, h15418, hlam]
                      · linarith only [h14160, h15418, hlam]
                    · linarith only [h15417, hlam, p15406_0]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    rcases p15406_3 (m.d 0 1) (by simp) with h15422 | h15422
                    · rcases p15406_3 (m.d 1 2) (by simp) with h15423 | h15423
                      · linarith only [h0, h15423, hlam]
                      · rcases p15406_3 (m.d 1 3) (by simp) with h15425 | h15425
                        · linarith only [h1, h15425, hlam]
                        · rcases p15406_3 (m.d 1 4) (by simp) with h15427 | h15427
                          · linarith only [h15427, hlam, p15406_0]
                          · rcases p15406_3 (m.d 1 5) (by simp) with h15429 | h15429
                            · linarith only [h15429, h3, hlam]
                            · rcases h1emax with h15431 | h15431 | h15431 | h15431 | h15431
                              · linarith only [h0, h14161, h15394, h15402, h15431, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases h2bigk with h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c | h15433c
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [hlam, p15433_0]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  rcases p15433_3 (m.d 0 2) (by simp) with h15435 | h15435
                                  · rcases p15433_3 (m.d 1 2) (by simp) with h15436 | h15436
                                    · linarith only [h0, h15436, hlam]
                                    · rcases p15433_3 (m.d 2 3) (by simp) with h15438 | h15438
                                      · linarith only [h15438, h4, hlam]
                                      · rcases p15433_3 (m.d 2 4) (by simp) with h15440 | h15440
                                        · linarith only [h15440, h5, hlam]
                                        · linarith only [h14161, h15440, hlam]
                                  · linarith only [h0, h15435, hlam]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [h14161, h15394, h15402, h5, hlam, p15433_2]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [h0, h14161, h15394, h15402, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15433_1]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [h14161, h15394, h5, hlam, p15433_2]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [h0, hlam, p15433_1]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [hlam, p15433_0]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [h14161, h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15433_1]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [h14161, hlam, p15433_0]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [h0, h14161, h15402, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15433_1]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [h4, hlam, p15433_0]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [h14160, hlam, p15433_0]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [hlam, p15433_0]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [h15400, hlam, p15433_1]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [h15402, hlam, p15433_1]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [h5, hlam, p15433_0]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [h0, h14160, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15433_1]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  rcases p15433_3 (m.d 0 2) (by simp) with h15459 | h15459
                                  · rcases p15433_3 (m.d 1 2) (by simp) with h15460 | h15460
                                    · linarith only [h14161, h15460, hlam]
                                    · linarith only [h14160, h15460, hlam]
                                  · linarith only [h15459, h4, hlam]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [hlam, p15433_0]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  rcases p15433_3 (m.d 0 2) (by simp) with h15465 | h15465
                                  · rcases p15433_3 (m.d 1 2) (by simp) with h15466 | h15466
                                    · linarith only [h14161, h15466, hlam]
                                    · linarith only [h15394, h15466, hlam]
                                  · linarith only [h15465, h6, hlam]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [h6, hlam, p15433_0]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [h15394, hlam, p15433_0]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [h0, h15394, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15433_1]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [h15404, hlam, p15433_1]
                                · have p15433_0 := h15433c.1
                                  have p15433_1 := h15433c.2.1
                                  have p15433_2 := h15433c.2.2.1
                                  have p15433_3 := h15433c.2.2.2
                                  linarith only [hlam, p15433_0]
                              · rcases h2bigk with h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c | h15475c
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [hlam, p15475_0]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  rcases p15475_3 (m.d 0 2) (by simp) with h15477 | h15477
                                  · rcases p15475_3 (m.d 1 2) (by simp) with h15478 | h15478
                                    · linarith only [h0, h15478, hlam]
                                    · rcases p15475_3 (m.d 2 3) (by simp) with h15480 | h15480
                                      · linarith only [h15480, h4, hlam]
                                      · rcases p15475_3 (m.d 2 4) (by simp) with h15482 | h15482
                                        · linarith only [h15482, h5, hlam]
                                        · linarith only [h14161, h15482, hlam]
                                  · linarith only [h0, h15477, hlam]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [h14160, h14161, h5, hlam, p15475_2]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [h0, h14161, h15394, hc01, hc25, hlam, hphi, ht0b, ht5b, p15475_1]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [h14161, h15394, h5, hlam, p15475_2]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [h0, hlam, p15475_1]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [hlam, p15475_0]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [h14161, h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15475_1]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [h14161, hlam, p15475_0]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [h0, h14161, h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p15475_1]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [h4, hlam, p15475_0]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [h14160, hlam, p15475_0]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [hlam, p15475_0]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [h15400, hlam, p15475_1]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [h15402, hlam, p15475_1]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [h5, hlam, p15475_0]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [h0, h14160, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15475_1]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  rcases p15475_3 (m.d 0 2) (by simp) with h15501 | h15501
                                  · rcases p15475_3 (m.d 1 2) (by simp) with h15502 | h15502
                                    · linarith only [h14161, h15502, hlam]
                                    · linarith only [h14160, h15502, hlam]
                                  · linarith only [h15501, h4, hlam]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [hlam, p15475_0]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  rcases p15475_3 (m.d 0 2) (by simp) with h15507 | h15507
                                  · rcases p15475_3 (m.d 1 2) (by simp) with h15508 | h15508
                                    · linarith only [h14161, h15508, hlam]
                                    · linarith only [h15394, h15508, hlam]
                                  · linarith only [h15507, h6, hlam]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [h6, hlam, p15475_0]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [h15394, hlam, p15475_0]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [h0, h15394, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15475_1]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [h15404, hlam, p15475_1]
                                · have p15475_0 := h15475c.1
                                  have p15475_1 := h15475c.2.1
                                  have p15475_2 := h15475c.2.2.1
                                  have p15475_3 := h15475c.2.2.2
                                  linarith only [hlam, p15475_0]
                              · rcases h2bigk with h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c | h15517c
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [hlam, p15517_0]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  rcases p15517_3 (m.d 0 2) (by simp) with h15519 | h15519
                                  · rcases p15517_3 (m.d 1 2) (by simp) with h15520 | h15520
                                    · linarith only [h0, h15520, hlam]
                                    · rcases p15517_3 (m.d 2 3) (by simp) with h15522 | h15522
                                      · linarith only [h15522, h4, hlam]
                                      · rcases p15517_3 (m.d 2 4) (by simp) with h15524 | h15524
                                        · linarith only [h15524, h5, hlam]
                                        · linarith only [h14161, h15524, hlam]
                                  · linarith only [h0, h15519, hlam]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [h14160, h14161, h5, hlam, p15517_2]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [h14160, h14161, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15517_1]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [h14161, h15394, h5, hlam, p15517_2]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [h0, hlam, p15517_1]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [hlam, p15517_0]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [h0, h14161, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15517_1]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [h14161, hlam, p15517_0]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [h0, h14161, h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p15517_1]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [h4, hlam, p15517_0]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [h14160, hlam, p15517_0]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [hlam, p15517_0]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [h15400, hlam, p15517_1]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [h15402, hlam, p15517_1]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [h5, hlam, p15517_0]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [h0, h14160, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15517_1]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  rcases p15517_3 (m.d 0 2) (by simp) with h15543 | h15543
                                  · rcases p15517_3 (m.d 1 2) (by simp) with h15544 | h15544
                                    · linarith only [h14161, h15544, hlam]
                                    · linarith only [h14160, h15544, hlam]
                                  · linarith only [h15543, h4, hlam]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [hlam, p15517_0]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  rcases p15517_3 (m.d 0 2) (by simp) with h15549 | h15549
                                  · rcases p15517_3 (m.d 1 2) (by simp) with h15550 | h15550
                                    · linarith only [h14161, h15550, hlam]
                                    · linarith only [h15394, h15550, hlam]
                                  · linarith only [h15549, h6, hlam]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [h6, hlam, p15517_0]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [h15394, hlam, p15517_0]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [h0, h15394, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15517_1]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [h15404, hlam, p15517_1]
                                · have p15517_0 := h15517c.1
                                  have p15517_1 := h15517c.2.1
                                  have p15517_2 := h15517c.2.2.1
                                  have p15517_3 := h15517c.2.2.2
                                  linarith only [hlam, p15517_0]
                              · rcases h2bigk with h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c | h15559c
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [hlam, p15559_0]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  rcases p15559_3 (m.d 0 2) (by simp) with h15561 | h15561
                                  · rcases p15559_3 (m.d 1 2) (by simp) with h15562 | h15562
                                    · linarith only [h0, h15562, hlam]
                                    · rcases p15559_3 (m.d 2 3) (by simp) with h15564 | h15564
                                      · linarith only [h15564, h4, hlam]
                                      · rcases p15559_3 (m.d 2 4) (by simp) with h15566 | h15566
                                        · linarith only [h15566, h5, hlam]
                                        · linarith only [h14161, h15566, hlam]
                                  · linarith only [h0, h15561, hlam]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [h14160, h14161, h5, hlam, p15559_2]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [h14160, h14161, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15559_1]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [h14161, h15394, h5, hlam, p15559_2]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [h0, hlam, p15559_1]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [hlam, p15559_0]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [h14161, h5, h7, hc23, hc34, hlam, hphi, p15559_1]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [h14161, hlam, p15559_0]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [h0, h14161, h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p15559_1]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [h4, hlam, p15559_0]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [h14160, hlam, p15559_0]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [hlam, p15559_0]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [h15400, hlam, p15559_1]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [h15402, hlam, p15559_1]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [h5, hlam, p15559_0]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [h0, h14160, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15559_1]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  rcases p15559_3 (m.d 0 2) (by simp) with h15585 | h15585
                                  · rcases p15559_3 (m.d 1 2) (by simp) with h15586 | h15586
                                    · linarith only [h14161, h15586, hlam]
                                    · linarith only [h14160, h15586, hlam]
                                  · linarith only [h15585, h4, hlam]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [hlam, p15559_0]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  rcases p15559_3 (m.d 0 2) (by simp) with h15591 | h15591
                                  · rcases p15559_3 (m.d 1 2) (by simp) with h15592 | h15592
                                    · linarith only [h14161, h15592, hlam]
                                    · linarith only [h15394, h15592, hlam]
                                  · linarith only [h15591, h6, hlam]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [h6, hlam, p15559_0]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [h15394, hlam, p15559_0]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [h0, h15394, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15559_1]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [h15404, hlam, p15559_1]
                                · have p15559_0 := h15559c.1
                                  have p15559_1 := h15559c.2.1
                                  have p15559_2 := h15559c.2.2.1
                                  have p15559_3 := h15559c.2.2.2
                                  linarith only [hlam, p15559_0]
                    · linarith only [h15422, hlam, p15406_0]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    rcases p15406_3 (m.d 0 1) (by simp) with h15602 | h15602
                    · rcases p15406_3 (m.d 1 2) (by simp) with h15603 | h15603
                      · linarith only [h0, h15603, hlam]
                      · linarith only [h15394, h15603, hlam]
                    · linarith only [h15602, hlam, p15406_0]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [h0, hlam, p15406_0]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [hlam, p15406_0]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [h0, h14161, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p15406_1]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [h14161, hlam, p15406_1]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [h0, h14160, h14161, h15397, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15406_1]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [h1, hlam, p15406_0]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [h14160, hlam, p15406_0]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [hlam, p15406_0]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [h15395, hlam, p15406_0]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [h15397, hlam, p15406_1]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [h2, hlam, p15406_0]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [h14160, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15406_1]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    rcases p15406_3 (m.d 0 1) (by simp) with h15619 | h15619
                    · rcases p15406_3 (m.d 1 2) (by simp) with h15620 | h15620
                      · linarith only [h14161, h15620, hlam]
                      · linarith only [h14160, h15620, hlam]
                    · linarith only [h1, h15619, hlam]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [hlam, p15406_0]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    rcases p15406_3 (m.d 0 1) (by simp) with h15625 | h15625
                    · rcases p15406_3 (m.d 1 2) (by simp) with h15626 | h15626
                      · linarith only [h14161, h15626, hlam]
                      · linarith only [h15394, h15626, hlam]
                    · linarith only [h15625, h3, hlam]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [h3, hlam, p15406_0]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [h15394, hlam, p15406_0]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [h0, h14160, h14161, h15394, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15406_1]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [h15399, hlam, p15406_0]
                  · have p15406_0 := h15406c.1
                    have p15406_1 := h15406c.2.1
                    have p15406_2 := h15406c.2.2.1
                    have p15406_3 := h15406c.2.2.2
                    linarith only [hlam, p15406_0]
                · linarith only [h14159, h15405, h7, hlam]
              · linarith only [h14161, h15394, h15399, h15404, hlam]
        · linarith only [h14159, h14160, h14161, h15399, h7, hc23, hc34, hlam, hphi]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h15638 | h15638
    · linarith only [h1, h14160, h14161, h15638, h5, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h15640 | h15640
      · linarith only [h1, h13284, h15640, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h15642 | h15642
        · rcases m.htr 2 3 4 (by decide) (by decide) with h15643 | h15643
          · linarith only [h0, h14160, h14161, h15643, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h15645 | h15645
            · linarith only [h13284, h14160, h15394, h15645, h6, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h15647 | h15647
              · rcases m.htr 3 4 5 (by decide) (by decide) with h15648 | h15648
                · rcases h1bigk with h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c | h15649c
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [hlam, p15649_0]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    rcases p15649_3 (m.d 0 1) (by simp) with h15651 | h15651
                    · rcases p15649_3 (m.d 1 2) (by simp) with h15652 | h15652
                      · linarith only [h15652, hlam, p15649_0]
                      · rcases p15649_3 (m.d 1 3) (by simp) with h15654 | h15654
                        · linarith only [h1, h15654, hlam]
                        · rcases p15649_3 (m.d 1 4) (by simp) with h15656 | h15656
                          · linarith only [h15656, h2, hlam]
                          · linarith only [h14161, h15656, hlam]
                    · linarith only [h15651, hlam, p15649_0]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    rcases p15649_3 (m.d 0 1) (by simp) with h15660 | h15660
                    · rcases p15649_3 (m.d 1 2) (by simp) with h15661 | h15661
                      · linarith only [h0, h15661, hlam]
                      · linarith only [h14160, h15661, hlam]
                    · linarith only [h15660, hlam, p15649_0]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    rcases p15649_3 (m.d 0 1) (by simp) with h15665 | h15665
                    · rcases p15649_3 (m.d 1 2) (by simp) with h15666 | h15666
                      · linarith only [h0, h15666, hlam]
                      · rcases p15649_3 (m.d 1 3) (by simp) with h15668 | h15668
                        · linarith only [h1, h15668, hlam]
                        · rcases p15649_3 (m.d 1 4) (by simp) with h15670 | h15670
                          · linarith only [h15670, hlam, p15649_0]
                          · rcases p15649_3 (m.d 1 5) (by simp) with h15672 | h15672
                            · linarith only [h15672, h3, hlam]
                            · rcases h1emax with h15674 | h15674 | h15674 | h15674 | h15674
                              · linarith only [h0, h15394, h15647, h15674, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases h2bigk with h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c | h15676c
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [hlam, p15676_0]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  rcases p15676_3 (m.d 0 2) (by simp) with h15678 | h15678
                                  · rcases p15676_3 (m.d 1 2) (by simp) with h15679 | h15679
                                    · linarith only [h0, h15679, hlam]
                                    · rcases p15676_3 (m.d 2 3) (by simp) with h15681 | h15681
                                      · linarith only [h15681, h4, hlam]
                                      · rcases p15676_3 (m.d 2 4) (by simp) with h15683 | h15683
                                        · linarith only [h15683, h5, hlam]
                                        · linarith only [h14161, h15683, hlam]
                                  · linarith only [h0, h15678, hlam]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [h14160, h15394, h15647, h5, hlam, p15676_2]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [h0, h14160, h15394, h15647, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15676_1]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [h0, h14160, h15394, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15676_1]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [h0, hlam, p15676_1]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [hlam, p15676_0]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [h14159, h15394, h6, h7, hc23, hc34, hlam, hphi, p15676_1]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [h14161, hlam, p15676_0]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [h15394, hlam, p15676_0]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [h4, hlam, p15676_0]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [h14160, hlam, p15676_0]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [hlam, p15676_0]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [h15643, hlam, p15676_1]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [h15645, hlam, p15676_1]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [h5, hlam, p15676_0]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [h0, h14160, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15676_1]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  rcases p15676_3 (m.d 0 2) (by simp) with h15702 | h15702
                                  · rcases p15676_3 (m.d 1 2) (by simp) with h15703 | h15703
                                    · linarith only [h14161, h15703, hlam]
                                    · linarith only [h14160, h15703, hlam]
                                  · linarith only [h15702, h4, hlam]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [hlam, p15676_0]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [h0, h14160, h15394, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15676_1]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [h6, hlam, p15676_0]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [h0, h14160, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15676_1]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  rcases p15676_3 (m.d 0 2) (by simp) with h15711 | h15711
                                  · rcases p15676_3 (m.d 1 2) (by simp) with h15712 | h15712
                                    · linarith only [h15394, h15712, hlam]
                                    · linarith only [h14160, h15712, hlam]
                                  · linarith only [h15711, h4, hlam]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [h15647, hlam, p15676_1]
                                · have p15676_0 := h15676c.1
                                  have p15676_1 := h15676c.2.1
                                  have p15676_2 := h15676c.2.2.1
                                  have p15676_3 := h15676c.2.2.2
                                  linarith only [hlam, p15676_0]
                              · rcases h2bigk with h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c | h15718c
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [hlam, p15718_0]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  rcases p15718_3 (m.d 0 2) (by simp) with h15720 | h15720
                                  · rcases p15718_3 (m.d 1 2) (by simp) with h15721 | h15721
                                    · linarith only [h0, h15721, hlam]
                                    · rcases p15718_3 (m.d 2 3) (by simp) with h15723 | h15723
                                      · linarith only [h15723, h4, hlam]
                                      · rcases p15718_3 (m.d 2 4) (by simp) with h15725 | h15725
                                        · linarith only [h15725, h5, hlam]
                                        · linarith only [h14161, h15725, hlam]
                                  · linarith only [h0, h15720, hlam]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [h14160, h14161, h5, hlam, p15718_2]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [h14160, h14161, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15718_1]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [h0, h14160, h15394, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15718_1]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [h0, hlam, p15718_1]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [hlam, p15718_0]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [h0, h14161, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15718_1]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [h14161, hlam, p15718_0]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [h15394, hlam, p15718_0]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [h4, hlam, p15718_0]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [h14160, hlam, p15718_0]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [hlam, p15718_0]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [h15643, hlam, p15718_1]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [h15645, hlam, p15718_1]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [h5, hlam, p15718_0]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [h0, h14160, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15718_1]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  rcases p15718_3 (m.d 0 2) (by simp) with h15744 | h15744
                                  · rcases p15718_3 (m.d 1 2) (by simp) with h15745 | h15745
                                    · linarith only [h14161, h15745, hlam]
                                    · linarith only [h14160, h15745, hlam]
                                  · linarith only [h15744, h4, hlam]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [hlam, p15718_0]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [h0, h14160, h15394, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15718_1]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [h6, hlam, p15718_0]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [h0, h14160, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15718_1]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  rcases p15718_3 (m.d 0 2) (by simp) with h15753 | h15753
                                  · rcases p15718_3 (m.d 1 2) (by simp) with h15754 | h15754
                                    · linarith only [h15394, h15754, hlam]
                                    · linarith only [h14160, h15754, hlam]
                                  · linarith only [h15753, h4, hlam]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [h15647, hlam, p15718_1]
                                · have p15718_0 := h15718c.1
                                  have p15718_1 := h15718c.2.1
                                  have p15718_2 := h15718c.2.2.1
                                  have p15718_3 := h15718c.2.2.2
                                  linarith only [hlam, p15718_0]
                              · rcases h2bigk with h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c | h15760c
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [hlam, p15760_0]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  rcases p15760_3 (m.d 0 2) (by simp) with h15762 | h15762
                                  · rcases p15760_3 (m.d 1 2) (by simp) with h15763 | h15763
                                    · linarith only [h0, h15763, hlam]
                                    · rcases p15760_3 (m.d 2 3) (by simp) with h15765 | h15765
                                      · linarith only [h15765, h4, hlam]
                                      · rcases p15760_3 (m.d 2 4) (by simp) with h15767 | h15767
                                        · linarith only [h15767, h5, hlam]
                                        · linarith only [h14161, h15767, hlam]
                                  · linarith only [h0, h15762, hlam]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [h14160, h14161, h5, hlam, p15760_2]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [h14160, h14161, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15760_1]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [h0, h14160, h15394, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15760_1]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [h0, hlam, p15760_1]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [hlam, p15760_0]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [h0, h14161, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15760_1]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [h14161, hlam, p15760_0]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [h15394, hlam, p15760_0]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [h4, hlam, p15760_0]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [h14160, hlam, p15760_0]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [hlam, p15760_0]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [h15643, hlam, p15760_1]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [h15645, hlam, p15760_1]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [h5, hlam, p15760_0]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [h0, h14160, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15760_1]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  rcases p15760_3 (m.d 0 2) (by simp) with h15786 | h15786
                                  · rcases p15760_3 (m.d 1 2) (by simp) with h15787 | h15787
                                    · linarith only [h14161, h15787, hlam]
                                    · linarith only [h14160, h15787, hlam]
                                  · linarith only [h15786, h4, hlam]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [hlam, p15760_0]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [h0, h14160, h15394, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15760_1]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [h6, hlam, p15760_0]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [h0, h14160, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15760_1]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  rcases p15760_3 (m.d 0 2) (by simp) with h15795 | h15795
                                  · rcases p15760_3 (m.d 1 2) (by simp) with h15796 | h15796
                                    · linarith only [h15394, h15796, hlam]
                                    · linarith only [h14160, h15796, hlam]
                                  · linarith only [h15795, h4, hlam]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [h15647, hlam, p15760_1]
                                · have p15760_0 := h15760c.1
                                  have p15760_1 := h15760c.2.1
                                  have p15760_2 := h15760c.2.2.1
                                  have p15760_3 := h15760c.2.2.2
                                  linarith only [hlam, p15760_0]
                              · rcases h2bigk with h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c | h15802c
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [hlam, p15802_0]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  rcases p15802_3 (m.d 0 2) (by simp) with h15804 | h15804
                                  · rcases p15802_3 (m.d 1 2) (by simp) with h15805 | h15805
                                    · linarith only [h0, h15805, hlam]
                                    · rcases p15802_3 (m.d 2 3) (by simp) with h15807 | h15807
                                      · linarith only [h15807, h4, hlam]
                                      · rcases p15802_3 (m.d 2 4) (by simp) with h15809 | h15809
                                        · linarith only [h15809, h5, hlam]
                                        · linarith only [h14161, h15809, hlam]
                                  · linarith only [h0, h15804, hlam]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [h14160, h14161, h5, hlam, p15802_2]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [h14160, h14161, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15802_1]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [h0, h14160, h15394, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15802_1]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [h0, hlam, p15802_1]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [hlam, p15802_0]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [h0, h14161, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15802_1]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [h14161, hlam, p15802_0]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [h15394, hlam, p15802_0]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [h4, hlam, p15802_0]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [h14160, hlam, p15802_0]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [hlam, p15802_0]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [h15643, hlam, p15802_1]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [h15645, hlam, p15802_1]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [h5, hlam, p15802_0]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [h0, h14160, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15802_1]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  rcases p15802_3 (m.d 0 2) (by simp) with h15828 | h15828
                                  · rcases p15802_3 (m.d 1 2) (by simp) with h15829 | h15829
                                    · linarith only [h14161, h15829, hlam]
                                    · linarith only [h14160, h15829, hlam]
                                  · linarith only [h15828, h4, hlam]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [hlam, p15802_0]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [h0, h14160, h15394, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15802_1]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [h6, hlam, p15802_0]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [h0, h14160, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15802_1]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  rcases p15802_3 (m.d 0 2) (by simp) with h15837 | h15837
                                  · rcases p15802_3 (m.d 1 2) (by simp) with h15838 | h15838
                                    · linarith only [h15394, h15838, hlam]
                                    · linarith only [h14160, h15838, hlam]
                                  · linarith only [h15837, h4, hlam]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [h15647, hlam, p15802_1]
                                · have p15802_0 := h15802c.1
                                  have p15802_1 := h15802c.2.1
                                  have p15802_2 := h15802c.2.2.1
                                  have p15802_3 := h15802c.2.2.2
                                  linarith only [hlam, p15802_0]
                    · linarith only [h15665, hlam, p15649_0]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    rcases p15649_3 (m.d 0 1) (by simp) with h15845 | h15845
                    · rcases p15649_3 (m.d 1 2) (by simp) with h15846 | h15846
                      · linarith only [h0, h15846, hlam]
                      · rcases p15649_3 (m.d 1 3) (by simp) with h15848 | h15848
                        · linarith only [h1, h15848, hlam]
                        · rcases p15649_3 (m.d 1 4) (by simp) with h15850 | h15850
                          · linarith only [h15850, h2, hlam]
                          · linarith only [h15642, h15850, hlam]
                    · linarith only [h15845, hlam, p15649_0]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [h0, hlam, p15649_0]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [hlam, p15649_0]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [h0, h14160, h14161, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15649_1]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [h14161, hlam, p15649_1]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [h15394, hlam, p15649_1]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [h1, hlam, p15649_0]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [h14160, hlam, p15649_0]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [hlam, p15649_0]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [h15638, hlam, p15649_0]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [h15640, hlam, p15649_1]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [h2, hlam, p15649_0]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [h14160, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15649_1]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    rcases p15649_3 (m.d 0 1) (by simp) with h15866 | h15866
                    · rcases p15649_3 (m.d 1 2) (by simp) with h15867 | h15867
                      · linarith only [h14161, h15867, hlam]
                      · linarith only [h14160, h15867, hlam]
                    · linarith only [h1, h15866, hlam]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [hlam, p15649_0]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [h0, h14160, h14161, h15394, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15649_1]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [h3, hlam, p15649_0]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [h14160, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15649_1]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    rcases p15649_3 (m.d 0 1) (by simp) with h15875 | h15875
                    · rcases p15649_3 (m.d 1 2) (by simp) with h15876 | h15876
                      · linarith only [h15394, h15876, hlam]
                      · linarith only [h14160, h15876, hlam]
                    · linarith only [h1, h15875, hlam]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [h15642, hlam, p15649_0]
                  · have p15649_0 := h15649c.1
                    have p15649_1 := h15649c.2.1
                    have p15649_2 := h15649c.2.2.1
                    have p15649_3 := h15649c.2.2.2
                    linarith only [hlam, p15649_0]
                · linarith only [h15642, h15648, h2, h7, hlam]
              · linarith only [h14161, h15642, h15647, hlam]
        · linarith only [h14159, h14160, h14161, h15642, h7, hc23, hc34, hlam, hphi]

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 1 2 4 (by decide) (by decide) with h14161 | h14161
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h14161
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h14161

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h15885 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 1 2 5 (by decide) (by decide) with h15886 | h15886
  · rcases m.htr 1 3 4 (by decide) (by decide) with h15887 | h15887
    · linarith only [h14160, h15885, h15887, h4, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
    · linarith only [h14160, h15885, h15887, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h15890 | h15890
    · linarith only [h14160, h15885, h15890, h4, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
    · linarith only [h14160, h15885, h15890, hlam]

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h15885 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h15893 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 1 3 4 (by decide) (by decide) with h15894 | h15894
  · linarith only [h1, h15894, h7, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h15896 | h15896
    · linarith only [h13284, h14160, h15896, h4, hlam]
    · linarith only [h14160, h15893, h15896, hlam]

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h15885 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h15893 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h15899 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  linarith only [h1, h14160, h15899, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h15885 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h15893 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h15899 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h15901 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  linarith only [h1, h13284, h14160, h15901, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

end R2N4
