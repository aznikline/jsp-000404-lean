import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S64
import Jsp000404.R1LeavesN7_0S65
import Jsp000404.R1LeavesN7_0S66

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x14 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 3) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 3) ∧ (m.d 1 5) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 5) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [h34266, hlam, p34277_1]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x15 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 4) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 4) ∧ (m.d 0 1) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 0 1) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [h33188, hlam, p34277_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x16 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 4) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 4) ∧ (m.d 1 2) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 2) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [h34262, hlam, p34277_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x17 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 4) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 4) ∧ (m.d 1 3) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 3) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [h0, h33189, h34268, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x18 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 4) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 4) ∧ (m.d 1 4) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 4) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [hlam, p34277_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x19 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 4) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 4) ∧ (m.d 1 5) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 5) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [h34268, hlam, p34277_1]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x20 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 5) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 5) ∧ (m.d 0 1) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 0 1) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [h33189, hlam, p34277_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x21 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 5) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 5) ∧ (m.d 1 2) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 2) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [h34263, hlam, p34277_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x22 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 5) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 5) ∧ (m.d 1 3) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 3) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [h0, h33189, h34261, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x23 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 5) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 5) ∧ (m.d 1 4) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 4) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [h0, h33189, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p34277_1]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x24 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 5) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 5) ∧ (m.d 1 5) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 5) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [hlam, p34277_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  rcases h1bigk with h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c | h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x2 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x3 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x4 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x5 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x6 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x7 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x8 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x9 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x10 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x11 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x12 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x13 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x14 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x15 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x16 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x17 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x18 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x19 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x20 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x21 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x22 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x23 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x24 m hb1 hb2 hb4 hb5 hg0 hg33187 hg33188 hg33189 hg33190 hg33191 hg33192 h33193 h33775 h33836 h34261 h34262 h34263 h34264 h34266 h34268 h34270 h34272 h34274 h34276 h34277c

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h35197c : ((m.d 0 1) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 1) ∧ (m.d 0 1) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 0 1) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p35197_0 := h35197c.1
  have p35197_1 := h35197c.2.1
  have p35197_2 := h35197c.2.2.1
  have p35197_3 := h35197c.2.2.2
  linarith only [hlam, p35197_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h35197c : ((m.d 0 1) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 0 1) ∧ (m.d 1 2) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 2) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p35197_0 := h35197c.1
  have p35197_1 := h35197c.2.1
  have p35197_2 := h35197c.2.2.1
  have p35197_3 := h35197c.2.2.2
  linarith only [h0, hlam, p35197_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x2 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h35197c : ((m.d 0 1) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 0 1) ∧ (m.d 1 3) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 3) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p35197_0 := h35197c.1
  have p35197_1 := h35197c.2.1
  have p35197_2 := h35197c.2.2.1
  have p35197_3 := h35197c.2.2.2
  rcases p35197_3 (m.d 0 1) (by simp) with h35200 | h35200
  · rcases p35197_3 (m.d 1 2) (by simp) with h35201 | h35201
    · rcases p35197_3 (m.d 1 3) (by simp) with h35202 | h35202
      · linarith only [h35202, hlam, p35197_0]
      · rcases p35197_3 (m.d 1 4) (by simp) with h35204 | h35204
        · linarith only [h33188, h35204, hlam]
        · linarith only [h34264, h35204, hlam]
    · linarith only [h34261, h35201, hlam]
  · linarith only [h35200, hlam, p35197_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x3 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h35197c : ((m.d 0 1) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 0 1) ∧ (m.d 1 4) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 4) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p35197_0 := h35197c.1
  have p35197_1 := h35197c.2.1
  have p35197_2 := h35197c.2.2.1
  have p35197_3 := h35197c.2.2.2
  rcases p35197_3 (m.d 0 1) (by simp) with h35209 | h35209
  · rcases p35197_3 (m.d 1 2) (by simp) with h35210 | h35210
    · rcases p35197_3 (m.d 1 3) (by simp) with h35211 | h35211
      · linarith only [h33187, h35211, hlam]
      · rcases p35197_3 (m.d 1 4) (by simp) with h35213 | h35213
        · linarith only [h35213, hlam, p35197_0]
        · rcases p35197_3 (m.d 1 5) (by simp) with h35215 | h35215
          · linarith only [h33189, h35215, hlam]
          · linarith only [h34268, h35215, hlam]
    · linarith only [h34262, h35210, hlam]
  · linarith only [h35209, hlam, p35197_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x4 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h35197c : ((m.d 0 1) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 0 1) ∧ (m.d 1 5) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 5) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p35197_0 := h35197c.1
  have p35197_1 := h35197c.2.1
  have p35197_2 := h35197c.2.2.1
  have p35197_3 := h35197c.2.2.2
  rcases p35197_3 (m.d 0 1) (by simp) with h35220 | h35220
  · rcases p35197_3 (m.d 1 2) (by simp) with h35221 | h35221
    · rcases p35197_3 (m.d 1 3) (by simp) with h35222 | h35222
      · linarith only [h33187, h35222, hlam]
      · rcases p35197_3 (m.d 1 4) (by simp) with h35224 | h35224
        · linarith only [h33188, h35224, hlam]
        · rcases p35197_3 (m.d 1 5) (by simp) with h35226 | h35226
          · linarith only [h35226, hlam, p35197_0]
          · rcases h1emax with h35228 | h35228 | h35228 | h35228 | h35228
            · linarith only [h35228, hc15, hlam, hphi, ht01, ht0b, ht5b, p35197_1]
            · linarith only [h0, h34262, h34268, h34270, h35228, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1]
            · rcases h2bigk with h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c | h35231c
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [hlam, p35231_0]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [h0, hlam, p35231_0]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                rcases p35231_3 (m.d 0 2) (by simp) with h35234 | h35234
                · rcases p35231_3 (m.d 1 2) (by simp) with h35235 | h35235
                  · rcases p35231_3 (m.d 2 3) (by simp) with h35236 | h35236
                    · linarith only [h35236, hlam, p35231_0]
                    · rcases p35231_3 (m.d 2 4) (by simp) with h35238 | h35238
                      · linarith only [h33191, h35238, hlam]
                      · linarith only [h34270, h35238, hlam]
                  · linarith only [h34261, h35235, hlam]
                · linarith only [h35234, hlam, p35231_0]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                rcases p35231_3 (m.d 0 2) (by simp) with h35243 | h35243
                · rcases p35231_3 (m.d 1 2) (by simp) with h35244 | h35244
                  · rcases p35231_3 (m.d 2 3) (by simp) with h35245 | h35245
                    · linarith only [h33190, h35245, hlam]
                    · rcases p35231_3 (m.d 2 4) (by simp) with h35247 | h35247
                      · linarith only [h35247, hlam, p35231_0]
                      · rcases p35231_3 (m.d 2 5) (by simp) with h35249 | h35249
                        · linarith only [h33192, h35249, hlam]
                        · linarith only [h34274, h35249, hlam]
                  · linarith only [h34262, h35244, hlam]
                · linarith only [h35243, hlam, p35231_0]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                rcases p35231_3 (m.d 0 2) (by simp) with h35254 | h35254
                · rcases p35231_3 (m.d 1 2) (by simp) with h35255 | h35255
                  · rcases p35231_3 (m.d 2 3) (by simp) with h35256 | h35256
                    · linarith only [h33190, h35256, hlam]
                    · rcases p35231_3 (m.d 2 4) (by simp) with h35258 | h35258
                      · linarith only [h33191, h35258, hlam]
                      · rcases p35231_3 (m.d 2 5) (by simp) with h35260 | h35260
                        · linarith only [h35260, hlam, p35231_0]
                        · rcases h4bigk with h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c | h35262c
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [hlam, p35262_0]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [h33193, h34262, h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35262_1]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [h33193, h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35262_1]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [h33193, hlam, p35262_1]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [h33836, hlam, p35262_0]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [h33188, hlam, p35262_0]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [hlam, p35262_0]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [h34268, h34270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p35197_1, p35262_1]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [h34264, hlam, p35262_1]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [h34268, hlam, p35262_0]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [h33191, hlam, p35262_0]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [h34262, hlam, p35262_0]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [hlam, p35262_0]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [h34270, hlam, p35262_1]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [h34274, hlam, p35262_0]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [h34276, hc04, hc45, hlam, hphi, p35262_1]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35262_1]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35262_1]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [hlam, p35262_0]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [h34276, hlam, p35262_0]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            rcases p35262_3 (m.d 0 4) (by simp) with h35283 | h35283
                            · linarith only [h35283, hlam, p35262_0]
                            · rcases p35262_3 (m.d 1 4) (by simp) with h35285 | h35285
                              · linarith only [h34268, h35285, hlam]
                              · rcases p35262_3 (m.d 2 4) (by simp) with h35287 | h35287
                                · linarith only [h34274, h35287, hlam]
                                · rcases p35262_3 (m.d 3 4) (by simp) with h35289 | h35289
                                  · linarith only [h34276, h35289, hlam]
                                  · linarith only [h33193, h35289, hlam]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            rcases p35262_3 (m.d 0 4) (by simp) with h35292 | h35292
                            · linarith only [h33836, h35292, hlam]
                            · linarith only [h33188, h35292, hlam]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            rcases p35262_3 (m.d 0 4) (by simp) with h35295 | h35295
                            · linarith only [h33836, h35295, hlam]
                            · linarith only [h33191, h35295, hlam]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [h33187, h33193, h34261, hc23, hc45, hlam, hphi, ht34, p35262_1]
                          · have p35262_0 := h35262c.1
                            have p35262_1 := h35262c.2.1
                            have p35262_2 := h35262c.2.2.1
                            have p35262_3 := h35262c.2.2.2
                            linarith only [hlam, p35262_0]
                  · linarith only [h34263, h35255, hlam]
                · linarith only [h35254, hlam, p35231_0]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p35197_1, p35231_1]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [hlam, p35231_0]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [h0, h34263, h34270, h34274, hlam, p35197_1, p35231_2]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [h0, h34263, h34274, hlam, p35197_1, p35231_2]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [h0, h34263, hlam, p35197_1, p35231_2]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [h33190, hlam, p35231_0]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [h34261, hlam, p35231_0]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [hlam, p35231_0]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [h34270, hlam, p35231_1]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [h34272, hlam, p35231_1]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [h33191, hlam, p35231_0]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [h34262, hlam, p35231_0]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [h34263, h34274, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p35197_1, p35231_1]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [hlam, p35231_0]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [h34274, hlam, p35231_0]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [h33192, hlam, p35231_0]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [h34263, hlam, p35231_0]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [h0, h34263, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35231_1]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [h0, h34263, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p35197_1, p35231_1]
              · have p35231_0 := h35231c.1
                have p35231_1 := h35231c.2.1
                have p35231_2 := h35231c.2.2.1
                have p35231_3 := h35231c.2.2.2
                linarith only [hlam, p35231_0]
            · rcases h2bigk with h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c | h35322c
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [hlam, p35322_0]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [h0, hlam, p35322_0]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                rcases p35322_3 (m.d 0 2) (by simp) with h35325 | h35325
                · rcases p35322_3 (m.d 1 2) (by simp) with h35326 | h35326
                  · rcases p35322_3 (m.d 2 3) (by simp) with h35327 | h35327
                    · linarith only [h35327, hlam, p35322_0]
                    · rcases p35322_3 (m.d 2 4) (by simp) with h35329 | h35329
                      · linarith only [h33191, h35329, hlam]
                      · linarith only [h34270, h35329, hlam]
                  · linarith only [h34261, h35326, hlam]
                · linarith only [h35325, hlam, p35322_0]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                rcases p35322_3 (m.d 0 2) (by simp) with h35334 | h35334
                · rcases p35322_3 (m.d 1 2) (by simp) with h35335 | h35335
                  · rcases p35322_3 (m.d 2 3) (by simp) with h35336 | h35336
                    · linarith only [h33190, h35336, hlam]
                    · rcases p35322_3 (m.d 2 4) (by simp) with h35338 | h35338
                      · linarith only [h35338, hlam, p35322_0]
                      · rcases p35322_3 (m.d 2 5) (by simp) with h35340 | h35340
                        · linarith only [h33192, h35340, hlam]
                        · linarith only [h34274, h35340, hlam]
                  · linarith only [h34262, h35335, hlam]
                · linarith only [h35334, hlam, p35322_0]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                rcases p35322_3 (m.d 0 2) (by simp) with h35345 | h35345
                · rcases p35322_3 (m.d 1 2) (by simp) with h35346 | h35346
                  · rcases p35322_3 (m.d 2 3) (by simp) with h35347 | h35347
                    · linarith only [h33190, h35347, hlam]
                    · rcases p35322_3 (m.d 2 4) (by simp) with h35349 | h35349
                      · linarith only [h33191, h35349, hlam]
                      · rcases p35322_3 (m.d 2 5) (by simp) with h35351 | h35351
                        · linarith only [h35351, hlam, p35322_0]
                        · rcases h4bigk with h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c | h35353c
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [hlam, p35353_0]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [h33836, hc14, hc45, hlam, hphi, p35353_1]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [h33836, h34270, hc23, hc45, hlam, hphi, ht34, p35353_1]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [h33193, hlam, p35353_1]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [h33836, hlam, p35353_0]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [h33188, hlam, p35353_0]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [hlam, p35353_0]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35353_1]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [h34264, hlam, p35353_1]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [h34268, hlam, p35353_0]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [h33191, hlam, p35353_0]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [h34262, hlam, p35353_0]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [hlam, p35353_0]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [h34270, hlam, p35353_1]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [h34274, hlam, p35353_0]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [h34276, hc04, hc45, hlam, hphi, p35353_1]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35353_1]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35353_1]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [hlam, p35353_0]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [h34276, hlam, p35353_0]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            rcases p35353_3 (m.d 0 4) (by simp) with h35374 | h35374
                            · linarith only [h35374, hlam, p35353_0]
                            · rcases p35353_3 (m.d 1 4) (by simp) with h35376 | h35376
                              · linarith only [h34268, h35376, hlam]
                              · rcases p35353_3 (m.d 2 4) (by simp) with h35378 | h35378
                                · linarith only [h34274, h35378, hlam]
                                · rcases p35353_3 (m.d 3 4) (by simp) with h35380 | h35380
                                  · linarith only [h34276, h35380, hlam]
                                  · linarith only [h33193, h35380, hlam]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            rcases p35353_3 (m.d 0 4) (by simp) with h35383 | h35383
                            · linarith only [h33836, h35383, hlam]
                            · linarith only [h33188, h35383, hlam]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            rcases p35353_3 (m.d 0 4) (by simp) with h35386 | h35386
                            · linarith only [h33836, h35386, hlam]
                            · linarith only [h33191, h35386, hlam]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [h33187, h33193, h34261, hc23, hc45, hlam, hphi, ht34, p35353_1]
                          · have p35353_0 := h35353c.1
                            have p35353_1 := h35353c.2.1
                            have p35353_2 := h35353c.2.2.1
                            have p35353_3 := h35353c.2.2.2
                            linarith only [hlam, p35353_0]
                  · linarith only [h34263, h35346, hlam]
                · linarith only [h35345, hlam, p35322_0]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p35197_1, p35322_1]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [hlam, p35322_0]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [h0, h34261, h34266, hlam, p35197_1, p35322_2]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [h0, h34262, h34268, hlam, p35197_1, p35322_2]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [h0, h34263, hlam, p35197_1, p35322_2]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [h33190, hlam, p35322_0]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [h34261, hlam, p35322_0]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [hlam, p35322_0]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [h34270, hlam, p35322_1]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [h34272, hlam, p35322_1]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [h33191, hlam, p35322_0]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [h34262, hlam, p35322_0]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [h34262, h34268, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p35197_1, p35322_1]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [hlam, p35322_0]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [h34274, hlam, p35322_0]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [h33192, hlam, p35322_0]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [h34263, hlam, p35322_0]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [h0, h34263, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35322_1]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [h0, h34263, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p35197_1, p35322_1]
              · have p35322_0 := h35322c.1
                have p35322_1 := h35322c.2.1
                have p35322_2 := h35322c.2.2.1
                have p35322_3 := h35322c.2.2.2
                linarith only [hlam, p35322_0]
            · rcases h2bigk with h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c | h35413c
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [hlam, p35413_0]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [h0, hlam, p35413_0]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                rcases p35413_3 (m.d 0 2) (by simp) with h35416 | h35416
                · rcases p35413_3 (m.d 1 2) (by simp) with h35417 | h35417
                  · rcases p35413_3 (m.d 2 3) (by simp) with h35418 | h35418
                    · linarith only [h35418, hlam, p35413_0]
                    · rcases p35413_3 (m.d 2 4) (by simp) with h35420 | h35420
                      · linarith only [h33191, h35420, hlam]
                      · linarith only [h34270, h35420, hlam]
                  · linarith only [h34261, h35417, hlam]
                · linarith only [h35416, hlam, p35413_0]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                rcases p35413_3 (m.d 0 2) (by simp) with h35425 | h35425
                · rcases p35413_3 (m.d 1 2) (by simp) with h35426 | h35426
                  · rcases p35413_3 (m.d 2 3) (by simp) with h35427 | h35427
                    · linarith only [h33190, h35427, hlam]
                    · rcases p35413_3 (m.d 2 4) (by simp) with h35429 | h35429
                      · linarith only [h35429, hlam, p35413_0]
                      · rcases p35413_3 (m.d 2 5) (by simp) with h35431 | h35431
                        · linarith only [h33192, h35431, hlam]
                        · linarith only [h34274, h35431, hlam]
                  · linarith only [h34262, h35426, hlam]
                · linarith only [h35425, hlam, p35413_0]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                rcases p35413_3 (m.d 0 2) (by simp) with h35436 | h35436
                · rcases p35413_3 (m.d 1 2) (by simp) with h35437 | h35437
                  · rcases p35413_3 (m.d 2 3) (by simp) with h35438 | h35438
                    · linarith only [h33190, h35438, hlam]
                    · rcases p35413_3 (m.d 2 4) (by simp) with h35440 | h35440
                      · linarith only [h33191, h35440, hlam]
                      · rcases p35413_3 (m.d 2 5) (by simp) with h35442 | h35442
                        · linarith only [h35442, hlam, p35413_0]
                        · rcases h4bigk with h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c | h35444c
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [hlam, p35444_0]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [h33836, hc14, hc45, hlam, hphi, p35444_1]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [h33836, h34270, hc23, hc45, hlam, hphi, ht34, p35444_1]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [h33193, hlam, p35444_1]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [h33836, hlam, p35444_0]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [h33188, hlam, p35444_0]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [hlam, p35444_0]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35444_1]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [h34264, hlam, p35444_1]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [h34268, hlam, p35444_0]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [h33191, hlam, p35444_0]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [h34262, hlam, p35444_0]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [hlam, p35444_0]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [h34270, hlam, p35444_1]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [h34274, hlam, p35444_0]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [h34276, hc04, hc45, hlam, hphi, p35444_1]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [h34276, hc14, hc45, hlam, hphi, p35444_1]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35444_1]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [hlam, p35444_0]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [h34276, hlam, p35444_0]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            rcases p35444_3 (m.d 0 4) (by simp) with h35465 | h35465
                            · linarith only [h35465, hlam, p35444_0]
                            · rcases p35444_3 (m.d 1 4) (by simp) with h35467 | h35467
                              · linarith only [h34268, h35467, hlam]
                              · rcases p35444_3 (m.d 2 4) (by simp) with h35469 | h35469
                                · linarith only [h34274, h35469, hlam]
                                · rcases p35444_3 (m.d 3 4) (by simp) with h35471 | h35471
                                  · linarith only [h34276, h35471, hlam]
                                  · linarith only [h33193, h35471, hlam]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            rcases p35444_3 (m.d 0 4) (by simp) with h35474 | h35474
                            · linarith only [h33836, h35474, hlam]
                            · linarith only [h33188, h35474, hlam]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            rcases p35444_3 (m.d 0 4) (by simp) with h35477 | h35477
                            · linarith only [h33836, h35477, hlam]
                            · linarith only [h33191, h35477, hlam]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [h33187, h33193, h34261, hc23, hc45, hlam, hphi, ht34, p35444_1]
                          · have p35444_0 := h35444c.1
                            have p35444_1 := h35444c.2.1
                            have p35444_2 := h35444c.2.2.1
                            have p35444_3 := h35444c.2.2.2
                            linarith only [hlam, p35444_0]
                  · linarith only [h34263, h35437, hlam]
                · linarith only [h35436, hlam, p35413_0]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p35197_1, p35413_1]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [hlam, p35413_0]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [h0, h34261, h34266, hlam, p35197_1, p35413_2]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [h0, h34262, h34268, hlam, p35197_1, p35413_2]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [h0, h34263, hlam, p35197_1, p35413_2]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [h33190, hlam, p35413_0]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [h34261, hlam, p35413_0]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [hlam, p35413_0]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [h34270, hlam, p35413_1]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [h34272, hlam, p35413_1]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [h33191, hlam, p35413_0]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [h34262, hlam, p35413_0]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [h34262, h34268, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p35197_1, p35413_1]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [hlam, p35413_0]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [h34274, hlam, p35413_0]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [h33192, hlam, p35413_0]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [h34263, hlam, p35413_0]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [h0, h34263, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35413_1]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [h0, h34263, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p35197_1, p35413_1]
              · have p35413_0 := h35413c.1
                have p35413_1 := h35413c.2.1
                have p35413_2 := h35413c.2.2.1
                have p35413_3 := h35413c.2.2.2
                linarith only [hlam, p35413_0]
    · linarith only [h34263, h35221, hlam]
  · linarith only [h35220, hlam, p35197_0]

end R2N4
