import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_23S5
import Jsp000404.R1LeavesN7_23S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x21 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg3234 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg3235 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg3236 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h3237 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h3238 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h3239 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h3389 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h3391c : ((m.d 2 5) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 2 5) ∧ (m.d 1 2) - (m.d 2 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 2 5) ∨ (m.d 1 2) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  have h3234 := hg3234
  have h3235 := hg3235
  have h3236 := hg3236
  have p3391_0 := h3391c.1
  have p3391_1 := h3391c.2.1
  have p3391_2 := h3391c.2.2.1
  have p3391_3 := h3391c.2.2.2
  linarith only [h3233, hlam, p3391_0]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x22 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg3234 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg3235 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg3236 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h3237 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h3238 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h3239 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h3389 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h3391c : ((m.d 2 5) < (m.d 2 3) ∧ 2 * m.lam ≤ (m.d 2 3) - (m.d 2 5) ∧ (m.d 2 3) - (m.d 2 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 2 5) ∨ (m.d 2 3) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  have h3234 := hg3234
  have h3235 := hg3235
  have h3236 := hg3236
  have p3391_0 := h3391c.1
  have p3391_1 := h3391c.2.1
  have p3391_2 := h3391c.2.2.1
  have p3391_3 := h3391c.2.2.2
  linarith only [h3238, hlam, p3391_0]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x23 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg3234 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg3235 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg3236 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h3237 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h3238 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h3239 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h3389 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h3391c : ((m.d 2 5) < (m.d 2 4) ∧ 2 * m.lam ≤ (m.d 2 4) - (m.d 2 5) ∧ (m.d 2 4) - (m.d 2 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 2 5) ∨ (m.d 2 4) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  have h3234 := hg3234
  have h3235 := hg3235
  have h3236 := hg3236
  have p3391_0 := h3391c.1
  have p3391_1 := h3391c.2.1
  have p3391_2 := h3391c.2.2.1
  have p3391_3 := h3391c.2.2.2
  rcases p3391_3 (m.d 0 2) (by simp) with h4288 | h4288
  · rcases p3391_3 (m.d 1 2) (by simp) with h4289 | h4289
    · rcases p3391_3 (m.d 2 3) (by simp) with h4290 | h4290
      · rcases p3391_3 (m.d 2 4) (by simp) with h4291 | h4291
        · linarith only [h3239, h4291, hlam]
        · rcases p3391_3 (m.d 2 5) (by simp) with h4293 | h4293
          · rcases h2emax with h4294 | h4294 | h4294 | h4294 | h4294
            · linarith only [h0, h4294, hlam, ht12, u1ehi0]
            · linarith only [h4294, hlam, ht12, u1ehi1]
            · linarith only [h3237, h3238, h4294, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3391_1]
            · rcases h4bigk with h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c | h4298c
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [hlam, p4298_0]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3221, hlam, p4298_1]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3230, h3239, hlam, p3391_1, p4298_2]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3230, h3237, h3239, hlam, p3391_1, p4298_2]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3225, h3228, h3237, h3239, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3391_1, p4298_1]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3221, hc14, hlam, hphi, p4298_1, u1ehi0]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [hlam, p4298_0]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3221, h3230, h3239, hlam, p3391_1, p4298_2]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3221, h3230, h3237, h3239, hlam, p3391_1, p4298_2]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3237, h3239, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3391_1, p4298_1]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3226, hlam, p4298_0]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3232, hlam, p4298_0]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [hlam, p4298_0]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3230, h3239, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p3391_1, p4298_1]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3239, hlam, p4298_0]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3228, hlam, p4298_0]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3234, hlam, p4298_0]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3237, hlam, p4298_0]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [hlam, p4298_0]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3389, hlam, p4298_0]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3230, hlam, p4298_0]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [h3236, hlam, p4298_0]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                rcases p4298_3 (m.d 0 4) (by simp) with h4321 | h4321
                · rcases p4298_3 (m.d 1 4) (by simp) with h4322 | h4322
                  · rcases p4298_3 (m.d 2 4) (by simp) with h4323 | h4323
                    · linarith only [h4323, hlam, p4298_0]
                    · rcases p4298_3 (m.d 3 4) (by simp) with h4325 | h4325
                      · linarith only [h3389, h4325, hlam]
                      · rcases p4298_3 (m.d 4 5) (by simp) with h4327 | h4327
                        · rcases h5bigk with h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c | h4328c
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [hlam, p4328_0]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [h3223, hlam, p4328_1]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p3391_1, p4328_1]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            rcases p4328_3 (m.d 0 5) (by simp) with h4332 | h4332
                            · rcases p4328_3 (m.d 1 5) (by simp) with h4333 | h4333
                              · rcases p4328_3 (m.d 2 5) (by simp) with h4334 | h4334
                                · linarith only [h3227, h4334, hlam]
                                · linarith only [h3238, h4334, hlam]
                              · linarith only [h3235, h4333, hlam]
                            · linarith only [h3229, h4332, hlam]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [h0, h3225, h3228, h3230, h3237, h3239, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3391_1, p4328_1]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [h3223, hc15, hlam, hphi, p4328_1, u1ehi0]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [hlam, p4328_0]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [h3233, h3237, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3391_1, p4328_1]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            rcases p4328_3 (m.d 0 5) (by simp) with h4343 | h4343
                            · linarith only [h3223, h4343, hlam]
                            · linarith only [h3229, h4343, hlam]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [h3234, h3236, h3237, h3239, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3391_1, p4328_1]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [h3227, hlam, p4328_1]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [h3233, hlam, p4328_1]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [hlam, p4328_0]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [h3239, h3389, hc34, hc45, hlam, hphi, p4328_1]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [h3239, hlam, p4328_0]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [h3229, hlam, p4328_1]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [h3235, hlam, p4328_1]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [h3238, hlam, p4328_0]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [hlam, p4328_0]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [h3389, hlam, p4328_0]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [h3230, hlam, p4328_1]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [h3236, hlam, p4328_1]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [h0, h3225, h3228, h3230, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p4328_1]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [h0, h3225, h3228, h3230, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4328_1]
                          · have p4328_0 := h4328c.1
                            have p4328_1 := h4328c.2.1
                            have p4328_2 := h4328c.2.2.1
                            have p4328_3 := h4328c.2.2.2
                            linarith only [hlam, p4328_0]
                        · linarith only [h4327, hlam, p4298_0]
                  · linarith only [h3232, h4322, hlam]
                · linarith only [h3226, h4321, hlam]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                rcases p4298_3 (m.d 0 4) (by simp) with h4365 | h4365
                · rcases p4298_3 (m.d 1 4) (by simp) with h4366 | h4366
                  · rcases p4298_3 (m.d 2 4) (by simp) with h4367 | h4367
                    · linarith only [h3239, h4367, hlam]
                    · linarith only [h3237, h4367, hlam]
                  · linarith only [h3234, h4366, hlam]
                · linarith only [h3228, h4365, hlam]
              · have p4298_0 := h4298c.1
                have p4298_1 := h4298c.2.1
                have p4298_2 := h4298c.2.2.1
                have p4298_3 := h4298c.2.2.2
                linarith only [hlam, p4298_0]
            · linarith only [h3237, h4294, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3391_1]
          · linarith only [h3239, h4293, hlam]
      · linarith only [h3237, h4290, hlam]
    · linarith only [h3232, h4289, hlam]
  · linarith only [h3226, h4288, hlam]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x24 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg3234 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg3235 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg3236 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h3237 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h3238 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h3239 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h3389 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h3391c : ((m.d 2 5) < (m.d 2 5) ∧ 2 * m.lam ≤ (m.d 2 5) - (m.d 2 5) ∧ (m.d 2 5) - (m.d 2 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 2 5) ∨ (m.d 2 5) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  have h3234 := hg3234
  have h3235 := hg3235
  have h3236 := hg3236
  have p3391_0 := h3391c.1
  have p3391_1 := h3391c.2.1
  have p3391_2 := h3391c.2.2.1
  have p3391_3 := h3391c.2.2.2
  linarith only [hlam, p3391_0]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg3234 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg3235 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg3236 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h3237 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h3238 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h3239 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h3389 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  have h3234 := hg3234
  have h3235 := hg3235
  have h3236 := hg3236
  rcases h2bigk with h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c | h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x2 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x3 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x4 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x5 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x6 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x7 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x8 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x9 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x10 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x11 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x12 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x13 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x14 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x15 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x16 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x17 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x18 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x19 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x20 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x21 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x22 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x23 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x24 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389 h3391c

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg3234 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg3235 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg3236 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h3237 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h3238 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h3239 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  have h3234 := hg3234
  have h3235 := hg3235
  have h3236 := hg3236
  rcases m.htr 3 4 5 (by decide) (by decide) with h3389 | h3389
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239 h3389

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg3234 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg3235 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg3236 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h3237 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h3238 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  have h3234 := hg3234
  have h3235 := hg3235
  have h3236 := hg3236
  rcases m.htr 2 4 5 (by decide) (by decide) with h3239 | h3239
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238 h3239

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg3234 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg3235 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg3236 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h3237 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h3238 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  have h3234 := hg3234
  have h3235 := hg3235
  have h3236 := hg3236
  rcases m.htr 2 4 5 (by decide) (by decide) with h4379 | h4379
  · linarith only [h3237, h3238, h4379, hlam]
  · rcases m.htr 3 4 5 (by decide) (by decide) with h4381 | h4381
    · linarith only [h0, h3225, h3229, h3237, h3238, h4379, h4381, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
    · rcases h2bigk with h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [hlam, p4383_0]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [h0, hlam, p4383_0]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        rcases p4383_3 (m.d 0 2) (by simp) with h4386 | h4386
        · rcases p4383_3 (m.d 1 2) (by simp) with h4387 | h4387
          · rcases p4383_3 (m.d 2 3) (by simp) with h4388 | h4388
            · linarith only [h4388, hlam, p4383_0]
            · rcases p4383_3 (m.d 2 4) (by simp) with h4390 | h4390
              · linarith only [h3226, h4390, hlam]
              · rcases p4383_3 (m.d 2 5) (by simp) with h4392 | h4392
                · linarith only [h3227, h4392, hlam]
                · linarith only [h3238, h4392, hlam]
          · linarith only [h3231, h4387, hlam]
        · linarith only [h4386, hlam, p4383_0]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        rcases p4383_3 (m.d 0 2) (by simp) with h4397 | h4397
        · rcases p4383_3 (m.d 1 2) (by simp) with h4398 | h4398
          · rcases p4383_3 (m.d 2 3) (by simp) with h4399 | h4399
            · linarith only [h3225, h4399, hlam]
            · linarith only [h3237, h4399, hlam]
          · linarith only [h3232, h4398, hlam]
        · linarith only [h4397, hlam, p4383_0]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        rcases p4383_3 (m.d 0 2) (by simp) with h4404 | h4404
        · rcases p4383_3 (m.d 1 2) (by simp) with h4405 | h4405
          · rcases p4383_3 (m.d 2 3) (by simp) with h4406 | h4406
            · linarith only [h3225, h4406, hlam]
            · rcases p4383_3 (m.d 2 4) (by simp) with h4408 | h4408
              · linarith only [h3226, h4408, hlam]
              · rcases p4383_3 (m.d 2 5) (by simp) with h4410 | h4410
                · linarith only [h4410, hlam, p4383_0]
                · rcases h2emax with h4412 | h4412 | h4412 | h4412 | h4412
                  · linarith only [h3225, h3228, h3230, h3238, h4381, h4412, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h0, h3225, h3228, h3230, h3238, h4381, h4412, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases h4bigk with h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [hlam, p4415_0]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [h3221, hlam, p4415_1]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      rcases p4415_3 (m.d 0 4) (by simp) with h4418 | h4418
                      · rcases p4415_3 (m.d 1 4) (by simp) with h4419 | h4419
                        · rcases p4415_3 (m.d 2 4) (by simp) with h4420 | h4420
                          · linarith only [h3226, h4420, hlam]
                          · rcases p4415_3 (m.d 3 4) (by simp) with h4422 | h4422
                            · linarith only [h3228, h4422, hlam]
                            · rcases p4415_3 (m.d 4 5) (by simp) with h4424 | h4424
                              · linarith only [h3230, h4424, hlam]
                              · linarith only [h4379, h4424, hlam]
                        · linarith only [h3232, h4419, hlam]
                      · linarith only [h3226, h4418, hlam]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [h3230, h3237, h3238, h4381, hlam, p4415_2]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [h3225, h3228, h3237, h3238, h4381, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4415_1]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p4415_1, u1ehi0]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [hlam, p4415_0]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      rcases p4415_3 (m.d 0 4) (by simp) with h4433 | h4433
                      · linarith only [h3221, h4433, hlam]
                      · linarith only [h3226, h4433, hlam]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [h3221, h3230, h3237, h3238, h4381, hlam, p4415_2]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [h3237, h3238, h4381, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4415_1]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [h3226, hlam, p4415_0]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [h3232, hlam, p4415_0]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [hlam, p4415_0]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [h3237, h3238, h4381, hc34, hc45, hlam, hphi, p4415_1]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [h4379, hlam, p4415_0]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [h3228, hlam, p4415_0]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [h3234, hlam, p4415_0]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [h3237, hlam, p4415_0]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [hlam, p4415_0]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [h4381, hlam, p4415_0]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [h3230, hlam, p4415_0]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [h3236, hlam, p4415_0]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      rcases p4415_3 (m.d 0 4) (by simp) with h4450 | h4450
                      · rcases p4415_3 (m.d 1 4) (by simp) with h4451 | h4451
                        · rcases p4415_3 (m.d 2 4) (by simp) with h4452 | h4452
                          · linarith only [h4452, hlam, p4415_0]
                          · rcases p4415_3 (m.d 3 4) (by simp) with h4454 | h4454
                            · linarith only [h4381, h4454, hlam]
                            · rcases p4415_3 (m.d 4 5) (by simp) with h4456 | h4456
                              · rcases h5bigk with h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [hlam, p4457_0]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h3223, hlam, p4457_1]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h3225, h3228, h3230, hlam, p4383_2, p4457_1]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h0, h3225, h3228, h3230, h3238, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4457_1]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h0, h3225, h3228, h3230, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4415_1, p4457_1]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h3223, h3231, h3234, h3236, hc12, hlam, hphi, p4457_1, u1ehi0]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [hlam, p4457_0]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h3231, h3234, h3236, h3237, h3238, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4457_1]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h3231, h3234, h3236, h3237, h3238, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4457_1]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h3231, h3234, h3236, h3237, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4415_1, p4457_1]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h3227, hlam, p4457_1]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h3233, hlam, p4457_1]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [hlam, p4457_0]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h3238, hlam, p4457_1]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h4379, hlam, p4457_0]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h3229, hlam, p4457_1]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h3235, hlam, p4457_1]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h3225, h3229, hlam, p4383_2, p4457_1]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [hlam, p4457_0]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h4381, hlam, p4457_0]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h3230, hlam, p4457_1]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h3236, hlam, p4457_1]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h3230, h3237, h3238, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p4457_1]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [h0, h3225, h3228, h3230, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4457_1]
                                · have p4457_0 := h4457c.1
                                  have p4457_1 := h4457c.2.1
                                  have p4457_2 := h4457c.2.2.1
                                  have p4457_3 := h4457c.2.2.2
                                  linarith only [hlam, p4457_0]
                              · linarith only [h4456, hlam, p4415_0]
                        · linarith only [h3232, h4451, hlam]
                      · linarith only [h3226, h4450, hlam]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      rcases p4415_3 (m.d 0 4) (by simp) with h4486 | h4486
                      · rcases p4415_3 (m.d 1 4) (by simp) with h4487 | h4487
                        · rcases p4415_3 (m.d 2 4) (by simp) with h4488 | h4488
                          · linarith only [h4379, h4488, hlam]
                          · linarith only [h3237, h4488, hlam]
                        · linarith only [h3234, h4487, hlam]
                      · linarith only [h3228, h4486, hlam]
                    · have p4415_0 := h4415c.1
                      have p4415_1 := h4415c.2.1
                      have p4415_2 := h4415c.2.2.1
                      have p4415_3 := h4415c.2.2.2
                      linarith only [hlam, p4415_0]
                  · rcases h4bigk with h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c | h4494c
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [hlam, p4494_0]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [h3221, hlam, p4494_1]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      rcases p4494_3 (m.d 0 4) (by simp) with h4497 | h4497
                      · rcases p4494_3 (m.d 1 4) (by simp) with h4498 | h4498
                        · rcases p4494_3 (m.d 2 4) (by simp) with h4499 | h4499
                          · linarith only [h3226, h4499, hlam]
                          · rcases p4494_3 (m.d 3 4) (by simp) with h4501 | h4501
                            · linarith only [h3228, h4501, hlam]
                            · rcases p4494_3 (m.d 4 5) (by simp) with h4503 | h4503
                              · linarith only [h3230, h4503, hlam]
                              · linarith only [h4379, h4503, hlam]
                        · linarith only [h3232, h4498, hlam]
                      · linarith only [h3226, h4497, hlam]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [h3230, h3237, h3238, h4381, hlam, p4494_2]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [h3237, h3238, h4381, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p4494_1]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p4494_1, u1ehi0]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [hlam, p4494_0]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      rcases p4494_3 (m.d 0 4) (by simp) with h4512 | h4512
                      · linarith only [h3221, h4512, hlam]
                      · linarith only [h3226, h4512, hlam]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [h3221, h3230, h3237, h3238, h4381, hlam, p4494_2]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [h3237, h3238, h4381, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4494_1]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [h3226, hlam, p4494_0]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [h3232, hlam, p4494_0]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [hlam, p4494_0]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [h3230, h3237, h3238, h4381, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p4494_1]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [h4379, hlam, p4494_0]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [h3228, hlam, p4494_0]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [h3234, hlam, p4494_0]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [h3237, hlam, p4494_0]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [hlam, p4494_0]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [h4381, hlam, p4494_0]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [h3230, hlam, p4494_0]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [h3236, hlam, p4494_0]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      rcases p4494_3 (m.d 0 4) (by simp) with h4529 | h4529
                      · rcases p4494_3 (m.d 1 4) (by simp) with h4530 | h4530
                        · rcases p4494_3 (m.d 2 4) (by simp) with h4531 | h4531
                          · linarith only [h4531, hlam, p4494_0]
                          · rcases p4494_3 (m.d 3 4) (by simp) with h4533 | h4533
                            · linarith only [h4381, h4533, hlam]
                            · rcases p4494_3 (m.d 4 5) (by simp) with h4535 | h4535
                              · rcases h5bigk with h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c | h4536c
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [hlam, p4536_0]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h3223, hlam, p4536_1]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h3227, hlam, p4383_2, p4536_1]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h3223, h3231, h3234, h3236, h3238, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4536_1]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h3223, h3231, h3234, h3236, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4494_1, p4536_1]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h3223, h3231, h3234, h3236, hc12, hlam, hphi, p4536_1, u1ehi0]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [hlam, p4536_0]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h3231, h3234, h3236, h3237, h3238, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4536_1]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h3231, h3234, h3236, h3237, h3238, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4536_1]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h3231, h3234, h3236, h3237, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4494_1, p4536_1]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h3227, hlam, p4536_1]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h3233, hlam, p4536_1]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [hlam, p4536_0]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h3238, hlam, p4536_1]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h4379, hlam, p4536_0]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h3229, hlam, p4536_1]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h3235, hlam, p4536_1]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h3237, h3238, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4536_1]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [hlam, p4536_0]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h4381, hlam, p4536_0]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h3230, hlam, p4536_1]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h3236, hlam, p4536_1]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h3225, h3228, h3230, h3237, h3238, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4536_1]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [h0, h3225, h3228, h3230, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4536_1]
                                · have p4536_0 := h4536c.1
                                  have p4536_1 := h4536c.2.1
                                  have p4536_2 := h4536c.2.2.1
                                  have p4536_3 := h4536c.2.2.2
                                  linarith only [hlam, p4536_0]
                              · linarith only [h4535, hlam, p4494_0]
                        · linarith only [h3232, h4530, hlam]
                      · linarith only [h3226, h4529, hlam]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      rcases p4494_3 (m.d 0 4) (by simp) with h4565 | h4565
                      · rcases p4494_3 (m.d 1 4) (by simp) with h4566 | h4566
                        · rcases p4494_3 (m.d 2 4) (by simp) with h4567 | h4567
                          · linarith only [h4379, h4567, hlam]
                          · linarith only [h3237, h4567, hlam]
                        · linarith only [h3234, h4566, hlam]
                      · linarith only [h3228, h4565, hlam]
                    · have p4494_0 := h4494c.1
                      have p4494_1 := h4494c.2.1
                      have p4494_2 := h4494c.2.2.1
                      have p4494_3 := h4494c.2.2.2
                      linarith only [hlam, p4494_0]
                  · rcases h4bigk with h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [hlam, p4573_0]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [h3221, hlam, p4573_1]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      rcases p4573_3 (m.d 0 4) (by simp) with h4576 | h4576
                      · rcases p4573_3 (m.d 1 4) (by simp) with h4577 | h4577
                        · rcases p4573_3 (m.d 2 4) (by simp) with h4578 | h4578
                          · linarith only [h3226, h4578, hlam]
                          · rcases p4573_3 (m.d 3 4) (by simp) with h4580 | h4580
                            · linarith only [h3228, h4580, hlam]
                            · rcases p4573_3 (m.d 4 5) (by simp) with h4582 | h4582
                              · linarith only [h3230, h4582, hlam]
                              · linarith only [h4379, h4582, hlam]
                        · linarith only [h3232, h4577, hlam]
                      · linarith only [h3226, h4576, hlam]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [h3230, h3237, h3238, h4381, hlam, p4573_2]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [h3237, h3238, h4381, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p4573_1]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p4573_1, u1ehi0]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [hlam, p4573_0]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      rcases p4573_3 (m.d 0 4) (by simp) with h4591 | h4591
                      · linarith only [h3221, h4591, hlam]
                      · linarith only [h3226, h4591, hlam]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [h3221, h3230, h3237, h3238, h4381, hlam, p4573_2]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [h3237, h3238, h4381, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4573_1]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [h3226, hlam, p4573_0]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [h3232, hlam, p4573_0]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [hlam, p4573_0]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [h3230, h3237, h3238, h4381, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p4573_1]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [h4379, hlam, p4573_0]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [h3228, hlam, p4573_0]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [h3234, hlam, p4573_0]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [h3237, hlam, p4573_0]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [hlam, p4573_0]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [h4381, hlam, p4573_0]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [h3230, hlam, p4573_0]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [h3236, hlam, p4573_0]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      rcases p4573_3 (m.d 0 4) (by simp) with h4608 | h4608
                      · rcases p4573_3 (m.d 1 4) (by simp) with h4609 | h4609
                        · rcases p4573_3 (m.d 2 4) (by simp) with h4610 | h4610
                          · linarith only [h4610, hlam, p4573_0]
                          · rcases p4573_3 (m.d 3 4) (by simp) with h4612 | h4612
                            · linarith only [h4381, h4612, hlam]
                            · rcases p4573_3 (m.d 4 5) (by simp) with h4614 | h4614
                              · rcases h5bigk with h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c | h4615c
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [hlam, p4615_0]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h3223, hlam, p4615_1]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h3227, hlam, p4383_2, p4615_1]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h3223, h3231, h3234, h3236, h3238, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4615_1]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h3223, h3231, h3234, h3236, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4573_1, p4615_1]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h3223, h3231, h3234, h3236, hc12, hlam, hphi, p4615_1, u1ehi0]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [hlam, p4615_0]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h3231, h3234, h3236, h3237, h3238, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4615_1]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h3231, h3234, h3236, h3237, h3238, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4615_1]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h3231, h3234, h3236, h3237, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4573_1, p4615_1]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h3227, hlam, p4615_1]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h3233, hlam, p4615_1]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [hlam, p4615_0]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h3238, hlam, p4615_1]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h4379, hlam, p4615_0]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h3229, hlam, p4615_1]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h3235, hlam, p4615_1]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h3237, h3238, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4615_1]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [hlam, p4615_0]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h4381, hlam, p4615_0]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h3230, hlam, p4615_1]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h3236, hlam, p4615_1]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h3225, h3228, h3230, h3237, h3238, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4615_1]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [h0, h3225, h3228, h3230, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4615_1]
                                · have p4615_0 := h4615c.1
                                  have p4615_1 := h4615c.2.1
                                  have p4615_2 := h4615c.2.2.1
                                  have p4615_3 := h4615c.2.2.2
                                  linarith only [hlam, p4615_0]
                              · linarith only [h4614, hlam, p4573_0]
                        · linarith only [h3232, h4609, hlam]
                      · linarith only [h3226, h4608, hlam]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      rcases p4573_3 (m.d 0 4) (by simp) with h4644 | h4644
                      · rcases p4573_3 (m.d 1 4) (by simp) with h4645 | h4645
                        · rcases p4573_3 (m.d 2 4) (by simp) with h4646 | h4646
                          · linarith only [h4379, h4646, hlam]
                          · linarith only [h3237, h4646, hlam]
                        · linarith only [h3234, h4645, hlam]
                      · linarith only [h3228, h4644, hlam]
                    · have p4573_0 := h4573c.1
                      have p4573_1 := h4573c.2.1
                      have p4573_2 := h4573c.2.2.1
                      have p4573_3 := h4573c.2.2.2
                      linarith only [hlam, p4573_0]
          · linarith only [h3233, h4405, hlam]
        · linarith only [h4404, hlam, p4383_0]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [h0, hc12, hlam, hphi, p4383_1, u1ehi0]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [hlam, p4383_0]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        rcases p4383_3 (m.d 0 2) (by simp) with h4656 | h4656
        · linarith only [h0, h4656, hlam]
        · linarith only [h3225, h4656, hlam]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        rcases p4383_3 (m.d 0 2) (by simp) with h4659 | h4659
        · linarith only [h0, h4659, hlam]
        · linarith only [h3226, h4659, hlam]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        rcases p4383_3 (m.d 0 2) (by simp) with h4662 | h4662
        · linarith only [h0, h4662, hlam]
        · linarith only [h3227, h4662, hlam]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [h3225, hlam, p4383_0]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [h3231, hlam, p4383_0]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [hlam, p4383_0]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [h3225, h3228, h3230, h3238, h4381, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p4383_1]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [h3238, hlam, p4383_1]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [h3226, hlam, p4383_0]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [h3232, hlam, p4383_0]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [h3237, hlam, p4383_0]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [hlam, p4383_0]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [h4379, hlam, p4383_0]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [h3227, hlam, p4383_0]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [h3233, hlam, p4383_0]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [h0, h3227, h3237, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4383_1]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        rcases p4383_3 (m.d 0 2) (by simp) with h4678 | h4678
        · rcases p4383_3 (m.d 1 2) (by simp) with h4679 | h4679
          · rcases p4383_3 (m.d 2 3) (by simp) with h4680 | h4680
            · linarith only [h3238, h4680, hlam]
            · linarith only [h3237, h4680, hlam]
          · linarith only [h3232, h4679, hlam]
        · linarith only [h3226, h4678, hlam]
      · have p4383_0 := h4383c.1
        have p4383_1 := h4383c.2.1
        have p4383_2 := h4383c.2.2.1
        have p4383_3 := h4383c.2.2.2
        linarith only [hlam, p4383_0]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg3234 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg3235 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg3236 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h3237 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  have h3234 := hg3234
  have h3235 := hg3235
  have h3236 := hg3236
  rcases m.htr 2 3 5 (by decide) (by decide) with h3238 | h3238
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h3238

end R2N4
