import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x4 (m : N7Model)
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
    (h3391c : ((m.d 0 2) < (m.d 2 5) ∧ 2 * m.lam ≤ (m.d 2 5) - (m.d 0 2) ∧ (m.d 2 5) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 0 2) ∨ (m.d 2 5) ≤ z)))
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
  rcases p3391_3 (m.d 0 2) (by simp) with h3906 | h3906
  · rcases p3391_3 (m.d 1 2) (by simp) with h3907 | h3907
    · rcases p3391_3 (m.d 2 3) (by simp) with h3908 | h3908
      · linarith only [h3225, h3908, hlam]
      · linarith only [h3238, h3908, hlam]
    · linarith only [h3233, h3907, hlam]
  · linarith only [h3906, hlam, p3391_0]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x5 (m : N7Model)
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
    (h3391c : ((m.d 1 2) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 1 2) ∧ (m.d 0 2) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 1 2) ∨ (m.d 0 2) ≤ z)))
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
  linarith only [h0, hc12, hlam, hphi, p3391_1, u1ehi0]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x6 (m : N7Model)
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
    (h3391c : ((m.d 1 2) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 2) ∧ (m.d 1 2) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 1 2) ∨ (m.d 1 2) ≤ z)))
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
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x7 (m : N7Model)
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
    (h3391c : ((m.d 1 2) < (m.d 2 3) ∧ 2 * m.lam ≤ (m.d 2 3) - (m.d 1 2) ∧ (m.d 2 3) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 1 2) ∨ (m.d 2 3) ≤ z)))
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
  rcases p3391_3 (m.d 0 2) (by simp) with h3915 | h3915
  · linarith only [h0, h3915, hlam]
  · linarith only [h3225, h3915, hlam]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x8 (m : N7Model)
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
    (h3391c : ((m.d 1 2) < (m.d 2 4) ∧ 2 * m.lam ≤ (m.d 2 4) - (m.d 1 2) ∧ (m.d 2 4) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 1 2) ∨ (m.d 2 4) ≤ z)))
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
  rcases p3391_3 (m.d 0 2) (by simp) with h3918 | h3918
  · linarith only [h0, h3918, hlam]
  · linarith only [h3226, h3918, hlam]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x9 (m : N7Model)
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
    (h3391c : ((m.d 1 2) < (m.d 2 5) ∧ 2 * m.lam ≤ (m.d 2 5) - (m.d 1 2) ∧ (m.d 2 5) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 1 2) ∨ (m.d 2 5) ≤ z)))
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
  rcases p3391_3 (m.d 0 2) (by simp) with h3921 | h3921
  · linarith only [h0, h3921, hlam]
  · linarith only [h3227, h3921, hlam]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x10 (m : N7Model)
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
    (h3391c : ((m.d 2 3) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 2 3) ∧ (m.d 0 2) - (m.d 2 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 2 3) ∨ (m.d 0 2) ≤ z)))
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
  linarith only [h3225, hlam, p3391_0]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x11 (m : N7Model)
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
    (h3391c : ((m.d 2 3) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 2 3) ∧ (m.d 1 2) - (m.d 2 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 2 3) ∨ (m.d 1 2) ≤ z)))
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
  linarith only [h3231, hlam, p3391_0]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x12 (m : N7Model)
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
    (h3391c : ((m.d 2 3) < (m.d 2 3) ∧ 2 * m.lam ≤ (m.d 2 3) - (m.d 2 3) ∧ (m.d 2 3) - (m.d 2 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 2 3) ∨ (m.d 2 3) ≤ z)))
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
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x13 (m : N7Model)
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
    (h3391c : ((m.d 2 3) < (m.d 2 4) ∧ 2 * m.lam ≤ (m.d 2 4) - (m.d 2 3) ∧ (m.d 2 4) - (m.d 2 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 2 3) ∨ (m.d 2 4) ≤ z)))
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
  rcases p3391_3 (m.d 0 2) (by simp) with h3927 | h3927
  · rcases p3391_3 (m.d 1 2) (by simp) with h3928 | h3928
    · rcases p3391_3 (m.d 2 3) (by simp) with h3929 | h3929
      · rcases p3391_3 (m.d 2 4) (by simp) with h3930 | h3930
        · linarith only [h3237, h3930, hlam]
        · rcases p3391_3 (m.d 2 5) (by simp) with h3932 | h3932
          · linarith only [h3238, h3932, hlam]
          · linarith only [h3239, h3932, hlam]
      · linarith only [h3237, h3929, hlam]
    · linarith only [h3232, h3928, hlam]
  · linarith only [h3226, h3927, hlam]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x14 (m : N7Model)
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
    (h3391c : ((m.d 2 3) < (m.d 2 5) ∧ 2 * m.lam ≤ (m.d 2 5) - (m.d 2 3) ∧ (m.d 2 5) - (m.d 2 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 2 3) ∨ (m.d 2 5) ≤ z)))
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
  rcases p3391_3 (m.d 0 2) (by simp) with h3938 | h3938
  · rcases p3391_3 (m.d 1 2) (by simp) with h3939 | h3939
    · rcases p3391_3 (m.d 2 3) (by simp) with h3940 | h3940
      · rcases p3391_3 (m.d 2 4) (by simp) with h3941 | h3941
        · linarith only [h3237, h3941, hlam]
        · rcases p3391_3 (m.d 2 5) (by simp) with h3943 | h3943
          · linarith only [h3238, h3943, hlam]
          · rcases h2emax with h3945 | h3945 | h3945 | h3945 | h3945
            · linarith only [h3225, h3239, h3945, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3391_1]
            · linarith only [h3945, hlam, ht12, u1ehi1]
            · linarith only [h3237, h3239, h3945, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3391_1]
            · rcases h4bigk with h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                linarith only [hlam, p3949_0]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                linarith only [h3221, hlam, p3949_1]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                rcases p3949_3 (m.d 0 4) (by simp) with h3952 | h3952
                · rcases p3949_3 (m.d 1 4) (by simp) with h3953 | h3953
                  · rcases p3949_3 (m.d 2 4) (by simp) with h3954 | h3954
                    · linarith only [h3226, h3954, hlam]
                    · rcases p3949_3 (m.d 3 4) (by simp) with h3956 | h3956
                      · linarith only [h3228, h3956, hlam]
                      · rcases p3949_3 (m.d 4 5) (by simp) with h3958 | h3958
                        · linarith only [h3230, h3958, hlam]
                        · linarith only [h3239, h3958, hlam]
                  · linarith only [h3232, h3953, hlam]
                · linarith only [h3226, h3952, hlam]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                rcases p3949_3 (m.d 0 4) (by simp) with h3963 | h3963
                · rcases p3949_3 (m.d 1 4) (by simp) with h3964 | h3964
                  · rcases p3949_3 (m.d 2 4) (by simp) with h3965 | h3965
                    · linarith only [h3226, h3965, hlam]
                    · linarith only [h3237, h3965, hlam]
                  · linarith only [h3234, h3964, hlam]
                · linarith only [h3228, h3963, hlam]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                rcases p3949_3 (m.d 0 4) (by simp) with h3970 | h3970
                · rcases p3949_3 (m.d 1 4) (by simp) with h3971 | h3971
                  · rcases p3949_3 (m.d 2 4) (by simp) with h3972 | h3972
                    · linarith only [h3226, h3972, hlam]
                    · rcases p3949_3 (m.d 3 4) (by simp) with h3974 | h3974
                      · linarith only [h3228, h3974, hlam]
                      · rcases p3949_3 (m.d 4 5) (by simp) with h3976 | h3976
                        · linarith only [h3976, hlam, p3949_0]
                        · rcases h5bigk with h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c | h3978c
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [hlam, p3978_0]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [h3223, hlam, p3978_1]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            rcases p3978_3 (m.d 0 5) (by simp) with h3981 | h3981
                            · rcases p3978_3 (m.d 1 5) (by simp) with h3982 | h3982
                              · rcases p3978_3 (m.d 2 5) (by simp) with h3983 | h3983
                                · linarith only [h3227, h3983, hlam]
                                · rcases p3978_3 (m.d 3 5) (by simp) with h3985 | h3985
                                  · linarith only [h3229, h3985, hlam]
                                  · rcases p3978_3 (m.d 4 5) (by simp) with h3987 | h3987
                                    · linarith only [h3230, h3987, hlam]
                                    · linarith only [h3239, h3987, hlam]
                              · linarith only [h3233, h3982, hlam]
                            · linarith only [h3227, h3981, hlam]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            rcases p3978_3 (m.d 0 5) (by simp) with h3992 | h3992
                            · rcases p3978_3 (m.d 1 5) (by simp) with h3993 | h3993
                              · rcases p3978_3 (m.d 2 5) (by simp) with h3994 | h3994
                                · linarith only [h3227, h3994, hlam]
                                · linarith only [h3238, h3994, hlam]
                              · linarith only [h3235, h3993, hlam]
                            · linarith only [h3229, h3992, hlam]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [h3225, h3228, h3230, h3237, h3239, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3978_1]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [h3223, hc15, hlam, hphi, p3978_1, u1ehi0]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [hlam, p3978_0]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            rcases p3978_3 (m.d 0 5) (by simp) with h4002 | h4002
                            · linarith only [h3223, h4002, hlam]
                            · linarith only [h3227, h4002, hlam]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            rcases p3978_3 (m.d 0 5) (by simp) with h4005 | h4005
                            · linarith only [h3223, h4005, hlam]
                            · linarith only [h3229, h4005, hlam]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [h3236, h3237, h3239, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3978_1]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [h3227, hlam, p3978_1]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [h3233, hlam, p3978_1]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [hlam, p3978_0]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [h3389, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3391_1, p3978_1]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [h3239, hlam, p3978_0]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [h3229, hlam, p3978_1]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [h3235, hlam, p3978_1]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [h3238, hlam, p3978_0]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [hlam, p3978_0]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [h3389, hlam, p3978_0]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [h3230, hlam, p3978_1]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [h3236, hlam, p3978_1]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [h0, h3225, h3228, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3949_1, p3978_1]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [h0, h3225, h3228, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3949_1, p3978_1]
                          · have p3978_0 := h3978c.1
                            have p3978_1 := h3978c.2.1
                            have p3978_2 := h3978c.2.2.1
                            have p3978_3 := h3978c.2.2.2
                            linarith only [hlam, p3978_0]
                  · linarith only [h3236, h3971, hlam]
                · linarith only [h3970, hlam, p3949_0]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p3949_1, u1ehi0]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                linarith only [hlam, p3949_0]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                rcases p3949_3 (m.d 0 4) (by simp) with h4028 | h4028
                · linarith only [h3221, h4028, hlam]
                · linarith only [h3226, h4028, hlam]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                rcases p3949_3 (m.d 0 4) (by simp) with h4031 | h4031
                · linarith only [h3221, h4031, hlam]
                · linarith only [h3228, h4031, hlam]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                rcases p3949_3 (m.d 0 4) (by simp) with h4034 | h4034
                · linarith only [h3221, h4034, hlam]
                · linarith only [h3230, h4034, hlam]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                linarith only [h3226, hlam, p3949_0]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                linarith only [h3232, hlam, p3949_0]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                linarith only [hlam, p3949_0]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                linarith only [h0, h3225, h3239, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3391_1, p3949_1]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                linarith only [h3239, hlam, p3949_0]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                linarith only [h3228, hlam, p3949_0]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                linarith only [h3234, hlam, p3949_0]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                linarith only [h3237, hlam, p3949_0]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                linarith only [hlam, p3949_0]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                linarith only [h3389, hlam, p3949_0]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                linarith only [h3230, hlam, p3949_0]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                linarith only [h3236, hlam, p3949_0]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                rcases p3949_3 (m.d 0 4) (by simp) with h4049 | h4049
                · rcases p3949_3 (m.d 1 4) (by simp) with h4050 | h4050
                  · rcases p3949_3 (m.d 2 4) (by simp) with h4051 | h4051
                    · linarith only [h4051, hlam, p3949_0]
                    · rcases p3949_3 (m.d 3 4) (by simp) with h4053 | h4053
                      · linarith only [h3389, h4053, hlam]
                      · rcases p3949_3 (m.d 4 5) (by simp) with h4055 | h4055
                        · rcases h5bigk with h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c | h4056c
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [hlam, p4056_0]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [h3223, hlam, p4056_1]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            rcases p4056_3 (m.d 0 5) (by simp) with h4059 | h4059
                            · rcases p4056_3 (m.d 1 5) (by simp) with h4060 | h4060
                              · rcases p4056_3 (m.d 2 5) (by simp) with h4061 | h4061
                                · linarith only [h3227, h4061, hlam]
                                · rcases p4056_3 (m.d 3 5) (by simp) with h4063 | h4063
                                  · linarith only [h3229, h4063, hlam]
                                  · rcases p4056_3 (m.d 4 5) (by simp) with h4065 | h4065
                                    · linarith only [h3230, h4065, hlam]
                                    · linarith only [h3239, h4065, hlam]
                              · linarith only [h3233, h4060, hlam]
                            · linarith only [h3227, h4059, hlam]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            rcases p4056_3 (m.d 0 5) (by simp) with h4070 | h4070
                            · rcases p4056_3 (m.d 1 5) (by simp) with h4071 | h4071
                              · rcases p4056_3 (m.d 2 5) (by simp) with h4072 | h4072
                                · linarith only [h3227, h4072, hlam]
                                · linarith only [h3238, h4072, hlam]
                              · linarith only [h3235, h4071, hlam]
                            · linarith only [h3229, h4070, hlam]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [h3223, h3231, h3234, h3236, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3949_1, p4056_1]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [h3223, h3231, h3234, h3236, hc12, hlam, hphi, p4056_1, u1ehi0]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [hlam, p4056_0]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            rcases p4056_3 (m.d 0 5) (by simp) with h4080 | h4080
                            · linarith only [h3223, h4080, hlam]
                            · linarith only [h3227, h4080, hlam]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            rcases p4056_3 (m.d 0 5) (by simp) with h4083 | h4083
                            · linarith only [h3223, h4083, hlam]
                            · linarith only [h3229, h4083, hlam]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [h3231, h3234, h3236, h3237, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3949_1, p4056_1]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [h3227, hlam, p4056_1]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [h3233, hlam, p4056_1]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [hlam, p4056_0]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [h0, h3227, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4056_1]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [h3239, hlam, p4056_0]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [h3229, hlam, p4056_1]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [h3235, hlam, p4056_1]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [h3238, hlam, p4056_0]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [hlam, p4056_0]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [h3389, hlam, p4056_0]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [h3230, hlam, p4056_1]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [h3236, hlam, p4056_1]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [h0, h3225, h3228, h3230, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p4056_1]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [h0, h3225, h3228, h3230, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4056_1]
                          · have p4056_0 := h4056c.1
                            have p4056_1 := h4056c.2.1
                            have p4056_2 := h4056c.2.2.1
                            have p4056_3 := h4056c.2.2.2
                            linarith only [hlam, p4056_0]
                        · linarith only [h4055, hlam, p3949_0]
                  · linarith only [h3232, h4050, hlam]
                · linarith only [h3226, h4049, hlam]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                rcases p3949_3 (m.d 0 4) (by simp) with h4105 | h4105
                · rcases p3949_3 (m.d 1 4) (by simp) with h4106 | h4106
                  · rcases p3949_3 (m.d 2 4) (by simp) with h4107 | h4107
                    · linarith only [h3239, h4107, hlam]
                    · linarith only [h3237, h4107, hlam]
                  · linarith only [h3234, h4106, hlam]
                · linarith only [h3228, h4105, hlam]
              · have p3949_0 := h3949c.1
                have p3949_1 := h3949c.2.1
                have p3949_2 := h3949c.2.2.1
                have p3949_3 := h3949c.2.2.2
                linarith only [hlam, p3949_0]
            · rcases h4bigk with h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c | h4113c
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                linarith only [hlam, p4113_0]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                linarith only [h3221, hlam, p4113_1]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                rcases p4113_3 (m.d 0 4) (by simp) with h4116 | h4116
                · rcases p4113_3 (m.d 1 4) (by simp) with h4117 | h4117
                  · rcases p4113_3 (m.d 2 4) (by simp) with h4118 | h4118
                    · linarith only [h3226, h4118, hlam]
                    · rcases p4113_3 (m.d 3 4) (by simp) with h4120 | h4120
                      · linarith only [h3228, h4120, hlam]
                      · rcases p4113_3 (m.d 4 5) (by simp) with h4122 | h4122
                        · linarith only [h3230, h4122, hlam]
                        · linarith only [h3239, h4122, hlam]
                  · linarith only [h3232, h4117, hlam]
                · linarith only [h3226, h4116, hlam]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                rcases p4113_3 (m.d 0 4) (by simp) with h4127 | h4127
                · rcases p4113_3 (m.d 1 4) (by simp) with h4128 | h4128
                  · rcases p4113_3 (m.d 2 4) (by simp) with h4129 | h4129
                    · linarith only [h3226, h4129, hlam]
                    · linarith only [h3237, h4129, hlam]
                  · linarith only [h3234, h4128, hlam]
                · linarith only [h3228, h4127, hlam]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                rcases p4113_3 (m.d 0 4) (by simp) with h4134 | h4134
                · rcases p4113_3 (m.d 1 4) (by simp) with h4135 | h4135
                  · rcases p4113_3 (m.d 2 4) (by simp) with h4136 | h4136
                    · linarith only [h3226, h4136, hlam]
                    · rcases p4113_3 (m.d 3 4) (by simp) with h4138 | h4138
                      · linarith only [h3228, h4138, hlam]
                      · rcases p4113_3 (m.d 4 5) (by simp) with h4140 | h4140
                        · linarith only [h4140, hlam, p4113_0]
                        · rcases h5bigk with h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c | h4142c
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [hlam, p4142_0]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [h3223, hlam, p4142_1]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            rcases p4142_3 (m.d 0 5) (by simp) with h4145 | h4145
                            · rcases p4142_3 (m.d 1 5) (by simp) with h4146 | h4146
                              · rcases p4142_3 (m.d 2 5) (by simp) with h4147 | h4147
                                · linarith only [h3227, h4147, hlam]
                                · rcases p4142_3 (m.d 3 5) (by simp) with h4149 | h4149
                                  · linarith only [h3229, h4149, hlam]
                                  · rcases p4142_3 (m.d 4 5) (by simp) with h4151 | h4151
                                    · linarith only [h3230, h4151, hlam]
                                    · linarith only [h3239, h4151, hlam]
                              · linarith only [h3233, h4146, hlam]
                            · linarith only [h3227, h4145, hlam]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            rcases p4142_3 (m.d 0 5) (by simp) with h4156 | h4156
                            · rcases p4142_3 (m.d 1 5) (by simp) with h4157 | h4157
                              · rcases p4142_3 (m.d 2 5) (by simp) with h4158 | h4158
                                · linarith only [h3227, h4158, hlam]
                                · linarith only [h3238, h4158, hlam]
                              · linarith only [h3235, h4157, hlam]
                            · linarith only [h3229, h4156, hlam]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [h3230, hlam, p4113_2, p4142_1]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [h3223, h3231, h3234, h3236, hc12, hlam, hphi, p4142_1, u1ehi0]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [hlam, p4142_0]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            rcases p4142_3 (m.d 0 5) (by simp) with h4166 | h4166
                            · linarith only [h3223, h4166, hlam]
                            · linarith only [h3227, h4166, hlam]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            rcases p4142_3 (m.d 0 5) (by simp) with h4169 | h4169
                            · linarith only [h3223, h4169, hlam]
                            · linarith only [h3229, h4169, hlam]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [h3231, h3234, h3236, h3237, h3239, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4142_1]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [h3227, hlam, p4142_1]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [h3233, hlam, p4142_1]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [hlam, p4142_0]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [h0, h3227, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4142_1]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [h3239, hlam, p4142_0]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [h3229, hlam, p4142_1]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [h3235, hlam, p4142_1]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [h3238, hlam, p4142_0]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [hlam, p4142_0]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [h3389, hlam, p4142_0]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [h3230, hlam, p4142_1]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [h3236, hlam, p4142_1]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [h3221, h3231, h3234, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p4113_1, p4142_1]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [h3221, h3231, h3234, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4113_1, p4142_1]
                          · have p4142_0 := h4142c.1
                            have p4142_1 := h4142c.2.1
                            have p4142_2 := h4142c.2.2.1
                            have p4142_3 := h4142c.2.2.2
                            linarith only [hlam, p4142_0]
                  · linarith only [h3236, h4135, hlam]
                · linarith only [h4134, hlam, p4113_0]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p4113_1, u1ehi0]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                linarith only [hlam, p4113_0]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                rcases p4113_3 (m.d 0 4) (by simp) with h4192 | h4192
                · linarith only [h3221, h4192, hlam]
                · linarith only [h3226, h4192, hlam]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                rcases p4113_3 (m.d 0 4) (by simp) with h4195 | h4195
                · linarith only [h3221, h4195, hlam]
                · linarith only [h3228, h4195, hlam]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                rcases p4113_3 (m.d 0 4) (by simp) with h4198 | h4198
                · linarith only [h3221, h4198, hlam]
                · linarith only [h3230, h4198, hlam]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                linarith only [h3226, hlam, p4113_0]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                linarith only [h3232, hlam, p4113_0]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                linarith only [hlam, p4113_0]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                linarith only [h0, h3225, h3239, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3391_1, p4113_1]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                linarith only [h3239, hlam, p4113_0]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                linarith only [h3228, hlam, p4113_0]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                linarith only [h3234, hlam, p4113_0]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                linarith only [h3237, hlam, p4113_0]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                linarith only [hlam, p4113_0]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                linarith only [h3389, hlam, p4113_0]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                linarith only [h3230, hlam, p4113_0]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                linarith only [h3236, hlam, p4113_0]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                rcases p4113_3 (m.d 0 4) (by simp) with h4213 | h4213
                · rcases p4113_3 (m.d 1 4) (by simp) with h4214 | h4214
                  · rcases p4113_3 (m.d 2 4) (by simp) with h4215 | h4215
                    · linarith only [h4215, hlam, p4113_0]
                    · rcases p4113_3 (m.d 3 4) (by simp) with h4217 | h4217
                      · linarith only [h3389, h4217, hlam]
                      · rcases p4113_3 (m.d 4 5) (by simp) with h4219 | h4219
                        · rcases h5bigk with h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c | h4220c
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [hlam, p4220_0]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [h3223, hlam, p4220_1]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            rcases p4220_3 (m.d 0 5) (by simp) with h4223 | h4223
                            · rcases p4220_3 (m.d 1 5) (by simp) with h4224 | h4224
                              · rcases p4220_3 (m.d 2 5) (by simp) with h4225 | h4225
                                · linarith only [h3227, h4225, hlam]
                                · rcases p4220_3 (m.d 3 5) (by simp) with h4227 | h4227
                                  · linarith only [h3229, h4227, hlam]
                                  · rcases p4220_3 (m.d 4 5) (by simp) with h4229 | h4229
                                    · linarith only [h3230, h4229, hlam]
                                    · linarith only [h3239, h4229, hlam]
                              · linarith only [h3233, h4224, hlam]
                            · linarith only [h3227, h4223, hlam]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            rcases p4220_3 (m.d 0 5) (by simp) with h4234 | h4234
                            · rcases p4220_3 (m.d 1 5) (by simp) with h4235 | h4235
                              · rcases p4220_3 (m.d 2 5) (by simp) with h4236 | h4236
                                · linarith only [h3227, h4236, hlam]
                                · linarith only [h3238, h4236, hlam]
                              · linarith only [h3235, h4235, hlam]
                            · linarith only [h3229, h4234, hlam]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [h3223, h3231, h3234, h3236, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4113_1, p4220_1]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [h3223, h3231, h3234, h3236, hc12, hlam, hphi, p4220_1, u1ehi0]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [hlam, p4220_0]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            rcases p4220_3 (m.d 0 5) (by simp) with h4244 | h4244
                            · linarith only [h3223, h4244, hlam]
                            · linarith only [h3227, h4244, hlam]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            rcases p4220_3 (m.d 0 5) (by simp) with h4247 | h4247
                            · linarith only [h3223, h4247, hlam]
                            · linarith only [h3229, h4247, hlam]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [h3231, h3234, h3236, h3237, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4113_1, p4220_1]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [h3227, hlam, p4220_1]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [h3233, hlam, p4220_1]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [hlam, p4220_0]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [h0, h3227, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4220_1]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [h3239, hlam, p4220_0]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [h3229, hlam, p4220_1]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [h3235, hlam, p4220_1]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [h3238, hlam, p4220_0]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [hlam, p4220_0]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [h3389, hlam, p4220_0]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [h3230, hlam, p4220_1]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [h3236, hlam, p4220_1]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [h0, h3225, h3228, h3230, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p4220_1]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [h0, h3225, h3228, h3230, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4220_1]
                          · have p4220_0 := h4220c.1
                            have p4220_1 := h4220c.2.1
                            have p4220_2 := h4220c.2.2.1
                            have p4220_3 := h4220c.2.2.2
                            linarith only [hlam, p4220_0]
                        · linarith only [h4219, hlam, p4113_0]
                  · linarith only [h3232, h4214, hlam]
                · linarith only [h3226, h4213, hlam]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                rcases p4113_3 (m.d 0 4) (by simp) with h4269 | h4269
                · rcases p4113_3 (m.d 1 4) (by simp) with h4270 | h4270
                  · rcases p4113_3 (m.d 2 4) (by simp) with h4271 | h4271
                    · linarith only [h3239, h4271, hlam]
                    · linarith only [h3237, h4271, hlam]
                  · linarith only [h3234, h4270, hlam]
                · linarith only [h3228, h4269, hlam]
              · have p4113_0 := h4113c.1
                have p4113_1 := h4113c.2.1
                have p4113_2 := h4113c.2.2.1
                have p4113_3 := h4113c.2.2.2
                linarith only [hlam, p4113_0]
      · linarith only [h3238, h3940, hlam]
    · linarith only [h3233, h3939, hlam]
  · linarith only [h3227, h3938, hlam]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x15 (m : N7Model)
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
    (h3391c : ((m.d 2 4) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 2 4) ∧ (m.d 0 2) - (m.d 2 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 2 4) ∨ (m.d 0 2) ≤ z)))
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
  linarith only [h3226, hlam, p3391_0]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x16 (m : N7Model)
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
    (h3391c : ((m.d 2 4) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 2 4) ∧ (m.d 1 2) - (m.d 2 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 2 4) ∨ (m.d 1 2) ≤ z)))
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
  linarith only [h3232, hlam, p3391_0]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x17 (m : N7Model)
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
    (h3391c : ((m.d 2 4) < (m.d 2 3) ∧ 2 * m.lam ≤ (m.d 2 3) - (m.d 2 4) ∧ (m.d 2 3) - (m.d 2 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 2 4) ∨ (m.d 2 3) ≤ z)))
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
  linarith only [h3237, hlam, p3391_0]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x18 (m : N7Model)
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
    (h3391c : ((m.d 2 4) < (m.d 2 4) ∧ 2 * m.lam ≤ (m.d 2 4) - (m.d 2 4) ∧ (m.d 2 4) - (m.d 2 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 2 4) ∨ (m.d 2 4) ≤ z)))
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
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x19 (m : N7Model)
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
    (h3391c : ((m.d 2 4) < (m.d 2 5) ∧ 2 * m.lam ≤ (m.d 2 5) - (m.d 2 4) ∧ (m.d 2 5) - (m.d 2 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 2 4) ∨ (m.d 2 5) ≤ z)))
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
  linarith only [h3239, hlam, p3391_0]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x20 (m : N7Model)
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
    (h3391c : ((m.d 2 5) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 2 5) ∧ (m.d 0 2) - (m.d 2 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 2 5) ∨ (m.d 0 2) ≤ z)))
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
  linarith only [h3227, hlam, p3391_0]

end R2N4
